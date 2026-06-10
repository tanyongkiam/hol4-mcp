#!/usr/bin/env python3
"""HOL4 MCP Server - provides theorem prover interaction tools.

Sessions are in-memory only. They survive within a single MCP server lifetime
(including across Claude context handoffs) but not across server restarts.
"""

import asyncio
import atexit
import hashlib
import json
import os
import re
import signal
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

from . import _mcp_cancel_patch  # noqa: F401 — patches mcp SDK on import
from fastmcp import FastMCP

from .hol_session import HOLSession, HOLDIR, escape_sml_string
from .hol_cursor import FileProofCursor, _try_find_json_line
from .hol_file_parser import (
    HOLParseError, step_line_numbers, format_steps, format_step_context,
    step_text_start,
)
from .quote_check import quote_diagnosis_lines


DEFAULT_MAX_OUTPUT = 4096

# Server-level tactic timeout (set via --tactic-timeout CLI flag or HOL_TACTIC_TIMEOUT env)
TACTIC_TIMEOUT = float(os.environ.get("HOL_TACTIC_TIMEOUT", "60.0"))


def _file_offset_to_line_col(file_offset: int, content: str) -> tuple[int, int]:
    """Convert a byte offset in file content to absolute (line, col), both 1-indexed."""
    before = content[:file_offset]
    line = before.count('\n') + 1
    last_nl = before.rfind('\n')
    col = file_offset - last_nl if last_nl >= 0 else file_offset + 1
    return line, col


def _auto_cheated_deps_lines(cursor) -> list[str]:
    """Lines naming dependencies auto-cheated during loading, with reasons.

    Auto-cheated deps silently weaken a per-theorem verification claim (the
    proof is checked against the dep's STATEMENT, not its proof), so outputs
    name each one and why it was cheated.
    """
    failed = getattr(cursor, "_failed_proofs", None)
    if not failed:
        return []
    deps = "; ".join(f"{name} ({reason})" for name, reason in failed.items())
    return ["", f"[auto-cheated deps: {deps}]"]


_PARSE_ERROR_RE = re.compile(r"parse|unknown character|lex", re.I)


def _quote_diagnosis_if_parse_error(file_path, error_text: str) -> list[str]:
    """On parse-flavoured errors, check the file for unmatched smart quotes.

    Unmatched U+2018/U+2019 (e.g. a pasted right-quote where an ASCII
    apostrophe belongs) are a recurring cause of opaque lexer errors.
    """
    if not error_text or not _PARSE_ERROR_RE.search(error_text):
        return []
    diag = quote_diagnosis_lines(file_path)
    return [""] + diag if diag else []


def _truncate_output(output: str, max_output: int, footer: str = "") -> str:
    """Truncate output to max_output bytes, showing tail.

    If footer is provided, it's appended AFTER truncation so it's never lost.
    """
    if max_output < 1:
        return f"ERROR: max_output must be positive (got {max_output})"
    # Reserve space for footer
    if footer:
        footer = "\n" + footer
        body_budget = max_output - len(footer)
        if body_budget < 100:
            # Not enough room — just show footer
            return footer.lstrip("\n")
        if len(output) > body_budget:
            return (
                f"[TRUNCATED: {len(output)} bytes, showing last {body_budget}]\n\n"
                + output[-body_budget:]
                + footer
            )
        return output + footer
    if len(output) > max_output:
        return f"[TRUNCATED: {len(output)} bytes, showing last {max_output}]\n\n{output[-max_output:]}"
    return output


@dataclass
class SessionEntry:
    """Registry entry for a HOL session."""
    session: HOLSession
    started: datetime
    workdir: Path
    last_used: float = 0.0  # time.time() of last activity
    cursor: Optional[FileProofCursor] = None
    holmake_env: Optional[dict] = None  # env vars for holmake (auto-captured on success)
    env: Optional[dict] = None  # env vars passed to HOL process

    def __post_init__(self):
        if self.last_used == 0.0:
            self.last_used = time.time()


mcp = FastMCP("hol", instructions="""HOL4 theorem prover - proof development workflow:

1. hol_state_at: Check proof state at cursor position (pass file= to auto-init)
2. Edit file directly, then hol_state_at to see new goals
3. Repeat until proof complete
4. holmake: Only at the end to verify the build

Information tools (prefer these over hol_send probes):
- hol_search(query=, pattern=): theorem database search (DB.find/DB.match)
- hol_goals(): goal count + headlines; n=k for one goal, n=k asm=j for one
  assumption — replaces top_goals() dumps and length(top_goals()) probes

hol_send is available for exploration and interactive proof attack — use it
freely. For replaying tactics in a script file, hol_state_at is preferred
because it handles checkpoints automatically.

Output notes:
- "[auto-cheated deps: ...]" names prefix theorems that failed/timed out at
  load and were replaced by cheat — the shown state/verification rests on
  their STATEMENTS only. Fix them before trusting an OK.
- A NOTE about a target "INSIDE step k" means the state shown is that
  opaque step's ENTRY; split the arm with `>- suspend` to navigate inside.

Guard rails (server-enforced):
- One HOL session at a time (RULE J): hol_start refuses a second concurrent
  session (force=True overrides); switching workdirs needs hol_stop first.
- hol_send rejects `val gs/fs/rw/simp/e/... = ...` shadow bindings.

Do NOT:
- Call hol_restart after file edits (state_at auto-detects changes)
""")
_sessions: dict[str, SessionEntry] = {}


def _sigint_handler(signum, frame):
    """Handle SIGINT by interrupting all HOL sessions.
    
    Called when pi sends SIGINT (e.g., user pressed ESC during tool execution).
    Interrupts all running HOL sessions to abort runaway tactics.
    
    Note: Takes a snapshot of sessions to avoid RuntimeError if dict is modified
    concurrently (e.g., session being added/removed when signal arrives).
    """
    # Snapshot to avoid "dictionary changed size during iteration"
    for entry in list(_sessions.values()):
        try:
            entry.session.interrupt()
        except Exception:
            pass  # Best effort - signal handlers must not raise


# Install SIGINT handler (replaces default KeyboardInterrupt behavior)
signal.signal(signal.SIGINT, _sigint_handler)


def _kill_all_sessions_sync():
    """Best-effort SIGKILL all HOL process groups. Safe from atexit/signal.

    Covers abnormal shutdown paths where async `hol_stop` won't run:
    - stdio_client's _terminate_process_tree sends SIGTERM to *our* pgid
      but HOL is in its own pgid (start_new_session=True in HOLSession).
    - atexit fires on normal interpreter shutdown.
    Without this, HOL children (multi-GB RSS) get reparented to PID 1 and leak.
    """
    for entry in list(_sessions.values()):
        try:
            entry.session.kill_sync()
        except Exception:
            pass  # best effort


def _sigterm_handler(signum, frame):
    """Kill HOL children, then re-raise default SIGTERM so we actually exit."""
    _kill_all_sessions_sync()
    signal.signal(signum, signal.SIG_DFL)
    os.kill(os.getpid(), signum)


signal.signal(signal.SIGTERM, _sigterm_handler)
atexit.register(_kill_all_sessions_sync)


_SESSION_IDLE_TIMEOUT = 1800  # 30 minutes
_PRUNE_INTERVAL = 300  # Check every 5 minutes at most
_last_prune_time = 0.0


def _gc_cursor_checkpoints(cursor: FileProofCursor):
    """Delete orphaned per-theorem checkpoint .save files from a dying cursor.

    Keeps base_deps.save and deps_only.save (expensive ~200MB rebuilds).
    Removes per-theorem context/end_of_proof saves (cheap to rebuild via replay).
    """
    ckpt_dir = cursor._checkpoint_dir
    if not ckpt_dir or not ckpt_dir.exists():
        return
    for f in ckpt_dir.glob("*_context.save"):
        f.unlink(missing_ok=True)
    for f in ckpt_dir.glob("*_end_of_proof.save"):
        f.unlink(missing_ok=True)
    try:
        ckpt_dir.rmdir()  # only removes if empty
    except OSError:
        pass


def _gc_dir_full(ckpt_dir: Path):
    """Remove all .save files and the checkpoint directory."""
    if not ckpt_dir or not ckpt_dir.exists():
        return
    for f in ckpt_dir.glob("*.save"):
        f.unlink(missing_ok=True)
    try:
        ckpt_dir.rmdir()
    except OSError:
        pass


def _gc_workdir_orphans(workdir: Path):
    """Clean orphaned per-theorem checkpoints from a workdir.

    Called on hol_start when no existing session owns the workdir.
    Deletes *_context.save and *_end_of_proof.save (cheap replay rebuilds)
    across all cursor_checkpoints/ dirs under the workdir.
    Keeps base_deps.save and deps_only.save (expensive ~200MB rebuilds).
    """
    for ckpt_dir in workdir.glob("**/cursor_checkpoints"):
        if not ckpt_dir.is_dir():
            continue
        for f in ckpt_dir.glob("*_context.save"):
            f.unlink(missing_ok=True)
        for f in ckpt_dir.glob("*_end_of_proof.save"):
            f.unlink(missing_ok=True)
        try:
            ckpt_dir.rmdir()
        except OSError:
            pass


async def _prune_idle_sessions():
    """Stop and remove sessions idle longer than _SESSION_IDLE_TIMEOUT.

    Throttled to run at most once per _PRUNE_INTERVAL seconds.
    """
    global _last_prune_time
    now = time.time()
    if now - _last_prune_time < _PRUNE_INTERVAL:
        return
    _last_prune_time = now
    to_prune = [
        name for name, entry in _sessions.items()
        if now - entry.last_used > _SESSION_IDLE_TIMEOUT
    ]
    for name in to_prune:
        entry = _sessions.get(name)
        if not entry:
            continue
        # Re-check: session may have been touched during a prior await
        if time.time() - entry.last_used <= _SESSION_IDLE_TIMEOUT:
            continue
        _sessions.pop(name, None)
        if entry.cursor:
            _gc_cursor_checkpoints(entry.cursor)
        await entry.session.stop()


_GC_CALL_INTERVAL = 10    # At most once per N tool calls
_GC_TIME_INTERVAL = 120   # At most once per K seconds
_gc_call_counter = 0
_gc_last_time = 0.0


async def _do_gc(session_name: str):
    """Actually run PolyML.fullGC(). Runs as background task."""
    entry = _sessions.get(session_name)
    if entry and entry.session.is_running:
        try:
            await entry.session.send('PolyML.fullGC();', timeout=10)
        except Exception:
            pass  # Best effort — don't crash on GC failure


def _schedule_gc(session_name: str):
    """Schedule background GC if due. Non-blocking — doesn't delay response.

    Triggers when both conditions met: N calls since last GC AND K seconds elapsed.
    """
    global _gc_call_counter, _gc_last_time
    _gc_call_counter += 1
    if _gc_call_counter < _GC_CALL_INTERVAL:
        return
    now = time.time()
    if now - _gc_last_time < _GC_TIME_INTERVAL:
        return
    _gc_call_counter = 0
    _gc_last_time = now
    asyncio.create_task(_do_gc(session_name))


async def _get_session(name: str) -> Optional[HOLSession]:
    """Get session from registry, or None if not found. Triggers idle pruning."""
    await _prune_idle_sessions()
    entry = _sessions.get(name)
    if entry:
        entry.last_used = time.time()
    return entry.session if entry else None


async def _get_cursor(name: str) -> Optional[FileProofCursor]:
    """Get cursor from registry, or None if not found. Triggers idle pruning."""
    await _prune_idle_sessions()
    entry = _sessions.get(name)
    if entry:
        entry.last_used = time.time()
    return entry.cursor if entry else None


def _session_age(name: str) -> str:
    """Get human-readable session age."""
    entry = _sessions.get(name)
    if not entry:
        return "unknown"
    started = entry.started
    delta = datetime.now() - started
    secs = int(delta.total_seconds())
    if secs < 60:
        return f"{secs}s"
    elif secs < 3600:
        return f"{secs // 60}m"
    else:
        return f"{secs / 3600:.1f}h"


@mcp.tool()
async def hol_start(workdir: str, name: str = "default", env: dict = None,
                    force: bool = False) -> str:
    """Start a HOL4 REPL session.

    Idempotent - returns existing session if already running.
    Usually called automatically by hol_state_at (via file= parameter).

    Refuses to start a SECOND concurrent session (RULE J: one session at a
    time — a second session can resolve bare theorem names against a built
    ancestor's old version and falsely pass). Pass force=True to override.

    Args:
        workdir: Working directory (should contain Holmakefile for dependencies)
        name: Session identifier (e.g., "main")
        env: Optional environment variables (e.g. {"VFMDIR": "/path/to/vfm"})
        force: Allow a second concurrent session despite RULE J (default False)

    Returns: Session status
    """
    await _prune_idle_sessions()
    # If session exists and is running, return its state
    if name in _sessions:
        session = _sessions[name].session
        if session.is_running:
            goals = await session.send("top_goals();", timeout=10)
            return f"Session '{name}' already running.\n\n=== Goals ===\n{goals}"
        # Dead session - clean up
        del _sessions[name]

    # RULE J: one HOL session at a time. A second concurrent session resolves
    # bare theorem names against stale built ancestors and can falsely pass.
    others = [
        (n, e) for n, e in _sessions.items()
        if n != name and e.session.is_running
    ]
    if others and not force:
        listing = "\n".join(
            f"  {n}  (workdir {e.workdir})" for n, e in others
        )
        return (
            f"ERROR: refusing to start session '{name}' — other HOL "
            f"session(s) already running:\n{listing}\n"
            f"RULE J: one session at a time; a second session can resolve "
            f"bare theorem names\nagainst stale built ancestors and falsely "
            f"pass. Stop the other session\n(hol_stop(session=...)) or pass "
            f"force=True if you really need both."
        )

    # Validate workdir
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Working directory does not exist: {workdir}"

    # Create session with optional env
    session = HOLSession(str(workdir_path), env=env)

    try:
        result = await session.start()
    except Exception as e:
        return f"ERROR starting HOL: {e}"

    if not session.is_running:
        return f"ERROR: HOL failed to start. Output: {result}"

    # Register session. Handle concurrent hol_start(name=...) calls:
    # if another caller already registered a running session, stop this one
    # and return the existing session state.
    existing = _sessions.get(name)
    if existing and existing.session.is_running:
        await session.stop()
        goals = await existing.session.send("top_goals();", timeout=10)
        return f"Session '{name}' already running.\n\n=== Goals ===\n{goals}"

    _sessions[name] = SessionEntry(session, datetime.now(), workdir_path, env=env)

    # Clean orphaned per-theorem checkpoints left by previous server lifetimes
    _gc_workdir_orphans(workdir_path)

    return f"Session '{name}' started. {result}\nWorkdir: {workdir_path}"


@mcp.tool()
async def hol_sessions() -> str:
    """List all active HOL sessions with their workdir, age, status, cursor."""
    await _prune_idle_sessions()
    if not _sessions:
        return "No active sessions."

    lines = ["SESSION      WORKDIR                                    AGE     IDLE    STATUS   CURSOR"]
    lines.append("-" * 105)

    now = time.time()
    for name, entry in _sessions.items():
        status = "running" if entry.session.is_running else "dead"
        age = _session_age(name)
        idle_secs = int(now - entry.last_used)
        if idle_secs < 60:
            idle_str = f"{idle_secs}s"
        elif idle_secs < 3600:
            idle_str = f"{idle_secs // 60}m"
        else:
            idle_str = f"{idle_secs / 3600:.1f}h"
        workdir_str = str(entry.workdir)
        if len(workdir_str) > 40:
            workdir_str = "..." + workdir_str[-37:]

        # Cursor info
        if entry.cursor:
            cs = entry.cursor.status
            cursor_str = f"{cs['active_theorem']}" if cs['active_theorem'] else "(none)"
        else:
            cursor_str = "(none)"

        lines.append(f"{name:<12} {workdir_str:<42} {age:<7} {idle_str:<7} {status:<8} {cursor_str}")

    return "\n".join(lines)


_PROOF_STATE_PATTERNS = []


# Commands that may mutate the live proofManager / goal stack. A hol_send of any
# of these desyncs hol_state_at's position cache (its `reused` fast path returns
# the live goal without re-establishing it). When matched, we taint the session's
# cursor so the NEXT hol_state_at re-establishes the goal via checkpoint/replay
# (cheap — current theorem only, prefix checkpoints untouched) instead of reusing
# the polluted state. Errs toward over-matching: a false positive only costs one
# cheap re-setup; a false negative reintroduces the silent-desync bug.
_PROOFMGR_MUTATING_RE = re.compile(
    r'\b(?:'
    r'drop_all|backup_n|new_goalstack'
    r'|set_goal|set_goalfrag|set_suspended_goal|set_resume_goalfrag\w*'
    r'|verify_resume\w*|run_resume\w*|verify_core'
    r'|markerLib\.resume|bossLib\.sg'
    r'|proofManagerLib\.(?:e|b|r|g|gf|ef|eall|ee|expand|expandf|expand_list'
    r'|expand_frag|rotate|restart|drop|dropn|backup|add|split)'
    r')\b'
    # bare top-level proof drivers (tactic_prefix shadows e/expand/ef at top level)
    r'|(?<![\w.])(?:e|ef|expand|expandf|expand_list|sg|g|gf|b|r)\s*[(`]'
)


def _command_mutates_proof_state(command: str) -> bool:
    return _PROOFMGR_MUTATING_RE.search(command) is not None


# `val gs = ...` etc. shadows a HOL primitive/tactic for the REST of the
# session — later tactics and probes using the name silently misbehave.
_SHADOW_BINDING_RE = re.compile(
    r'\bval\s+(gs|fs|rw|simp|e|b|g|it|concl|hyp|dest_thm|tag|aconv|drop)\s*='
)


def _check_shadow_binding(command: str) -> str | None:
    """Reject hol_send commands that shadow HOL primitives. None if allowed."""
    m = _SHADOW_BINDING_RE.search(command)
    if not m:
        return None
    nm = m.group(1)
    return (
        f"ERROR: hol_send BLOCKED — `val {nm} = ...` shadows the HOL4 "
        f"primitive/tactic `{nm}` for the rest of the session; later tactics "
        f"and probes that use `{nm}` will silently misbehave.\n"
        f"Bind a prefixed name instead, e.g. `val my_{nm} = ...`."
    )


def _check_proof_state_command(command: str) -> str | None:
    """Block hol_send commands that interact with proof state.

    Returns an error message if blocked, None if allowed.
    """
    cmd = command.strip()
    for pattern, name in _PROOF_STATE_PATTERNS:
        if pattern.search(cmd):
            return (
                f"ERROR: hol_send BLOCKED — '{name}' interacts with proof state.\n"
                f"\n"
                f"hol_send must ONLY be used for read-only queries:\n"
                f"  DB.match, DB.find, type_of, EVAL, printing theorems\n"
                f"\n"
                f"For proof development, use:\n"
                f"  hol_state_at(line, col) — navigate to position, see goals\n"
                f"  Edit tool — modify tactics in the file\n"
                f"  hol_check_proof — validate complete proofs\n"
            )
    return None


@mcp.tool()
async def hol_send(command: str, timeout: int = 5, max_output: int = DEFAULT_MAX_OUTPUT, session: str = "default") -> str:
    """Send raw SML command to HOL session.

    Use freely for exploration and interactive proof attack — try tactic
    chains, inspect terms, check rewrites, evaluate expressions, query the
    database. Persist successful chains back into the script file once they
    work.

    For navigating an existing script file (replaying tactics from theorem
    start to a position), prefer hol_state_at — it handles file changes,
    checkpoints, and tactic replay automatically. For goal counts/slices use
    hol_goals; for DB searches use hol_search. hol_send is the right tool
    for everything else, including stepping through partial tactics ad hoc.

    Rejected mechanically: `val gs/fs/rw/simp/e/b/g/it/concl/hyp/dest_thm/
    tag/aconv/drop = ...` (shadows a HOL primitive for the rest of the
    session — bind a prefixed name like `val my_gs = ...` instead).

    Args:
        command: SML command to execute
        session: Session name (default: "default")
        timeout: Max seconds to wait (default 5, max 600)
        max_output: Max bytes of output to return (default 4096).
                    Shows tail when truncated (errors/results come after echoed input).

    Returns: HOL output (may include errors), truncated if exceeds max_output
    """
    blocked = _check_proof_state_command(command)
    if blocked:
        return blocked

    blocked = _check_shadow_binding(command)
    if blocked:
        return blocked

    s = await _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."

    # Validate timeout
    if timeout < 1:
        timeout = 1
    elif timeout > 600:
        timeout = 600

    t0 = time.monotonic()
    result = await s.send(command, timeout=timeout)
    elapsed = time.monotonic() - t0

    # If this command may have mutated the live proofManager, taint the cursor so
    # the next hol_state_at re-establishes its goal instead of reusing the now-
    # desynced cached position (see _PROOFMGR_MUTATING_RE).
    if _command_mutates_proof_state(command):
        entry = _sessions.get(session)
        if entry and entry.cursor:
            entry.cursor._session_dirty = True

    _schedule_gc(session)
    timing = f"\n[{elapsed:.3f}s]"
    return _truncate_output(result, max_output, footer=timing)


@mcp.tool()
async def hol_search(
    query: str = None,
    pattern: str = None,
    theory: str = None,
    limit: int = 10,
    max_statement: int = 200,
    session: str = "default",
) -> str:
    """Search the theorem database by name and/or term pattern.

    First-class replacement for hol_send DB.find/DB.match probes: results
    come back as a compact `theory.name` + truncated-statement table.

    Args:
        query: Case-insensitive substring of the theorem name (DB.find).
        pattern: Term pattern, e.g. "MEM _ (MAP _ _)" (DB.match). When both
                 query and pattern are given, results must match both.
        theory: Restrict results to one theory (e.g. "list").
        limit: Max results shown (default 10; total count always reported).
        max_statement: Truncate each statement to this many chars (default 200).
        session: Session name (default: "default")

    Returns: Matching theorems with statements, or an error.
    """
    if not query and not pattern:
        return ("ERROR: provide query= (name substring) and/or "
                "pattern= (term pattern).")
    s = await _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."
    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."

    cmd = (
        f'db_search_json "{escape_sml_string(query or "")}" '
        f'"{escape_sml_string(pattern or "")}" '
        f'"{escape_sml_string(theory or "")}" {int(limit)};'
    )
    output = await s.send(cmd, timeout=30)
    data = _try_find_json_line(output)
    if 'err' in data:
        return f"ERROR: {data['err']}"
    if 'ok' not in data:
        return f"ERROR: unexpected db_search_json output: {output[:300]}"

    total = data['ok'].get('total', 0)
    results = data['ok'].get('results', [])
    if total == 0:
        return "No matches."
    header = f"{total} match(es)"
    if total > len(results):
        header += f", showing first {len(results)} (raise limit= for more)"
    lines = [header + ":"]
    for r in results:
        stmt = " ".join(str(r.get('statement', '')).split())
        if len(stmt) > max_statement:
            stmt = stmt[:max_statement] + " …"
        lines.append(f"{r.get('theory')}.{r.get('name')}")
        lines.append(f"  {stmt}")
    _schedule_gc(session)
    return "\n".join(lines)


@mcp.tool()
async def hol_goals(
    n: int = None,
    asm: int = None,
    max_term: int = 300,
    file: str = None,
    line: int = None,
    col: int = 1,
    workdir: str = None,
    session: str = "default",
) -> str:
    """Goal count and structured goal slices, without a full top_goals() dump.

    Default: goal count plus a one-line headline per goal (truncated
    conclusion, assumption count). Drill down with n= and asm=.

    Args:
        n: Show goal n (1-based, 1 = top goal) with numbered assumptions.
        asm: With n, show assumption asm (1-based) of that goal in full.
        max_term: Truncate each shown term to this many chars (default 300).
        file: Script file — navigates like hol_state_at before reading goals
              (auto-inits the cursor when needed).
        line: With file (or an active cursor), position to navigate to first.
              Without line, reads the LIVE session goal state (works for
              hol_send-driven goals too).
        col: 1-indexed column for line (default 1).
        workdir: Working directory for HOL (used with file).
        session: Session name (default: "default")

    Returns: Goal count + headlines, one goal, or one assumption.
    """
    cursor = await _get_cursor(session)

    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if line is not None:
        if not cursor:
            return (f"ERROR: No cursor for session '{session}'. "
                    f"Pass file= to auto-init.")
        result = await cursor.state_at(line, col)
        if result.error and not result.goals:
            return f"ERROR: {result.error}"
        goals = result.goals
        origin = f"at line {line}"
    else:
        s = await _get_session(session)
        if not s:
            return f"ERROR: Session '{session}' not found. Use hol_sessions() to list available sessions."
        if not s.is_running:
            del _sessions[session]
            return f"ERROR: Session '{session}' died. Use hol_start() to create a new session."
        output = await s.send('goals_json();', timeout=10)
        data = _try_find_json_line(output)
        if 'err' in data:
            return f"No live proof: {data['err']}"
        if 'ok' not in data:
            return f"ERROR: unexpected goals_json output: {output[:300]}"
        goals = [
            g if isinstance(g, dict) and 'goal' in g
            else {"asms": [], "goal": str(g)}
            for g in data['ok']
        ]
        origin = "live session"

    _schedule_gc(session)

    def trunc(s: str, limit: int, flatten: bool = True) -> str:
        if flatten:
            s = " ".join(s.split())
        if len(s) > limit:
            return s[:limit] + f" … [{len(s)} chars total]"
        return s

    if not goals:
        return f"0 goals ({origin}) — proof complete."

    if n is None:
        lines = [f"{len(goals)} goal(s) ({origin}, goal 1 = top):"]
        for i, g in enumerate(goals, start=1):
            asms = g.get('asms', [])
            lines.append(f"{i}: [{len(asms)} asm] {trunc(g['goal'], max_term)}")
        if any(g.get('asms') for g in goals):
            lines.append("Use n=k for goal k's assumptions; n=k, asm=j for one in full.")
        return "\n".join(lines)

    if n < 1 or n > len(goals):
        return f"ERROR: n={n} out of range (1..{len(goals)})"
    g = goals[n - 1]
    asms = g.get('asms', [])

    if asm is not None:
        if asm < 1 or asm > len(asms):
            return (f"ERROR: asm={asm} out of range "
                    f"(goal {n} has {len(asms)} assumptions)")
        return f"Goal {n} assumption {asm}:\n{asms[asm - 1]}"

    lines = [f"Goal {n} of {len(goals)} ({len(asms)} asm):"]
    for j, a in enumerate(asms, start=1):
        lines.append(f"  asm {j}: {trunc(a, max_term)}")
    if asms:
        lines.append("  " + "-" * 40)
    lines.append(f"  {trunc(g['goal'], max_term, flatten=False)}")
    return "\n".join(lines)


@mcp.tool()
async def hol_interrupt(session: str = "default") -> str:
    """Send SIGINT to abort runaway tactic.

    Args:
        session: Session name (default: "default")

    Returns: Confirmation message
    """
    s = await _get_session(session)
    if not s:
        return f"ERROR: Session '{session}' not found."

    if not s.is_running:
        del _sessions[session]
        return f"ERROR: Session '{session}' died."

    s.interrupt()

    # Flush interrupt message by sending dummy command
    # HOL queues "Compilation interrupted" which pollutes next send() otherwise
    await asyncio.sleep(0.1)
    await s.send(";", timeout=1)

    return f"Sent SIGINT to session '{session}'. The tactic should be interrupted."


@mcp.tool()
async def hol_stop(session: str = "default") -> str:
    """Terminate HOL session.

    Args:
        session: Session name (default: "default")

    Returns: Confirmation message
    """
    entry = _sessions.get(session)
    if entry:
        if entry.cursor:
            _gc_cursor_checkpoints(entry.cursor)
        await entry.session.stop()
        del _sessions[session]
        return f"Session '{session}' stopped."
    return f"Session '{session}' not found."


@mcp.tool()
async def hol_restart(session: str = "default") -> str:
    """Restart HOL session (stop + start, preserves workdir).

    Only needed when:
    - HOL state is corrupted (rare)
    - Upstream dependencies changed (edited other .sml files that need Holmake)

    NOT needed for edits to current proof file - state_at auto-detects changes.

    Args:
        session: Session name to restart

    Returns: Same as hol_start (cursor is cleared, use hol_state_at file= to re-init)
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found."

    workdir = entry.workdir
    env = entry.env  # Preserve env through restart
    await hol_stop(session)
    return await hol_start(workdir=str(workdir), name=session, env=env)


@mcp.tool()
async def hol_setenv(env: dict, session: str = "default") -> str:
    """Set environment variables for a HOL session and auto-restart to apply.

    These are passed to the HOL process and affect Holmakefile INCLUDES expansion.

    Example: hol_setenv({"VFMDIR": "/home/user/verifereum"})

    Args:
        env: Environment variables to set (merged with existing)
        session: Session name (default: "default")

    Returns: Confirmation message (includes restart output if session was running)
    """
    entry = _sessions.get(session)
    if not entry:
        return f"Session '{session}' not found. Use hol_start first."

    # Merge with existing env
    if entry.env:
        entry.env.update(env)
    else:
        entry.env = env

    # Auto-restart to apply new env to running process
    if entry.session.is_running:
        restart_result = await hol_restart(session)
        return f"Environment updated and session restarted: {env}\n{restart_result}"

    return f"Environment updated for session '{session}': {env}"


async def _kill_process_group(proc):
    """Kill process group: SIGTERM, wait, SIGKILL if needed.

    Must kill even if parent exited - children (buildheap) may still be alive.
    """
    if proc is None:
        return

    pgid = proc.pid

    # Send SIGTERM to the whole process group
    try:
        os.killpg(pgid, signal.SIGTERM)
    except OSError:
        return  # Process group doesn't exist

    # Wait for processes to die gracefully (up to 1s)
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=1.0)
        except (asyncio.TimeoutError, asyncio.CancelledError):
            pass
    else:
        # Parent already exited, give children time to die from SIGTERM
        try:
            await asyncio.sleep(1.0)
        except asyncio.CancelledError:
            pass  # Still need to SIGKILL

    # SIGKILL anything remaining in the group
    try:
        os.killpg(pgid, signal.SIGKILL)
    except OSError:
        pass  # Already gone

    # Reap parent if needed
    if proc.returncode is None:
        try:
            await asyncio.wait_for(proc.wait(), timeout=0.5)
        except:
            pass


# Progress reporting interval for long builds (resets MCP client timeout)
_PROGRESS_INTERVAL = 10  # seconds


@mcp.tool()
async def holmake(workdir: str, target: str = None, env: dict = None, log_limit: int = 1024, timeout: int = 90, heap_size: int = 12288, jobs: int = None) -> str:
    """Run Holmake --qof in directory.

    Args:
        workdir: Directory containing Holmakefile
        target: Optional specific target to build
        env: Optional environment variables (e.g. {"MY_VAR": "/some/path"})
        log_limit: Max bytes per log file to include on failure (default 1024)
        timeout: Max seconds to wait (default 90, max 1800)
        heap_size: Max heap size in MB for Poly/ML builds (default 12288)
        jobs: Max parallel jobs (-j flag). Default from HOL4_MCP_HOLMAKE_JOBS env var, or 1.

    Returns: Holmake output (stdout + stderr). On failure, includes recent build logs.
    """
    # Validate limits
    timeout = max(1, min(timeout, 1800))
    heap_size = max(256, heap_size)
    workdir_path = Path(workdir).resolve()
    if not workdir_path.exists():
        return f"ERROR: Directory does not exist: {workdir}"

    holmake_bin = HOLDIR / "bin" / "Holmake"
    if not holmake_bin.exists():
        return f"ERROR: Holmake not found at {holmake_bin}"

    logs_dir = workdir_path / ".hol" / "logs"

    # Delete all prior logs so only this run's logs exist afterward.
    # Holmake only truncates a target's log when that target's job starts,
    # so stale logs from prior runs would otherwise persist for any target
    # not reached (e.g. due to timeout or dependency failure).
    if logs_dir.exists():
        for log_file in logs_dir.iterdir():
            if log_file.is_file():
                log_file.unlink()

    # Resolve parallelism: explicit param > env var > 1
    if jobs is None:
        jobs = int(os.environ.get("HOL4_MCP_HOLMAKE_JOBS", "1"))
    jobs = max(1, jobs)

    cmd = [str(holmake_bin), "--qof", f"--heap-size={heap_size}"]
    if jobs > 1:
        cmd.extend(["-j", str(jobs)])
    if target:
        cmd.append(target)

    # Build environment
    proc_env = os.environ.copy()
    if env:
        proc_env.update(env)

    proc = None
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            cwd=workdir_path,
            env=proc_env,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
            start_new_session=True,
        )

        # Poll stdout. Progress notifications were removed: a notification
        # in flight when the response is emitted races on the wire and the
        # client tears down the stdio transport on the late progressToken.
        start_time = time.time()
        stdout_chunks = []
        timed_out = False

        while True:
            elapsed = time.time() - start_time
            if elapsed >= timeout:
                timed_out = True
                break

            try:
                chunk = await asyncio.wait_for(
                    proc.stdout.read(4096),
                    timeout=min(_PROGRESS_INTERVAL, timeout - elapsed)
                )
                if chunk:
                    stdout_chunks.append(chunk)
                else:
                    # EOF - wait for process to finish
                    try:
                        await asyncio.wait_for(proc.wait(), timeout=5)
                    except asyncio.TimeoutError:
                        pass
                    break
            except asyncio.TimeoutError:
                # Check if process finished
                if proc.returncode is not None:
                    break
                continue  # Keep polling

        wall = time.time() - start_time

        if timed_out:
            return f"ERROR: Build timed out after {timeout}s."

        output = b''.join(stdout_chunks).decode("utf-8", errors="replace")

        if proc.returncode == 0:
            result = f"Build succeeded.\n\n{output}"
            if env:
                # Store env in matching session entries for auto-holmake at startup
                for entry in _sessions.values():
                    if entry.workdir == workdir_path:
                        entry.holmake_env = env
                # Include env in output for caller to capture if needed
                result += f"\nHOLMAKE_ENV: {json.dumps(env)}"
            return f"{result}\n[{wall:.1f}s]"

        # Build failed - append relevant logs (all logs are from this run)
        result = f"Build failed (exit code {proc.returncode}).\n\n{output}"

        if logs_dir.exists():
            logs = sorted(
                [f for f in logs_dir.iterdir() if f.is_file()],
                key=lambda f: -f.stat().st_mtime
            )
            if logs:
                result += "\n\n=== Build Logs ===\n"
                for log_file in logs[:3]:
                    content = log_file.read_text(errors="replace")
                    if len(content) > log_limit:
                        content = f"...(truncated, showing last {log_limit} bytes)...\n" + content[-log_limit:]
                    result += f"\n--- {log_file.name} ---\n{content}\n"

        return f"{result}\n[{wall:.1f}s]"

    except Exception as e:
        return f"ERROR: {e}"
    finally:
        await _kill_process_group(proc)


@mcp.tool()
async def hol_log(workdir: str, theory: str, limit: int = 1024) -> str:
    """Read build log for a specific theory.

    Use after holmake to inspect warnings or errors in detail.

    Args:
        workdir: Directory containing .hol/logs/
        theory: Theory name (e.g., "fooTheory")
        limit: Max bytes to return (default 1024, 0 for unlimited)

    Returns: Log file contents (tail if truncated).
    """
    workdir_path = Path(workdir).resolve()
    log_file = workdir_path / ".hol" / "logs" / theory

    if not log_file.exists():
        # Try without "Theory" suffix
        log_file = workdir_path / ".hol" / "logs" / f"{theory}Theory"
        if not log_file.exists():
            available = []
            logs_dir = workdir_path / ".hol" / "logs"
            if logs_dir.exists():
                available = [f.name for f in logs_dir.iterdir() if f.is_file()]
            if available:
                return f"Log not found: {theory}\nAvailable: {', '.join(sorted(available))}"
            return f"Log not found: {theory}\nNo logs in {logs_dir}"

    content = log_file.read_text(errors="replace")
    if limit > 0 and len(content) > limit:
        return f"...(truncated, showing last {limit} bytes)...\n{content[-limit:]}"
    return content


@mcp.tool()
async def hol_logs(workdir: str) -> str:
    """List available build logs.

    Args:
        workdir: Directory containing .hol/logs/

    Returns: List of log files with sizes and modification times
    """
    workdir_path = Path(workdir).resolve()
    logs_dir = workdir_path / ".hol" / "logs"

    if not logs_dir.exists():
        return f"No logs directory: {logs_dir}"

    logs = []
    for log_file in sorted(logs_dir.iterdir()):
        if log_file.is_file():
            stat = log_file.stat()
            size = stat.st_size
            mtime = datetime.fromtimestamp(stat.st_mtime).strftime("%H:%M:%S")
            logs.append(f"  {log_file.name}: {size} bytes, modified {mtime}")

    if not logs:
        return "No log files found."
    return "Build logs:\n" + "\n".join(logs)


# =============================================================================
# Cursor Tools (for multi-theorem files)
# =============================================================================


async def _init_file_cursor(
    file: str,
    session: str = "default",
    workdir: str = None,
) -> str:
    """Initialize cursor for a HOL4 script file (internal helper).

    Parses file for theorems and their proofs. Auto-starts HOL session if needed.
    After init, use hol_state_at to navigate to specific positions and see goals.

    Args:
        file: Path to *Script.sml file containing theorems
        session: Session name (default: "default")
        workdir: Working directory for HOL (default: file's parent directory)

    Returns: List of theorems with line numbers and cheat status
    """
    # Validate file first
    file_path = Path(file).resolve()
    if not file_path.exists():
        return f"ERROR: File not found: {file}"

    # Determine target workdir
    target_workdir = Path(workdir).resolve() if workdir else file_path.parent

    # Auto-start or restart session if workdir changed or file content changed
    s = await _get_session(session)
    entry = _sessions.get(session)

    if s and s.is_running:
        # Workdir mismatch: refuse instead of silently rebasing the session
        # (RULE J trap: a session mid-proof in clone A, a file= from clone B —
        # the old silent restart destroyed open suspensions/loaded context).
        if entry and entry.workdir != target_workdir:
            return (
                f"ERROR: session '{session}' is bound to workdir "
                f"{entry.workdir},\nbut {file_path} resolves to workdir "
                f"{target_workdir}.\n"
                f"RULE J: one session per workdir/theory — switching "
                f"workdirs mid-session would\nsilently drop the session's "
                f"loaded context and open suspensions.\n"
                f"Stop it first (hol_stop(session='{session}')) and re-run "
                f"with file= to re-init\ninto the new workdir."
            )
        # Check if file content changed - session has stale definitions
        if entry and entry.cursor:
            old_cursor = entry.cursor
            if Path(old_cursor.file).resolve() == file_path:
                # Same file - check if content changed
                old_hash = old_cursor._content_hash
                new_content = file_path.read_text()
                new_hash = hashlib.sha256(new_content.encode()).hexdigest()
                if old_hash and new_hash != old_hash:
                    # File changed - restart session to clear stale definitions
                    await hol_stop(session)
                    s = None

    if not s or not s.is_running:
        # Preserve per-session HOL env (e.g., VFMDIR) across auto-restarts.
        start_env = entry.env if entry else None
        start_result = await hol_start(workdir=str(target_workdir), name=session, env=start_env)
        if start_result.startswith("ERROR"):
            return start_result
        s = await _get_session(session)

    # GC stale per-theorem checkpoints from old cursor before replacing
    if entry and entry.cursor:
        _gc_cursor_checkpoints(entry.cursor)

    t0 = time.perf_counter()
    
    cursor = FileProofCursor(file_path, s, tactic_timeout=TACTIC_TIMEOUT)
    result = await cursor.init()
    
    init_time = time.perf_counter() - t0

    _sessions[session].cursor = cursor

    if result.get("error"):
        err_lines = [f"ERROR: {result['error']}"]
        err_lines.extend(
            _quote_diagnosis_if_parse_error(file_path, result['error'])
        )
        return "\n".join(err_lines)

    # Build status output
    lines = [
        f"File: {file_path}",
        f"Theorems: {len(result['theorems'])} ({len(result['cheats'])} cheats)",
    ]

    if result['cheats']:
        lines.append("")
        lines.append("Cheats to fix:")
        for cheat in result['cheats']:
            lines.append(f"  {cheat['theorem']} (line {cheat['line']})")

    lines.append("")
    lines.append(f"[Init time: {init_time*1000:.0f}ms]")

    return "\n".join(lines)


@mcp.tool()
async def hol_state_at(
    line: int,
    col: int = 1,
    file: str = None,
    workdir: str = None,
    max_output: int = DEFAULT_MAX_OUTPUT,
    session: str = "default",
    show_partial: bool = False,
    all_goals: bool = False,
    context_before: int = 0,
    context_after: int = 0,
) -> str:
    """Get proof state at a file position.

    Replays tactics from theorem start up to (but not including) the tactic at
    the given position, then shows current goals. Auto-enters theorem if needed.

    By default only the top goal is shown (with total count). Set all_goals=True
    to see every goal on the stack.

    If replay fails before reaching the requested position, the default behavior
    is to refuse to show goals (they would be from the wrong proof state).
    Set show_partial=True to see the best-effort goals anyway.

    Args:
        line: 1-indexed line number (position in the proof)
        col: 1-indexed column number (default 1)
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        max_output: Max bytes of output (default 1000)
        session: Session name (default: "default")
        show_partial: If True, show best-effort goals even when replay fails
                      before reaching the requested position (default: False)
        all_goals: If True, show all goals; otherwise only the top goal (default: False)
        context_before: On PROOF BROKEN, number of source lines before the failure
                       to include in the step plan context (default: 0, off).
                       The failing step is always shown; this adds steps whose
                       source positions fall within the line range.
        context_after: On PROOF BROKEN, number of source lines after the failure
                      to include in the step plan context (default: 0, off).
                      Both default to 0 (only failing step shown); pass e.g. 3
                      for surrounding context.

    When a proof is broken, the failing step's text is always shown.
    With context_before/context_after > 0, a "=== Steps around failure ===" section
    shows step plan entries whose source lines fall within the requested range,
    indented by nesting depth.
    Each step's text depends on its kind:
      - expand: the tactic text itself (e.g. strip_tac, simp[], Induct_on `x`)
      - open: the goalFrag function name (open_then1, open_by) — marks start of >- / by
      - mid: the goalFrag function name (then2, then3) — marks additional >- branches
      - close: close_paren — marks end of a >- / by group
    The failing step is marked with "<-- FAILED" in the steps section.

    Diagnostic lines to read, not ignore:
      - "[auto-cheated deps: name (reason); ...]" — prefix theorems that
        failed/timed out at load were replaced by cheat; the state shown
        rests on their STATEMENTS only. Verify them before trusting an OK.
      - "NOTE: target line N is INSIDE step k ..." — the position is inside
        one opaque (lumped/parenthesized) step; the state shown is that
        step's ENTRY, not the state at line N. Split the arm with
        `>- suspend` to navigate inside.
      - "TIMEOUT: step k (lines A-B) ..." — the failing step's source span;
        split it with `>- suspend` or raise the per-tactic timeout.
      - "Ancestor chain for suspension '...'" — a Resume's label was missing;
        the chain names the first broken ancestor to fix.
      - "unmatched smart quote at line L col C" — likely cause of a parse
        error; fix with the printed command.

    Returns: Proof position, goals at that position, errors if any
    """
    cursor = await _get_cursor(session)

    # Auto-init if file provided and no cursor (or different file)
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    result = await cursor.state_at(line, col)
    active_theorem = cursor._active_theorem
    thm = cursor._get_theorem(active_theorem) if active_theorem else None

    # Helper to convert tactic index to absolute line:col
    def tactic_to_loc(idx):
        if not thm:
            return None
        if not thm.proof_body or idx <= 0:
            # Start of proof body content (accounts for stripped whitespace)
            return _file_offset_to_line_col(thm.proof_body_offset, cursor._content)
        if idx > len(cursor._step_plan):
            idx = len(cursor._step_plan)
        if idx > 0:
            step = cursor._step_plan[idx - 1]
            file_pos = thm.proof_body_offset + step.end
            return _file_offset_to_line_col(file_pos, cursor._content)
        return _file_offset_to_line_col(thm.proof_body_offset, cursor._content)

    lines = []
    error_footer = ""  # Errors go in footer so truncation never hides them
    
    # Check if "no goals" error is actually success (proof complete)
    is_proof_complete = (
        result.error and 
        "no goals" in result.error.lower() and
        result.tactics_replayed == result.tactics_total and
        not result.goals
    )
    
    # Structural error (not in theorem, etc.) - no goals to show
    if result.error and result.tactics_total == 0:
        lines.append(f"ERROR: {result.error}")
        lines.extend(_quote_diagnosis_if_parse_error(cursor.file, result.error))
        return "\n".join(lines)

    # Detect broken proof: replay couldn't reach the requested position
    is_broken = (
        result.error
        and not is_proof_complete
        and result.tactics_replayed < result.tactic_idx
    )

    # Show theorem name (useful for hol_check_proof after edits)
    if active_theorem:
        lines.append(f"Theorem: {active_theorem}")
    
    if is_broken:
        # Proof is broken before the requested position.
        stuck_loc = tactic_to_loc(result.tactics_replayed)
        stuck_str = f"line {stuck_loc[0]} col {stuck_loc[1]}" if stuck_loc else ""
        # 0-indexed: the step the replay could not get past.
        fail_idx = result.tactics_replayed
        fail_loc = tactic_to_loc(fail_idx)          # START of that step
        fail_end_loc = tactic_to_loc(fail_idx + 1)  # END of that step
        fail_str = f"line {fail_loc[0]} col {fail_loc[1]}" if fail_loc else ""

        step_plan = cursor._step_plan if cursor else []
        fail_step = step_plan[fail_idx] if 0 <= fail_idx < len(step_plan) else None

        # An opaque leaf step (`expand`/`expand_list`) that spans MULTIPLE source
        # lines cannot be inspected inside: the real failure is somewhere within
        # its line range, NOT at its first line. This is common when a `\\`-chain
        # feeds a `>- (parenthesized arm)` / `>|` / other goal-positional
        # combinator — the step decomposer (reexpand_group_atoms) keeps the whole
        # construct as one opaque Group, swallowing the chain that precedes it.
        # Report the RANGE honestly instead of pinning (and blaming) the start line.
        opaque_multiline = (
            fail_step is not None
            and fail_step.kind in ("expand", "expand_list")
            and fail_loc is not None and fail_end_loc is not None
            and fail_end_loc[0] > fail_loc[0]
        )

        if opaque_multiline:
            range_str = f"lines {fail_loc[0]}-{fail_end_loc[0]}"
            fail_str = range_str  # footer uses this too
            lines.append(f"PROOF BROKEN somewhere in the opaque step at {range_str}")
            lines.append(
                f"ERROR: the failing step is a SINGLE opaque tactic spanning "
                f"{range_str}; the replay cannot localize WHERE inside it the "
                f"failure is — the line shown is the step's START, not the "
                f"failure. (Cause: a `\\\\`-chain feeding a `>- (parenthesized "
                f"arm)` / `>|` / similar goal-positional combinator is kept opaque "
                f"by the step decomposer, swallowing the whole preceding chain.)"
            )
            lines.append("")
            lines.append(
                f"To localize: put `\\\\ cheat` partway through {range_str} and move "
                f"it until the proof passes — the failure is in the last region the "
                f"cheat covered. Or split the `>-`/`>|` arm into a Suspend/Resume so "
                f"each piece is navigable. The goal shown below is the state "
                f"ENTERING this opaque step, not the failure point."
            )
            if thm:
                s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
                lines.extend(format_step_context(
                    step_plan, fail_idx, s_lines,
                    context_before=context_before, context_after=context_after,
                ))
        else:
            lines.append(f"PROOF BROKEN at {fail_str}")

            # Step plan context shows which tactic failed — raw Poly/ML error is redundant
            lines.append(f"ERROR: Tactic failed at step {fail_idx}")

            # Show failing tactic and optional step plan context
            if fail_idx < len(step_plan) and thm:
                s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
                lines.extend(format_step_context(
                    step_plan, fail_idx, s_lines,
                    context_before=context_before, context_after=context_after,
                ))

            lines.append("")
            lines.append(
                f"Replay cannot reach the requested position because an earlier "
                f"tactic failed. The proof is sequential — later goals depend on "
                f"earlier tactics succeeding."
            )
            if fail_loc:
                lines.append(
                    f"Fix the broken tactic, or inspect the failure point with:\n"
                    f"  hol_state_at(line={fail_loc[0]}, col={fail_loc[1]})"
                )

        # Timeout attribution: name the step's source span so the user can
        # shrink the replayed unit instead of guessing which tactic is slow.
        if result.error and "timed out" in result.error:
            lines.append("")
            lines.append(
                f"TIMEOUT: step {fail_idx} ({fail_str}) exceeded the "
                f"per-tactic timeout. If this span is a lumped chain, split "
                f"it with `>- suspend` to shrink the replayed unit; a "
                f"long-running but correct tactic needs a higher "
                f"--tactic-timeout."
            )

        if result.goals:
            # Always show goals at failure point (useful for debugging)
            # show_partial controls whether ALL goals or just the first are shown
            display_goals = result.goals if all_goals else result.goals[:1]
            total = len(result.goals)
            if opaque_multiline:
                goal_label = "Goals entering the opaque step" if all_goals else f"Goal entering the opaque step (1 of {total})"
                goal_loc_str = ""
            else:
                goal_label = f"Goals at failure point" if all_goals else f"Goal at failure point (1 of {total})"
                goal_loc_str = f" ({stuck_str})"
            lines.append("")
            lines.append(f"=== {goal_label}{goal_loc_str} ===")
            for i, g in enumerate(display_goals):
                if i > 0:
                    lines.append("")
                if g.get('asms'):
                    for asm in g['asms']:
                        lines.append(f"  {asm}")
                    lines.append("  " + "-" * 40)
                lines.append(f"  {g['goal']}")

        # Error footer for truncation safety
        if opaque_multiline:
            error_footer = (
                f"ERROR: PROOF BROKEN somewhere in the opaque step at {fail_str}. "
                f"The line shown is the step's start, not the failure — bisect with `cheat`."
            )
        else:
            error_footer = (
                f"ERROR: PROOF BROKEN at {fail_str}. "
                f"Fix the broken tactic before inspecting later positions."
            )
    else:
        # Normal path: replay succeeded (or position is at/before the failure)
        loc = tactic_to_loc(result.tactic_idx)
        loc_str = f"Line {loc[0]} col {loc[1]}, " if loc else ""
        lines.append(f"{loc_str}Proof position")
        if result.error and not is_proof_complete:
            error_footer = f"ERROR: {result.error}"
        lines.append("")
        if result.goals:
            display_goals = result.goals if all_goals else result.goals[:1]
            total = len(result.goals)
            if all_goals:
                lines.append(f"=== Goals ({total}) ===")
            else:
                lines.append(f"=== Goal (1 of {total}) ===")
            for i, g in enumerate(display_goals):
                if i > 0:
                    lines.append("")  # Blank line between goals
                if g.get('asms'):
                    for asm in g['asms']:
                        lines.append(f"  {asm}")
                    lines.append("  " + "-" * 40)
                lines.append(f"  {g['goal']}")
        elif is_proof_complete:
            lines.append("=== Goals ===")
            lines.append("No goals (proof complete)")
        else:
            lines.append("=== Goals ===")
            lines.append("No goals (proof complete)")

        # Chain-entry landing: the requested position is strictly inside one
        # opaque step (lumped/parenthesized chain). The state shown is the
        # step's ENTRY, which is easy to misread as the state at that line.
        if (result.inside_step_idx is not None and not result.error
                and thm and thm.proof_body):
            k = result.inside_step_idx
            step_plan = cursor._step_plan
            if k < len(step_plan):
                text_start = step_text_start(step_plan, k, thm.proof_body)
                start_line = _file_offset_to_line_col(
                    thm.proof_body_offset + text_start, cursor._content)[0]
                end_line = _file_offset_to_line_col(
                    thm.proof_body_offset + step_plan[k].end,
                    cursor._content)[0]
                if end_line > start_line:
                    lines.append("")
                    lines.append(
                        f"NOTE: target line {line} is INSIDE step {k} "
                        f"(lumped/parenthesized chain, lines {start_line}-"
                        f"{end_line}); the state shown is this step's ENTRY "
                        f"at line {start_line}, not the state at line {line}. "
                        f"To navigate inside, split the arm with `>- suspend` "
                        f"into a Resume body."
                    )

    # Suggest extracting by/>- subproof into a suspend/Resume block
    if result.inside_by and not result.error:
        lines.append("")
        lines.append("[Inside by/>- subproof. Consider extracting into a suspend/Resume block "
                     "for independent verification and easier editing.]")

    # Smart-quote diagnosis on parse/lex-flavoured errors (the raw replay
    # error may carry lexer text the formatted output above does not show).
    if result.error:
        lines.extend(_quote_diagnosis_if_parse_error(cursor.file, result.error))

    # Lost-suspension diagnosis: a Resume whose label cannot be found usually
    # means an ancestor (dispatcher or earlier Resume) broke during loading.
    if result.error and active_theorem and (
            "No such label" in result.error
            or "Failed to set up Resume goal" in result.error):
        diag = await cursor.diagnose_resume_failure(active_theorem)
        if diag:
            lines.append("")
            lines.append(diag)

    # Name any deps auto-cheated while loading the file prefix (the state
    # shown was computed with those theorems replaced by `cheat`).
    lines.extend(_auto_cheated_deps_lines(cursor))

    # Add timing info if available
    if result.timings:
        t = result.timings
        lines.append("")
        method = t.get('strategy', 'replay')
        lines.append(f"[Timing: total={t.get('total', 0)*1000:.0f}ms, "
                     f"replay={t.get('replay', 0)*1000:.0f}ms, "
                     f"method={method}]")
        # Cache-state diagnostics: show what _pos was BEFORE the call,
        # the target, and what got reused vs replayed. Useful for
        # reproducing cache bugs.
        before_idx = t.get('pos_before_idx', None)
        if before_idx is not None:
            before_offset = t.get('pos_before_offset', -1)
            before_init = t.get('pos_before_init', 0)
            hash_match = t.get('pos_hash_match', 0)
            target_idx = t.get('target_idx', '?')
            target_partial = t.get('target_partial', 0)
            file_changed = t.get('file_changed', 0)
            offset_str = f",off={before_offset}" if before_offset >= 0 else ""
            init_str = "init" if before_init else "uninit"
            hash_str = "hash=match" if hash_match else "hash=miss"
            partial_str = "partial" if target_partial else "boundary"
            changed_str = "changed" if file_changed else "unchanged"
            parts = [
                f"pos_before=(idx={before_idx}{offset_str},{init_str},{hash_str})",
                f"target=(idx={target_idx},{partial_str})",
                f"file={changed_str}",
                f"replayed={result.tactics_replayed}/{result.tactics_total}",
            ]
            if 'incr_first_diff' in t:
                parts.append(
                    f"incr=(first_diff={t['incr_first_diff']},"
                    f"old_idx={t['incr_old_idx']})"
                )
            if result.inside_by:
                parts.append("inside_by=true")
            lines.append(f"[Cache: {', '.join(parts)}]")

    _schedule_gc(session)
    return _truncate_output("\n".join(lines), max_output, footer=error_footer)


@mcp.tool()
async def hol_check_proof(
    theorem: str,
    file: str = None,
    workdir: str = None,
    trace: bool = True,
    session: str = "default",
) -> str:
    """Check if a theorem's proof completes after editing.

    Use this after editing a proof to see if it works now. More reliable than
    hol_state_at with line numbers which may be stale after edits.

    Args:
        theorem: Theorem name to check
        file: Path to .sml file (auto-inits cursor if no cursor exists)
        workdir: Working directory for HOL (used with file)
        trace: If True, include full per-step timing trace
        session: Session name (default: "default")

    Returns: Whether proof completes, failure location, brief goal summary.
             With trace=True, also includes per-step timing and goal counts.

    Status values: OK / FAILED / INCOMPLETE / CHEAT / NO TACTICS, plus
    CANNOT CHECK for a Resume whose suspension goal is unavailable (comes
    with an ancestor-chain diagnosis naming the first broken ancestor).
    "Status: OK ... ⚠ depends on cheat" is followed by
    "[auto-cheated deps: name (reason); ...]" naming WHICH prefix theorems
    were auto-cheated at load and why — the OK rests on their statements
    only. A timeout failure adds "TIMEOUT: step k spans lines A-B" naming
    the span to split with `>- suspend`.
    """
    cursor = await _get_cursor(session)

    # Auto-init if file provided
    if file:
        file_path = Path(file).resolve()
        if not cursor or Path(cursor.file).resolve() != file_path:
            init_result = await _init_file_cursor(
                file=file, session=session, workdir=workdir
            )
            if init_result.startswith("ERROR"):
                return init_result
            cursor = await _get_cursor(session)

    if not cursor:
        return f"ERROR: No cursor for session '{session}'. Pass file= to auto-init."

    # Re-parse file to pick up edits
    try:
        cursor._reparse_if_changed()
    except FileNotFoundError:
        return f"ERROR: File not found: {cursor.file}"

    # Enter theorem and get step plan
    enter_result = await cursor.enter_theorem(theorem)
    if "error" in enter_result:
        err_lines = [f"ERROR: {enter_result['error']}"]
        err_lines.extend(
            _quote_diagnosis_if_parse_error(cursor.file, enter_result['error'])
        )
        return "\n".join(err_lines)

    thm = cursor._get_theorem(theorem)
    if not thm:
        return f"ERROR: Theorem '{theorem}' not found"

    lines = [
        f"Theorem: {theorem}",
        f"Lines: {thm.start_line}-{thm.proof_end_line - 1}",
        "",
    ]

    if thm.has_cheat:
        lines.append("Status: CHEAT (not verified)")
        lines.append("NOTE: Tactics before 'cheat' are not replayed in this mode.")
        lines.append("      Remove 'cheat' and rerun hol_check_proof for full replay.")
        return "\n".join(lines)

    # Oracle tags are populated after execute_proof_traced (calls verify_theorem_json).
    # We check them after execution below.

    # Execute proof (clean mode by default - matches holmake, uses cache)
    trace_data = await cursor.execute_proof_traced(theorem)
    
    if not trace_data:
        if thm.kind == "Definition" and thm.proof_body:
            # Definition blocks can't use execute_proof_traced (TC goal context).
            # Fall back to state_at at the End line to check proof completion.
            result = await cursor.state_at(thm.proof_end_line - 1, col=1)
            # "no goals" error from goals_json means proof completed successfully
            no_goals_ok = result.error and "no goals" in result.error
            if not result.goals or no_goals_ok:
                lines.append(f"Status: OK (Definition termination proof)")
            elif result.error:
                lines.append(f"Status: FAILED")
                lines.append(f"Error: {result.error}")
            else:
                lines.append(f"Status: INCOMPLETE ({len(result.goals)} goals remaining)")
            return "\n".join(lines)
        if thm.kind == "Resume":
            # Empty trace on a Resume almost always means the suspension
            # goal could not be extracted (label missing from the store).
            lines.append("Status: CANNOT CHECK (Resume suspension goal unavailable)")
            diag = await cursor.diagnose_resume_failure(theorem)
            if diag:
                lines.append("")
                lines.append(diag)
            return "\n".join(lines)
        lines.append("Status: NO TACTICS (trivial or unparseable)")
        return "\n".join(lines)

    # Find failure point
    failed_idx = None
    for i, entry in enumerate(trace_data):
        if entry.error or (i == len(trace_data) - 1 and entry.goals_after != 0):
            failed_idx = i
            break

    step_plan = cursor._step_plan

    final = trace_data[-1]
    total_ms = sum(e.real_ms for e in trace_data)
    total_steps = len(trace_data)
    
    if final.error:
        lines.append(f"Status: FAILED at step {failed_idx + 1}/{total_steps} ({total_ms}ms)")
        lines.append(f"Error: {final.error}")
        # Timeout attribution: name the step's source span so the user can
        # shrink the lump instead of guessing which tactic is slow.
        fe = trace_data[failed_idx]
        if fe.error and "timeout" in fe.error.lower():
            so = fe.start_offset or 0
            sl = _file_offset_to_line_col(
                thm.proof_body_offset + so, cursor._content)[0]
            el = (_file_offset_to_line_col(
                thm.proof_body_offset + fe.end_offset, cursor._content)[0]
                if fe.end_offset is not None else sl)
            span = f"line {sl}" if el <= sl else f"lines {sl}-{el}"
            lines.append(
                f"TIMEOUT: step {failed_idx + 1} spans {span} — split this "
                f"span with `>- suspend` to shrink the lump, or raise the "
                f"per-tactic timeout for a long-running but correct tactic."
            )
    elif final.goals_after == 0:
        oracles = cursor._theorem_oracles.get(theorem, [])
        if oracles:
            lines.append(f"Status: OK ({total_ms}ms, {total_steps} steps) ⚠ depends on cheat")
            lines.extend(_auto_cheated_deps_lines(cursor))
        else:
            lines.append(f"Status: OK ({total_ms}ms, {total_steps} steps)")
        if not trace and not oracles:
            return "\n".join(lines)
    else:
        lines.append(f"Status: INCOMPLETE at step {len(trace_data)}/{total_steps} ({total_ms}ms)")

    # Per-step trace: step plan with timing and goal annotations
    if trace:
        lines.append("")
        lines.extend(format_steps(step_plan, fail_idx=failed_idx, trace_data=trace_data))

    # Show failing tactic with location (when not in trace mode)
    if not trace and failed_idx is not None and failed_idx < len(trace_data):
        s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
        lines.extend(format_step_context(step_plan, failed_idx, s_lines))

    # Brief goal summary for failure/incomplete
    if failed_idx is not None:
        lines.append("")
        ga = final.goals_after if final.goals_after is not None else "unknown"
        lines.append(f"Remaining: {ga} goal(s)")
        s_lines = step_line_numbers(step_plan, thm.proof_body_offset, cursor._content)
        fail_line = s_lines[failed_idx] if failed_idx < len(s_lines) else thm.proof_start_line
        lines.append(f"Use hol_state_at(line={fail_line}) for full goals")

    _schedule_gc(session)
    return "\n".join(lines)


def _install_pi_extension():
    """Install the pi extension to ~/.pi/agent/extensions/."""
    import shutil
    
    # Find the extension file bundled with the package
    ext_source = Path(__file__).parent / "pi_extension" / "hol4-mcp.ts"
    if not ext_source.exists():
        print(f"Error: Extension file not found at {ext_source}", file=sys.stderr)
        sys.exit(1)
    
    # Target directory
    ext_dir = Path.home() / ".pi" / "agent" / "extensions"
    ext_dir.mkdir(parents=True, exist_ok=True)
    
    ext_target = ext_dir / "hol4-mcp.ts"
    shutil.copy2(ext_source, ext_target)
    print(f"Installed pi extension to {ext_target}")


def main():
    """CLI entry point for HOL4 MCP server."""
    import argparse
    import logging

    parser = argparse.ArgumentParser(description="HOL4 MCP Server and Tools")
    subparsers = parser.add_subparsers(dest="command")

    # install-pi subcommand
    subparsers.add_parser("install-pi", help="Install pi extension to ~/.pi/agent/extensions/")

    # serve subcommand (default behavior)
    serve_parser = subparsers.add_parser("serve", help="Run the MCP server (default)")
    serve_parser.add_argument(
        "--transport",
        choices=["stdio", "http", "sse"],
        default="stdio",
        help="Transport protocol (default: stdio)",
    )
    serve_parser.add_argument("--port", type=int, default=8000, help="Port for HTTP/SSE (default: 8000)")
    serve_parser.add_argument("--host", default="127.0.0.1", help="Host for HTTP/SSE (default: 127.0.0.1)")
    serve_parser.add_argument("-v", "--verbose", action="store_true", help="Enable debug logging")
    serve_parser.add_argument("--tactic-timeout", type=float, default=None, help="Max seconds per tactic during proof replay (default: 5.0, or HOL_TACTIC_TIMEOUT env)")

    # Also allow serve options at top level for backwards compat
    parser.add_argument("--transport", choices=["stdio", "http", "sse"], default="stdio", help=argparse.SUPPRESS)
    parser.add_argument("--port", type=int, default=8000, help=argparse.SUPPRESS)
    parser.add_argument("--host", default="127.0.0.1", help=argparse.SUPPRESS)
    parser.add_argument("-v", "--verbose", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--tactic-timeout", type=float, default=None, help=argparse.SUPPRESS)

    args = parser.parse_args()

    if args.command == "install-pi":
        _install_pi_extension()
        return

    # Default to serve behavior
    global TACTIC_TIMEOUT
    if args.tactic_timeout is not None:
        TACTIC_TIMEOUT = args.tactic_timeout

    if args.verbose:
        logging.basicConfig(
            level=logging.DEBUG,
            format="%(asctime)s %(levelname)s %(name)s: %(message)s",
            stream=sys.stderr,
        )
        logging.getLogger("mcp").setLevel(logging.DEBUG)

    if args.transport == "stdio":
        mcp.run(show_banner=False)
    else:
        print(f"HOL MCP server starting on {args.host}:{args.port} ({args.transport})", file=sys.stderr)
        mcp.run(transport=args.transport, host=args.host, port=args.port, show_banner=False)


if __name__ == "__main__":
    main()
