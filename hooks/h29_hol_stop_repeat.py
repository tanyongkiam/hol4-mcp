#!/usr/bin/env python3
"""
H29 -- PreToolUse hook blocking REPEAT mcp__hol4__hol_stop / hol_restart on
the same theory directory (the ritual-stop pattern). Supersedes the retired
advisory-only restart hook (restart only; hol_stop had no coverage): the repeat-key auto-allows the
legitimate cases instead of gating everything behind consent.

A first stop/restart always passes (finished a theory, switching theory
directories, fresh start) with a one-line reminder, and so does any stop once
the cached working file (H25's hol4_file) sits in a different directory --
another theory. Blocked: a second stop/restart within 30 minutes while still
working in the same directory, whichever file inside it is current -- the
signature of using stop/restart inside the edit-check loop. That loop never
needs one: hol_state_at auto-detects file edits and rebuilt ancestors and
moves the session across workdirs itself (MCP server), and every stop forces
a cold prefix reload of the whole theory on the next navigation.

Fail-open: unknown working file, unreadable state, or unreadable transcript
never blocks. Escape hatch: literal phrase `restart ok` in the latest user
message (the retired hook's phrase, kept).
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_stop|mcp__hol4__hol_restart"

import json
import os
import re
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import latest_user_message  # noqa: E402

STATE = os.path.expanduser("~/.claude/hook-state")
COOLDOWN_S = 30 * 60
CONSENT_RE = re.compile(r"\brestart\s+ok\b", re.IGNORECASE)
TOOLS = ("mcp__hol4__hol_stop", "mcp__hol4__hol_restart")


def session_dir(payload):
    return os.path.join(STATE, payload.get("session_id") or "nosession")


def working_file(payload):
    try:
        with open(os.path.join(session_dir(payload), "hol4_file"),
                  encoding="utf-8") as fh:
            return fh.read().strip() or None
    except OSError:
        return None


def last_stop(payload):
    try:
        with open(os.path.join(session_dir(payload), "h29_last_stop"),
                  encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return None


def record_stop(payload, tool, path):
    d = session_dir(payload)
    try:
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "h29_last_stop"), "w",
                  encoding="utf-8") as fh:
            json.dump({"ts": time.time(), "tool": tool, "file": path}, fh)
    except OSError:
        pass


def advise(tool):
    msg = (
        f"hol4-hook H29: {tool} allowed -- first stop/restart in this window. "
        "Justify it: right when a theory is FINISHED, or when leaving its "
        "directory. It is never part of the edit-check loop -- hol_state_at "
        "auto-detects file edits, reloads after an ancestor rebuild and moves "
        "the session to a new workdir itself; every stop costs a cold prefix "
        "reload on the next navigation. A repeat in the same directory within "
        "30 min is blocked (override: `restart ok`)."
    )
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse", "additionalContext": msg}}))
    return 0


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    if tool not in TOOLS:
        return 0
    latest = latest_user_message(payload)
    if latest is None:
        return 0  # fail-open
    if CONSENT_RE.search(latest):
        record_stop(payload, tool, working_file(payload))
        return 0  # the user asked for it
    path = working_file(payload)
    prev = last_stop(payload)
    prev_file = prev.get("file") if prev else None
    if (path and prev_file
            and os.path.dirname(prev_file) == os.path.dirname(path)):
        age = time.time() - float(prev.get("ts", 0))
        if 0 <= age < COOLDOWN_S:
            mins = int(age // 60)
            print(f"hol4-hook H29: refused {tool} -- repeat stop/restart "
                  f"{mins} min after the last one, still working in the same "
                  f"directory:", file=sys.stderr)
            print(f"  {os.path.dirname(path)}", file=sys.stderr)
            print("", file=sys.stderr)
            print("A stop/restart is NEVER part of the edit-check loop:",
                  file=sys.stderr)
            print("hol_state_at auto-detects file edits, reloads the session "
                  "after an ancestor", file=sys.stderr)
            print("rebuild and moves it to a new workdir itself (MCP server "
                  "contract), and every", file=sys.stderr)
            print("stop forces a cold prefix reload of the whole theory on "
                  "the next navigation.", file=sys.stderr)
            print("", file=sys.stderr)
            print("Auto-allowed: the first stop/restart, and any stop once "
                  "the working file", file=sys.stderr)
            print("is in another directory (finished a theory / switched "
                  "theories).", file=sys.stderr)
            print("", file=sys.stderr)
            print("If this one is genuinely needed (session pollution; a "
                  "changed", file=sys.stderr)
            print("Definition misbehaving in a live session), say so and ask "
                  "the user to", file=sys.stderr)
            print("include the literal phrase `restart ok` in their next "
                  "message.", file=sys.stderr)
            return 2
    record_stop(payload, tool, path)
    return advise(tool)


if __name__ == "__main__":
    sys.exit(main())
