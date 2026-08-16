#!/usr/bin/env python3
"""
H28 -- PreToolUse hook blocking shell invocations of the HOL4 build/REPL
binaries, redirecting to the MCP tools that own those interactions.

Reads PreToolUse JSON on stdin. If the tool is Bash and the command invokes
`Holmake` (or a raw `poly`/`hol` REPL) in a command position, the call is
blocked with a pointer to the owning MCP tool.

Rationale: the MCP tool reports its own completion and returns the failing
log excerpt. A shell build needs a hand-rolled completion sentinel, and
Holmake's real failure lines (`Proof of ... failed`, `error in quse`) do not
match the obvious guesses -- so the poller hangs while the build is dead.

Matched in a command position only (start, or after | & ; ( && || newline),
so prose mentions and paths like .hol/logs/... pass through.

Escape hatch: the literal phrase `shell holmake ok` in the latest user
message. Fails open if the transcript is missing or unreadable.

Rule source: hol4-proving skill '⛔ RULE A' (holmake is the file-build gate)
and the corpus layer table (MCP tools are the point of contact).
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "Bash"   # None = all calls for this event

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import latest_user_message  # noqa: E402

# A command position: string start, or after a shell separator. Prevents
# matching `grep Holmake log`, `--- holmake procs ---`, paths, and comments.
_CMD_POS = r"(?:^|[|&;(\n]|&&|\|\|)\s*"

# Optional env-var assignments and `nohup`/`time`/`env` wrappers.
_PREFIX = r"(?:(?:[A-Za-z_]\w*=\S*|nohup|time|env|command|exec)\s+)*"

BUILD_RE = re.compile(_CMD_POS + _PREFIX + r"(Holmake)\b")
REPL_RE = re.compile(_CMD_POS + _PREFIX + r"(poly|hol)\b(?!\w)")

CONSENT_RE = re.compile(r"\bshell\s+holmake\s+ok\b", re.IGNORECASE)

REPLACEMENT = {
    "Holmake": "mcp__hol4__holmake (params: workdir, target, jobs, timeout)",
    "poly": "mcp__hol4__hol_start / hol_send",
    "hol": "mcp__hol4__hol_start / hol_send",
}


def find_match(command):
    m = BUILD_RE.search(command)
    if m:
        return m.group(1)
    m = REPL_RE.search(command)
    if m:
        return m.group(1)
    return None


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "Bash":
        return 0
    cmd = payload.get("tool_input", {}).get("command", "")
    matched = find_match(cmd)
    if not matched:
        return 0
    latest = latest_user_message(payload)
    if latest is None:
        return 0  # fail-open
    if CONSENT_RE.search(latest):
        return 0
    print(f"hol4-hook H28: refused shell invocation of {matched!r}.", file=sys.stderr)
    print("", file=sys.stderr)
    print(f"Use {REPLACEMENT[matched]} instead.", file=sys.stderr)
    print("", file=sys.stderr)
    print("The MCP tool reports its own completion and returns the failing log", file=sys.stderr)
    print("excerpt; a shell build needs a hand-rolled sentinel, and Holmake's", file=sys.stderr)
    print("failure lines do not match the obvious guesses -- the poller hangs", file=sys.stderr)
    print("while the build is already dead.", file=sys.stderr)
    print("", file=sys.stderr)
    print("If a shell build is genuinely required, include the literal phrase", file=sys.stderr)
    print("`shell holmake ok` in your next message.", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
