#!/usr/bin/env python3
"""
H31 -- PreToolUse hook blocking `skip_prefix: true` on hol_state_at /
hol_goals unless the latest user message contains the literal phrase
`skip prefix ok`.

RULE K: prefix-skip binds every theorem before the target by `cheat`, so the
goal shown rests on unverified statements. The rule allows it only with the
user's explicit authorization for THAT use; the server prints the caveat but
cannot know whether the user asked. This hook reads the transcript and does.

Fails open if the transcript is missing or unreadable. `skip_prefix: false`
or absent never fires.

Rule source: hol4-proving skill '⛔ RULE K'.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_state_at|mcp__hol4__hol_goals"

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import latest_user_message  # noqa: E402

CONSENT_RE = re.compile(r"\bskip\s+prefix\s+ok\b", re.IGNORECASE)
TOOLS = ("mcp__hol4__hol_state_at", "mcp__hol4__hol_goals")


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    if tool not in TOOLS:
        return 0
    if payload.get("tool_input", {}).get("skip_prefix") is not True:
        return 0
    latest = latest_user_message(payload)
    if latest is None:
        return 0  # fail-open
    if CONSENT_RE.search(latest):
        return 0
    short = tool.rsplit("__", 1)[-1]
    print(f"hol4-hook H31: refused {short}(skip_prefix=True) -- RULE K.", file=sys.stderr)
    print("", file=sys.stderr)
    print("skip_prefix binds every theorem BEFORE the target by `cheat`; the goal",
          file=sys.stderr)
    print("it shows rests on unverified statements and proves nothing on its own.",
          file=sys.stderr)
    print("It is allowed only when the user authorizes THAT use. Navigate the real",
          file=sys.stderr)
    print("way: full replay, a sub-suspended arm, or the built ancestors (holmake).",
          file=sys.stderr)
    print("", file=sys.stderr)
    print("If the user wants prefix-skip here, ask them to include the literal",
          file=sys.stderr)
    print("phrase `skip prefix ok` in their next message.", file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
