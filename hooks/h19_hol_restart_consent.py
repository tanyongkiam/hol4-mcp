#!/usr/bin/env python3
"""
H19 -- PreToolUse hook blocking mcp__hol4__hol_restart without explicit
`restart ok` consent in the latest user message.

Reads PreToolUse JSON on stdin. If the tool is mcp__hol4__hol_restart, the
hook reads `transcript_path` from the payload and inspects the latest user
message for the literal phrase `restart ok` (case-insensitive). If absent
-> exit 2; the tool call is blocked.

Rationale: hol4-proving skill RULE J / 'HOL4 -- iteration loop': hol_restart is
effectively never needed. A broken/weird replay is a proof or navigation
error to re-diagnose and fix -- NOT stale state / cache / corruption (which
is essentially never the cause). Restarting wipes session state and masks
the real bug. Consent must be explicit, per-request, like `git ok` (H14).

Fails open if transcript_path is missing or unreadable -- never blocks
legitimately-needed work due to a hook bug.
"""

HOOK_EVENT = "PreToolUse"
HOOK_MATCHER = "mcp__hol4__hol_restart"   # None = all calls for this event

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import latest_user_message  # noqa: E402

CONSENT_RE = re.compile(r"\brestart\s+ok\b", re.IGNORECASE)

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__hol_restart":
        return 0
    latest = latest_user_message(payload)
    if latest is None:
        return 0  # fail-open
    if CONSENT_RE.search(latest):
        return 0
    # Block
    print("hol4-hook H19: refused hol_restart without consent.", file=sys.stderr)
    print("", file=sys.stderr)
    print("hol4-proving skill RULE J / 'HOL4 -- iteration loop':", file=sys.stderr)
    print("  hol_restart is effectively never needed. A broken/weird replay", file=sys.stderr)
    print("  is a proof or navigation error to re-diagnose and fix -- NOT", file=sys.stderr)
    print("  stale state / cache / corruption (essentially never the cause).", file=sys.stderr)
    print("", file=sys.stderr)
    print("Latest user message does not contain consent token `restart ok`.", file=sys.stderr)
    print("To grant consent, include the literal phrase `restart ok` somewhere", file=sys.stderr)
    print("in your next message.", file=sys.stderr)
    return 2

if __name__ == "__main__":
    sys.exit(main())
