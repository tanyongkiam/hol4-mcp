#!/usr/bin/env python3
"""
H19 -- PreToolUse hook advising against casual mcp__hol4__hol_restart.

Never blocks. Reads PreToolUse JSON on stdin. If the tool is
mcp__hol4__hol_restart and the latest user message does NOT contain the
literal phrase `restart ok` (case-insensitive), emits an advisory reminding
that a restart is rarely the right answer and must not become a reflex. When
the user did ask for it, the hook stays silent.

Rationale: hol4-proving skill 'HOL4 -- iteration loop': a broken/weird replay
is usually a proof or navigation error to re-diagnose, not stale state or
cache corruption. A restart wipes session state, so a reflexive one hides the
real error. It IS the right move for a genuinely stale ancestor .dat, which is
why this advises rather than refuses.
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
    if latest is not None and CONSENT_RE.search(latest):
        return 0  # the user asked for it
    msg = (
        "hol4-hook H19: restarting without the user asking. Allowed, but justify "
        "it. A restart is the right move for one thing: a genuinely stale ancestor "
        ".dat that a live session cannot reload (link_parents complains). It is NOT "
        "the fix for a broken replay, a confusing goal, or a tactic that will not "
        "close -- those are proof or navigation errors, and restarting wipes the "
        "session state that would have localised them. Do not repeat it: a second "
        "restart for the same symptom means the first one treated a diagnosis you "
        "had not made."
    )
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "additionalContext": msg,
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
