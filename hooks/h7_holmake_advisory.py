#!/usr/bin/env python3
"""
H7 -- PostToolUse hook injecting a RULE A reminder after a holmake call.

Stateless, advisory only. Never blocks. Every holmake invocation surfaces the
iteration-discipline reminder; the wording is calibrated so a legitimate
end-of-file holmake (after the per-theorem verification ladder passed) can
disregard.

Rule source: hol4-proving skill '⛔ RULE A' / 'HOL4 - iteration loop'.
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = "mcp__hol4__holmake"   # None = all calls for this event

import json
import sys

REMINDER_TEMPLATE = """\
hol4-hook H7: Holmake ran on {target}.

Per hol4-proving skill RULE A: holmake is the FILE-BUILD GATE only -- not for
iteration, not for "see if it builds", not for proof discovery.

If you reached for holmake to check progress mid-proof, STOP. Use the
end-of-proof verification ladder instead:
  - Per-theorem: hol_state_at past QED shows "No goals (proof complete)"
    OR hol_check_proof returns Status: OK.
  - Cheat-tag check (multi-Resume theorems): Tag.dest_tag (Thm.tag <thm>)
    returns (["DISK_THM"], []).
  - Per-file: only after every theorem passes the above, holmake ONCE.

If this holmake call was the legitimate end-of-file gate or a setup step
to unstick a stale .dat dependency, disregard."""

def describe_target(tool_input):
    workdir = tool_input.get("workdir", "")
    target = tool_input.get("target", "")
    if workdir and target:
        return f"{workdir} (target={target})"
    if workdir:
        return workdir
    if target:
        return target
    return "<unknown target>"

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__holmake":
        return 0
    target_desc = describe_target(payload.get("tool_input", {}))
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": REMINDER_TEMPLATE.format(target=target_desc),
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
