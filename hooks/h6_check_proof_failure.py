#!/usr/bin/env python3
"""
H6 -- PostToolUse hook injecting a terse reminder after hol_check_proof
returns FAILED / TIMEOUT / PROOF BROKEN / "Tactic execution failed".

Reads PostToolUse JSON on stdin. If the tool's output contains a failure
signature, emits a `hookSpecificOutput.additionalContext` system reminder
visible to the model on the next turn. Never blocks; exit 0 always.

CHEAT (not verified) output is intentionally NOT a trigger -- that's a
legitimate cheat probe per CLAUDE.md cheat-probing pattern.

CLAUDE.md source: RULE C (~/.claude/CLAUDE.md 'HOL4 - iteration loop').
"""
import json
import re
import sys

FAILURE_PATTERNS = [
    re.compile(r"TIMEOUT after \d+(\.\d+)?s"),
    re.compile(r"Status:\s*FAILED"),
    re.compile(r"Status:\s*INCOMPLETE"),
    re.compile(r"Status:\s*ERROR"),
    re.compile(r"<--\s*FAILED"),
    re.compile(r"Tactic execution failed"),
    re.compile(r"PROOF BROKEN"),
]

REMINDER = """\
hol4-hook H6: hol_check_proof returned FAILED / TIMEOUT.

Per CLAUDE.md RULE C: do NOT re-run hol_check_proof to diagnose.
  - Read the failing goal with `hol_state_at` (or `hol_send` / `expandf` if
    the failure sits inside a `THEN1 (...)` / `>- (...)` chain).
  - If this is the second failed attempt on the same theorem, sub-suspend
    the failing arm: `>~ [pat] >- suspend "Label"` + `Resume thm[Label]:`
    body after the parent QED.

Re-running hol_check_proof on the same theorem without inspecting goal state
is a RULE C violation: the failure location stays hidden inside the opaque
"Tactic execution failed" wrapper."""

def extract_output_text(payload):
    """Defensive: extract candidate output text from any of the plausible
    PostToolUse field names. The schema for MCP tool results is not
    canonical, so we collect from a small set and concatenate."""
    candidates = []
    for key in ("tool_output", "tool_response", "result", "output", "response"):
        v = payload.get(key)
        if v is None:
            continue
        if isinstance(v, str):
            candidates.append(v)
        elif isinstance(v, dict):
            candidates.append(json.dumps(v))
        elif isinstance(v, list):
            for item in v:
                candidates.append(item if isinstance(item, str) else json.dumps(item))
        else:
            candidates.append(str(v))
    return "\n".join(candidates)

def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    if payload.get("tool_name", "") != "mcp__hol4__hol_check_proof":
        return 0
    text = extract_output_text(payload)
    if not any(rx.search(text) for rx in FAILURE_PATTERNS):
        return 0
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": REMINDER,
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
