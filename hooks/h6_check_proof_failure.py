#!/usr/bin/env python3
"""
H6 -- PostToolUse hook injecting a terse reminder after hol_check_proof
returns FAILED / TIMEOUT / PROOF BROKEN / "Tactic execution failed".

Reads PostToolUse JSON on stdin. If the tool's output contains a failure
signature, emits a `hookSpecificOutput.additionalContext` system reminder
visible to the model on the next turn. Never blocks; exit 0 always.

CHEAT (not verified) output is intentionally NOT a trigger -- that's a
legitimate cheat probe per the cheat-probing pattern (feedback_hol4_mcp_proving).

Rule source: hol4-proving skill RULE C ('HOL4 - iteration loop').
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

Per hol4-proving skill RULE C, hol_check_proof is NOT a diagnosis tool — do
not re-run it to localize the failure.
  - Failure inside an opaque `THEN1 (...)` / `>- (...)` / `\\`-chain (the usual
    case)? SUB-SUSPEND the failing arm NOW — FIRST move, not after a second
    attempt: `>~ [pat] >- suspend "Label"` (or `>- suspend "Label"`) +
    `Resume thm[Label]: cheat QED` after the parent QED. Then `hol_state_at`
    lands on the real goal — the file owns the prefix. This is the default
    (~99% of opaque breaks).
  - FLAT body, no `>-`/chain above the frontier? Read with `hol_state_at`.
  - Do NOT bisect by moving a `cheat` through the chain, and do NOT
    reconstruct the goal with `hol_send`/`e`/`sg`/`expandf` — a scratch goal
    diverges silently from the file form (RULE G), and the all-goals drivers
    (`expandf`/`Manager.expand`) are banned.

Re-running hol_check_proof on the same theorem without sub-suspending is a
RULE C violation: the failure location stays hidden inside the opaque
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
