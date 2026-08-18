#!/usr/bin/env python3
"""
H6 -- PostToolUse hook injecting a reminder after a navigation/check tool
returns FAILED / TIMEOUT / PROOF BROKEN / "Tactic execution failed".

Fires on hol_check_proof AND on the navigation tools (hol_state_at,
hol_goals): those are the iteration-loop tools (RULE C reserves
hol_check_proof for end-of-theorem confirmation), so a session that follows
the rules meets every one of its failures through them.

Two parts, both advisory (exit 0 always):

1. A RULE C reminder: hol_check_proof is not a diagnosis tool, sub-suspend the
   failing arm instead of re-running it.
2. When the failing tactic matches the symptom table below, the corpus fact
   that explains that symptom. The facts are written down already and are
   still rediscovered by debugging, because the notes are indexed by CAUSE
   and the reader arrives with a SYMPTOM. The hook has the symptom in hand.

Calibration: the hint fires ONLY on a table match against a SHORT failing
step whose FIRST tactic is a listed one -- a token buried in a lumped opaque
arm is not evidence about that arm. Unmatched failures get part 1 alone. A
hint that is wrong at the moment of failure is worse than silence, because
it is read when trust is highest.

CHEAT (not verified) output is intentionally NOT a trigger -- reaching a
parked `cheat` is the expected result of the cheat-the-frontier pattern
(hol4-proving skill RULE I), not a failure.

Rule source: hol4-proving skill RULE C ('HOL4 - iteration loop').
"""

HOOK_EVENT = "PostToolUse"
HOOK_MATCHER = ("mcp__hol4__hol_check_proof|mcp__hol4__hol_state_at"
                "|mcp__hol4__hol_goals")

import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hook_payload import output_text  # noqa: E402

FAILURE_PATTERNS = [
    re.compile(r"TIMEOUT after \d+(\.\d+)?s"),
    re.compile(r"Status:\s*FAILED"),
    re.compile(r"Status:\s*INCOMPLETE"),
    re.compile(r"Status:\s*ERROR"),
    re.compile(r"<--\s*FAILED"),
    re.compile(r"Tactic execution failed"),
    re.compile(r"PROOF BROKEN"),
]

TOOLS = ("mcp__hol4__hol_check_proof", "mcp__hol4__hol_state_at",
         "mcp__hol4__hol_goals")

BANNER = "hol4-hook H6: {tool} returned FAILED / TIMEOUT / PROOF BROKEN."

REMINDER = """\
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

Re-running the same check, or re-probing line numbers around the break,
without sub-suspending leaves the failure hidden inside the opaque wrapper
(re-running hol_check_proof for this is also a RULE C violation)."""

OPAQUE_HINT = """\
The break is inside an OPAQUE step, so READ THE REPORT'S GOAL WITH CARE: it
is the state ENTERING that step, NOT the failure point. Editing against it is
editing against the wrong goal — the commonest way to burn a session here.
`hol_state_at` cannot land inside a `THEN1 (...)` / `>- (...)` / `by (...)`
chain, by design; more probes at nearby lines return that same entry goal
(`replayed=k/N`, the identical goal at two consecutive lines), which is
evidence of the parked break, not of a tactic that did nothing.
Recovery, in order: (1) SUB-SUSPEND the arm — the default; (2) probe IN PLACE
— the failed replay parks the proofManager at the pre-block goals, so small
`e` steps work there now, with `b()` to undo and retry, no re-navigation.
Detail: [[feedback_replay_discipline]] §state_at navigation limit."""

# --- symptom table ----------------------------------------------------------
#
# Each row: (mode, tactic regex, hint). `mode` is the failure shape the hint
# is true of:
#   "raised"  -- replay stopped on a HOL_ERR / exception (the tactic itself
#                threw), so the tactic is the fault and the hint diagnoses it
#   "unsolved"-- no exception and no timeout, so the tactic ran and left goals
# A timeout never matches: the server already prints a looping-tactic advisory,
# and a second opinion on top of it is noise.

PATTERN_HINT = """\
A pattern tactic RAISED — its pattern no longer matches anything. Two causes,
both of which leave the proof text looking correct:
  - it pins a PROVER-GENERATED name (`h''`, `h'³'`, `v15`, `q'`) that an
    adjacent edit or a library change re-rolled (skill RULE H: bind a stable
    name AT the split with `namedCases_on`/`rename1`, or reach by SHAPE);
  - a TYPE-variable mismatch: the pattern and the goal's term PRINT
    IDENTICALLY and still fail to match — annotate the type at the call site.
Read the live goal with `hol_state_at` and compare, rather than trying
pattern variants. Detail: [[feedback_hol4_mcp_proving]] §Prover-generated
names, §Polymorphic constructors."""

MATCHER_HINT = """\
A matcher RAISED — it found nothing to match. Check in this order:
  - a free TYPE VARIABLE in the LEMMA'S OWN statement: it prints the same as
    the goal's instance and still will not unify — pin the type where the
    lemma is stated, not at the use site;
  - the constant was `[simp]`-tagged, so it is no longer an ATOM in the
    assumptions and every lemma taking it as a hypothesis silently stops
    matching;
  - the assumption is not yet in the lemma's shape — an assumption-simplifying
    normaliser (`gvs []`) before the matcher, not a bigger rewrite set.
Detail: [[feedback_hol4_mcp_proving]] §Matchers won't match, §Polymorphic
constructors, §`[simp]` tags."""

SIMP_HINT = """\
`simp` left goals. `simp` uses the assumptions AS THEY STAND (it *is*
`asm_simp_tac`); `fs`/`gvs`/`rw` SIMPLIFY the assumptions first. So a fact
that is "right there in the assumptions" but needs rewriting before it is
usable will never close under `simp`, and will under `gvs`. ⚠ `fs`/`gvs`/`rw`
also SPLIT a disjunctive assumption into one goal per disjunct — check that a
following `>-` still dispatches the branch you meant.
Detail: [[feedback_hol4_mcp_proving]] §Which normaliser."""

TABLE = [
    ("raised", re.compile(r"\b(qpat_x_assum|qpat_assum|rename1|qmatch_\w+)\b"),
     PATTERN_HINT),
    ("raised", re.compile(r"\b(drule\w*|irule\w*|match_mp_tac|mp_then)\b"),
     MATCHER_HINT),
    # `simp` family ONLY. `srw_tac` belongs with `rw` (bossLib: `srw_tac` is
    # BasicProvers.srw_tac, `rw` is PRIM_SRW_TAC), and for that family the hint
    # is not merely unhelpful but false.
    ("unsolved", re.compile(r"^(simp|simp_tac|asm_simp_tac)\b"),
     SIMP_HINT),
]

FAIL_HEADERS = ("=== Failing tactic ===",
                "=== Where replay stopped (raised exception) ===")
# The failing-tactic block ends at the first line that starts a new report
# section rather than continuing the tactic text.
BLOCK_END = re.compile(r"^\s*(===|Remaining:|Use hol_state_at|NOTE:|To localize:"
                       r"|Opaque tactic|Status:|ERROR:|TIMEOUT:)")
COMBINATOR = re.compile(r"\s*(>>|>-|>~|>>~|\\\\|THEN1|THEN)\s*")
MAX_STEP_CHARS = 200   # above this the step is a lump, not one tactic


def failing_tactic(text):
    """The first tactic of the failing step, or None if there is no usable
    single-tactic step to key a hint on."""
    lines = text.split("\n")
    start = None
    for i, l in enumerate(lines):
        if l.strip() in FAIL_HEADERS:
            start = i + 1
            break
    if start is None:
        return None
    body = []
    for l in lines[start:]:
        if not l.strip() or BLOCK_END.match(l):
            break
        body.append(l.strip())
    step = " ".join(body)
    if not step or len(step) > MAX_STEP_CHARS:
        return None
    step = COMBINATOR.sub(" ", step, count=1).strip() if COMBINATOR.match(step) else step
    # Only the FIRST tactic of the step ran unconditionally; a token after a
    # combinator may never have been reached.
    return re.split(r">>|>-|>~|\\\\|\bTHEN1\b|\bTHEN\b", step)[0].strip()


def failure_mode(text):
    if "TIMEOUT" in text or "timed out" in text.lower():
        return "timeout"
    if ("HOL_ERR" in text or "Exception-" in text
            or "raised exception" in text.lower()):
        return "raised"
    return "unsolved"


OPAQUE = re.compile(r"opaque step at lines|Opaque tactic — cannot inspect")


def matched_hint(text):
    tac = failing_tactic(text)
    if not tac:
        return None
    mode = failure_mode(text)
    for want, rx, hint in TABLE:
        if mode == want and rx.search(tac):
            return f"LIKELY CAUSE — the failing tactic is `{tac}`.\n{hint}"
    return None


def main():
    try:
        payload = json.load(sys.stdin)
    except Exception:
        return 0
    tool = payload.get("tool_name", "")
    if tool not in TOOLS:
        return 0
    text = output_text(payload)
    if not any(rx.search(text) for rx in FAILURE_PATTERNS):
        return 0
    banner = BANNER.format(tool=tool.rsplit("__", 1)[-1])
    hint = matched_hint(text)
    opaque = OPAQUE_HINT if OPAQUE.search(text) else None
    parts = ([banner] + ([hint] if hint else []) + ([opaque] if opaque else [])
             + [REMINDER])
    print(json.dumps({
        "hookSpecificOutput": {
            "hookEventName": "PostToolUse",
            "additionalContext": "\n\n".join(parts),
        }
    }))
    return 0

if __name__ == "__main__":
    sys.exit(main())
