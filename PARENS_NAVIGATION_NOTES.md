# Mid-arm navigation inside parens-grouped LT chains — investigation notes

Date: 2026-06-10. Timeboxed investigation (plan item P4b); outcome at the
time: **not implemented** — P1b's explicit chain-entry NOTE was the shipped
fallback. This file records why, and the one feasible path identified.

**Status (2026-09-03): the single-goal special case below is implemented.**
`FileProofCursor._navigate_inside_group` replays the opaque step's flat
sub-plan (`goalfrag_step_plan_json_flat`, which re-expands positional
groups) up to the target, checking live that every positional group entered
under a THEN combinator receives exactly one goal; otherwise it restores the
entry state and the NOTE stands. Inside-group positions are never cached
(the session is marked dirty). Tests: `tests/test_parens_single_goal_nav.py`.

## Background

`b43c34c` fixed the parens-around-LT distribution bug: a `Group`-wrapped
`(TAC1 >- TAC2)` inside a `\\` chain must stay **opaque** (one atomic
`expand` step), because Holmake distributes the whole parenthesised tactic
per source goal, while re-expanded flat fragments (`expand TAC1`,
`open_then1`, `expand TAC2`, `close_paren`) run the `>-` globally against
goal 1 of the whole goalstate. The two diverge whenever the surrounding
context has >1 goal. Trade-off taken: lose mid-arm navigation inside such
groups.

## Why proper FOpen/FMid/FClose fragments can't simply come back

The linear StepPlan replay model maps each source offset to ONE position
in ONE fragment sequence. Under distribution-per-goal semantics, a source
position inside `(TAC1 >- TAC2)` corresponds to **N replay points** — one
per source goal the group is applied to. There is no single "state at this
line" to show; any choice (e.g. goal 1's instance) is a state the file
never presents to the remaining goals. Supporting it honestly would need a
per-goal iteration construct in the goalFrag layer (`FDistribute`-style),
sub-plan position math, and a position-cache model for inside-group
positions — the position cache is the most regression-prone part of this
codebase, and any divergence between the preview and Holmake behavior is
exactly the class of bug b43c34c removed.

## The one sound special case (feasible future work)

When the goalstate at the group's ENTRY has **exactly one goal**,
per-goal distribution and global execution provably coincide (THEN over a
single goal IS global application). In that case the group could be
re-expanded **dynamically at navigation time**:

1. P1b's `_detect_inside_step` already identifies "target strictly inside
   opaque step k".
2. If `len(goals_at_entry) == 1`: run `goalfrag_step_plan_json` on the
   group's source text, replay the sub-fragments up to
   `target_offset - group_start`, show that state (clearly labelled).
3. Never checkpoint/cache inside-group positions (always recompute from
   the step-k entry checkpoint).

Cost when attempted: sub-plan offset bookkeeping relative to the group
start, interaction with `_pos`/`SessionPosition` (inside-group positions
must NOT be recorded as step boundaries), `backup_n` semantics across the
sub-plan, and tests mirroring `test_parens_lt_distribution_bug.py` for the
multi-goal refusal. Estimate: a focused session, mostly spent on cache
non-interference.

## What shipped instead (P1)

- `hol_state_at` appends an explicit NOTE when the target is strictly
  inside a multi-line opaque step: state shown is the step's ENTRY, with
  the step's line range and `>- suspend` advice (P1b).
- The PROOF BROKEN path reports opaque multi-line failures as a line range
  with cheat-bisection advice (582f8cc).
- Timeouts name the lumped span to split (P1d).

These remove the misreading hazard; actual mid-arm work goes through the
documented sub-suspend workflow (split the arm into a Resume body, which
makes every piece navigable AND independently verifiable).
