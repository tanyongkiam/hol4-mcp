# hol4-mcp defect register

**Status: all 16 defects, 3 field items and 5 improvements are FIXED.** Every
`xfail` marker is gone; the tests below are now ordinary regression tests.

```
.venv/bin/python -m pytest tests/ -q
# 428 passed, 2 failed (both pre-existing and unrelated: test_cli_help,
#                       test_hol_goals_live_session)
```

Master index for the navigation/caching defect review. Every finding here is
backed by a test in `tests/` that failed before the fix and passes after it.

Companion documents, which this one indexes rather than repeats:

- `MCP_BUGS_review.md` — the source audit: 16 findings with `file:line` anchors,
  mechanism, severity and confidence.
- `MCP_TACTIC_COST_review.md` — design work on attributing tactic cost.

Severity: **1** silent wrong state · **2** invalidation gap · **3** position/step
mapping · **4** concurrency/lifecycle · **5** performance.

---

## 1. The gate

**No fix lands without a reproducer first.** A transcript showing "I called X and
got Y" is evidence something happened once; it is not proof of a defect, and it
cannot tell us whether a candidate fix works. Every finding below was therefore
put through an independent reproduction pass before being treated as actionable.

That pass paid for itself: **three claims were refuted** (§3). Had we fixed from
the review text alone, we would have written code against two mechanisms that do
not exist and skipped a real bug we had talked ourselves out of.

Each test asserted the **correct** behaviour under
`@pytest.mark.xfail(strict=True, …)`, so it stayed green while the bug existed
and flipped loudly (XPASS → strict failure) the moment the fix landed, at which
point the marker came off. Every test was additionally re-run under `--runxfail`
to confirm it failed on its *intended assertion* rather than on setup or an
incidental exception — an xfail that is red for the wrong reason pins nothing.

```
.venv/bin/python -m pytest tests/test_repro_*.py tests/test_spec_*.py -o addopts="" -q
# 36 passed
```

---

## 2. Status — all fixed

36 tests, 7 files, all green with no markers.

| # | finding | sev | test file | fix |
|---|---|---|---|---|
| 1 | `hol_goals` drops navigation errors **and every advisory** | 1 | reporting | `_classify_state_at` + `_state_caveat_lines`, shared by both tools |
| 2 | unbalanced delimiters truncate the step plan → false "proof complete" | 1 | parser_coverage | plan-coverage check in `parse_step_plan_output`; second-declaration check in `parseTacticBlockFromString` |
| 3 | `hol_check_proof` Definition fallback reports OK on error/timeout | 1 | reporting | branches ordered error-first; `"no goals"` matched case-insensitively |
| 4 | edits to untracked constructs silently ineffective | 1/2 | session_pollution | `construct_start_line` snaps the truncation to a construct boundary |
| 5 | `_session_dirty` ignored by the incremental path | 1 | session_pollution | same veto added to `_try_incremental_navigate` |
| 6 | backward `state_at` replays in a future-polluted context | 1/2 | session_pollution | predecessor-checkpoint guard in `_prepare_session` |
| 7 | HOL goal-time diagnostics never reach the caller | 1 | diagnostics | `HOLSession.diagnostics` sink + `StateAtResult.warnings`; `goals_json` reports same-name/different-type clashes |
| 8 | stale "⚠ depends on cheat" verdicts never invalidated | 2 | session_pollution | oracles dropped by `_invalidate_from_line`; a clean re-verify overwrites |
| 9 | checkpoint `content_hash` is the **full-file** hash | 5/2 | checkpoints | `_theorem_prefix_hash`; both merge saves refresh it |
| 10 | timeout-abort leaves the pipe frame-shifted | 4 | concurrency | `HOLSession.resync` sentinel flush after the interrupt |
| 11 | **no cursor-level concurrency guard** | 4 | concurrency | per-cursor `asyncio.Lock` in `_state_at_bounded` |
| 12 | mutator taint regex misses `eall`/`enth`/`ee`/`eta` | 4 | parser_coverage | added to both alternatives of `_PROOFMGR_MUTATING_RE` |
| 13 | `replayed=N/M` is a position, not a cost | 5 | reporting | `_NavResult.reached_idx`; the line now reads `reached=N/M` |
| 14 | documented 120 s per-theorem budget is dead code | 5/2 | checkpoints | budget applied in `_load_context_to_line`, timeout auto-cheats; dead `_load_remaining_content` deleted |
| 15 | `show_partial` accepted, documented, unused | — | reporting | the documented refusal is implemented |
| 16 | `status` reports `stale: True` spuriously | — | reporting | falls out of #9 — both sides are prefix hashes now |
| A-4 | edit in one `Resume` body discards the untouched prefix | 5 | checkpoints | falls out of #9 |
| A-5 | pending full session reinit never disclosed | 5 | checkpoints | `status["pending_work"]` |
| A-6 | `TIMEOUT: step k` truncated out of the message | 5 | diagnostics | `_truncate_output` keeps head AND tail |

Test files are `tests/test_repro_<name>.py`; improvements are `tests/test_spec_improvements.py`.

### Sharpest reproductions

**#11** — two real `hol_state_at` calls under `asyncio.gather`, which is exactly
what batching two tool calls produces: a call for a line inside `conc_beta`
returned `Theorem: conc_alpha` with that theorem's goal **and no error**. 9/9
under pytest; 4 of 5 park/target combinations corrupted 3/3.

**#2** — a body with two `ASM_REWRITE_TAC` arms yields a plan containing one,
ending at `end=33` of a 59-char body, with no error from either parser; the block
then reports `No goals (proof complete)` while the *same unmodified file* fails
the next block's load with `parse error at 2:22: expected 'QED'`.

**#9** — the retention logic was dead weight: `_invalidate_from_line` correctly
keeps an earlier theorem's entry, and `_is_context_checkpoint_valid` then rejected
it purely on the full-file hash. Both merge-save paths kept the pre-edit hash, so
a checkpoint written from current session state was invalid the instant it was
saved (`044c6f9f…` vs `26652cb9…`).

**#7** — HOL emits, for a goal with two same-named differently-typed variables:
`WARNING: goal contains variables of same name but different types / x : num, bool`.
The rendered goal shows `x` and `x` with nothing to distinguish them, so losing
the warning is unrecoverable. The warning was present verbatim in the cursor's own
`ef(...)` send output while the returned result had `error=None` and no warnings
field.

---

## 3. Refutations — read before fixing

**#1, reverse-polarity corollary — WRONG.** The review claimed that at a completed
proof's QED line `hol_goals` returns `ERROR: goals_json: …`. Probed directly
across two complete proofs and a revisit: `goals_json()` returns an empty **ok**
list, not an err, and `hol_goals` correctly prints `0 goals … — proof complete.`
Do not "fix" this.

**#4, mechanism — WRONG.** The review attributed the damage to swallowed
redefinition `HOL_ERR`s. HOL4 **accepts** the redefinition: a `Definition` rebinds
to the new rhs and a `Datatype` rebinds `TypeBase.constructors_of`. The real
defect is the **mid-construct resend** — `_loaded_to_line = first_changed - 1`
lands inside the construct, HOL receives a fragment, and the resulting
`Unknown identifier` error is *sticky* across later navigations.

**#10, "won't reproduce" — WRONG, and it was our error.** An early measurement
("HOL answers SIGINT in ~0.1–1 ms, inside the 20 ms window") was reported as
pointing against #10. That figure holds only for CPU-bound tactics. The same
agent's own survey log ended `WORST frame-completion latency after SIGINT:
352.04 ms`; allocation-heavy work measured 0.22, 0.36, 12.84, 49.23, 58.40,
352.04 ms — four of six outside the window. #10 reproduces deterministically.
A partial measurement was relayed as though it settled the question.

Two further caveats that constrain fixes:

- **#3** — the case-sensitive `"no goals"` sub-bug is *masked* by the branch
  ordering (empty goals already win). Fixing the ordering does **not**
  automatically cover it.
- **#10** — the frame shift **persists**. `_drain_pipe` recovers only if the
  previous reply is already in the pipe within its 10 ms poll; with any command
  slower than that — i.e. any real tactic replay — the pipeline stays exactly one
  frame behind indefinitely (5/5 trials × 4 consecutive sends).

---

## 4. Field evidence

Two sources, kept because they say what the source audit cannot: what this costs
in use.

**Session-log mining** — 26 transcripts, 71 MB, **1221 hol4-mcp tool calls**
recovered. Of 396 calls reporting a `total=`, **25.3 min of 46.1 min (55%) ended
in an error**, and **19.6 min across 95 calls** ended in `PROOF BROKEN somewhere
in the opaque step at lines N-N`. Counting all `PROOF BROKEN` reports, **104 of
121 cannot localize the failure**; only 17 give a line and column. These figures
*understate* — calls exceeding the foreground limit were not captured, including
two measured separately at 182 s and 490 s.

**Cross-tool contradiction, reproduced in the field before it was reproduced in a
test.** 29 positions were probed more than once with disagreeing verdicts;
filtering to cross-tool pairs with no intervening edit leaves four, across three
files and **two independent sessions** — including the same position
(`basis_ffiScript.sml:495`) contradicting itself identically in both.

Other recurring shapes worth fixing while nearby: `Failed to set up Resume goal …
No such label in theorem: X` clustering 8–10× on single labels; two different
messages for a bad position, only the rarer naming the valid range; and an
internal timeout surfacing as `Failed to parse step plan: No JSON object found …`
rather than as a timeout.

---

## 5. Improvements (not defects)

`tests/test_spec_improvements.py` — 5 specified, 1 deferred. All 5 are now
implemented and the file is an ordinary regression suite.

1. per-step timing/attribution on `hol_state_at`'s failure path —
   `_replay_steps_with_fallback` records `_step_costs` and reports them
2. a soft per-step budget — the timed-out step is named, not just the budget
3. a loop/blow-up discriminator — completed steps carry an elapsed time, a
   step that only ever hits its budget is reported as a candidate loop
4. `asms=N` in the `[Timing:]` line
5. one "bad position" message, always naming the valid range
   (`_nearest_theorem_ranges`)
6. *(deferred — covered by `test_broken_chain_edit_discloses_pending_cold_replay`;
   implemented as `status["pending_work"]`)*

### On assumption count

`asms=N` is **information, not prediction**. `fs`, `gs`, `gvs`, `simp` and
`metis_tac` can all fail to terminate regardless of assumption count. Two
distinct pathologies are easily conflated:

- **blow-up** — superlinear but terminating; assumption count is a fair correlate.
- **looping** — size-independent; a rewrite that never normalises, or a diverging
  first-order search. **No context-size threshold predicts it.**

Only an empirical per-step timer plus a soft budget covers both, because a
looping tactic never returns.

### Do not build

Static detection of permutative rewrites in a simp-set literal. HOL4 applies them
only under an AC term-order guard (`$HOLDIR/src/simp/src/Cond_rewr.sml:163-167`),
so `simp[…_COMM]` is legitimate and common; the false-positive rate makes the
channel useless. Scope of this negative result: *that particular static check* is
unsound, not that rewrite sets cannot fail to terminate — they can, by mechanisms
the guard does not cover, which is exactly why per-step timing is the answer.

---

## 6. Not covered by a test

These were fixed alongside their findings but have no test of their own.

- **#1** — the advisory-carrying aspect (inside-step note, `⚠ NOT VALIDATED`
  self-cheat, `[auto-cheated deps: …]`, `[prefix-skip mode ON]`). `hol_goals`
  now renders `_state_caveat_lines`, the same helper `hol_state_at` uses, but
  nothing pins that it keeps doing so.
- **#11** — the two `session._drain_pipe()` calls outside `HOLSession._lock`
  (`RuntimeError: read() called while another coroutine is already waiting for
  incoming data` on the failed-proof path). Both now go through
  `HOLSession.drain_stale`, which takes the lock. Observed once; no test.
- **A-5** — disclosure is pinned via `cursor.status`, not via `hol_state_at`, the
  tool a caller actually invokes.
