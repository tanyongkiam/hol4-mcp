# Detecting and attributing looping / blowing-up tactics — design review

Question: how should hol4-mcp detect, attribute, and surface a looping or
combinatorially-exploding tactic, so a caller learns *which tactic* is
pathological and *why*, instead of waiting minutes for an opaque verdict?

Everything cited as `file:line` was read in this tree (or in `$HOLDIR`) for
this review. Sections marked **inference** are reconstructions I could not
verify against a live run.

---

## 1. The machinery as it stands (verified)

### Step model and granularity

- A proof body is decomposed by the SML helper `goalfrag_step_plan_json`
  (`hol4_mcp/sml_helpers/tactic_prefix.sml:598-607`), driven by HOL4's
  TacticParse. Python receives a list of `StepPlan(end, kind, text)`
  (`hol4_mcp/hol_file_parser.py:149-159`); each executable step is wrapped as
  one `ef(goalFrag.expand(<text>));` command (`hol_file_parser.py:133-146`).
- Granularity: one step per linearized fragment. A parenthesized `>- (...)`
  arm, a `>|`, or a `\\`-chain feeding a goal-positional combinator stays **one
  opaque step** (acknowledged in `hol4_mcp/hol_mcp_server.py:1699-1711` and in
  `_detect_inside_step`, `hol4_mcp/hol_cursor.py:2172-2193`). So the finest
  attribution unit any timing scheme can name is a step, which may span many
  source lines. In the episode the culprit was pinned only to "the opaque step
  at lines 10315-10316" — for a 2-line step that is nearly tactic-precision;
  for a 40-line lumped arm it is not, and the existing sub-suspend guidance is
  the drill-down (that part of the design is sound and should stay).

### The state_at replay path records nothing per step

`FileProofCursor.state_at` navigation dispatch (`hol_cursor.py:2098-2130`):

1. **reuse** (file unchanged, forward): `_navigate_steps` →
   `_send_step_batch` (`hol_cursor.py:1757-1783`) — all delta step commands
   concatenated into **one** `session.send`, timeout
   `tactic_timeout × n_cmds` (`_batch_timeout_for`, `hol_cursor.py:1740-1743`).
2. **incremental** (file changed, common prefix): `_try_incremental_navigate`
   (`hol_cursor.py:1809-1835`) — same single batched send.
3. **checkpoint / full replay**: `_replay_to_boundary` →
   `_replay_steps_with_fallback` (`hol_cursor.py:1837-1870`):
   - batch send of the whole prefix, timeout `tactic_timeout × n`;
   - on any batch error: `_setup_proof_goal` again, then **step-by-step**
     re-replay, each step its own `session.send` with per-step timeout
     `self._tactic_timeout or 30` (`hol_cursor.py:1861-1866`), error strings
     `"Tactic replay timed out (>Ns)"` / `"Tactic replay failed: ..."`.

Consequences, all verified in the code:

- **No timing is recorded anywhere on this path.** The fallback loop already
  has per-step boundaries — the exact structure needed for attribution — and
  throws the information away. `StateAtResult.timings` carries only aggregate
  `replay`/`total`/strategy (`hol_cursor.py:2141-2158`), which is what the
  `[Timing: total=…, replay=…, method=…]` line prints
  (`hol_mcp_server.py:1930-1932`).
- **A failed navigation pays for the slow step several times.** Every failing
  strategy falls through to the next: a slow-then-failing step can run once in
  the reuse/incremental batch, once in the full-replay batch, and once more in
  the step-by-step fallback. Nothing in the output says the same tactic was
  executed 2-3×.
- **The per-step timeout already exists** — but only on the fallback leg
  (Python-side, via `HOLSession.send`'s `asyncio.wait_for` + SIGINT to the
  process group, `hol4_mcp/hol_session.py:111-129, 165-174`). On the batch
  legs a single looping step can consume up to `tactic_timeout × n` before
  anything intervenes.
- Interrupt recovery is clean at step granularity: `ef` =
  `proofManagerLib.expand_frag` updates the proofs ref **only on success**
  (`$HOLDIR/src/proofman/proofManagerLib.sml:124-128`; the `handle` clause is
  `Feedback.display_uncaught`, which on Poly/ML is a bare re-raise —
  `$HOLDIR/src/prekernel/Feedback.sml:182` →
  `$HOLDIR/src/portableML/poly/MLSYSPortable.sml:63`). An interrupted or
  failed step leaves the manager at the last good boundary.

### What `hol_check_proof trace=True` already produces, and why state_at lacks it

`hol_check_proof` (`hol_mcp_server.py:1973-2173`) calls
`cursor.execute_proof_traced` (`hol_cursor.py:2321-2448`), which runs the
**whole** proof through one SML call `verify_theorem_json`
(`tactic_prefix.sml:720-726` → `verify_core`, `tactic_prefix.sml:643-716`).
`verify_core.run_one` (`tactic_prefix.sml:645-678`) is precisely the per-step
engine the replay path is missing:

- per-step wall clock (`Timer.startRealTimer`),
- per-step goal counts before/after (`length (top_goals())`),
- per-step **soft budget** via `smlTimeout.timeout timeout_sec`
  (`tactic_prefix.sml:649`) — HOL4's TacticToe timeout: the step runs in a
  forked worker thread, interrupted and if necessary killed on expiry
  (`$HOLDIR/src/AI/sml_inspection/smlTimeout.sml`), reported as a structured
  `{"err":"TIMEOUT after Ns", "real_ms":…}` trace entry.

Python parses this into `TraceEntry(cmd, real_ms, goals_before, goals_after,
error, start_offset, end_offset)` (`hol_cursor.py:340-352, 2414-2434`), caches
it in `_proof_traces`, and `format_steps` renders `step: text  Nms  X→Y`
annotations (`hol_file_parser.py:295-304`). A timeout gets a precise verdict:
`Status: FAILED at step k/N (…)` plus `TIMEOUT: step k spans lines A-B` with
looping-tactic advice (`hol_mcp_server.py:2108-2132`).

Why the same information is not available from `hol_state_at`:

1. Different engine: state_at replays via raw batched `ef(...)` text sent to
   the REPL; check_proof goes through `verify_core`, which does the
   per-step instrumentation in SML.
2. `verify_core` cannot serve state_at as-is: it always runs the **full**
   tactic list from a fresh goal (`drop_all` + `gf`,
   `tactic_prefix.sml:722-723`) and at the end either stores the theorem or
   `drop_all`s the state (`tactic_prefix.sml:702-705`) — state_at must stop at
   a target index and leave the manager **parked** there.
3. `execute_proof_traced` additionally restores a deps-only/predecessor
   checkpoint to match holmake semantics (`hol_cursor.py:2349-2368`), which
   state_at must not do.

None of these is architectural. A parameterized sibling of `verify_core`
(stop index, no store, no drop, park on failure) is a small SML function; the
per-step engine, timeout, JSON shape, and Python parser all exist.

### Existing surfacing, and where it failed in the episode

- The **global budget** message (`_state_at_bounded`,
  `hol_mcp_server.py:48-96`) carries a strong "this is almost always a LOOPING
  TACTIC" advisory — but only fires at 300 s. The episode returned at 182 s,
  so it never fired.
- The **per-tactic timeout attribution** (`hol_mcp_server.py:1788-1796`) fires
  only when `result.error` contains "timed out". If the slow tactic
  eventually *fails* rather than times out (blowup, then error), the output is
  a plain `PROOF BROKEN` with no cost attribution at all.
- Even when the TIMEOUT line is emitted, it is printed **before** the goal
  block. With a 90-assumption goal the body exceeds the default
  `max_output=4096` and `_truncate_output` keeps the **tail**
  (`hol_mcp_server.py:291-314`) — the attribution line is exactly what gets
  truncated away in exactly the big-context scenario. Only `error_footer`
  survives truncation, and it does not carry timing/timeout attribution.
- `_slow_nav_lines` (`hol_mcp_server.py:168-200`) deliberately stays silent on
  the **first** slow navigation (`n < 2`). Sound for its purpose (repeated
  slow probes are the process failure), but it means a first 182 s call says
  nothing.
- Hooks H8 (post-state_at replay ≥30 s reminder) and H6 (post-check_proof
  failure symptom hints) inject guidance, but both are generic — neither can
  name the slow step, because the tool output they parse doesn't contain it.

### Episode reconstruction (**inference**)

`[Timing: total=182172ms, replay=181588ms, method=replay]` pins the run to
strategy 3 (full replay). Consistent reconstruction: the arm-edit invalidated
reuse; the `gvs[word_sub_def, WORD_ADD_COMM]` step — instant at 8 assumptions
— either blew up or looped in the ~90-assumption context (unmeasured, see §1;
either way it ran until a timeout or a failure ended it); that cost was paid
twice (batch + fallback) or three times (incremental batch + replay batch +
fallback), summing to ~178 s inside the arm, and the surviving output was the
opaque-step `PROOF BROKEN` footer with no per-step cost. Note 2-3×60 s ≈
180 s matches the observation almost exactly. I could not verify which
variant occurred; all of them are cured by the same changes below, and the
per-step trace (D1) is what would have told us which mode it was.

Two distinct pathologies, which the rest of this report keeps separate
(correction from the user — an earlier draft conflated them):

- **Blow-up** — superlinear but terminating work in the size of the context.
  Assumption count is a fair *correlate* of this mode; the episode's 8-vs-90
  contrast (0.025 s → minutes, same tactic text) is evidence for this mode
  only.
- **Looping / non-termination** — a rewrite set that never reaches a normal
  form, or `metis_tac`'s search diverging. This mode is **size-independent**:
  `fs`/`gs`/`gvs`/`simp`/`metis_tac` can all loop just as readily on a goal
  with two assumptions. No context-size threshold — and no static signal
  evaluated below — predicts it. The only mechanism that catches it is an
  empirical per-step timer with a soft budget (D1/D2), because a looping step
  never returns on its own.

**Which mode was the episode?** Unknown — the tactic was never measured in
isolation; the run was killed by timeouts both times. The 8-vs-90 contrast is
suggestive of blow-up, but a loop whose entry conditions happened to arise
only in the larger context is equally consistent with what was observed. That
this cannot be answered from the tool output is itself the cleanest argument
for per-step timing: one trace line (`step k: 61000ms(timeout)` vs
`step k: 85000ms, ok`) settles loop-vs-blow-up per occurrence.

One narrower factual note, relevant to direction 3: the *specific* classic
mechanism "permutative rewrite in a simp set loops" is guarded in HOL4 — the
simplifier applies a permutative rewrite only when the instantiated LHS is
strictly greater than the RHS in an AC term order
(`$HOLDIR/src/simp/src/Cond_rewr.sml:163-167`; bounded (`Once`) rewrites
bypass the check — `simp/src/selftest.sml:71`). This defeats that one static
detector; it does **not** mean simp-family calls terminate in general — a
rewrite set can diverge for reasons the guard does not cover (recursive-def
unfolds, GSYM oscillation, rule interaction).

---

## 2. Evaluated directions

### D1 — Per-tactic wall-clock in the replay path

**Cheapest form (Python-only):** time each `session.send` in the existing
step-by-step fallback (`hol_cursor.py:1859-1867`) with `time.perf_counter()`,
keep `(step_idx, ms)` pairs, attach them to `StateAtResult`, and report the
top offenders **in the error footer** (truncation-proof) on every broken/slow
navigation. Zero cost on the happy path (the fallback only runs after a batch
failure — and every failing navigation ends there). In the episode this alone
would have printed something like
`slowest steps: step 41 (lines 10315-10316) gvs[word_sub_def,WORD_ADD_COMM] 61000ms(timeout)`.

**Full form (SML stepped runner):** replace the body of `_send_step_batch`
(`hol_cursor.py:1757-1763`) — inherited by all three navigation strategies —
and `_replay_steps_with_fallback` with one SML call
`replay_steps_timed_json [cmds] soft_sec hard_sec`, modeled on
`verify_core.run_one` minus store/drop: run each `ef` under
`smlTimeout.timeout`, record `real_ms`/`goals_before`/`goals_after`, stop at
the first failure/timeout **leaving the manager parked at the last good
boundary** (safe: failed `ef` does not update the proofs ref, §1), and emit
one JSON trace. This removes the batch/fallback **double-pay entirely** and
gives per-step timing on green paths too (surfaced only above a threshold,
e.g. any step > 5 s, to keep output flat).

- Granularity: still the step. A lumped chain is attributed as the chain +
  line range — same honest limitation the check_proof trace already has; the
  existing "split with `>- suspend`" advice is the drill-down.
- Runtime cost: per step, one `Timer` read, two `length (top_goals())`, one
  worker-thread fork (already paid per tactic in every `hol_check_proof` /
  `verify_all_proofs` run — proven acceptable), one JSON line. The
  per-step Python round-trip cost of naive one-`send`-per-step
  (`_drain_pipe` alone floors ~10 ms/step, `hol_session.py:98-109`) is why
  the SML runner is preferred over splitting the batch in Python.
- False signals: (a) wall clock charges GC and first-use loading of lazy
  theory data to whichever step triggers them — an innocent tactic can look
  slow once; report ms as observations, not verdicts. (b) machine load skews
  real time; `verify_core` already accepts this. (c) a step that is slow only
  because a *previous* step exploded the goal (100 subgoals) is correctly
  timed but the wrong repair target — the `goals_before/after` columns
  disambiguate, so include them.
- What I could not confirm: that `smlExecute.quse_string`-compiled `ef` is
  observationally identical to REPL-compiled `ef` in every parsing corner
  (quotation filters, local parse context). `verify_core` and
  `verify_all_proofs` already run entire proofs this way and are trusted as
  the check_proof engine, so the precedent is strong, but state_at switching
  to it should be regression-tested against the navigation test suite
  (`tests/test_goalfrag_emode.py`, `tests/test_step_divergence.py`,
  `tests/test_state_at_timeout.py`, …).

### D2 — A soft per-tactic budget on the replay path

The machinery exists and is proven: `smlTimeout` per step (check_proof path)
and Python-side per-send SIGINT (fallback path). What is missing is per-step
enforcement on the **batch** legs, where a looping step can burn
`tactic_timeout × n` before the fallback's per-step limit ever applies. The
SML stepped runner (D1 full form) is the per-step budget — directions 1 and 2
collapse into one change.

This is also the **only mechanism that covers both pathologies** (§1): a
blow-up at least returns eventually and can be seen in a timing trace, but a
genuinely looping tactic never returns — no static check, no context-size
heuristic, and no post-hoc trace of a completed run can observe it. Only an
empirical timer with a per-step interrupt turns "the navigation hung" into
"step k did not finish within Ns". That makes D1+D2 the load-bearing
recommendation, not an optimization.

Design point — do not silently tighten semantics: today a slow-but-correct
80 s step *passes* inside a batch (which has `60 × n` slack) and only the
fallback enforces 60 s. A flat per-step hard kill at `tactic_timeout` would
regress such proofs on the green path. Recommended shape: **soft threshold =
`tactic_timeout`** (report the step, keep going is not an option since the
step didn't finish — so: kill), but give the runner a hard cap of
`max(tactic_timeout, remaining_pool)` where `remaining_pool` starts at the
current batch budget, i.e. exactly today's total slack redistributed with
attribution. Either policy must name the step:
`TIMEOUT: step k (lines A-B) exceeded Ns — first suspect a blowup against
this goal's M assumptions; …` — and put it in the **error footer**.
Recovery after the kill is the already-verified parked-manager property plus
the existing `mark_interrupted` path for the outer budget
(`hol_cursor.py:2256-2264`).

### D3 — Static pre-flight warnings

- **Permutative-rewrite detection**: recommend **against**. Verified basis:
  simpLib's ordered-rewriting guard (§1) means `simp/gvs[…, ADD_COMM]` is
  legitimate, common, and usually cheap; the tactic text is not a loop
  predictor. A warning on every simp-set literal from a fixed permutative
  list would fire constantly in healthy proofs (CakeML word proofs use
  `WORD_ADD_COMM` routinely) and train the reader to ignore it. It also
  requires maintaining a theorem list that HOL4 itself computes semantically
  (`is_var_perm`) — the wrong layer for a text-match. Scope of this negative
  result: it defeats *this particular static check*, not looping in general —
  rewrite sets still diverge for reasons the AC-order guard does not cover,
  which is why the empirical timer (D1/D2) is the actual loop detector.
- **Recursive-def-without-`Once` detection** is the one static pattern with a
  decent hit rate (it *is* the #1 cause named in
  `skills/hol4-proving/notes/feedback_replay_discipline.md:36`), but deciding
  "this rewrite target is a recursive definition" statically requires DB
  knowledge Python doesn't have; as a *post-failure hint* H6 already has the
  symptom table for it. Leave it in the guidance/hook layer.
- There is **no pre-flight signal for the looping mode at all** (§1). The
  only warning with any predictive basis is context-conditioned and covers
  the blow-up mode alone — direction 4, with that scope stated explicitly.

### D4 — Reporting context size

Cheap, and worth doing **as information, not prediction**. Assumption count
correlates with the blow-up mode only; it says nothing about loops, which are
size-independent (§1). Verified availability:

- state_at already fetches structured goals at the end of every call
  (`goals_json()` in `_build_result`, `hol_cursor.py:2151`); the top goal's
  assumption count is `len(result.goals[0]['asms'])` — free.
- `hol_goals` already prints `[N asm]` headlines (`hol_mcp_server.py:1044`),
  so the number exists in the UI vocabulary; it just isn't in the state_at
  diagnostic line, and nothing connects it to the *next* step.

Two changes:

1. **Keep**: append `asms=N` (top goal) to the `[Timing: …]` line
   (`hol_mcp_server.py:1930-1932`) and to the check_proof per-step trace
   (2-line SML change in `run_one`: also emit
   `length (fst (top_goal()))`). Justification is informational: it lets a
   reader correlate a slow trace entry with the context it ran in
   (`asms=90` at the arm entry vs `asms=8` in the original lemma), and it
   costs nothing. It predicts nothing by itself.
2. **Demoted — optional, blow-up-scoped advisory** in `hol_state_at`: when
   the step at the cursor (`cursor._step_plan[result.tactic_idx]`) textually
   starts with an assumption-scanning normaliser
   (`gvs|fs|rfs|gs|rw|metis_tac|full_simp_tac`) and the top goal carries ≥ K
   assumptions (K ≈ 40), append one line noting that the next step's cost
   scales with this context (`kall_tac` spent hypotheses / extract a
   `[local]` lemma — skill §Assumption context). This must **not** be
   presented or implemented as a loop detector: it addresses the blow-up mode
   only and will miss **every genuine loop** (loops need no large context).
   False-positive mode: many big-context normaliser calls are fine — keep it
   one line, advisory, high threshold. False-negative modes: all loops, plus
   any heavy step buried inside an opaque chain (not "the step at the
   cursor"). D1/D2 are the mechanisms that actually catch what this misses;
   ship this only alongside them, if at all.

### D5 — Guidance rather than mechanism

The corpus already covers the *knowledge*: SKILL.md symptom rows 21 and 26
route "a rewrite loops or blows up" and "fs/gvs/metis suddenly takes 60s" to
`feedback_hol4_mcp_proving` §Rewriting-that-loops (lines 35-47) and
§Assumption-context (lines 138-143, including the exact fixes: `kall_tac` the
heavy hyps, or extract a `[local]` helper). `feedback_replay_discipline`
§TIMEOUT (lines 34-38) and the 300 s-budget message both teach
cheat-the-frontier diagnosis.

Why it did not prevent the episode:

1. **No tool output presented the symptom.** The rows trigger on "a tactic
   takes 60 s" — but the caller never learned that *a tactic* took 60 s; they
   saw one 182 s aggregate. The symptom index cannot fire on a symptom the
   tool hides. That is the mechanism gap (D1/D2, with D4 as supporting
   information), not a guidance gap.
2. **The suspect lists name only the looping mode.** Both the §TIMEOUT note
   and the `_state_at_bounded` message name recursive-def unfolds, GSYM
   oscillation, metis — not the blow-up mode ("an assumption-scanning
   normaliser × a large inherited context"), which is at least the plausible
   reading of the episode (unmeasured, §1) and a common CakeML-scale case.
   The lists should name both modes.
3. **Nothing warns at the inlining moment.** The episode's proximate cause was
   *moving* a proof body from an 8-assumption context into a 90-assumption
   one. Gate 1 / `feedback_suspend_resume` drive inline-back as hygiene; the
   §Assumption-context note even names extraction as the *fix* — but no rule
   says "when inlining a body into a heavier context, its normaliser calls
   inherit the new context; re-check gvs/fs/metis choices". That is a genuine
   one-sentence gap.

Proposals (per `notes/reference_hol4_docs.md` governance — propose, don't
edit; a behaviour change must move docstring + hook + skill in one pass):

- Add the blow-up mode as a second suspect family alongside the existing
  loop suspects — "assumption-count blowup: gvs/fs/metis against a large
  context (the same text that is instant in a small lemma)" — in
  `feedback_replay_discipline` §TIMEOUT and in the `_state_at_bounded`
  message (`hol_mcp_server.py:84-95`), keeping the loop suspects first (a
  loop needs no large context).
- Add one bullet at the inline-back site (skill Gate 1 / iteration-loop step
  6 or `feedback_suspend_resume`): inlining moves the body under the parent's
  full assumption context — expect assumption-scanning steps to get more
  expensive; re-check them, or `kall_tac`/extract per §Assumption context.
- When D1/D4 ship: update H6/H8 and the `hol_state_at`/`hol_check_proof`
  docstrings to describe the new `slowest steps` / `asms=` markers
  (governance step 4), and let H8 quote the named slow step instead of the
  generic reminder.

### Extras found while reading

- **Attribution must ride the error footer.** Any new cost/timeout line
  appended mid-body can be truncated away by `_truncate_output` exactly when
  the goal is huge (§1). Move/duplicate the `TIMEOUT: step k …` attribution
  (`hol_mcp_server.py:1788-1796`) into `error_footer` regardless of the rest
  of this plan.
- `--tactic-timeout` CLI help says "default: 5.0" but the effective default is
  60.0 (`hol_mcp_server.py:37` vs `:2217`); `FileProofCursor`'s own
  constructor default of 5.0 (`hol_cursor.py:383`) is overridden at the only
  server call site (`hol_mcp_server.py:1503`). Cosmetic, but it misleads
  anyone reasoning about budgets. (Noted for the concurrent audit; not acted
  on here.)
- `TraceEntry.usr_ms/sys_ms` are dead (always 0 from `verify_core`;
  `timed_step_json` emits them but nothing calls it —
  `tactic_prefix.sml:617-638`). If D1 lands, CPU-vs-real per step would
  actually be a nice loop-vs-GC discriminator, but that's optional polish.

---

## 3. Recommended plan (ranked, cheapest high-value first)

Ordering note: per-step timing + a soft per-step budget (items 1 and 2) are
the **only** mechanisms that cover both pathologies in §1 — a looping tactic
never returns, so nothing static or context-based can catch it. They carry
the plan; item 3 is cheap supplementary information about the blow-up mode
only.

1. **Footer-proof the existing attribution + time the fallback replay**
   (D1 cheap form). Python-only: perf-counter each step in
   `_replay_steps_with_fallback`, attach `(idx, ms, err)` to `StateAtResult`,
   render `slowest steps` + the step's line span in the **error footer** of
   `hol_state_at`; move the existing `TIMEOUT: step k` line into the footer
   too. Fires on every broken/slow navigation (all failures end in the
   fallback), and the per-step SIGINT timeout already there means loops are
   caught and named, not just blow-ups. ~0.5 day + tests.
2. **SML stepped runner for the replay path** (D1 full + D2): a parameterized
   sibling of `verify_core` behind `_send_step_batch` /
   `_replay_steps_with_fallback` — per-step timing always, per-step soft
   budget via `smlTimeout`, single-pay on failure, manager parked at the last
   good boundary, precise `step k did not finish within Ns` verdicts —
   the loop detector, and the loop/blow-up discriminator (a blow-up
   eventually shows a finished `real_ms`; a loop only ever shows timeouts).
   Preserve today's total budget as a shared pool to avoid regressing
   slow-but-correct steps. ~2-3 days incl. regression tests against the
   navigation suite.
3. **Context-size reporting** (D4): `asms=N` in the `[Timing:]` line and an
   `asms` column in the check_proof trace (2-line SML change) — cheap
   *information* for reading traces, not a predictor. The optional next-step
   advisory (normaliser × ≥ ~40 assumptions) is blow-up-scoped only and
   misses every genuine loop; ship it, if at all, alongside 1-2 and worded
   accordingly. ~0.5 day.
4. **Corpus/message proposals** (D5): add the blow-up mode to the suspect
   lists alongside the existing loop suspects, the
   inline-into-heavier-context bullet, and — once 1-3 ship — the paired
   H6/H8/docstring updates required by corpus governance. Hours, gated on
   user approval per `reference_hol4_docs.md`.
5. **Do not build** a permutative-rewrite pre-flight scanner (D3): simpLib's
   ordered-rewriting guard (`Cond_rewr.sml:163-167`) makes the pattern
   legitimate and common; the false-positive rate would destroy trust in the
   channel. The negative result is about that particular static check —
   rewrite sets can still diverge for reasons the guard does not cover, which
   is exactly what items 1-2 exist to catch empirically.
