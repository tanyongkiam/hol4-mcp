# MCP navigation/caching bug review

Audit of the navigation and caching machinery on branch `localfixes`, by source
reading (no HOL session was started; the test suite was not run). Severity
categories: 1 = silent wrong state, 2 = invalidation gap, 3 = position/step
mapping, 4 = concurrency/lifecycle, 5 = performance. Confidence: CONFIRMED =
every branch of the claimed path traced in source (and/or field-observed with
the mechanism located); PLAUSIBLE = the code reads wrong but a timing- or
environment-dependent guard could not be ruled out without running it.

Files read IN FULL: `hol4_mcp/hol_cursor.py`, `hol4_mcp/hol_file_parser.py`,
`hol4_mcp/hol_mcp_server.py`, `hol4_mcp/hol_session.py`,
`hol4_mcp/sml_helpers/tactic_prefix.sml`, `hol4_mcp/quote_check.py`,
`tests/test_state_at_position_clamping_bug.py`,
`tests/test_derived_theorem_staleness.py`.
Skimmed: `tests/` (names, docstrings, fixture heads of
`test_failed_proofs_invalidation.py`, `test_chain_broken_scope.py`,
`test_context_checkpoints.py`, `test_interrupt.py`, `test_state_at_timeout.py`,
`test_verification.py`), `LOCAL_CHANGES.md`, the three `*_NOTES.md` files,
`hol4_mcp/_mcp_cancel_patch.py` (not reviewed in depth). Only one skipped test
exists (`test_hol_file_parser.py:85`, fixture-missing guard) — no xfail/known-bug
tests were found; one *notes file* documents an OPEN bug (see finding 4).

---

## 1. `hol_goals` silently drops navigation errors and every advisory

**Severity 1 — CONFIRMED.** `hol_mcp_server.py:1003-1007`: after
`_state_at_bounded`, `hol_goals` returns an error **only when
`result.error and not result.goals`**. A broken replay almost always comes back
with `error` set AND non-empty `goals` (the goals at the point replay stopped,
fetched unconditionally by `_build_result`, `hol_cursor.py:2141-2170`), so the
error is discarded and the failure-point goals are printed as
`N goal(s) (at line L…)`.

This exactly reproduces the field observation: `hol_state_at(line=L)` says
`PROOF BROKEN` (its `is_broken` machinery at `hol_mcp_server.py:1675-1834`),
while `hol_goals(line=L)` on the same unmodified file prints a clean goal count
labeled with the requested line. It also explains the entry-line/exit-line
identity: for a target past a broken opaque step k, replay stops at step k's
entry; for a target at step k's entry, replay legitimately lands there — same
state, and `hol_goals` labels both with the requested line, one of them with a
suppressed error.

`hol_goals` also omits every advisory that `hol_state_at` emits
(`hol_mcp_server.py:1868-1923`): the `inside_step_idx` "state shown is the
step's ENTRY" note, the `⚠ NOT VALIDATED` self-cheat refusal, the
`[auto-cheated deps: …]` list, and the `[prefix-skip mode ON]` notice. With
`skip_prefix=True`, `hol_goals` presents goals resting on cheated statements
with no marker at all.

~~Reverse-polarity corollary: at a *complete* proof's QED line, `goals_json()`
errors ("no goals"), so `hol_goals` returns `ERROR: goals_json: …` instead of
"0 goals — proof complete".~~ **REFUTED — do not fix.** Probed directly across
two complete proofs and a revisit: `goals_json()` returns an empty **ok** list,
not an err, and `hol_goals` correctly prints `0 goals … — proof complete.`

**Fix:** `hol_goals`'s line-navigation path must apply the same
broken/complete/advisory classification as `hol_state_at` (or share the
rendering), instead of the single `error and not goals` test.

## 2. Unbalanced delimiters silently truncate the step plan → false "proof complete"

**Severity 1 — CONFIRMED (field-observed; mechanism located; the exact
HOLSourceParser recovery behaviour was not executed).** Two parsers disagree
about where a block ends, and nothing cross-checks them:

- Python (`hol_file_parser.py:757-814` for Resume, similarly for Theorem)
  finds the block's `QED` **textually**, so `proof_body` contains everything up
  to QED, surplus `)` included.
- The step plan comes from `goalfrag_step_plan_json`
  (`sml_helpers/tactic_prefix.sml:598-607`), whose
  `parseTacticBlockFromString` (`tactic_prefix.sml:30-44`) takes **the first
  declaration** `HOLSourceParser.parseSML` yields and never checks that the
  parse consumed the whole body. A surplus `)` ends the expression early; the
  tactics after it are silently dropped from the plan.
- Python (`hol_cursor.py:1650-1661` in `enter_theorem`, `2072-2087` in
  `_reparse_steps_on_edit`; `hol_file_parser.py:381-418`
  `parse_step_plan_output`) accepts the plan with **no coverage check** — e.g.
  that the last step's `end` reaches `len(proof_body)` (modulo trailing
  whitespace/comments).

Result: the truncated 35-step prefix replays, completes, and `hol_state_at`
reports `No goals (proof complete)`, `replayed=35/35` — for a block whose file
form does not even parse. The contradiction only surfaces when the *next*
block is targeted: `_load_context_to_line` then sends the raw broken block text
to HOL (`hol_cursor.py:1538-1546`), which fails with
`parse error … expected 'QED'` — confirming the file is broken while the
report on the block itself said complete.

**Fix:** validate plan coverage after `parse_step_plan_output` (last `end` vs
`len(proof_body)` net of trailing comment/whitespace) and refuse navigation
with a parse-coverage error naming the uncovered span; ideally also make the
SML side error when input is not fully consumed.

## 3. `hol_check_proof` Definition fallback reports OK whenever the goals list is empty — including on errors and timeouts

**Severity 1 — CONFIRMED.** `hol_mcp_server.py:2064-2078`: when
`execute_proof_traced` returns an empty trace for a `Definition`, the fallback
navigates to the End line and then tests

```python
if not result.goals or no_goals_ok:
    lines.append("Status: OK (Definition termination proof)")
elif result.error: ...
```

`not result.goals` is checked **before** `result.error`. Every error path that
returns empty goals — the `_state_at_bounded` overall-budget TIMEOUT
(`hol_mcp_server.py:78-96` returns `goals=[]`), a goal-setup failure, a
goals_json parse failure — therefore yields `Status: OK (Definition termination
proof)` for a termination proof that was never validated. Additionally
`no_goals_ok` uses a case-sensitive `"no goals" in result.error` where the
equivalent test in `hol_state_at` uses `.lower()` (`hol_mcp_server.py:1663`).

**Fix:** order the branches error-first, and only report OK when there is no
error (or the error is exactly the no-goals-marker, matched case-insensitively).

## 4. Edits to untracked constructs (plain `Definition`, `Datatype`, multi-line derived theorems) are silently ineffective; the reload can start mid-construct

**Severity 1/2 — CONFIRMED mechanism by reading; field-corroborated by
`HOL_STATE_AT_DEF_EDIT_STALENESS_NOTES.md` (status: OPEN).** The partial-reload
path only understands the constructs `parse_theorems` tracks
(Theorem/Triviality, Definition-with-Termination, Resume). Everything else is
"pre-content". Three compounding defects:

- **Off-by-one truncation.** `_reparse_if_changed`
  (`hol_cursor.py:530-533`) sets `_loaded_to_line = first_changed - 1`. The
  loader's invariant (established by `_load_context_to_line`,
  `hol_cursor.py:1493-1510`) is "lines `1..loaded_to_line-1` are loaded; line
  `loaded_to_line` is next to send", so the correct truncation is
  `first_changed`. As written, the unchanged line `first_changed - 1` is
  re-sent — and when it is a construct's closing `End`/`QED` or a line inside
  one, the resend fragment is garbage.
- **Mid-construct resend.** For an edit inside an *untracked* multi-line
  construct, the resend starts at `first_changed - 1`, i.e. mid-construct: a
  syntactically broken fragment. When it fails loudly this is the notes file's
  Defect B (`Unknown identifier` / parse error, region unreachable). Nothing
  snaps the truncation to a construct boundary.
- ~~**Swallowed redefinition errors → silent staleness.** The session heap
  still holds the old definition; HOL rejects the re-definition with a
  `HOL_ERR` that `_send_and_check` discards, so every goal shown is computed
  against the pre-edit constant.~~ **REFUTED — this mechanism does not
  exist.** HOL4 **accepts** the redefinition: a `Definition` rebinds to the new
  rhs and a `Datatype` rebinds `TypeBase.constructors_of`. The field staleness
  comes entirely from the mid-construct resend above — HOL receives a fragment,
  and the resulting `Unknown identifier` is *sticky* across later navigations.

**Fix:** snap the truncation to a construct boundary.

## 5. `_session_dirty` is honored only by the reuse path — the incremental path navigates from a polluted position

**Severity 1 — CONFIRMED.** A `hol_send` that mutates the proofManager (the
explicitly sanctioned "short `e` probe on a navigated frontier") sets
`cursor._session_dirty = True` (`hol_mcp_server.py:866-874`). The flag is read
**only** in `_try_reuse_state` (`hol_cursor.py:1796-1799`). The incremental
strategy never checks it:

- User navigates to step 5 (`_pos` = 5, initialized), probes with
  `hol_send("e(tac)")` — live goal stack now one step past `_pos`.
- User edits the file inside the active theorem (say the step-5 tactic).
- `state_at`: `changed=True` skips strategy 1; `_reparse_steps_on_edit`
  (`hol_cursor.py:2091-2096`) gates incremental only on
  `_pos.initialized and old_tactic_idx > 0 and first_diff > 0` — all true —
  and `_try_incremental_navigate` (`hol_cursor.py:1809-1835`) navigates
  *relative to* `old_tactic_idx=5`. With target ≤ first_diff this is
  `_navigate_steps(5,5)` → immediate success with **zero commands issued**.
- Goals returned are the post-probe state labeled as the file's state at the
  target; `_update_position` (`hol_cursor.py:2132-2139`) then **clears the
  dirty flag**, so every subsequent call trusts the polluted position.

(The `mark_interrupted` path is safe because it also resets `_pos` to
uninitialized, which fails the incremental gate; the `hol_send` taint leaves
`_pos` intact, which is exactly the hole.)

**Fix:** `_session_dirty` must also veto the incremental strategy (return
`None` from `_reparse_steps_on_edit`, or check the flag in
`_navigate_to_target` before strategy 2).

## 6. Backward `state_at` without a checkpoint replays in a future-polluted context; checkpoints saved from that state understate `_loaded_to_line`

**Severity 1/2 — CONFIRMED by reading (design gap; the hazard is handled for
`hol_check_proof` but not for `state_at`).** `execute_proof_traced` explicitly
restores a predecessor context checkpoint or deps-only state when
`_loaded_to_line > thm.start_line` (`hol_cursor.py:2349-2368`, with the
rationale in its comment). The `state_at` path has no such handling: after
navigating a later theorem T10 (loading T3..T10 into the heap), `state_at` on
earlier T2 falls to `_replay_to_boundary` → `_setup_proof_goal`
(`hol_cursor.py:1682-1732`), which does `drop_all` + `gf` **in the current
session** — with T3..T10 bound, any of their `[simp]` attributes registered in
the ambient simpset, and T2 itself bound. Consequences:

- T2's replay can succeed (or fail) differently than under Holmake — e.g. a
  later `[simp]` theorem closes a goal, or a tactic resolves a name that is a
  forward reference in file order. A "No goals (proof complete)" here does not
  correspond to the file's semantics at that point.
- On a full replay of T2 in this state, `_save_end_of_proof_checkpoint`
  (`hol_cursor.py:1908-1910`) snapshots the **polluted** heap; a later
  `_load_checkpoint_and_backup` then sets
  `_loaded_to_line = thm.proof_end_line` (`hol_cursor.py:886-888`) —
  understating what the restored heap actually contains, so a subsequent
  `_load_context_to_line` re-sends T3.. into a heap that already has them
  (theorem re-binding is tolerated; untracked definitions hit finding 4's
  swallowed-redefinition path).

**Fix:** the `state_at` full-replay path should restore a valid predecessor
context (as `execute_proof_traced` does) before `_setup_proof_goal` when
`_loaded_to_line` extends past the target theorem — or at minimum stamp
checkpoints with the true loaded extent.

## 7. HOL's "same name but different types" goal warning (and all goal-time diagnostics) never reach the caller on the structured paths

**Severity 1 — CONFIRMED (pipeline traced end-to-end in source; the one
unexecuted assumption is that Poly/ML's toplevel pretty-prints the `proof`
value returned by `gf`/`ef` in this session — standard HOL REPL behaviour,
and nothing in the MCP suppresses it).** HOL4 emits

```
WARNING: goal contains variables of same name but different types
```

from `check_vars` in the **goal pretty-printer**
(`$HOLDIR/src/proofman/goalStack.sml:231-259`), which is invoked by every
variant of `ppgoal` (`goalStack.sml:314-343`, exported as
`pr_goal = ppgoal`) and hence by the GOALFRAG state printer the navigation
machinery drives (`$HOLDIR/src/proofman/goalFrag.sml:228-280`,
`pp_goalstate` uses `goalStack.pr_goal`). It is a property of printing a
*goal*; it cannot arise from printing *terms*. Per user report the condition
it flags is never benign — and because `term_to_string` does not show types
by default, the colliding variables are **indistinguishable** in the goal
text the MCP renders, so the caller has no way to detect the condition once
the warning is lost.

Per-path determination — which of (a) never generated / (b) generated but
discarded / (c) truncated holds:

- **`hol_state_at` and `hol_goals` (both the line-navigation and live
  sub-paths): (a) for the caller-facing rendering, (b) for every copy that
  is generated.** The goal text returned to the caller is built exclusively
  by `goals_json()` → `goal_to_json` → `Parse.term_to_string` per
  assumption/conclusion (`sml_helpers/tactic_prefix.sml:69-80`), which never
  runs `ppgoal`/`check_vars` — unreachable by construction (the Resume-entry
  rendering via `extract_resume_goal_json`, `tactic_prefix.sml:777-787`, is
  likewise term-level). Meanwhile the warning IS generated during
  navigation: `gf `goal`;` and each `ef(goalFrag.…);` return a `proof`
  whose toplevel pretty-print goes through `pp_goalstate` → `check_vars`,
  landing in the raw output of those sends — which Python only error-scans
  and then discards on success (`hol_cursor.py:1757-1763` `_send_step_batch`
  returns a bool; `hol_cursor.py:1850-1852` discards the batch result;
  `hol_cursor.py:1723-1730` discards the `gf` output after the error check).
  So the "unreachable by construction rather than filtered out" hypothesis
  is right for the *final rendering channel*, but incomplete: generated
  copies also exist mid-replay and are dropped by output capture.
- **`hol_check_proof`: (a).** `verify_core`
  (`sml_helpers/tactic_prefix.sml:643-716`) reports only goal **counts**
  in its JSON trace — no goal rendering at all, so `check_vars` cannot
  contribute; tactics run via `smlExecute.quse_string`, and Python extracts
  only the JSON line from the response (`_try_find_json_line` →
  `_find_json_line`, `hol_file_parser.py:51-100`), dropping every other
  line ((b) for any diagnostic that does appear in the raw stream). The
  Definition fallback goes through `goals_json` (finding 3's path) — (a).
- **`hol_send`: NOT dropped.** Raw passthrough
  (`hol_mcp_server.py:865-878`): a probe that pretty-prints a proof state
  (e.g. `e(tac);`) delivers the warning. Only marginal (c) risk from
  `max_output` truncation — and since `check_vars` appends *after* the
  goal, the tail-keeping truncation actually favours it. The irony: the
  server instructions steer users away from `hol_send` toward
  `hol_goals`/`hol_state_at` — exactly the channels where the warning is
  unreachable.

**Wider class — yes, and it is the bigger finding.** The same mechanism
drops *every* HOL diagnostic emitted during successful navigation or
verification: `<<HOL message: inventing new type variable names…>>`,
overload-resolution messages, `<<HOL message: Stashing suspended
theorem…>>`, simplifier notes, all `WARNING:` output. The rule that
distinguishes the counter-examples where diagnostics were seen to survive:
**raw-passthrough channels preserve them** — `hol_send`, `hol_log`/holmake
log files (`hol_mcp_server.py:1341-1357, 1393-1396`, written by Holmake
outside the MCP session), and *error strings that embed raw send output*
(`_error_reason`, `hol_cursor.py:84-101`;
`f"Tactic replay failed: {step_result}"`, `hol_cursor.py:1866`;
`_format_context_error`'s generic tail, `hol_cursor.py:271`) — which is why
an `<<HOL message…>>` can surface *inside* a `hol_check_proof` error.
**Structured channels regenerate content** (goals from `term_to_string`,
progress from counters, plans from JSON) and drop everything else; on
success paths the raw output is discarded wholesale, and `_is_hol_error`
deliberately classifies `<<HOL message:`/warnings as non-errors
(`hol_cursor.py:117-131`), so they cannot even ride the error path. Net: a
HOL diagnostic reaches the caller iff something *fails* nearby or the user
bypasses the workflow tools.

**Fix:** two layers — (1) specifically, `goals_json`
(`tactic_prefix.sml:69-80`) should replicate `check_vars` (fold
`FVL (w::asl)` by name, keep names with >1 type) and emit the collision set
as a `warnings` field that `hol_state_at`/`hol_goals` render; (2) generally,
either have the SML helpers capture-and-return diagnostics emitted during
tactic execution, or have the Python side scan otherwise-discarded replay
output for `WARNING:` / `<<HOL message:` lines and attach them to the
result instead of dropping them.

## 8. Stale "⚠ depends on cheat" verdicts are never invalidated

**Severity 2 — CONFIRMED.** `_theorem_oracles` is populated on verification
(`hol_cursor.py:2441-2447`, `2664-2671`) but:

- `_invalidate_from_line` (`hol_cursor.py:968-1051`) cleans checkpoints,
  traces, tc_goals, resume_goals and `_failed_proofs` — **not**
  `_theorem_oracles`. It is cleared only on pre-theorem edits / broken-chain
  reinit / skip-prefix toggle (`hol_cursor.py:554, 572, 2219`).
- On re-verification the entry is overwritten **only when the new oracle list
  is non-empty** (`if oracles: self._theorem_oracles[…] = oracles`), so a
  now-clean result never erases the old verdict.

Scenario: theorem T once depended on an auto-cheated dep; the user fixes the
dep; `hol_check_proof T` re-runs clean — but
`hol_mcp_server.py:2135-2145` still finds the stale entry and reports
`Status: OK … ⚠ depends on cheat` (now with an empty `[auto-cheated deps]`
explanation, since `_failed_proofs` *was* correctly invalidated). Wrong in the
safe direction, but it permanently contradicts the tool's own dep listing and
sends the user hunting a cheat that no longer exists.

**Fix:** delete the theorem's oracle entry in `_invalidate_from_line`, and
assign unconditionally (including empty) after each verification.

## 9. Checkpoint `content_hash` is the full-file hash: any edit anywhere kills every checkpoint, and merge saves never refresh the hash

**Severity 5 (with a category-2 flavor) — CONFIRMED.**
`_is_checkpoint_valid` / `_is_context_checkpoint_valid`
(`hol_cursor.py:746-766`) require `ckpt.content_hash == self._content_hash`
— the hash of the **whole file**. So although `_invalidate_from_line`
carefully *retains* checkpoints for theorems before the change point, they can
never validate again after any edit: `_find_predecessor_checkpoint`
(`hol_cursor.py:900-911`) and `_replay_to_boundary`'s checkpoint fast path are
dead the moment the file differs. Worse, both merge branches —
`_save_end_of_proof_checkpoint` (`hol_cursor.py:800-811`) and
`_save_context_checkpoint` (`hol_cursor.py:839-849`) — update paths but **not**
`content_hash` on an existing entry, so a checkpoint re-saved under the current
file content keeps the stale hash and is judged invalid immediately after
being written. Net effect: predecessor/backward checkpointing only works in a
never-edited file; after the first edit, `hol_check_proof` on an earlier
theorem always falls back to `_restore_to_deps` + full prefix re-replay. This
is a large, silent contributor to the field-observed pathological wall-clock
times (see finding 13).

**Fix:** stamp checkpoints with a *prefix* hash (content up to the theorem's
`proof_end_line`, which `_check_stale_state` already knows how to compute) and
refresh the hash on every save.

## 10. Timeout-abort leaves the output pipe frame-shifted; `_state_at_bounded` never flushes

**Severity 4 — CONFIRMED.** An early measurement ("HOL answers SIGINT in
~0.1–1 ms, inside the 20 ms window") was reported as pointing AGAINST this
finding. That was our error: the figure holds only for CPU-bound tactics. The
same survey ended `WORST frame-completion latency after SIGINT: 352.04 ms`;
allocation-heavy work measured 0.22, 0.36, 12.84, 49.23, 58.40 and 352.04 ms —
four of six outside the window. The frame shift also **persists**: `_drain_pipe`
recovers only if the previous reply is already in the pipe within its 10 ms
poll, so with any command slower than that the pipeline stays exactly one frame
behind indefinitely (5/5 trials × 4 consecutive sends).

On overall-budget expiry, `_state_at_bounded` cancels `state_at` mid-`send`,
SIGINTs HOL, and returns (`hol_mcp_server.py:64-96`) — the response to the
in-flight command is **never read**. Recovery relies on the next `send`'s
`_drain_pipe` (`hol_session.py:98-109`), which polls with a 10 ms timeout: if
HOL is still unwinding the interrupt (common for a heavy tactic), the drain
gets nothing, the next command is written, and `_read_response`
(`hol_session.py:131-146`) returns at the **first** NUL frame — which is the
aborted command's late output, not the new command's. From then on every
response can be attributed to the previous command. Since responses are parsed
by scanning for the first `{"ok":…}` line (`hol_file_parser.py:51-100`), a
stale `goals_json` frame can satisfy a later `goals_json` call with the wrong
goals. `mark_interrupted` (`hol_cursor.py:2256-2264`) resyncs the *cursor*
(position/dirty) but nothing resyncs the *pipe*; contrast `hol_interrupt`,
which deliberately flushes with a dummy `send(";")` after 0.1 s
(`hol_mcp_server.py:1086-1092`). Also `mark_interrupted` does not reset
`_loaded_to_line`, so a cancellation mid-`_load_context_to_line` can leave the
tracker behind what HOL executed; the re-send is mostly benign for theorems but
hits finding 4's swallowed-redefinition path for definitions.

**Fix:** after the timeout interrupt, flush to a fresh prompt (dummy send with
a real wait) before returning, and/or tag commands with a nonce echoed in the
response.

## 11. No cursor-level concurrency guard — parallel tool calls interleave navigation

**Severity 4 — PLAUSIBLE.** `HOLSession.send` is serialized by
`HOLSession._lock` (`hol_session.py:47,116`), but `FileProofCursor` has no
lock, and FastMCP executes concurrent tool calls as concurrent tasks. Two
overlapping `hol_state_at`/`hol_goals`/`hol_check_proof` calls on the same
session interleave at every `await`: their replay command streams alternate on
the single proofManager, and both read `goals_json()` from a state neither of
them established. Both then report goals with no error. Agents routinely batch
independent tool calls, so this is a realistic trigger. (Related registry-level
races — `_prune_idle_sessions` stopping a session between `_get_cursor` and
use, `hol_start`'s double-registration window at
`hol_mcp_server.py:619-628` — are mitigated but the cursor itself has
nothing.)

**Fix:** a per-cursor (or per-session-entry) asyncio lock around
navigate-and-read-goals sequences.

## 12. Proof-state-mutator taint regex misses bare `eall`/`enth`/`ee`/`eta`

**Severity 4 — CONFIRMED (regex reading).** `_PROOFMGR_MUTATING_RE`
(`hol_mcp_server.py:683-694`) matches qualified
`proofManagerLib.(e|b|…|eall|ee|…)` and a bare-driver list
`(?<![\w.])(?:e|ef|expand|expandf|expand_list|sg|g|gf|b|r)\s*[(`]` — but bare
`eall (tac)`, `enth tac 1`, `eta …` (the "explicit low-level escape hatches"
that `tactic_prefix.sml:906-910` deliberately leaves unshadowed) match neither
alternative. A `hol_send("eall(simp[])")` mutates the live goal stack without
setting `_session_dirty`, so the next `state_at` on an unchanged file takes the
`reused` fast path (`hol_cursor.py:1796-1807`) and returns the polluted live
goal with no error — the exact silent-desync bug the taint exists to prevent,
and the regex's own comment claims it "errs toward over-matching".

**Fix:** add `eall|enth|ee|eta` (and any other bare drivers) to the bare list.

## 13. `replayed=N/M` is a position, not a cost; the dominant wall-clock work is never counted

**Severity 5 — CONFIRMED (answers field observation 3).** `tactics_replayed`
is `_NavResult.actual_replayed`, which is:

- `target.tactic_idx` for the `reused` strategy (`hol_cursor.py:2109`) — even
  when zero commands were issued;
- `target.tactic_idx` for `incremental` (`hol_cursor.py:2115`) — even though
  only the delta past `first_diff` ran;
- `tactic_idx` for the checkpoint path (`hol_cursor.py:1884-1885`) — a
  `loadState` + `backup_n`, no tactics run;
- the count of target-theorem `ef()` commands actually issued only for the
  full-`replay` strategy (`hol_cursor.py:1904`).

What it never includes: prefix context loading in
`enter_theorem`/`_load_context_to_line` — every earlier theorem's **entire
proof re-proved** (up to 300 s each, see finding 14) — plus goal setup and
`goalfrag_step_plan_json` parsing. That is what dominated the measured times
(`0/2`→4.2 s cold-setup; `1/2`→182 s = prefix re-proof after an edit, amplified
by finding 9's global checkpoint invalidation; `35/35`→58 s = target-theorem
tactic cost). The counter is fine as a *position* indicator, but it is
presented next to `[Timing: …]` in a way that invites reading it as work done.

**Fix (reporting):** either rename/annotate (`position=N/M`) or report replayed
commands and prefix-theorems-loaded separately.

## 14. The documented per-theorem 120 s auto-cheat budget never applies on the live navigation path — its implementation is dead code

**Severity 5/2 — CONFIRMED.** `PER_THEOREM_TIMEOUT = 120`
(`hol_cursor.py:51-54`) and the timeout-auto-cheat logic
(`interrupt → _cheat_failed_theorem(thm, "timeout >120s loading whole proof")`)
live in `_load_remaining_content` (`hol_cursor.py:1373-1465`) — which **no
production code calls** (grep: only its definition, comments, and none of the
tools). The live loader `_load_context_to_line` (`hol_cursor.py:1467`) sends
each prefix theorem with the caller's `timeout` (default **300 s**,
`hol_cursor.py:1540`) and classifies a TIMEOUT as **fatal**
(`_is_fatal_hol_error`, `hol_cursor.py:169-170`) — no auto-cheat, whole
navigation fails (usually the `_state_at_bounded` 300 s budget fires first and
blames "a looping tactic you just wrote", which for a slow *prefix* theorem is
the wrong diagnosis). So: a slow prefix theorem costs up to 300 s and then
aborts navigation instead of being cheated-and-reported at 120 s as the
constant's comment, `_target_self_cheated_lines`' wording
(`hol_mcp_server.py:210-218`), and the `_failed_proofs` docstring all promise.
`hol_check_proof`'s `enter_theorem` path has **no** overall budget at all, so
its prefix loading can spend 300 s per theorem unbounded. Auto-cheat on the
live path currently fires only for genuine tactic *errors* (via
`_handle_theorem_error`), never for timeouts.

**Fix:** either delete `_load_remaining_content` and port its per-theorem
timeout/auto-cheat handling into `_load_context_to_line`, or wire it back in;
align the timeout constant with the documentation.

## 15. `show_partial` parameter of `hol_state_at` is accepted, documented, and unused

**Minor (doc/UI) — CONFIRMED.** `hol_mcp_server.py:1543` declares it,
`1559-1561`/`1569-1570` document "the default behavior is to refuse to show
goals … Set show_partial=True to see the best-effort goals anyway", and the
body never reads it (only a stale comment at `1800`). Actual behavior: goals at
the failure point are always shown (first goal, or all with `all_goals=True`).
The docstring promises a refusal semantics that does not exist — an agent may
believe goals shown after a failure were opt-in "best effort" when they are the
default.

**Fix:** remove the parameter or implement the documented refusal.

## 16. `status` reports `stale: True` spuriously after any checkpoint load

**Minor — CONFIRMED.** `_check_stale_state` (`hol_cursor.py:610-616`) hashes
`content[:loaded_to_line-1]` and compares with `_loaded_content_hash`. But
`_load_checkpoint_and_backup` (`hol_cursor.py:886-888`) and
`_load_context_checkpoint` (`hol_cursor.py:948-950`) set
`_loaded_content_hash = ckpt.content_hash` — a **full-file** hash — while
setting `_loaded_to_line = thm.proof_end_line`. The prefix hash can never equal
the full-file hash (unless the theorem is last in the file), so
`cursor.status`/`hol_sessions` reports `stale: True` for a perfectly
synchronized session. Display-only (`status` is not consulted by navigation),
but it misinforms whoever reads the session listing.

**Fix:** store the prefix hash (hash of content up to `proof_end_line-1`) when
restoring from a checkpoint.

---

### Field observations — disposition

1. **`hol_goals` vs `hol_state_at` disagreement**: confirmed, finding 1.
2. **Unbalanced-delimiter block reported complete**: hypothesis confirmed as
   the mechanism (early-terminated SML parse, no coverage check), finding 2.
3. **`replayed=N/M` does not track cost**: confirmed, finding 13; the 182 s
   `1/2` case is prefix re-proof after an edit, amplified by findings 9 and 14.

### Deliberate-behaviour items checked and NOT reported as bugs

- Opaque `Group` steps staying atomic (mid-arm navigation loss) — deliberate
  trade-off, documented in `PARENS_NAVIGATION_NOTES.md` and surfaced honestly
  via the `inside_step_idx` NOTE in `hol_state_at` (but not in `hol_goals` —
  finding 1).
- Broken suspend/Resume chain forcing a full session reinit on edit
  (`hol_cursor.py:536-554`) — deliberate, scoped by
  `_affected_chain_is_broken`, tested (`test_chain_broken_scope.py`); its cost
  (whole-prefix re-replay) is inherent to the append/consume-only suspension
  store.
- `Resume` per-tactic timing collapsed under `run_resume_canonical_json` in
  `verify_all_proofs` — deliberate, commented (`hol_cursor.py:2608-2620`), and
  the sub-suspension-preserving path is the correct one.
