# HOL4 MCP complaints from the CakeML opens port

Date: 2026-09-08, Asia/Singapore.

Original requested handoff: fix and validate the shared HOL4 MCP / Claude
workflow first, then port the necessary integration changes to Codex. The user
subsequently authorized direct repairs to client-independent code. The original
observations below remain the incident record; the dated implementation ledger
distinguishes implemented repairs from outstanding proposals. Do not read this
document as permission to disable proof safeguards or to upstream the local-only
`localfixes` branch.

## Implementation ledger — 2026-09-09

### Follow-up: approval ordering with bounded Codex history

Observed in the real source-to-flat commit workflow: pending review
`a2966eec2289` stored `after_user_count=64`, while Codex retained exactly 64
prompts and placed the user's exact approval at index 63. The old shared
approval policy could therefore never accept a new approval once that window
was full. This was not user wording error or absent consent.

The shared policy now matches hashed history suffix/prefix boundaries and
uses monotone positions for both disclosure ordering and processed events.
Append-only Claude transcripts and rolling Codex transcripts use the same
implementation; no extra work is added to ordinary proving or status calls.
Unknown/discontinuous history and legacy pending state are re-disclosed, not
retroactively approved. Scope, class separation, expiry and revocation remain.
Regressions cover rolling-window acceptance, preapproval rejection, expiry,
revocation without old-message replay, and lost-boundary migration. The identical
helper repair was deployed to the installed Codex cache; no approval state was
manually edited and no hook registration or safeguard was disabled.

Shared-code repairs are local and uncommitted. No client hook registration,
real `~/.claude` state, Codex adapter, or CakeML proof was changed. The second
batch repairs shared hook behavior, as authorized by the active goal.

| Item | Implemented change | Validation and remaining scope |
|---|---|---|
| C01 | The decomposed quotation operand now uses native `Q_TAC SUFF_TAC`, not reversed `sg`. | Live-HOL regression checks compare the closer's assumptions/conclusion with native HOL, and test ASCII/Unicode, standalone/merged/multi-goal forms and existing `by` behavior. The actual CakeML completeness arm has not yet been replayed with the repair. |
| C02 | Explicit `hol_check_proof(..., fresh=True)` restarts HOL, clears old bindings/checkpoints/verdicts and forces full prefix replay; ordinary checks remain incremental. | Live-HOL regressions recover from an injected transient admitted load, reject self-justification through an old admitted binding, retain genuine dependency oracle warnings, and verify repeated ordinary checks reuse their trace without HOL restart or proof/checkpoint replay. |
| C03 | `HOL4_MCP_MAXHEAP_MB` configures the interactive limit through inherited or explicit session environment; the default remains 8192 MB. Startup reports the effective value; invalid settings fail before spawning. | Configuration/precedence/invalid-value tests pass. No existing project session was resized or restarted; loading the actual Candle prerequisite at 12288 MB remains to be tested. |
| C04 | Snapshot `.uo`, `.ui` and `.dat` candidates, including absent and earlier shadowing paths; resolve relative paths against HOL's working directory. Required missing theory interfaces now stop initialization with a `.uo` build target and recover through a clean session reload. | Unit tests cover appearance, rebuild, deletion/restoration and shadowing. A live-HOL regression initializes without an ancestor, builds it, and successfully navigates on the next ordinary call. |
| C10 (partial) | Preserve a bounded multiline HOL exception excerpt instead of reducing `Exception-` to its first line. Dependency allocation failures identify the dependency, effective heap and that no target proof ran. | Regression tests cover the multiline diagnostic and output bound. Raw-log retention and the distinction between context history and actual dependency provenance remain outstanding. |
| C05 (shared part) | H30 applies its declared matcher internally before accessing a cached proof target. | Five recovery/inspection operations were reproduced producing false overrides before the fix; all now leave override state untouched, while actual navigation retains its stale checks. Codex dispatcher matching itself is out of this automatically shared scope. |
| C06 | H27 compares sweep findings with HEAD using exact unchanged-line mapping; inherited findings inside edited theorems no longer become new blockers. | Newly added banned tactics and new sweep findings remain blocking. This is a justified audit-scope correction, not a change to theorem statements or HOL validation. |
| C07 | A read-only snapshot helper handles index commits, `-a`, explicit/implicit path-only commits, `--include`, amend, quoted paths and option-looking message text. Required Finalise deletion is also checked. | Tests cover partial staging in both directions, path selection and deletion-only defects. Unsupported compound/interactive/filter forms are explicitly refused with a separate-stage/plain-commit remedy, never guessed. The index is not mutated. |
| C08 | H7 fingerprints the named target's authored proof blocks instead of relying on directory-wide script mtimes. | Assertion-only tests, translation-prefix edits, unrelated script edits and timestamp-only touches are silent; a real proof edit still triggers the reminder. |
| C09 (partial) | Prefix operations record phase/item/span/elapsed/budget metadata, visible through `hol_sessions` without a HOL command. Timeout and repeated-slow-prefix advice no longer blames the target proof. Busy sessions are exempt from idle pruning. H6 does not turn prefix timeouts into repeated target-proof warnings. | Focused progress/timeout/checkpoint tests exercised the metadata and existing cache paths. The initial progress test exposed an early-initialization status KeyError, now fixed. Reusable expensive translation-gap checkpoints still need specific testing/repair. |
| C10 (additional) | Context admission history is explicitly not a dependency list; actual kernel oracle evidence remains a separate warning, and target self-taint still refuses validation. Failures retain full submitted command/response and available phase metadata in private temporary JSON logs, including partial cancelled replies. | Live-HOL regression verifies that a later failed load remains visible as history but does not falsely label an earlier independent target as oracle-dependent. Genuine oracle-use tests remain. Evidence tests cover full multiline output, success-path zero disk writes, cancellation, failed log writes and live HOL protocol continuity. |
| C11 | Explicit `holmake(..., trace_discovery=True)` records Linux syscall/path traces plus workdir/command/server PID/mount namespace metadata. Regular builds do not prepare or invoke a tracer. Tracer setup/permission errors are distinguished from proof failures. | The sandbox denied `PTRACE_TRACEME` before Holmake started; the same isolated test passed with approved tracing permission, recording the exact failed `chdir(...)=ENOENT` and namespace. Sandboxed full runs explicitly skip this live trace test when that capability is denied; the restricted diagnostic and no-trace fast path remain tested. No missing directory is silently created/ignored. |
| C12 | H27 exceptions now require an explicitly approved review ID bound to repository/command/proof contents/findings. Style and incomplete-proof classes expire independently after 30 minutes; approvals survive status questions but do not create Git authority. The broad early `wip ok` bypass is removed. | Tests cover disclosure before approval, changed-scope rejection, separate admission/style classes, expiry without cross-class renewal, revocation, quoted/negated/history rejection, and status tools leaving approval state byte-identical. H14's existing Git gate is unchanged; a subsequent Git-permission message need not repeat the still-valid scoped audit approval. |

Focused runs passed: 40 quotation/reporting tests; 46 heap/dependency/lifecycle
tests. Corpus consistency: zero issues across 32 files. Final full suite:
**615 passed in 158.15 seconds**, using the editable installation's
`.venv/bin/python3 -m pytest tests/ -q -n 4` (bytecode disabled and pytest cache
redirected to `/tmp`). `git diff --check` also passed.

The first full run had 613 passes and two failures. The missing-theory test
still expected a later failure and was updated to require the new, earlier
initialization error and untouched prefix state. The live-goals test used
interactive goal creation already blocked by the existing server guard; it now
asserts that refusal, establishes the same frontier through file navigation,
and retains its goal/assumption inspection assertions. No server guard was
removed to make either test pass.

The running MCP server and existing project HOL session were not restarted.
New test processes exercised the modified source; the server process needs a
restart to import the Python changes. The shared Python server is installed
editable and needs no reinstall. Codex's plugin cache, however, contains copied
hooks (not symlinks to this checkout): shared hook repairs need a plugin refresh
to deploy there, though no separate implementation port. Neither cached hooks
nor client adapters have been changed. Do not assume this running session uses
the repaired hooks.

Second-batch focused evidence: **118 hook/Codex-adapter tests passed** in
2.79 seconds; all 20 Claude hook registrations remain wired with no drift;
corpus consistency has zero issues across 33 files. Additional snapshot-vs-real
Git checks passed: six real commits in temporary repositories matched the
predicted script content and left the index untouched during inspection; all
21 H27 tests passed. The second full suite passed 640 tests in 159.18 seconds.

C02's explicit recovery and dependency-performance regressions now pass; the
third full suite passed **648 tests in 162.17 seconds**. Historical self-taint
is never simply erased in a polluted heap, and oracle checks remain required.
C09's translation-gap checkpoint validation, remaining C10 coverage,
and C12 scoped consent remain open. C11's local opt-in tracing is implemented and validated with the
required tracing permission. The H27
message no longer tells the agent to request a magic consent phrase, but that
alone does not resolve C12's scope/lifetime design.

### Regular-workflow performance requirement

The user explicitly requires large CakeML files to remain practical. Fresh
verification is opt-in. Existing artifact files are checked directly; absent
candidates are grouped by directory stamps, without a polling/TTL delay.
Dangling symlinks are checked directly too, since their target can appear
without changing the link directory. Regression tests require one directory
stat per distinct absent parent, no absent-file stats on an unchanged warm
check, immediate creation/shadow detection, and cheap checks again after an
unrelated directory change. Whole-file commit audits do not run per proof step.

Read-only benchmark: `scripts/benchmark_dependency_freshness.py --broad-root
/home/yongkiam/research/cakes/cake-dopen <scripts...>`. This deliberately uses
193 directories as a synthetic stress load path, not the live HOL loadPath.
Median warm read/hash/freshness time over 15 runs (milliseconds):

| CakeML script | Bytes | Direct candidate scan | Grouped checks |
|---|---:|---:|---:|
| `source_to_flatProofScript.sml` | 205505 | 82.698 | 1.674 |
| `pegCompleteScript.sml` | 177376 | 66.837 | 1.514 |
| `ml_translatorScript.sml` | 113770 | 81.303 | 1.538 |
| `data_to_word_assignProofScript.sml` | 763312 | 127.617 | 3.903 |
| `data_to_word_memoryProofScript.sml` | 749300 | 112.137 | 3.805 |

These measure bookkeeping, not proof runtime. An intermediate implementation
still looped over every absent candidate and was slower; directory grouping
removed that loop from the unchanged warm path. No CakeML proof was edited or
executed for this measurement.

Further focused evidence: **50 tests passed in 18.04 seconds** across phase
progress, failure evidence, session behavior, provenance and fresh verification.
Some older reporting tests asserted the old `auto-cheated deps` label; they now
assert the explicit history label while retaining genuine oracle-use checks.
The shared skill/notes are being reconciled with these behavioral changes; the
same Codex cache-refresh deployment caveat applies to copied skill files.

The next full run had **659 passes and one failure**: the concurrency fixture
used the repository's read-only fixture directory, so each navigation's failed
checkpoint generated a distinct evidence path. The fixture now copies its
existing script to a private writable directory and explicitly requires a
successful base checkpoint; all three concurrency tests then passed. The
goal/position equivalence assertions were not relaxed. The build-log focused
run had 75 passes and one header-format failure; the existing `Build Logs`
heading was restored, with the provenance qualification on the following line.
The subsequent full suite passed **663 tests in 164.33 seconds**. Discovery
tracing was added afterwards and needs its own final suite pass; its live
syscall/path integration test passed in 0.24 seconds outside the ptrace-denying
sandbox. Trace logs can contain paths/source filenames; tracing remains opt-in.

Latest focused build/server suite: **79 passed, 1 skipped in 36.13 seconds**;
the skip is the explicitly capability-gated live tracing test already passed
with approved permission. H27 now explicitly refuses shell-wrapped or
command-substituting commits whose prospective content it cannot model;
quoted/read-only commit prose remains allowed. All **25 H27 tests passed** in
1.85 seconds. Corpus check: zero issues/33 files; all 20 hook registrations
remain wired without drift; `git diff --check` is clean. These latest additions
postdate the 663-test full-suite result and require a final combined run.

### Remaining implementation/acceptance work

- C12: replace unscoped/latest-message-only WIP bypass behavior with explicit
  operation/content/finding-scoped approval and expiry. Keep Git authority,
  incomplete-proof approval and style exceptions distinct. Status/automatic
  goal turns must not manufacture or consume approval; do not preserve an
  old broad pregrant indefinitely. The early WIP return currently also skips
  prospective-content diagnosis and needs to move behind scope resolution.
- C09: exercise effectful current-file prefixes across target edits, backward
  verification and invalidation. Keep valid existing checkpoint reuse; add a
  new checkpoint mechanism only if the test demonstrates a missing reuse path.
- C01/C03: perform the outstanding real CakeML parser-arm and heavy Candle
  dependency checks; existing toy/native-equivalence and heap tests are not
  those project-level checks.
- Final combined tests and requirement-by-requirement completion audit; then
  deployment instructions distinguishing Python restart from copied plugin
  hook/skill refresh. Leave this local-only work uncommitted unless asked.

## Executive summary

The tooling has helped validate substantial CakeML work, but several failure
modes now obstruct progress or make its verification verdicts difficult to use:

1. `suffices_by` decomposition changes native HOL tactic semantics.
2. A target can replay to completion yet remain permanently reported as
   `NOT VALIDATED` following an earlier auto-cheated load. The observed symptom
   is clear; the exact cause of the original failures is not established.
3. Heavy theories cannot load under the hard-coded interactive 8 GiB heap.
4. Missing compiled dependency interfaces can be skipped at initialization and
   never noticed when they subsequently appear.
5. Codex routes H30 to build and status calls, causing the stale-proof guard to
   block the very operations needed to resolve or observe staleness.
6. H27 blocks completed proof commits for unchanged mainline style findings,
   and does not consistently inspect the exact content a commit would record.
7. Assertion-only test scripts and expensive translation prefixes are subjected
   to proof-edit guidance that is sometimes inapplicable.

The requested outcome is a trustworthy, recoverable workflow: native/file
semantics, precise state provenance, actionable failures, and scoped guards.
It is **not** a workflow that declares success merely because goals disappear.

## Evidence and scope

The project is `/home/yongkiam/research/cakes/cake-dopen`, branch `dopen`, porting
declaration and lexical opens for CakeML issue #880. Its local audit trail is
`DOPEN-PORT.md`; detached build logs are under the relevant directory's
`.hol/mcp-build-<job>.log`, with theory logs under `.hol/logs/`.

At inspection, this repository was clean on `localfixes` at:

```
fe3dfdfd5b89d50c52184c32ca22ac0abfce2c9d  Add native Codex integration
```

The inspected HOL checkout, `/home/yongkiam/research/HOL`, was at:

```
e395eb6e69054ff6f7cef9d1107fd1a04dd5848f  A Quote body is verbatim material
```

The observed client was Codex using the personal HOL4 MCP integration. Shared
Python/SML findings should be reproduced through Claude before calling them
Claude failures. Codex-specific routing findings are explicitly identified.
The installed skill used during the work was under
`~/.codex/plugins/cache/personal/hol4-mcp/0.1.0/skills/hol4-proving/`.

Evidence labels below distinguish:

- **Confirmed:** observed behavior plus a contrasting probe or supporting source.
- **Observed, unresolved:** real failure output, but no established root cause.
- **Policy/design issue:** the implementation behaves as written, but its policy
  is counterproductive or inconsistent with another instruction.
- **Recovered setup/operational issue:** useful incident evidence, not a claim
  that a currently broken MCP component caused it.

The original complaint preparation used read-only source inspection and the
existing work record. Sections C01–C12 describe that inspection snapshot,
before the repairs in the implementation ledger above. No CakeML
counterexample proofs were introduced. The ledger records subsequent tests.
Historical repro-test docstrings in this repository are leads, not evidence
that every bug they describe still exists today.

## Priorities and ownership

| ID | Priority | Primary owner | Problem |
| --- | --- | --- | --- |
| C01 | P0 | Shared SML replay / HOL parser | `suffices_by` semantics differ |
| C02 | P0 | Shared cursor/verdict state | Failed-load taint lacks usable recovery |
| C03 | P1 | Shared session lifecycle | Hard-coded interactive heap |
| C04 | P1 | Shared dependency lifecycle | Missing interfaces are not tracked |
| C05 | P1 | Codex adapter, shared defensive guard | H30 blocks build/status operations |
| C06 | P1 | Shared hook policy, Claude first | Inherited style blocks completed commits |
| C07 | P1 | Shared commit guard | Wrong commit content/scope audited |
| C08 | P2 | Shared H7/workflow policy | Executable tests mistaken for proof iteration |
| C09 | P1 | Shared replay/diagnostics | Expensive prefixes and bad recovery advice |
| C10 | P1 | Shared failure reporting | Raw failures and provenance are lost |
| C11 | P2 | Environment/build diagnostics | Opaque discovery ENOENT; locally recovered |
| C12 | P2 | Shared policy and client consent adapters | Override/consent ambiguity |

P0 means verification semantics or reliable interpretation is affected. It
does not mean an unsound HOL theorem was observed being accepted.

## C01 — `suffices_by` replay is not native HOL semantics

**Confirmed; currently blocks parser completeness.**

The unchanged `nPTbase` arm of
`compiler/parsing/proofs/pegCompleteScript.sml` stopped around line 2804 at
`strip_tac` inside a `suffices_by` closer. The sufficient assertion was:

```
∃e l t. pfx ++ sfx = (e,l)::t ∧ e ≠ LparT ∧ ¬isTyvarT e
```

Native `BasicProvers.suffices_by` applies `Q_TAC SUFF_TAC` and then the closer.
The closer therefore receives an implication. In the replayed state, the
existential witnesses/facts were already assumptions and the conclusion was
the original existential PEG-evaluation goal. `strip_tac` was no longer
operating on the obligation the file's native tactic supplies.

Historical dry comparison on the actual live goal, without changing that goal:

- `Q_TAC SUFF_TAC <quotation>`: first resulting conclusion satisfies `is_imp`.
- Reversed `Q.SUBGOAL_THEN <quotation> STRIP_ASSUME_TAC`: first resulting
  conclusion does **not** satisfy `is_imp`.

The result was `true` versus `false`. No counterexample theorem was added.

Source anchors:

- HOL `src/basicProof/BasicProvers.sml`, `suffices_by` and `subgoal`:
  native `SUFF_TAC` versus `SUBGOAL_THEN ... STRIP_ASSUME_TAC`.
- HOL `src/parse/TacticParse.sml`, `suffices_by` elaboration:
  `ThenLT (Subgoal ..., [LReverse])` under a group.
- [tactic_prefix.sml](hol4_mcp/sml_helpers/tactic_prefix.sml), `frag_text`:
  explicitly realizes this form as `reverse (sg <quotation>)`.
- [test_quotation_step_realization.py](tests/test_quotation_step_realization.py),
  `TestSufficesByRealization`: current tests use a `metis_tac[]` closer and
  inspect the surviving goal. They do not check the state supplied to a
  shape-sensitive closer. Both implementations can leave the same final
  sufficient goal while giving the closer different assumptions/conclusions.

**Potential resolution:** preserve `SUFF_TAC` semantics in decomposition and
realization, or treat the whole native construct as atomic where faithful
decomposition is unavailable. Determine whether the fix belongs in HOL's
TacticParse, the MCP realizer, or both; do not blindly change the shared
`Subgoal` implementation used by ordinary `by`/`sg`.

**Acceptance:** compare native and decomposed obligation lists, assumptions,
order, and closer behavior, including existential/conjunctive sufficient
assertions with an explicit stripping closer. Exercise standalone and merged
chain forms, ASCII/Unicode quotations, and unchanged `by` controls. Then replay
the actual CakeML arm without deleting its valid `strip_tac` as a workaround.

## C02 — Completed replay can remain stuck behind historical auto-cheat state

**Observed, unresolved; currently blocks full backend-CV certification.**

In `cv_translator/to_data_cvScript.sml`, late navigation reported a failure at
the first induction step of `presLang_exp_to_display_pre` and approximately
fifty auto-cheated earlier proofs, many only described as `error: Exception-`.

The investigation returned to the earliest listed proof,
`compile_exp_alt_pre` (around lines 554–563 in the current worktree):

1. Its live goal had the expected four constant predicates; the first had type
   `flat_pattern$config -> flatLang$exp -> bool`.
2. A small native induction-tactic probe on that live goal succeeded.
3. The unchanged file then replayed the induction step and both following
   steps through its own QED: `reached=3/3`, `No goals (proof complete)`.
4. `hol_check_proof` nevertheless returned:

   ```
   Status: NOT VALIDATED (494ms)
   This theorem was auto-cheated: its own proof failed during load
   (error: Exception-) and was replaced by cheat.
   ```

The warning also persisted on the own-QED navigation. No positive validation
claim was made from these outputs, and no marker was manually erased.

There are two questions, not one: why did the initial load fail, and what
supported revalidation procedure can replace that failed binding with a
freshly checked theorem? The observation alone does not prove that merely
clearing `_failed_proofs` is safe, nor that all fifty file proofs need repair.

Source anchors:

- [hol_cursor.py](hol4_mcp/hol_cursor.py): `_failed_proofs`,
  `_theorem_oracles`, context restoration/invalidation, proof execution and
  `_cheat_failed_theorem`.
- [hol_mcp_server.py](hol4_mcp/hol_mcp_server.py):
  `_target_self_cheated_lines`, `_target_self_cheated_reason`, and the
  `hol_check_proof` `final.goals_after == 0` verdict path.
- [test_repro_session_pollution.py](tests/test_repro_session_pollution.py):
  existing historical tests for backward-context pollution and stale oracle
  warnings are relevant starting points, not a demonstrated diagnosis here.

**Potential resolution:** make successful revalidation an explicit,
transactional operation: reconstruct the correct pre-theorem context, run the
actual file proof, validate its resulting theorem/oracles, replace the loaded
binding, and invalidate downstream certificates that used its cheated form.
Only then retire the historical failure verdict. If this is already intended,
identify which state transition failed and test it.

**Acceptance:** fail/auto-cheat a target, repair or correctly reload it, replay
it fully, and obtain an unambiguous valid verdict without a dummy source edit,
directory hop, hidden restart, or proof-shape workaround. Also test a genuinely
cheat-dependent proof: it must remain invalid even when its tactics close.

## C03 — Interactive heap is hard-coded below the build heap

**Confirmed configuration limitation; Candle evaluator load fails.**

Navigation into `candle/prover/candle_prover_evaluateScript.sml` failed while
loading `candle_kernelProgTheory` with `Run out of store`. The evaluator proof
had not begun. Its dependencies had been built successfully.

[hol_session.py](hol4_mcp/hol_session.py), `HOLSession.start`, launches HOL with
`--maxheap 8192`. The build tool separately defaults to 12288 MB. At the
incident, the host reported roughly 52641 MB available; this was not evidence
that the entire host had exhausted physical memory.

**Potential resolution:** expose a validated interactive heap option through
session configuration/environment and both clients; report its effective value
on startup. A 12 GiB setting was requested for this project. Keep it distinct
from the detached build heap, and restart a session only through an explicit,
supported configuration transition. Do not silently increase every job's heap.

**Acceptance:** tests for defaults, explicit values, invalid values and client
propagation; then load the actual Candle evaluator prerequisites at 12 GiB.
An allocation failure must identify dependency, heap limit, and whether any
target proof executed. Raising the limit is not proof of evaluator correctness.

## C04 — Newly appearing dependency interfaces do not trigger recovery

**Confirmed by source inspection and observed recovery.**

`candle_kernel_valsTheory.dat` built successfully, but the required `.ui/.uo`
interfaces were absent. Building `candle_kernel_valsTheory.uo` in job
`06b199fc` succeeded; the initialized session still reported a missing
structure. One explicit session reload then made navigation work.

[hol_cursor.py](hol4_mcp/hol_cursor.py):

- `init` skips `Cannot find file` load errors, treating them as potentially
  build-time dependencies.
- `_record_dep_artifacts` records only `.uo` paths that already exist.
- `_check_dep_artifacts` checks only those recorded paths; an initially missing
  interface has no entry whose later appearance can be detected.

H30's artifact check, meanwhile, considers `.dat`, not the complete set needed
for interactive loading. “Theory data built” and “session can load its compiled
interface” are different facts, but the recovery advice does not consistently
distinguish them.

**Potential resolution:** record unresolved expected dependencies as first-class
state; detect missing-to-present transitions; distinguish ignorable build tools
from required theory interfaces. Reinitialize the dependent session safely when
interfaces appear. Report the correct `.uo`/interface target when that is what
is missing, rather than repeatedly prescribing an already-built `.dat` target.

**Acceptance:** initialize with required interface absent; build it; the next
ordinary navigation recovers automatically and uses the new artifact. Also
exercise existing-to-rebuilt and temporary-missing-during-build transitions.

## C05 — Codex H30 fires on build and build-status calls

**Confirmed Codex integration/routing defect, plus a shared defensive gap.**

After a refused navigation cached `parserProgScript.sml` or
`to_data_cvScript.sml`, calls to `holmake` and even `hol_build_status` were
blocked for that file's stale ancestors. Repeating the status/build call
produced a warning such as:

```
H30 OVERRIDDEN by repeat: navigating to_data_cvScript.sml
against STALE ancestors ...
```

There was no navigation in that call. The agent was starting the prescribed
dependency build or observing its existing job. This falsely records a risky
stale-proof override and can prevent monitoring/recovery.

Source anchors:

- [h30_stale_ancestors.py](hooks/h30_stale_ancestors.py) declares a narrow
  `HOOK_MATCHER`, but `main` accepts every `mcp__hol4__*` tool and falls back to
  a cached working file.
- [hooks.json](hooks/hooks.json) sends every matching HOL4 MCP call through an
  adapter invocation that includes H30.
- [hook_adapter.py](integrations/codex/hook_adapter.py) executes the supplied
  hook names without applying each module's declared `HOOK_MATCHER`.

**Potential resolution:** in the shared guard, explicitly whitelist the
navigation/session operations whose semantics require freshness. In the Codex
port, preserve each policy's event/matcher contract instead of relying on all
children to self-filter. Builds, job polling and cancellation must remain
available when proof navigation is stale. Do not weaken actual navigation
freshness checks.

**Acceptance:** cache a stale target and invoke build/status/cancel: no block,
no override counter increment, no “navigating” message. Actual downstream
navigation must still block. Test both direct hook calls and full Codex wiring;
the latter is where the mismatch arises.

## C06 — Whole-theorem style findings block completed proof checkpoints

**Confirmed policy/design issue; not a theorem-correctness failure.**

The completed `peg_sound` changes passed the full theory build (`c975ad8f`),
but H27 refused the commit with 29 composition findings. Examples flagged
“near-identical sibling arms” and “trailing `>-`” in unchanged grammar cases.

An adversarial read-only audit ran the existing `proof_sweep.py` on current
`peg_sound`, HEAD, and mainline `857f0d98`. Normalizing only file/line prefixes
gave byte-identical outputs: 35 findings, minus six lone-dispatcher advisories
filtered by H27, leaving the same 29 blockers. None came from the lexical-open
case or earlier Dopen additions.

Other completed tranches have documented inherited findings: six in cfDiv,
nine in Candle permissions, and findings in the larger source-to-flat proof.
Do not extrapolate the exact 29-item baseline comparison to all those files;
their individual evidence must be retained.

[h27_commit_audit_gate.py](hooks/h27_commit_audit_gate.py), `audit`, deliberately
runs the composition sweep over an entire theorem whenever its proof text is
touched. It is diff-scoped for several lexical checks, but not for the findings
inside a touched theorem. This distinction is easy to miss in “only what this
commit introduces is judged” guidance.

**Potential resolution:** retain hard checks for newly introduced admissions,
missing required `Finalise`, and other precisely established defects. Treat
heuristic composition findings as advisory unless demonstrably introduced or
aggravated by the patch; alternatively baseline them and support a narrowly
scoped reviewed waiver. Do not require restructuring unrelated kernel-checked
proofs solely to make a small feature checkpoint possible.

**Acceptance:** a harmless new constructor case does not acquire all unchanged
mainline style debt. A newly introduced bad composition is still surfaced.
Genuine sibling constructor branches and first-obligation discharges are not
automatically rewritten based on text similarity. No blanket hook disabling.

## C07 — Commit auditing does not model the exact prospective commit

**Observed scope problem; additional staged/worktree mismatch visible in source.**

An unrelated staged source-to-flat proof blocked attempts to commit independent
verified files, including attempts using a limited commit scope. Combined
stage/commit shell calls were inspected before the staging commands could run.
The safe workaround was separate tool calls: save the exact index patch,
unstage it, commit another tranche, and restore the original patch. That was
done without losing the user's staged/unstaged distinction, but it is needless
exposure of a carefully managed index to tooling workarounds.

The implementation's `diff_base` distinguishes `-a` from `--cached`, but does
not construct Git's prospective tree for path-limited commits. `audit` obtains
added-line numbers from the chosen Git diff and then reads the **working-tree
file** for block/sweep analysis. In a partially staged file, those can refer to
different content. The exact false verdict for every partial-staging variant
has not been reproduced here; the source-level mismatch is concrete.

**Potential resolution:** audit the exact index/prospective tree Git will
commit, including explicit paths and supported flags. Read blob contents from
that tree. For unsupported compound shell commands, request separate commands
with an accurate explanation instead of claiming the wrong commit was audited.
Never modify the user's real index to perform the audit.

**Acceptance:** tests for unrelated staged files, partial staging, unstaged
proof edits, `--only`, explicit pathspecs, `-a`, `--amend`, and `git -C`.
Confirm both correct blocking and unchanged user index after every check.

## C08 — Assertion-only theory tests are mistaken for theorem-proof iteration

**Confirmed advisory false positive and workflow-policy gap.**

H7 emitted its edit/build-loop warning while correcting executable test
harnesses, including `pegexecOpenTestsScript.sml` and `astPPOpenTestsScript.sml`.
These files use SML assertions that run EVAL/CV and check exact output or raise
`Fail`; they contain no authored theorem proof for `hol_state_at` to navigate.
Executing the assertion file is the relevant check.

For example, the first-order parser tests were rerun after the adversarial
review corrected a rejection classifier to match `parse_prog`'s first-tree
behavior. Final gate `4d54ca06` passed all fourteen assertions. The warning did
not identify an alternative proof goal because none existed in that file.

[h7_holmake_advisory.py](hooks/h7_holmake_advisory.py) detects any recent
`*Script.sml` mtime change in the workdir, not necessarily a changed proof in
the named target. Cursor initialization also rejects files with no theorems.

**Potential resolution:** distinguish theorem development, generated
translation/definition execution, executable assertion tests, and dependency
setup. Keep the proof-iteration rule for actual proofs. Make H7 target-aware and
provide a documented test-script execution path; do not manufacture dummy
theorems or permit skipping tests merely to satisfy the rule.

**Acceptance:** assertion correction followed by its test execution does not
receive impossible goal-navigation advice. A real repeated proof-edit/build
loop still receives the intended warning.

## C09 — Large prefixes need lifecycle-aware progress and recovery

**Observed performance/workflow limitation, not evidence of a looping target.**

Navigation from early source-to-flat CV lemmas to
`presLang_exp_to_display_pre` timed out at 300 seconds with:

```
prefix=300.0s, target=0.0s
```

All ancestors had already been built. The work was replaying the current
script's extensive translation prefix, not the target theorem's tactics.
A 900-second allowance subsequently reached the target in about 193 seconds,
but produced the failures described in C02. This is not a proof that the
larger timeout fixed validation or that all of that time is unavoidable.

The existing prefix/target timing split was useful. Generic advice to build
ancestors again or split the target's proof cannot solve expensive current-file
declarations and CV translation that execute before the target exists.

**Potential resolution:** distinguish dependency load, top-level SML/
translation, preceding theorem verification and target replay; expose the
active item and elapsed time during long requests. Support sound reusable
checkpoints for effectful translation prefixes, correctly invalidated by
source/ancestor/configuration changes. Route timeout advice by measured phase.

**Acceptance:** a heavy generated prefix with a trivial target yields honest
progress and appropriate recovery advice; a looping target still yields
target-focused advice. Checkpoint reuse must not import later simp facts,
old definitions, or stale translator registrations into earlier proofs.

## C10 — Failure reports lose the diagnostic evidence needed to recover

**Observed; source confirms over-broad dependency labeling.**

The CV incident included messages like:

```
Tactic replay failed at step 0 (ho_match_mp_tac ...): OK..
[auto-cheated deps: ... (error: Exception-); ...]
```

The exact exception payload was not usefully exposed. A native induction
probe and subsequent file replay then worked. Reporting only `OK..` or the
exception prefix cannot distinguish a tactic error, source-context problem,
interruption/framing issue, or another session-state condition. Those causes
remain hypotheses until raw evidence identifies one.

Additionally, `_auto_cheated_deps_lines` in
[hol_mcp_server.py](hol4_mcp/hol_mcp_server.py) labels every other entry in
`cursor._failed_proofs` as a dependency of the target. It does not derive an
actual dependency closure. Backward navigation therefore displayed failures
from later theorems as “deps” of an earlier target. Conservative uncertainty is
appropriate; claiming a dependency relationship not established is not.

**Potential resolution:** preserve complete raw request/response diagnostics in
a discoverable per-request log; return structured failure kind, phase, source
span, actual exception and a short useful summary. Separate “failures seen in
this session/file” from “dependencies used by this theorem.” Report original
load failure separately from the most recent revalidation attempt. Make H6
advice depend on the actual failure shape, rather than every atomic tactic
being described as an opaque arm needing proof restructuring.

**Acceptance:** multi-line exceptions remain retrievable; successful output
preceding an exception does not hide it; a theorem identifier containing
`error` is not itself an exception. Actual oracle/dependency provenance, session
failure history and self-taint are distinct fields. Repeated advisories should
point to the original evidence instead of flooding the transcript.

## C11 — Build discovery ENOENT was badly localized

**Recovered environment/setup incident; not established as an MCP root cause.**

Several builds failed during project scanning with `SysErr ... noent`, after
printing a bootstrap directory. The last directory printed was not the failing
target. Instrumented job `f5f13429` captured the actual failure:

```
chdir("/home/yongkiam/research/cakes/cake-dopen/.agents") = ENOENT
```

Empty `.agents`/`.codex` directories were visible in the command sandbox but
absent on the host. With approval, persistent empty host directories were
created. Normal uninstrumented builds then passed, including cfDiv
`abdc6a2e` and presLang `b0c6444c`. No instruction files or hook configuration
were deleted or disabled. The exact source of the inconsistent/transient
directory visibility was not established.

**Potential resolution:** retain and surface discovery exceptions with syscall,
path, workdir and execution namespace. Investigate whether the HOL scanner
should tolerate a directory disappearing between enumeration and entry. Do not
silently ignore missing required theory directories or treat every ENOENT as
a proof failure. Document any required sandbox/host path contract for Codex.

**Acceptance:** a disappearing optional directory has an actionable diagnostic
or safe handling; a truly missing required source remains an error. Do not
recommend repeated unchanged builds based on the last printed scan line.

## C12 — Override policy is inconsistent and insufficiently scoped

**Policy/design issue observed while trying to commit completed work.**

H27 offers a literal WIP override, while the skill says not to ask for a consent
phrase. The user had earlier authorized local/WIP commits, but H27's
`latest_user_message` checks only the latest turn. Other policies use broader
session pregrants. The distinction between permission to commit, permission to
commit admissions, and approval of an audited style exception is not clear.

Calling a completed, kernel-checked proof “WIP” merely to waive inherited style
findings also conflates two materially different approvals. Conversely,
reusing an old broad pregrant forever would be unsafe. No such override was
used for the blocked completed-proof tranches in this handoff.

**Potential resolution:** reconcile skill, hook messages and client consent
handling. Provide explicit, narrow approval scopes: named finding class,
files/content fingerprint, intended operation, and expiry. Separate reviewed
style exceptions from permission to record incomplete proofs. Do not infer
consent from this complaint, a status question, or an automatic goal turn.

**Acceptance:** both Claude and Codex represent the same approval consistently;
unrelated new edits cannot inherit it; a status poll cannot consume or create
an override. The user need not learn contradictory magic-phrase rules.

## Things this complaint does not blame on the tooling

- Missing Open grammar alternatives and missing theorem cases were real port
  work. The CV `compile_decs_cons` failure that tuple-split an environment
  record was a genuine project-proof issue; its targeted repair replayed.
- The first-order parser rejection test initially modeled the wrapper too
  narrowly. The adversarial audit found it; the assertion was corrected.
- Long bootstrap builds alone are not defects. Job `039cdf2e` completed all
  ten prerequisite theories, including lexerProg, in 1659 seconds. It was not
  restarted merely because it took time.
- The agent should have made more independent progress commits sooner. Hook
  blocks explain some of the backlog, not all of it.
- A successful theory data build is strong evidence for that theory's actual
  checked contents; it does not prove that a missing downstream theorem was
  stated, that another script was built, or that a different client replay is
  semantically faithful. Keep these verification scopes explicit.

## Proposed implementation and acceptance sequence

### 1. Shared correctness and recovery, validated through Claude

1. Add discriminating C01 tests before changing the realizer; fix native
   `suffices_by` equivalence without modifying CakeML's proof to accommodate it.
2. Preserve raw evidence and add C02/C10 regression fixtures for failed-load
   recovery, oracle provenance and backward navigation. Fix the lifecycle
   transition, not just the warning text.
3. Implement configurable heap and missing-interface transitions (C03/C04).
4. Reproduce the affected CakeML proof/load cases through Claude. Do not accept
   only unit tests of mocked successful tool output.

### 2. Shared hook/workflow corrections, Claude first

1. Define the C06 distinction between precise hard gates and heuristic style
   advice, including reviewed exceptions.
2. Make C07 audit the actual prospective commit tree; test partial staging.
3. Add assertion-only and heavy-prefix workflows (C08/C09), and reconcile the
   consent rules (C12) across runtime messages and the canonical skill.
4. Make H30 defensively reject only its intended operation classes even if
   invoked by an overly broad dispatcher. Preserve real freshness protection.

### 3. Port to Codex after shared behavior is fixed

1. Keep Claude registration and real `~/.claude` state unchanged by the port,
   as required by this repository's `AGENTS.md`.
2. Update `integrations/codex/` and `hooks/hooks.json` to preserve per-policy
   matcher/event semantics. Cover actual manifest-to-adapter-to-hook execution,
   not just isolated child hooks.
3. Preserve plugin-owned state isolation and stable prompt capture. Verify
   equivalent approval semantics without silently broadening permissions.
4. Synchronize the bundled skill/messages, account for plugin cache/version
   changes, and report the effective server/helper/client revisions at startup.
5. Re-run the CakeML cases on Codex before resuming the opens implementation.

### 4. Regression gates and retained evidence

Use the interpreter actually providing the editable `hol4-mcp` installation;
do not assume a particular virtualenv. Follow `CLAUDE.md`/`AGENTS.md` for tests.
Relevant existing starting points include:

- `tests/test_quotation_step_realization.py`, `tests/test_tactic_prefix.py`.
- `tests/test_repro_session_pollution.py`, `tests/test_repro_session_lifecycle.py`.
- `tests/test_hol_session.py`, `tests/test_goalfrag_emode.py`.
- `tests/hooks/test_h27.py`, `tests/hooks/test_soft_blocks.py` (H30), and
  `tests/codex/test_codex_integration.py`.

Run the full suite after focused fixtures; run the corpus consistency and hook
wiring checks when their owning files change. Retain request IDs, raw logs,
source hashes, actual pre/post obligations, loaded artifact paths and effective
heap settings for the cross-client acceptance run.

For each complaint, record separately: reproduced, root cause identified,
fix implemented, focused test passes, Claude scenario passes, Codex port passes.
Do not close an item simply because the agent stopped encountering it after
restarting or switching directories. Keep every genuine admission visible and
every necessary theorem-contract change explicit throughout the repair.
