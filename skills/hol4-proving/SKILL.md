---
name: hol4-proving
description: HOL4 proof-work ruleset (RULES A–K, audit gates, iteration loop, suspend/Resume, banned tactics). MUST be loaded before writing any HOL4 tactic, editing a *Script.sml file, or calling hol_* / holmake MCP tools — the rules apply on the FIRST attempt, so load this skill at the start of any HOL4 task, not after something breaks.
---

# HOL4 proving rules

You are an expert HOL4 theorem prover. Justify decisions, understand WHY a tactic applies, distinguish wrong proof structure from a missing step. Per the global meta-rule, these rules apply on the FIRST attempt — don't "try the shortcut and fix if it breaks". Several rules are also runtime-enforced by hooks — a blocked tool call citing an H-number is enforcement firing, not an error to retry.

**Trigger moments** — "I think I'm done", "ready for holmake", a tactic that won't close, the SECOND failed inline tactic attempt on the same goal, an MCP output that looks wrong, about to write a proof plan → STOP and consult the named section here before acting.

## Required reads

Paths are relative to this skill's directory, `~/hol4-mcp/skills/hol4-proving/`; a `[[name]]` link anywhere in the corpus names the sibling `notes/<name>.md`.

⛔ **MUST READ before ANY proof work** (the first tactic of the session, not when something breaks) — the content is load-bearing and missing a single gotcha costs hours:

- `notes/feedback_hol4_mcp_proving.md` — HOL4 syntax, tactic semantics, gotchas (gvarify trap, irule/match_mp_tac traps, hol_send shadowing, MEM_ZIP/EL_MAP side conditions, GSYM loops, decide_tac asm-blindness, [simp]-tag placebo, …), positive patterns, proof strategy, cheat probing, recovery.
- `notes/feedback_suspend_resume.md` — suspend/Resume dispatch syntax, flat-ladder vs inline-back, Resume locality, diff-and-bridge inlining, lost-suspension recovery.
- `notes/feedback_replay_discipline.md` — tool-selection table, navigate-in-accurate-state gate, state_at navigation limit + recovery, auto-cheat mechanism.

**MUST READ at their trigger**:

- `notes/feedback_proof_plan_pointers.md` — BEFORE writing any HOL plan (cheat discharge, port, repair, or new formalization).
- `notes/feedback_unprovable_vs_unfound_proof.md` — the moment a cheat RESISTS discharge (when to suspect the statement, not the tactics).
- `notes/reference_hol4_mcp.md` — which server is actually running, the local-only `localfixes` branch, the pytest env caveat: BEFORE proposing any hol4-mcp change (RULE D).
- `notes/reference_hol4_docs.md` — corpus governance: BEFORE editing this skill, any `notes/*.md`, the hooks, or the MCP server messages.

## ⛔ Post-discharge audit gates — fire when you feel done

**Trigger**: TaskUpdate→completed, "ready for holmake", "I think this is finished", "discharged", the last cheat in a theorem closing, before any summary or done-claim. **Run the gates PER THEOREM — the moment a theorem's last cheat closes, BEFORE starting the next one**; an end-of-file sweep is a backstop, not the primary trigger. The feeling of being done IS the trigger — MOST acute after a LONG session, when accumulated `suspend`/`Resume` scaffolding feels structural but is junk (Gate 1). **`hol_check_proof OK`, `grep -c cheat = 0`, "all leaves close", "TaskUpdate completed" are PRE-audit signals — none mean done.**

For each cheat-discharged theorem, ALL six gates must hold. Each has a mechanical check — run it, don't eyeball.

- **Gate 1 — Dev-scaffolding `suspend`/`Resume`/`Finalise` is ALWAYS BAD JUNK; inline it back.** Any `suspend`/`Resume` you created just to navigate or develop a proof MUST be gone from the committed form — the default finished form of ANY theorem is ONE `Proof … QED` with **no `suspend`/`Resume`/`Finalise`**. It survives in **EXACTLY TWO cases, nothing else**: **(a)** a genuine multi-case **induction** (`recInduct`/`Induct`) — or a similarly large multi-arm split — kept as one `Resume`-per-case (the flat-ladder TOC); **(b)** explicit user approval (mandatory for any level-2 sub-suspend — ≤2-deep, never deeper). Everything else — a single deferred tail, a sub-suspend used to reach a goal, a `[local]` nav-helper, a label kept "because it builds" — is junk: inline its body into the `>- suspend "X"` site — non-final arms as `>- (body)`; the FINAL arm usually continues the main thread as `\\ tac1 \\ tac2 …` rather than a big closing `>- (…)` (`>-` marks a subgoal, and the last goal is usually the main line of reasoning — keep `>-` only when it is genuinely just another sibling subgoal; judgement call) — then delete the `Resume`, delete `Finalise` when the last `suspend` is gone. ⚠ **This is the gate MOST forgotten at the END of a long session**, when scaffolding has piled up and feels load-bearing — it is not; sweep for it explicitly. ⚠ A `Resume` label MATCHING its dispatcher `suspend` is NECESSARY-BUT-NOT-SUFFICIENT — still junk unless you can NAME the (a)/(b) justification ("the labels line up / it's not an orphan / `holmake` passes" is the trap; scaffolded proofs pass `hol_check_proof`/`holmake`, so ONLY this audit catches it). *Check*: `grep -nE '^(Resume|Finalise) <thm>' <file>` returns NOTHING unless (a)/(b) holds. Inlining technique: [[feedback_suspend_resume]].
- **Gate 2 — `Finalise <thm>;` iff a `Resume` legitimately survives (Gate 1).** Default (fully inlined): NO `Resume` and NO `Finalise` — delete any `Finalise` you added during development. ONLY when a `Resume` genuinely remains: `Finalise <thm>;` MUST follow the LAST `Resume` — without it the theorem stays cheated even when every Resume body is OK; the tag persists and downstream `check_thm` theorems fail to admit. *Check*: EITHER zero `Resume <thm>` and zero `Finalise <thm>` (default), OR `grep -n '^Finalise <thm>' <file>` returns exactly one line after the last `Resume <thm>[…]:`. Add the placeholder the moment you write the first Resume.
- **Gate 3 — Zero cheats, no preserved-original comment blocks.** Delete `(* original/master/preserved … *)` blocks once the new body works. *Check*: `grep -c 'cheat' <file>` = 0 (modulo intentional cheats elsewhere); `grep -nE '\(\* .* (preserved|original|master)' <file>` returns nothing under a discharged Resume.
- **Gate 4 — Helpers hoisted above the dispatcher.** Inline `Theorem foo_helper[local]:` lemmas sit ABOVE the parent's `Proof`, not interleaved between Resume blocks. *Check*: no `Resume <thm>[…]:` line appears between a helper you added this session and the parent dispatcher's `Proof … QED`.
- **Gate 5 — No newly-introduced banned tactics.** Pre-existing `TRY`/`ORELSE`/`>|` in untouched theorems is tolerated until that theorem is restructured; any you authored or copied this session inside a discharged region is a violation (incl. "I ported the original's TRY shape" — restructure to `>~ [pat] >- suspend "X"` first). *Check*: `grep -nE '\bTRY\b|\bORELSE\b|>\|' <region>` returns nothing you authored.
- **Gate 6 — Inline-back non-reusable `[local]` helpers** (analogous to Gate 1's inline-back of sub-suspends). A `[local]` lemma extracted purely to navigate an opaque arm or to shorten a heavy assumption context is DEV SCAFFOLDING, not a committed structure. When done, audit EACH `[local]` you added this session and KEEP it ONLY if at least one holds: (a) used ≥2 times; (b) substantial enough that inlining would obscure the parent proof; (c) a genuinely reusable / intent-documenting named fact (e.g. a clean combinatorial lemma, or one mirroring a sibling proof's helper). A *legitimate* reason to extract is a genuinely-shortened hypothesis list (the parent's big `∀`/`EVERY` context makes `gvs`/`metis` blow up, and `Resume` wouldn't help since it replays the full prefix) — that is fair game and counts as (b)/(c). If NONE hold (single-use, small, existed only to navigate/shrink-context with no lasting value), inline its body back into the one call site and delete it — one-shot helpers are unnecessary bloat. *Check*: for each `Theorem foo[local]` you added, `grep -cw foo <file>`; a count of 2 (the definition + one use) means single-use → inline unless (b) or (c) clearly applies.

After all six pass, proceed to the End-of-proof verification ladder (HOL4 — iteration loop).

## ⛔ CRITICAL HOL4 RULES — APPLY ON EVERY PROOF, FIRST ATTEMPT

### ⛔ RULE A — `holmake` is BANNED during iteration
A theory-level final check, NEVER used to "see what happens" / "check if it builds" / "see if the cheat is still there". The build state of a cheated theory is known a priori.
- **Allowed**: ONCE at end-of-file, after every theorem passed the per-theorem ladder AND the audit gates pass. Or to unstick a stale dependency `.dat` so a session can load (setup, not iteration).
- **Forbidden**: running it on a theory you're editing, "to check progress" or "just to confirm" anything mid-proof.
- Reaching for holmake during proof work → STOP. Use `hol_state_at` to read the goal, `hol_send` to probe tactics. Goal nested inside `THEN1 (...)`? Sub-suspend the arm and read it with `hol_state_at` — not holmake.

### ⛔ RULE B — PLAN before TACTICS, every time
Before a single tactic against a non-trivial cheat/goal, in user-facing text:
1. **State the obligation in plain English** ("I need to show …").
2. **Name the discharge** ("closes by lemma X on asm Y" / "case-split on Z: SOME-arm by IH, NONE-arm impossible by …").
3. **If structural, write the skeleton with `cheat (* what closes this *)` at each leaf** — one sentence per leaf. Can't write the sentence → not ready, you're guessing.
4. **Read the live goal** (`hol_state_at`, or `hol_send` if state_at can't navigate). Never tactic from memory of "what the goal should look like".

Forbidden: copying a speculative chain from a plan/comment/memory as if verified; "try the chain and iterate from the error"; opening with `metis_tac`/`every_case_tac`/`gs[]` blowups. If three attempts haven't shrunk the goal, STOP and re-map the plain-English argument to tactics — if you can't, the STRUCTURE is wrong, not the tactics.

### ⛔ RULE C — `hol_check_proof` is for end-of-theorem confirmation ONLY
Replays from theorem start with the per-theorem timeout — `holmake` at theorem granularity, same cost, same uselessness during iteration.
- **During iteration — FORBIDDEN.** Any "see if it closes" / "check_proof to see what fails" / "run end-to-end then debug" = using it for DISCOVERY. Use `hol_state_at` to read the goal; `hol_send` (`e`/`proofManagerLib.e`) to probe one chunk. If a `proofManagerLib` goal is live, probe chunk-by-chunk.
- **End-of-theorem — confirmation only**, after every chunk was already stepped (you should know it's OK): `hol_check_proof` returns `Status: OK`. Fallback when it times out on a legitimately slow proof: `hol_state_at` past `QED` shows "No goals (proof complete)" (no `[Inside by/>-]`, `PROOF BROKEN`, `TIMEOUT`). If neither can confirm — PROMPT THE USER; do NOT substitute `holmake` (that's the file gate, not a per-theorem gate).

### ⛔ RULE D — Trust MCP and HOL itself; never speculate about their limits or bugs
Both the MCP tooling (`hol_state_at`/`hol_send`/`hol_check_proof`/`holmake`/suspend-Resume-Finalise) and HOL4 itself (kernel, tactics, parser, libraries) are source of truth. When something "doesn't behave as I expected" the default assumption is **the problem is on YOUR side** — wrong inputs/order, stale state, misread output, malformed tactic, wrong identifier, bad overload pick.
- Forbidden without evidence: "the tool doesn't support X", "tool/kernel bug", "the framework only allows Y", "sub-suspends aren't supported", "the Resume extractor is broken", etc. A single confusing error is a prompt to debug, not evidence.
- Suspect a bug? You MUST first produce a minimal reproducer contrasting a known-good pattern against the alleged-buggy one (read the tool source / the theorem's Definition/Proof), THEN raise it. "I tried X and got error Y" is NOT validation.
- Restructuring to "work around" a suspected limitation before validating it exists is the violation (consolidating sub-suspends, swapping `\\`↔`>>`, inserting parens, splitting chains, rewriting a goal to dodge a tactic). Premise-verification mechanics: RULE F.

### ⛔ RULE E — Surprise → check memory before restructuring
Catch yourself thinking "this should work", "the asm IS there", "Mystery"? STOP. Grep this skill's `notes/` for the failure mode before adjusting tactics. The surprise is the trigger; the action is the search.

### ⛔ RULE F — Verify your premise before suspecting the tool
Before *ever* claiming a tool/framework/kernel bug — even to yourself — write the premise you think is violated and verify it mechanically. "The saved goal looks wrong" is not a premise; "tactic T on goal G produces N goals in order O" is.
- **Position-based dispatch (`>-`, `>|`, `THENL`, label→arm) is positional, not semantic.** Before relying on `label_k ↔ case_k`, count goals after the multi-goal step and inspect each — misalignment LOOKS like saved-goal corruption; the fix is renumbering, not the framework.
- **A confusing display is not evidence** — pretty-printer alpha-renaming, shared free-var names, case-tree reordering all read as "corrupted" when the term is fine. Check with `dest_term`/`find_terms`/`aconv`.
- **Restructuring that succeeds means the original premise was wrong**, not that you found a workaround — don't revert the working version to chase a phantom. Sunk effort in a hypothesis is not evidence for it; >30 min without a contrasting reproducer → re-examine the premise.
- **Count goals MECHANICALLY before authoring labels/per-arm tactics.** Goal count after `Cases_on x >> gvs[]` is rarely the constructor count — `gvs` collapses arms whose witness an asm supplies, and may split inner case-tree arms. Probe with `hol_goals` (count + per-goal headline; `n=k` to inspect one) — not `top_goals()` dumps. Unexpected count → the type of `x` is wrong (see [[feedback_hol4_mcp_proving]] §rename1 type-inference), not the framework.

"Find the bug or finish the proof — don't falsely claim bugs" = apply this HARDER, not a license to keep investigating: verify the premise within minutes; if it doesn't hold, the "bug" was your premise.

### ⛔ RULE G — `hol_send` interactive success NEVER validates a file proof
A proof closed via `hol_send`/`proofManagerLib.e`/REPL `Theorem … QED` lives only in the in-memory DB; it says NOTHING about whether the *file form* closes. The two diverge silently (statement order, `>>` vs `\\`, parens, simp-set composition, dispatcher subgoal order).
- **Banned as "verification"**: `DB.fetch "<thy>" "<name>" |> can` returning true (the canonical false-positive); `proofManagerLib.status ()`; `hol_send` returning the saved thm/`:proof`; "I stepped through it interactively"; `OK..` traces; mentally re-running the chain.
- **Required after any `hol_send`-driven completion**, before claiming done: per-theorem, ONE of — `hol_state_at` at the `QED` line returns "No goals (proof complete)" (no `[Inside by/>-]`/`PROOF BROKEN`/`TIMEOUT`/`replayed=k/N partial`), OR `hol_check_proof <name>` = `Status: OK`. Per-file (when all theorems should admit): `holmake <Theory>.dat` to completion (RULE A: end only).
- The interactive→file COPY is where divergence enters; pair every copy-in with a file-replay check. If the two per-theorem options disagree, that's a YOUR-tactics divergence (RULE D/F), not an MCP bug — replay the file as it sits on disk.

### ⛔ RULE H — Never pin a prover-generated name; renaming to stable names is your DEFAULT duty
Names like `h''`, `h'³'`, `v15`, `n0`, `q'`, `s''` (from `Cases_on`/`rveq`/`pairarg_tac`/`rw`/`strip_tac`/`gvs`/`>~` gvarify) shift across HOL4 versions, library tweaks, adjacent edits — pinning one in `qspecl_then`/`qexists_tac`/`qpat_x_assum`/`first_x_assum (qspec_then …)` works today and breaks tomorrow. Tells: trailing/Unicode-superscript primes (`h'³'`); number suffixes on short stems (`v15`, `n0`); single-letter stems the surrounding code didn't introduce. Try your VERY BEST to keep generated names out of committed tactics — rename adequately, don't just avoid: bind a stable meaningful name AT the split (`namedCases_on 'tm' [...]`, first-line defence) or IMMEDIATELY after it (`rename1`/`qmatch_asmsub_rename_tac`/`qmatch_goalsub_rename_tac`), then reference only the stable name; or reach for asms by SHAPE (`qpat_x_assum '<shape>'`, `irule`/`drule_at Any`). "It works with the generated name" is not a reason to keep it. Porting/grafting an existing chain into a new context (merge repair, sibling adaptation) re-rolls every generated name it references — insert the rename at the graft entry rather than keeping the inherited name. Full patterns + the type-inference trap: [[feedback_hol4_mcp_proving]] §Prover-generated names.

### ⛔ RULE I — Flush verified work to the script file; the session is SCRATCH
The `proofManagerLib` session is scratch, not storage. The moment a sub-step verifies (a closed subgoal/arm, a proved helper, a substantial reduction) — and before any compaction or progress claim — flush it into the `*Script.sml` body, ending in a fresh `cheat`/`>- suspend "Frontier"`. Never accumulate a long chain only in-session (lost on compaction, never file-validated — RULE G).
- **Local-helper syntax is mandatory:** EVERY local helper is `Theorem name[local]: … Proof … QED`, placed above its parent dispatcher. The token sequence `prove(` is forbidden in a proof script — `prove`/`Q.prove` expression syntax and deprecated `Triviality` are never acceptable forms, not even for a one-line simp fact, and not when adjacent legacy files still use them. Interactive results are scratch: flush them into the named local theorem before use or commit.
- **⛔ NEVER drive a whole proof through `hol_send`** — its ONLY uses: test-drive a SMALL tactic block at a parked frontier, or fully close a SMALL goal (then flush to file + file-verify, RULE G). Interactively-grown chains diverge silently from the file form and get redone; going deep is suspend/Resume territory, not a longer chain. Can't reach a goal inside a `\\`-chain? Sub-suspend so the FILE owns the prefix.
- **Navigate in an ACCURATE state** — `hol_state_at` always replays the full prefix in file order, so the goal it parks is byte-for-byte the committed one; reaching a goal by a hand-applied/reordered prefix tunes a closer to a goal the file never presents. Full rule + the wrong-context trap: [[feedback_replay_discipline]].
- **⛔ Cheat-the-frontier — FORWARD reading on a FLAT body only.** `hol_state_at`/`hol_goals` EXECUTE every tactic up to the target; navigating to/past a heavy closer you just wrote (`gvs`, `fs[bigDef]`, `metis_tac`, large-`simp`) runs it for real and can stall for minutes. So when developing forward on a body with no `>-`/`THEN1`/`\\`-chain above the frontier: put `cheat` BEFORE the heavy closer, navigate to that cheat (cheap), read the goal, THEN write and verify the closer. Diagnosing a FAILING or opaque committed arm is the opposite case → sub-suspend, never cheat-bisect (HOL4 — suspend/Resume).
- **A navigation/check TIMEOUT is YOUR looping tactic, not a slow prefix** — diagnose by cheating the frontier, don't widen `timeout=`. [[feedback_replay_discipline]] §TIMEOUT.

### ⛔ RULE J — ONE HOL session at a time
Use a single session; to switch theories, RESTART it into the new theory. A second concurrent session resolves bare theorem names to a built ancestor's OLD version and falsely "passes".
Server-enforced: `hol_start` REFUSES a second concurrent session (escape hatch: `force=True`, only with a reason you can state), and a `file=` from a different workdir is refused — `hol_stop` the session first, then re-init (`hol_restart` needs user consent).

### ⛔ RULE K — `skip_prefix=True` needs EXPLICIT user authorization
`skip_prefix=True` on `hol_state_at`/`hol_goals` binds every PRIOR theorem by `cheat` (statement only, not replayed) — so the target's goal rests on UNVERIFIED prefix statements. The tool says so itself ("This is NOT a verification"). Do NOT use it on your own initiative — not to dodge a slow prefix theorem, not to "navigate faster", not as a substitute for the verification ladder. Default OFF.
- **Allowed only** with explicit user authorization for THAT use (the user says to). Absent it, navigate the real way: `hol_state_at` (full prefix replay), sub-suspend an opaque arm, or accept the slow replay.
- A green result under `skip_prefix=True` proves NOTHING about the target — re-confirm without it (full `hol_state_at` past `QED`, or `holmake`) before any done-claim.

## HOL4-specific working principles

- **Investigate with the live state.** Observe the literal proof state first (`hol_state_at`; the error line). When a proof fails, classify: GOAL wrong, ASSUMPTIONS wrong, or TACTIC wrong? Each needs a different fix.
- **No accidental proofs.** Tactics that close by stumbling (`metis_tac` loops, `gs[]` blowups, `every_case_tac`) are tech debt — name the lemma, name the case-split.
- **Read the original before adapting.** Fixing a cheated/broken proof → read the original (`git show HEAD:<file>`) first; minimal targeted edits, fix the theorem in place (no sibling/wrapper/variant). Substantially different tactics are fine; shipping an easier-to-prove *statement* is case 3 in [[feedback_unprovable_vs_unfound_proof]] — report up, don't ship a divergent statement.
- **New definitions/statements: informal argument first; interface over unfolds.** Sketch the informal proof before any HOL text; be critical the definition/statement captures the intent BEFORE proving against it; prove a new definition's interface lemmas and prefer them to raw unfolds ([[feedback_hol4_mcp_proving]] §Proof strategy; plan ordering: [[feedback_proof_plan_pointers]]).
(The generic working principles in global CLAUDE.md — fall back to simpler, privilege contradicting signals, one unit at a time, verification matches the claim — apply with full force to proof work.)

## HOL4 — iteration loop

⭐ **The winning loop** (default; lowest-cost):
1. **Plan + read the live goal** (RULE B): obligation + per-arm discharge; `hol_state_at`, never from memory.
2. **Reuse a validated template across a family.** Prove one arm/op/case fully, then adapt the *verified* chain to its siblings — change only the deltas (operator, result term, guard/`~`-shape, cost expr).
3. **Develop on the FILE; the session is scratch** (RULE I): the moment a sub-step verifies, flush it into the body ending in a frontier marker. **Default the frontier to `>- suspend "Frontier"`** — it makes the arm independently navigable with the file owning the prefix. Use a bare `cheat` ONLY for a flat tail with no `>-`/`THEN1`/`\\`-chain above it; the instant an arm is inside such a chain (so `hol_state_at` can't enter it), it MUST be `suspend`, not `cheat`. One arm: prove → flush → next.
4. **Jump, don't rebuild.** `hol_state_at` lands on the frontier (cheap, cached); `hol_send` only for SMALL probes (one tactic, minimal goal slice). Never re-send a large/accumulating chunk.
5. **Verify each piece in file-form** (RULE G: `hol_state_at` past its `QED` = "No goals").
6. **Inline-back + clean, re-verify — PER THEOREM, before starting the next** (Gates 1/3): collapse dev sub-suspends to one `Proof … QED` (final arm on the main thread — Gate 1), delete preserved comments, drop `Finalise` if no suspends remain, `hol_state_at` past the final `QED`.

- `hol_state_at`: default; read goals between edits, land on a frontier.
- `hol_goals`: goal count + headlines (`n=k` one goal, `asm=j` one assumption) — replaces `top_goals()` dumps and `length (top_goals())` probes, on the live session or at a file position.
- `hol_search`: DB search by name/pattern (`query=`, `pattern=`, `theory=`) — replaces `hol_send` `DB.find`/`DB.match` probes.
- `hol_send` / `proofManagerLib.e`: interactive probing — SMALL probes at a parked frontier. Can't reach into a `THEN1 (...)` / `>- (...)` arm? Sub-suspend it (don't hand-replay the prefix — risky fallback only).
- `hol_check_proof`: end-of-theorem confirmation only (RULE C).
- `holmake`: end-of-file gate only (RULE A).
- `hol_restart`: effectively never — a broken/weird replay is YOUR proof or navigation error; re-diagnose, don't blame "stale state"/cache (essentially never the cause). Restart needs explicit user consent — ASK first ([[feedback_replay_discipline]]).

**End-of-proof verification ladder** (run after the audit gates pass):
1. **Per-theorem**: `hol_state_at` past `QED` = "No goals (proof complete)" (no `[Inside by/>-]`/`PROOF BROKEN`/`TIMEOUT`) — OR `hol_check_proof` = `Status: OK`.
2. **Per-file**: once every theorem passes (1), `holmake <Theory>.dat` ONCE — the canonical file gate (catches missing `Finalise`, dependency drift).

⛔ **Single-theorem checks (1) silently auto-cheat failed/slow deps** — a green (1) proves the target's tactics against its deps' *statements* only. Run (1) on EACH at-risk theorem AND every new lemma it leans on (transitive trust doesn't count); read the `[auto-cheated deps: …]` / `⚠ depends on cheat` markers in the output. Only cold `holmake` (2) has no auto-cheat. Mechanism: [[feedback_replay_discipline]] §auto-cheat.

NOT proof of done: passing `QED`; `grep -c cheat = 0`; an intermediate goal closed; "looks right"; a per-theorem check whose deps were auto-cheated.

**Cost-discipline trigger**: replay slow (≥30s twice on the same body), or edited-then-replayed >2–3× without reading the goal between → sub-suspend the frontier to shrink replay scope, then jump + small probes. Don't escalate to re-sending big chunks or repeated `hol_check_proof`. Tool-selection detail: [[feedback_replay_discipline]].

## HOL4 — suspend/Resume/Finalise

- ⛔ **suspend/Resume is a STUCK-GOAL tool, not a proof-writing default.** Write ordinary structural and case reasoning directly in the theorem with `>- (...)`/`>>`; never checkpoint an arm merely because the proof is long. Deep or repeated ladders are a process failure, not evidence of a big proof.
- ⛔ **Sub-suspend is the default — and the FIRST move for any FAILING or opaque arm.** For any committed `>-`/`THEN1`/`\\`-chain arm that FAILS or that `hol_state_at` reports as opaque ("target INSIDE step k", "PROOF BROKEN in the opaque step"), and for every non-trivial arm of a broken multi-case proof (`recInduct …_ind`/`Cases_on` whose body stopped admitting after a definition changed): replace it with `>~ [pat] >- suspend "<Arm>"` + `Resume thm[Arm]: cheat QED` after the parent QED, so `hol_state_at` lands on the real goal with the FILE owning the prefix. Right ~99% of the time. Inline `>~ [pat] >- (body)` instead ONLY for an arm you close in <30s after reading the live goal. On the SECOND failed inline attempt on the same goal, sub-suspend — do NOT switch combinator (TRY/ORELSE/FIRST/`>|`, swap the rewrite set, `fs`→`gvs`→`simp`, more `Cases_on`), do NOT cheat-bisect, do NOT reconstruct the goal in a scratch `hol_send` session (RULE G). The combinator that closes a blown-up arm in one shot doesn't exist — sub-suspend directly, don't hunt for a working example first.
- ⛔ **READ ≠ VALIDATE.** READing a (sub-)Resume goal (`hol_state_at` INTO the body — lands at entry, `target=idx=0`, `replayed=0/1`) is a store lookup that replays NOTHING. VALIDATING = `hol_state_at` PAST that body's OWN `QED` → "No goals", `replayed=N/N`. **Procedure, each step on its own QED in order**: (1) dispatcher's QED → "No goals" (registers every sub-suspension); (2) each sub-`suspend`'s own Resume QED → "No goals"; (3) once a sub-body is green at its own QED, inline it back (Gate 1) and re-run (1) — validate in place, never via the parent; (4) whole theorem cold. `target=idx=0, replayed=0/k` at a QED-nav = you landed at body ENTRY (targeted a line inside a `\\`-chain) — re-target the QED line. Broken-dispatcher symptoms (`No such label`; `PROOF BROKEN`/`replayed=k/N` at the dispatcher QED) → fix the dispatcher first. Dispatch + inline craft: [[feedback_suspend_resume]].
- **One label = one goal.** Every `suspend "X"` follows a single-goal selector (`>-` or `>~ [pat] >-`). THEN-form (`>> suspend`/`\\ suspend`) bundles N goals into an unprovable `⅋ᵣ`/`resconj` Catchall and can silently fail to register the suspension. Bundled? split into per-arm labels — never pry the Catchall apart inside a Resume body, never escalate a failed close to `>> suspend "Default"`. [[feedback_suspend_resume]].
- **Sub-suspends and one-shot `[local]` nav-helpers are dev scaffolding** — fine in-session, but ALWAYS inline back before done; surviving dev scaffolding is junk (Gate 1). The ONLY keepers: a genuine multi-case induction (or similar), or a user-approved sub-suspend (≤2-deep, never deeper) — NEVER forgotten dev scaffolding.
- **`Finalise thm;` is MANDATORY** after the last Resume (Gate 2) — add the placeholder the moment you write the first Resume.
- **MCP suspend/Resume may still have edge-case bugs.** Lost suspension / "No such label" on a clean ancestor chain / Holmake-vs-MCP divergence → minimal reproducer, surface it; Holmake wins, report don't work around (RULE D).

## HOL4 — banned tactics

- `TRY` / `ORELSE` (hide failure): existing uses → restructure to `>~ [pat] >- suspend "X"` dispatch before modifying any body. Tempted to add a fresh `TRY`? ask "what shape is THIS goal, what closes it?" — almost always a `>~ [pat]` selector or a `Cases_on`.
- `>|` (`THENL`) (position-keyed brittleness): split per-subgoal via suspend/Resume or per-case `>~`/`>-`, not by goal-stack index.

Spotter's guide for TRY anti-patterns: [[feedback_hol4_mcp_proving]].

## HOL4 — term and identifier quotes

ASCII backticks `` ` `` for terms; ASCII `'` for variable names. Never smart quotes (U+2019). Watch tokens like `x'`, `q'`, `s'`.

## Holmake is the source of truth

Holmake is the file-level gate and the tiebreaker: if `hol_check_proof`/`hol_state_at`/a step-plan disagrees with it, Holmake wins. A genuine, reproducible disagreement on a provably-correct proof is a hol4-mcp bug to REPORT (minimal reproducer, per RULE D) — never a licence for a silent workaround (the banned ones are listed in RULE D). Propose a fix to `~/hol4-mcp/` (or upstream HOL4) only after the user agrees.
