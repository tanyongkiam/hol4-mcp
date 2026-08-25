# hol4-mcp Claude Code hooks

Runtime-enforced interaction policies for HOL4 proof work. Each hook is a
standalone script invoked by Claude Code at a defined lifecycle event
(`PreToolUse`, `PostToolUse`, ...); see
<https://docs.claude.com/en/docs/claude-code/hooks> for the framework.

Hooks are wired in `~/.claude/settings.json` under the top-level `hooks` key
and point at scripts in this directory. The scripts are policy code, kept
under `~/hol4-mcp/` because they enforce HOL4-specific behaviour; settings.json
just references them.

## Why hooks

CLAUDE.md / skill rules are advisory — the model can violate them and rely on the
audit gates to catch it later. Hooks are **runtime-enforced**: a PreToolUse
hook returning exit 2 blocks the tool call entirely, with the stderr message
surfaced to the model as a tool error. This forecloses entire failure modes
(e.g. newly-authoring `TRY` in a `.sml` file) rather than relying on post-hoc
catch.

## Suite map

Status legend: ✅ shipped · 🚧 in progress · 📝 proposed (not yet implemented) · ⏭ skipped (won't implement).

| ID  | Status | Event(s)              | Matcher                | What it does |
|-----|--------|-----------------------|------------------------|--------------|
| H1  | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Block newly-authored banned HOL4 tactics (`TRY`, `ORELSE`, `FIRST`, `THENL`, `>\|`) in `*Script.sml` edits |
| H2  | ⏭     | PreToolUse            | `Edit\|Write\|MultiEdit` | ~~Nudge to run `check_quotes.py` when smart-quote U+2019 appears in a variable-name position~~ — skipped (high FP risk; HOL4 fancy quotes `‘…’` legitimately use U+2018/U+2019, distinguishing variable-name position from term position is brittle) |
| H3  | ⏭     | PreToolUse            | `Write`                 | ~~Block writes to `~/.claude/memory/` containing project-specific anchors~~ — skipped (token fingerprint list is high-maintenance; not worth the upkeep for a placement rule the audit gates already catch on read) |
| H4  | 📝     | PreToolUse            | `Edit\|Write\|MultiEdit` | Warn on `Resume` body starting with `‘Q’ by tac` (step-plan splits at `by`) |
| H5  | ⏭     | PreToolUse            | `mcp__hol4__hol_check_proof` | ~~Block re-call after FAILED with no intervening `hol_state_at` (RULE C)~~ — skipped (H6 covers the failure-time nudge; the block-step needs per-session state that wasn't worth the machinery) |
| H6  | ✅     | PostToolUse           | `mcp__hol4__hol_check_proof` | Inject reminder on `FAILED` / `TIMEOUT` / `PROOF BROKEN` / "Tactic execution failed" (advisory only; never blocks) |
| H7  | ✅     | PostToolUse           | `mcp__hol4__holmake`    | Inject RULE A reminder on every `holmake` call (advisory only; calibrated for legitimate end-of-file gate to disregard) |
| H8  | ✅     | PostToolUse           | `mcp__hol4__hol_state_at` | Inject cost-discipline reminder on any single `hol_state_at` call whose `replay` time ≥ 30s (stateless; cache hits and error paths skipped) |
| H9  | ⏭     | PreToolUse            | `mcp__hol4__hol_restart` | ~~Default-block; CLAUDE.md says "effectively never"~~ — skipped (escape-hatch design too messy for the rare legitimate case; CLAUDE.md text is sufficient deterrent) |
| H10 | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Inject Finalise reminder when a Resume block introduces a new theorem to a `Script.sml` without a matching `Finalise <thm>;` (diff-aware on theorem names; sub-Resumes on existing theorems silent) |
| H11 | ⏭     | PreToolUse            | `mcp__hol4__holmake`    | ~~Gate 1: no leftover sub-Resume labels outside the dispatcher's `suspend` set~~ — skipped (parsing complexity not justified now; Gate 1 audit at end-of-discharge still covers) |
| H12 | ⏭     | PreToolUse            | `mcp__hol4__holmake`    | ~~Gate 3: no `(* preserved/original/master *)` comment blocks in discharged regions~~ — skipped (low-value debris check) |
| H13 | ⏭     | PreToolUse            | `mcp__hol4__holmake`    | ~~Gate 5 cross-check: scan git-modified theorems for banned tactics~~ — skipped (subsumed by H1 at write-time; safety-net value low) |
| H14 | ✅     | PreToolUse            | `Bash`                  | Block destructive git ops without literal `git ok` in the latest user message (transcript-aware; fail-open if transcript unreadable) |
| H15 | ⏭     | PreToolUse            | `Write`                 | ~~On `~/.claude/plans/` writes, advise if "Operating principles" section is missing~~ — skipped (high FP on non-proof plans; marker regex fragile; plan template is the better forcing function) |
| H16 | ✅     | PostToolUse           | `mcp__hol4__hol_state_at\|mcp__hol4__hol_send\|mcp__hol4__hol_check_proof` | Inject advisory when goal display contains `⅋ᵣ` / `resconj` — the canonical indicator that multiple subgoals were bundled into one Resume body via a shared `suspend` label (hol4-proving skill "one label = one goal" violation) |
| H17 | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Block newly-authored non-canonical `suspend` in `*Script.sml` edits: THEN-form (`>>` / `\\` / `THEN` then `suspend "..."`) and the `by (suspend "...")` justification form — must be `>-` (THEN1) per "one label = one goal" (edit-time guard for the runtime failure H16 detects) |
| H18 | ✅     | PreToolUse            | `mcp__hol4__hol_send\|Edit\|Write\|MultiEdit` | Block the `markerLib` suspension-lookup query (the `(string*thm) option` one — returns NONE in a bare session, tempts guessing the suspended goal); point to `set_suspended_goal` to actually load it |
| H19 | ✅     | PreToolUse            | `mcp__hol4__hol_restart` | Advise (never block) when `hol_restart` is called without the user asking — restart fits a stale ancestor `.dat`, not a broken replay; silent when the latest user message says `restart ok` |
| H20 | ✅     | PreToolUse            | `mcp__hol4__hol_send`   | Block sending a massive tactic chain through `hol_send` (≥6 THEN-combinators, or ≥8 non-blank lines with ≥2 combinators) — RULE I: flush to the file, jump with `hol_state_at`; small probes pass |
| H22 | ✅     | SessionStart          | (all sessions)          | In HOL4 directories (Holmakefile/.holpath in cwd or ≤3 ancestors, or `*Script.sml` in cwd), inject a directive to load the `hol4-proving` skill before any proof work |
| H23 | ✅     | PreToolUse            | `mcp__hol4__hol_send`   | Block the standalone-`prove` workflow in `hol_send` (`prove(` / `store_thm(` / `save_thm(` / `TAC_PROOF(`) — RULE I + RULE G: a proof closed in the scratch session with a hand-typed goal proves nothing about the file form; write a `Theorem … QED` or sub-suspend the arm (`>- suspend` + `Resume`) |
| H24 | ✅     | PreToolUse            | `Edit\|Write\|MultiEdit` | Advise (never block) on newly-defined tactic abbreviations (`val foo_tac = …` / `fun foo_tac … = …`) in `*Script.sml` — lifting a tactic needs a strong stated justification; defaults are lift a LEMMA or leave the duplication. Diff-aware on binding names; `*Lib.sml`/`*Syntax.sml` out of scope by the path test |
| H25 | ✅     | PostToolUse           | `mcp__hol4__hol_check_proof\|mcp__hol4__hol_state_at\|mcp__hol4__holmake` | Sweep finished proof text for composition defects (adjacent normalisers, `impl_tac` sandwich, `>-` not marking a sibling, near-identical sibling arms, nested splitter ladders, n-ary tactic forms, self-feeding lambdas). Fires per theorem on `hol_check_proof` → `Status: OK`; counts-only backstop on `holmake` for git-modified scripts. Advisory; checks live in `proof_sweep.py` |
| H26 | ✅     | —                     | —                      | **Implemented inside H6**, not as its own hook: it fires on the same event with the same payload, so a separate hook would mean two messages on one failure. See "The symptom table" under H6 |
| H27 | ✅     | PreToolUse            | `Bash`                  | Run the audit gates against a `git commit` touching `*Script.sml` and block on what it finds — diff-scoped, so only theorems the commit touches are judged. Gates 1/2/3/5 on added lines plus `proof_sweep` per touched theorem. Override with `wip ok` |
| H28 | ✅     | PreToolUse            | `Bash`                  | Block shell invocations of `Holmake` / raw `poly`\|`hol`, redirecting to `mcp__hol4__holmake` / `hol_start`. Command-position match only, so prose and log paths pass. Override with `shell holmake ok` |

Skipped: H2, H3, H5, H9, H11, H12, H13, H15. H21 (holmake-on-cheated-theory
blocker) was proposed and rejected. H4 is the only live proposal.

The live wiring is `~/.claude/settings.json`; `install_hooks.py --check`
reports any drift between it and the scripts in this directory.

## H1 — banned-tactics scanner

**File**: `h1_banned_tactics.py`
**Event**: `PreToolUse`
**Matcher**: `Edit|Write|MultiEdit`
**Effect**: blocks the tool call (exit 2) if the new content of a `*Script.sml`
file contains any banned HOL4 tactic that did not appear in the pre-edit
content. Library SML files (`*Lib.sml`, `*Syntax.sml`, `Tactical.sml`, `Q.sml`,
etc.) are exempt — they legitimately define `TRY` / `ORELSE` as identifiers.

### What counts as banned

From the `hol4-proving` skill (`HOL4 — banned tactics` section; formerly in `~/.claude/CLAUDE.md`):

- `TRY` — hides failure.
- `ORELSE` — hides failure.
- `FIRST` — hides failure.
- `THENL` and its operator form `>|` — position-keyed brittleness.

### How it decides

1. Reads PreToolUse JSON on stdin (fields: `tool_name`, `tool_input`).
2. Skips if `tool_name` is not in `{Edit, Write, MultiEdit}` or `file_path`
   does not end `Script.sml`.
3. Computes pre-edit and post-edit content per tool:
   - `Edit` → `old_string` vs `new_string`.
   - `Write` → existing file content (read from disk) vs `content`.
   - `MultiEdit` → concatenated `old_string`s vs concatenated `new_string`s.
4. Strips `(* ... *)` comments and `"..."` string literals (non-nested),
   then counts each banned-tactic regex in both sides.
5. Exits 2 + stderr if any banned tactic's post-edit count exceeds its
   pre-edit count. Otherwise exits 0.

The diff-based check means a pre-existing `TRY` carried verbatim through an
edit does NOT trigger the hook — only **newly introduced** occurrences do.
This mirrors Gate 5 in the skill, which tolerates pre-existing uses until the
theorem is restructured and treats anything you authored or copied this
session inside a discharged region as a violation.

### Bypass

The hook intentionally has no env-var override (an env set at Claude Code
launch is not a useful per-edit escape hatch). To bypass, comment out the H1
entry in `~/.claude/settings.json`:

```json
{
  "hooks": {
    "PreToolUse": [
      // { ... H1 entry ... }
    ]
  }
}
```

…and restart Claude Code (or re-source settings if the version supports
hot-reload).

### Limitations

- Comment / string stripping is non-nested. `(* (* TRY *) *)` would incorrectly
  leave the inner `TRY` visible after one strip pass. This is acceptable
  because nested comments are vanishingly rare in this codebase.
- `Write` reads pre-existing content from disk. If the file is being created
  for the first time, pre-edit content is treated as empty (correct).
- Matches the HOL4 proof-script suffix `Script.sml`. If you ever hand-edit a
  HOL4 internal proof script (e.g. under `~/research/HOL/src/.../*Script.sml`)
  where `TRY` is used as an SML identifier rather than a banned tactic, the
  hook will still fire — comment it out in settings.json for that session.

## H6 — post-`hol_check_proof` failure reminder + symptom hint

**File**: `h6_check_proof_failure.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__hol_check_proof`
**Effect**: never blocks. Injects a RULE C reminder on a failed
`hol_check_proof`, plus — when the failing tactic matches the symptom table —
the corpus fact that explains that symptom.

### What triggers it

A failure signature in the tool result: `TIMEOUT after Ns`, `Status: FAILED`,
`Status: INCOMPLETE`, `Status: ERROR`, `<-- FAILED`, `Tactic execution failed`,
`PROOF BROKEN`. Miss → silent exit 0.

`Status: CHEAT (not verified)` is intentionally **not** a trigger — reaching a
parked `cheat` is the expected result of the cheat-the-frontier pattern
(hol4-proving skill RULE I), not a failure.

Exact wording of the reminder lives in the hook (`REMINDER`); it is not
duplicated here, so the two cannot drift.

### The symptom table

The corpus already contains the facts that would prevent the most expensive
debugging detours — and they still do not reach the point of use. Two
structural reasons, neither fixable by wording: **volume vs recall** (dense
facts read at session start are not available at hour six), and **indexed by
cause, searched by symptom** (sections are named for causes; at the moment of
failure the cause is the ANSWER, not the question). H6 already fires at the
right moment and already has the failing tactic in its payload.

| failing tactic | failure shape | injected hint |
|---|---|---|
| `qpat_x_assum` / `qpat_assum` / `rename1` / `qmatch_*` | raised | pattern no longer matches: a prover-generated name that got re-rolled, or a tyvar mismatch that prints identically |
| `drule*` / `irule*` / `match_mp_tac` / `mp_then` | raised | free tyvar in the lemma's OWN statement; or the constant is `[simp]`-tagged and no longer an atom; or the assumption is not yet in the lemma's shape |
| `simp` / `simp_tac` / `asm_simp_tac` / `srw_tac` | left goals | `simp` uses assumptions as they stand; `fs`/`gvs`/`rw` simplify them first — and split a disjunctive assumption |

**Calibration.** The hint fires only when all of these hold, because a hint
that is wrong at the moment of failure is worse than silence — it is read when
trust is highest:

- the failing step is **short** (≤200 chars) — a token buried in a lumped
  opaque arm is not evidence about that arm, and the server already tells you
  to sub-suspend those;
- the matched tactic is the step's **first** one — a tactic after a combinator
  may never have run;
- the **failure shape matches the row**. `raised` rows need a HOL_ERR /
  exception signature, so a matcher that ran fine and merely left goals gets
  nothing. The `simp` row needs the opposite: goals left, no exception. No row
  matches a TIMEOUT — the server already prints a looping-tactic advisory
  there, and a second opinion on top of it is noise.

Rows deliberately exclude `fs`/`gvs`/`rw`: for those the simp hint is not just
unhelpful but false. `srw_tac` counts as `rw` and is excluded with it — in
`bossLib`, `srw_tac` is `BasicProvers.srw_tac` and `rw` is `PRIM_SRW_TAC`,
the same family.

### Limitations / known unknowns

- The PostToolUse JSON schema for MCP tool results is not canonical across
  Claude Code versions. `hook_payload.output_text` scans several plausible
  field names and collects every string leaf. If a future version uses a name
  outside that list the trigger silently doesn't fire — failing open is the
  right default.
- No dedupe. If you fail `hol_check_proof` 5 times in a row on the same
  theorem, you get 5 reminders. Each says the same useful thing — that's
  intentional.
- The hint is keyed on the failing tactic alone. It cannot see the goal, so
  it is a checklist to run, not a verdict; it says so.

## H8 — `hol_state_at` replay-cost nudge

**File**: `h8_state_at_replay_cost.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__hol_state_at`
**Effect**: never blocks. On a `hol_state_at` call whose `replay` time crossed
30s, injects a system reminder framed for the *repeated-use* anti-pattern from
the hol4-proving skill cost-discipline trigger.

### What triggers it

The hook parses the trailing `[Timing: total=Nms, replay=Mms, method=...]`
line emitted by hol4-mcp's `hol_state_at`. If `replay >= 30000ms` (30s) and
the call did real replay (not a cache hit), inject. Otherwise silent.

Skips (silent exit 0):
- Missing `[Timing:` line → error path; no replay happened.
- `replayed=0/N` in the cache-state diagnostics → cache hit; replay
  didn't run despite the timing field.
- `replay < 30000ms` → under threshold.
- `tool_name` not `mcp__hol4__hol_state_at`.

### What the reminder says

Points at the two cheap alternatives — sub-suspend the frontier, or `hol_send`
SMALL probes at the already-parked frontier — and explicitly acknowledges that
a single slow call may be legitimate (first touch, cold cache), so it reads as
conditional advice rather than a per-call accusation. Exact wording lives in
the hook (`REMINDER_TEMPLATE`).

### Threshold rationale

30s matches the skill's cost-discipline trigger text verbatim. `replay` is
used in preference to `total` because hol_send / sub-suspend address replay
overhead specifically; if `total` were dominated by file load (`replay` low),
neither tactic would help and the nudge would be misleading.

### Limitations

- Single-call decision. A genuinely cold-cache first call on a large file
  triggers the reminder once; the wording is calibrated for this, but the
  reminder still appears. If this proves noisy, escalate to a stateful
  variant that requires two consecutive slow calls.
- Output-format dependent: relies on hol4-mcp's `[Timing: ... replay=Nms]`
  format. A future hol4-mcp change to this format would silently disable the
  hook (fails open — no false blocks).

## H7 — holmake iteration-discipline reminder

**File**: `h7_holmake_advisory.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__holmake`
**Effect**: never blocks. Every `holmake` call gets a RULE A reminder
injected via `additionalContext`.

The reminder ends with an explicit "if this was the legitimate end-of-file
gate or a setup step to unstick a stale .dat, disregard" — so the cost on
legitimate use is just a few lines of system reminder noise. The cost on
illegitimate use (iteration-mode holmake) is the RULE A nudge appearing at
exactly the moment of the violation.

This is the lightest form of H7. A stateful variant that *blocks* on the
edit-then-holmake-without-verification pattern is possible but adds session
state machinery; the advisory-only form was chosen as adequate.

## H10 — Resume-needs-Finalise reminder

**File**: `h10_resume_needs_finalise.py`
**Event**: `PreToolUse`
**Matcher**: `Edit|Write|MultiEdit`
**Effect**: never blocks. When an Edit/Write/MultiEdit on a `Script.sml`
file introduces a new Resume theorem whose `Finalise <thm>;` line is not in
the post-edit content, injects a one-line `additionalContext` reminder.

### Diff-aware on theorem NAMES

The hook computes pre-edit and post-edit content (reads the file from disk,
applies the edit virtually) and fires only when a Resume theorem name is
**newly added** in this edit (`post_names - pre_names`). Consequences:

- Adding `Resume foo[A]` to a file that has no other Resume foo: fires if
  no `Finalise foo;` present.
- Adding a **sub-Resume** `Resume foo[A_subarm]` to a file that already has
  `Resume foo[A]:` and `Finalise foo;`: silent. The theorem name `foo` is
  not newly introduced; sub-suspending is a normal mid-discharge operation.
- Re-editing an existing Resume body (no new Resume header): silent.

### Reminder content

Names the theorem(s) missing a `Finalise` and cites Gate 2; separate wordings
for the one-theorem and several-theorem cases. Exact text lives in the hook.

## H14 — destructive git ops require `git ok` consent

**File**: `h14_git_destructive_consent.py`
**Event**: `PreToolUse`
**Matcher**: `Bash`
**Effect**: blocks (exit 2) destructive `git` invocations unless the literal
phrase `git ok` (case-insensitive) appears somewhere in the latest user
message in the session transcript.

### Destructive verb list

Matched after `git` **and any global options it carries** — `git -C dir commit`,
`git --no-pager push` and `git -c k=v commit` all reach the verb, so the
options are not a bypass:
`commit`, `push`, `stash`, `revert`, `reset`, `checkout`, `switch`, `restore`,
`clean`, `rm`, `mv`, `pull`, `merge`, `rebase`, `cherry-pick`, `apply`, `am`.

Plus: `git branch -D`, `git branch -d`, `git branch --delete`.

Read-only verbs (status, log, diff, show, grep, blame, fetch, ls-*, rev-*,
remote without -add/-rm, branch listing) are unmatched and pass through.

### Consent mechanism

The hook reads `transcript_path` from its PreToolUse payload (Claude Code
populates this with the path to the session transcript JSONL). It scans the
**latest user message** for `\bgit\s+ok\b` (case-insensitive). Present →
permit. Absent → block.

`git ok` is a one-shot grant tied to that specific message — it does not
persist across subsequent user messages. If you say `git ok` and I push;
your next message without `git ok` does NOT consent to another push.

### Fail-open conditions

The hook permits the call (exits 0) if:
- `transcript_path` is missing from the payload, or
- The transcript file doesn't exist or can't be read, or
- The transcript has no user message identifiable in any of the supported
  schema variants.

This avoids the hook blocking legitimate work due to a hook bug or schema
change.

### Limitations

- **`git checkout` granularity**: this hook blocks ALL `git checkout`,
  including benign branch switches like `git checkout main`. CLAUDE.md
  distinguishes destructive `checkout <file>` from harmless branch switches,
  but reliably detecting that with regex is fragile. Type `git ok` to grant
  branch switches when needed.
- **Consent FN**: a user message containing the word "git" *and* the word
  "ok" in unrelated contexts could falsely consent — but the regex
  `\bgit\s+ok\b` requires them adjacent, so the false-consent risk is low.
- **Token shadowing**: if your latest user message asks me to write the
  literal phrase "git ok" to a file, the hook still reads it as consent.
  Acceptable risk.

## H16 — bundled-subgoal (`resconj`) detector

**File**: `h16_bundled_suspend_goals.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__hol_state_at|mcp__hol4__hol_send|mcp__hol4__hol_check_proof`
**Effect**: never blocks. When the tool output contains the goal-display
marker `⅋ᵣ` (U+214B + U+1D63) or the constant name `resconj`, injects an
advisory `additionalContext` reminder.

### What triggers it

The HOL4 `proofManagerLib`-based `suspend` framework uses a binary constant
`resconj` to MERGE the residual goals of multiple suspended subgoals under
the SAME label into one combined goal at Resume time. Display rendering of
`resconj x y` is `x ⅋ᵣ y`. Either token in a goal display means goals were
bundled.

This is symptomatic of:
- A dispatcher that routes the same `suspend "Label"` to multiple arms
  (`>~ [pat_a] >- suspend "X" >~ [pat_b] >- suspend "X"` …). Each arm's
  residual gets tagged identically, and Resume sees them merged. This covers
  the alike-patterns case too: a single `>~ [pat] >- tac` arm runs on the
  FIRST match only, so bundling means two arms reached one label, not one arm
  firing twice.
- A `>>` (THEN) distributing across multiple residual goals before
  `suspend "Label"`, bundling them.

Bundled goals cannot be decomposed cleanly with standard HOL tactics —
the user must split the dispatcher into per-arm labels (one label = one
goal) so each Resume body sees a single goal.

### What the reminder says

Lists the three causes above and the fix — give each suspended arm its OWN
label and write one Resume body per label — and warns against attacking the
merged `resconj` goal directly. Exact text lives in the hook.

### Limitations

- Triggers on any goal display containing the marker. A legitimate proof
  artifact that intentionally references `resconj` (e.g. a meta-discussion
  via `term_to_string`) would also fire — acceptable, since there's no
  legitimate reason to ship code containing the symbol.
- Depends on `hook_payload.output_text` keeping strings raw: JSON-escaping the
  payload would hide the U+214B marker and silently disable the hook.

## H17 — non-canonical `suspend` blocker

**File**: `h17_then_suspend.py`
**Event**: `PreToolUse`
**Matcher**: `Edit|Write|MultiEdit`
**Effect**: blocks (exit 2) if the new content of a `*Script.sml` edit places
`suspend "..."` non-canonically — either after a THEN-form combinator (`>>`,
`\\`, or the word `THEN`), or as a `by` justification
(`` `P` by (suspend "X") `` / `` `P` by suspend "X" ``).

### Why

`suspend "L"` is a single-goal tactic; THEN distributes its right operand across
ALL residual goals, tagging each with the same label. At Resume time those goals
are merged via `resconj` into one unprovable bundled goal — the runtime failure
H16 detects. The canonical form is THEN1 (`>-`) immediately before every
`suspend`. H17 catches the mistake at edit time so it never reaches live state.

### What counts

Regex `(?:>>(?!~)|\\\\|\bTHEN(?![1L_]))\s*suspend\s*"..."`:
- `>>` — negative lookahead excludes `>>~` / `>>~-` (different combinators).
- `\\` — CakeML preamble synonym for THEN.
- the word `THEN` — word-boundary; `THEN1` / `THENL` / `THEN_LT` excluded.

Plus regex `\bby\s*\(?\s*suspend\s*"..."` for the `by`-justification form
(`` `P` by (suspend "X") `` / `` `P` by suspend "X" ``) — a single-goal tactic
parked off-pattern instead of dispatched with `>-`. No legitimate `by ... suspend`
exists, so no false positives; the THEN regex never sees these (`suspend` is
preceded by `by`/`(`, not a THEN-form).

Both fire anywhere in the edit text, including inside parens
(`>- (... >> suspend "L")`).

### Correct forms (not blocked)

`>- suspend "L"` · `>- suspend "L1" >- suspend "L2"` ·
`tac1 >> tac2 >- suspend "L"` (THEN for the transforms, THEN1 only at the
boundary) · `>~ [pat] >- suspend "L"`.

## H18 — suspension-lookup ban

**File**: `h18_ban_lookup_suspension.py`
**Event**: `PreToolUse`
**Matcher**: `mcp__hol4__hol_send|Edit|Write|MultiEdit`
**Effect**: blocks (exit 2) if a `hol_send` command (or an Edit/Write/MultiEdit
body) contains the banned `markerLib` suspension-lookup token (regex
`\blookup_` + `suspension\b`).

### Why

That query is the wrong tool for inspecting a suspended goal. Its type is
`(string * thm) option`, and in a bare MCP session it returns NONE — the
suspension store is populated by file replay, not by a lone `hol_send`. A NONE
return tempts guessing the suspended goal's assumptions instead of reading them,
a RULE F / RULE D violation that has cost real session time.

### What it points to

To READ a suspended goal, LOAD it and inspect normally:

    markerLib.set_suspended_goal {suspension_name = "<thm>", label_name = "<label>"};
    val (asl,w) = proofManagerLib.top_goal();
    List.app (fn t => print (term_to_string t ^ "\n")) asl;

The parent Theorem must be processed up to its QED first — navigate
`hol_state_at` to the dispatcher's QED so the suspension is in the store. In a
script, write the body inside `Resume thm[Label]: ... QED` and navigate with
`hol_state_at`.

### Limitation

Fires on any occurrence of the banned token, including in a memory note or
comment about the ban itself (this README phrases around it for that reason).
Acceptable — the token has no legitimate use in committed proof work.

## H27 — audit gates at commit time

**File**: `h27_commit_audit_gate.py`
**Event**: `PreToolUse`
**Matcher**: `Bash`
**Effect**: blocks (exit 2) a `git commit` that would record proof code failing
the audit gates. Override: `wip ok` in the latest user message.

### Why

The skill's audit gates fire "when you feel done" — self-reported, so nothing
fires when the feeling doesn't arrive. Scaffolded proofs pass `hol_check_proof`
AND `holmake`, so no other signal catches them either. H25 reports composition
defects but is a PostToolUse advisory and cannot stop anything. This makes the
gates mechanical at the one moment that is unambiguous: proof code leaving your
hands.

### Diff-scoped

Only what the commit introduces is judged. A theorem is swept only if the commit
touches it; `cheat`, banned tactics and `Resume` count only on ADDED lines.
Pre-existing debris in untouched theorems is tolerated until that theorem is
restructured — exactly what Gate 5 says. `-a` and `--amend` shift the diff base.

### What it checks, and what it deliberately does not

Blocks on Gates 1, 2, 3, 5 and the `proof_sweep` composition checks.

**Gate 6 (single-use `[local]` helpers) is deliberately excluded.** Its keeper
case — a small, intent-documenting named fact — is the common and correct idiom,
and no mechanical test separates it from a one-shot nav-helper. Calibrating
against a reviewed script, the check fired on `clean_prog_CONS`,
`in_cc_eq_state_cc` and five siblings, all of which should stay. It remains a
judgement prompt in the skill's audit, where a human does the judging.

Gate 1 is kept only because size discriminates it: keeper (a) is a per-case
`Resume` ladder, so a theorem with a *short* run of Resume blocks reads as the
deferred tail the gate calls junk, while a long ladder is the sanctioned form
and passes silently.

### Calibration

The bar was "refuse the commit that needed a cleanup, pass the cleaned result",
measured on a real before/after pair: the pre-cleanup revision of a proof script
is refused with ~190 findings, the reviewed version that shipped passes clean.
Anything that fired on the shipped version was treated as a false positive and
removed or narrowed, not tolerated.

### Limitations

- `--amend` uses `HEAD~1` as the base, which also picks up unstaged working-tree
  changes. Approximate by design; it errs toward showing more.
- Fails open on anything unexpected — not a repo, a git error, an unreadable
  file. A gate bug must never block real work.
- Runs alongside H14, which gates the same commits on `git ok`. Two hooks on one
  call is intentional here: they answer different questions (may you commit at
  all, and is this code fit to commit).

## Installing the full suite

The scripts in this directory are dormant until wired into Claude Code's
`~/.claude/settings.json`. Schema reference:
<https://docs.claude.com/en/docs/claude-code/settings#hooks>.

### Installing (one command)

```bash
~/hol4-mcp/hooks/install_hooks.py          # merge every hook into settings.json
~/hol4-mcp/hooks/install_hooks.py --check  # report drift, write nothing (exit 1 if any)
~/hol4-mcp/hooks/install_hooks.py --print  # emit the JSON block for a manual merge
```

`install_hooks.py` discovers every `h<N>_<name>.py` beside it and reads the
registration each hook declares at module level:

```python
HOOK_EVENT   = "PreToolUse"               # or PostToolUse, SessionStart, ...
HOOK_MATCHER = "Edit|Write|MultiEdit"     # or None = all calls for this event
```

**Adding a hook file is therefore the only step needed to install it** — there
is no list here to keep in sync, and a hook that omits `HOOK_EVENT` is an error
rather than a silent omission. Declarations are read statically (`ast`), never
imported, so a broken hook cannot execute during install.

Merging is idempotent and additive: entries already pointing at a hook are left
alone, entries for scripts outside this directory are never touched, and a
timestamped backup of `settings.json` is written before any change. Backups
accumulate one per change — sweep them occasionally with
`rm ~/.claude/settings.json.bak.*`. Merging by hand also works — JSON has no
multiple `hooks` keys, and a trailing comma makes the whole block vanish with
no warning.


### Manual / single-hook wiring

To install a subset, drop the desired script (`chmod +x` already if cloned),
and add only its entry under the matching event. Per-hook
matchers and event placement are in the Suite map table near the top of
this document.

### Hot-reload

`settings.json` reloads on the next tool call — no Claude Code restart
required. If a hook silently stops firing after an edit, the JSON is
malformed (typically a trailing comma); fix and retry.

### Quick sanity check

```bash
# Confirm each script is executable and parses
for f in ~/hol4-mcp/hooks/*.py; do
  python3 -c "import ast; ast.parse(open('$f').read())" && echo "ok: $f"
done

# Confirm settings.json is valid JSON
python3 -c "import json; json.load(open('$HOME/.claude/settings.json'))" \
  && echo "settings.json ok"

# Confirm every hook here is wired and no wired hook has vanished
~/hol4-mcp/hooks/install_hooks.py --check

# Confirm the guidance these hooks cite still resolves (links, §sections,
# paths, H-numbers) — a hook message naming a renamed section is a dead
# reference the model reads at the worst possible moment
~/hol4-mcp/skills/hol4-proving/corpus_check.py
```

### Disabling

Remove or rename the `hooks` key in `~/.claude/settings.json` (e.g.
`hooks` → `hooks_disabled`). To disable one hook, delete its entry.

## Stdin / stdout / exit-code contract

Reference: <https://docs.claude.com/en/docs/claude-code/hooks>.

- **stdin**: JSON payload. PreToolUse includes `tool_name`, `tool_input`,
  `session_id`, `cwd`, `hook_event_name`. PostToolUse additionally includes
  the tool result.
- **exit 0**: action proceeds.
- **exit 2 + stderr**: action is blocked; stderr surfaced to the model as
  tool error.
- **JSON on stdout** (exit 0) can inject `hookSpecificOutput.additionalContext`
  to add context visible to the model.
- Hook should be fast. A per-entry `timeout` may be set in settings.json;
  none of these hooks does, so all run under Claude Code's default. Every hook
  here returns in well under a second, so the default is not a constraint.

## Shared modules

Two files here are **not** hooks — `install_hooks.py` discovers only
`h<N>_<name>.py`, so a plain name is never wired by accident:

- `hook_payload.py` — `output_text(payload)` (a PostToolUse result flattened to
  searchable text, strings kept raw) and `latest_user_message(payload)` (newest
  real user turn, for the consent-gated hooks). Every hook that reads a payload
  uses these; reimplementing one is how the copies drift apart.
- `proof_sweep.py` — the composition checks H25 runs, also usable standalone:
  `./proof_sweep.py FILE [FIRST_LINE LAST_LINE]`.

## Per-session state

H25 caches the last file any hol4 call named under
`~/.claude/hook-state/<session_id>/`, keyed by the `session_id` field on the
hook input — `hol_check_proof` is usually called without `file=`, so without
the cache the sweep has nothing to read. Every other hook is stateless.
Cleanup: weekly `find ~/.claude/hook-state -mtime +7 -delete`.

## See also

- `../skills/hol4-proving/SKILL.md` (+ its `notes/`) — the HOL4 proof-interaction rules these hooks enforce; exposed globally via the `~/.claude/skills/hol4-proving` symlink.
- `~/.claude/CLAUDE.md` — generic behavioural rules (editing/git — H14's source — memory-writing, working principles).
- `~/hol4-mcp/LOCAL_CHANGES.md` — local divergences of the running MCP server.
