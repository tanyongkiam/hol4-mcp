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
| H19 | ✅     | PreToolUse            | `mcp__hol4__hol_restart` | Block `hol_restart` without literal `restart ok` in the latest user message (RULE J / "effectively never"; transcript-aware, fail-open, same consent design as H14) |
| H20 | ✅     | PreToolUse            | `mcp__hol4__hol_send`   | Block sending a massive tactic chain through `hol_send` (≥6 THEN-combinators, or ≥8 non-blank lines with ≥2 combinators) — RULE I: flush to the file, jump with `hol_state_at`; small probes pass |
| H22 | ✅     | SessionStart          | (all sessions)          | In HOL4 directories (Holmakefile/.holpath in cwd or ≤3 ancestors, or `*Script.sml` in cwd), inject a directive to load the `hol4-proving` skill before any proof work (the HOL4 ruleset moved out of global CLAUDE.md into the skill, June 2026) |
| H23 | ✅     | PreToolUse            | `mcp__hol4__hol_send`   | Block the standalone-`prove` workflow in `hol_send` (`prove(` / `store_thm(` / `save_thm(` / `TAC_PROOF(`) — RULE I + RULE G: a proof closed in the scratch session with a hand-typed goal proves nothing about the file form; write a `Theorem … QED` or sub-suspend the arm (`>- suspend` + `Resume`) |

Ship order recommendation: H1 → H6 → H8 → H7 → H10 → H14 → H16 → H17 → H18 → H19 → H20 → H22 → H23. (H2, H3, H5, H9, H11, H12, H13, H15 skipped; H21 — holmake-on-cheated-theory blocker — proposed and rejected by user, June 2026.)

The live wiring is `~/.claude/settings.json` (source of truth); the sample
JSON at the bottom of this file may lag it.

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
This matches the rule: *"Pre-existing TRY / ORELSE / `>|` in untouched
theorems is acceptable until that theorem itself is restructured. Any banned
tactic you authored or copied this session inside a discharged region is a
discharge violation."*

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

## H6 — post-`hol_check_proof` failure reminder

**File**: `h6_check_proof_failure.py`
**Event**: `PostToolUse`
**Matcher**: `mcp__hol4__hol_check_proof`
**Effect**: never blocks. On a failed `hol_check_proof` invocation, injects a
terse system reminder citing RULE C and the sub-suspend pattern.

### What triggers it

The hook scans the PostToolUse `tool_output` / `tool_response` payload for any
of these regexes:

- `TIMEOUT after Ns`
- `Status: FAILED`
- `Status: INCOMPLETE` (the real hol4-mcp failure-state status string)
- `Status: ERROR`
- `<-- FAILED` (per-step annotation in the trace)
- `Tactic execution failed`
- `PROOF BROKEN`

Hit → inject reminder via `hookSpecificOutput.additionalContext`. Miss → silent
exit 0.

`Status: CHEAT (not verified)` is intentionally **not** a trigger — that's a
legitimate cheat-probing return per the cheat-probing pattern (feedback_hol4_mcp_proving).

### What the reminder says

```
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
"Tactic execution failed" wrapper.
```

### Limitations / known unknowns

- The PostToolUse JSON schema for MCP tool results is not canonical across
  Claude Code versions. The hook scans several plausible field names
  (`tool_output`, `tool_response`, `result`, `output`, `response`) and
  serialises dict/list shapes to JSON before searching. If a future version
  uses a name not in that list, the trigger silently doesn't fire — failing
  open is the right default.
- No dedupe. If you fail `hol_check_proof` 5 times in a row on the same
  theorem, you get 5 reminders. Each says the same useful thing — that's
  intentional.

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

```
hol4-hook H8: hol_state_at replay took <N.N>s on <file>.

A single slow replay can be legitimate (cold cache, first call on a large
file, no incremental reuse available). The anti-pattern flagged by the hol4-proving skill
cost-discipline trigger is REPEATEDLY running expensive hol_state_at calls
on the same body -- that's "burning replay time".

If you find yourself re-running hol_state_at on this body:
  - Sub-suspend the frontier (primary fix): `>- suspend "Label"` +
    `Resume thm[Label]: cheat QED` after the parent QED. Replay scope shrinks
    to the body only, and the file owns the prefix.
  - For a quick check, `hol_send` SMALL probes (a single `e`/`ef` tactic) at the
    already-parked frontier -- NOT `eall`/`expandf` (all-goals drivers misfire
    on a goalfrag), NOT a re-sent chain (RULE I/G).
```

The wording explicitly acknowledges that a single slow call may be legitimate
(first touch, cold cache), so the reminder is conditional advice rather than
a per-call accusation.

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

Single missing theorem:
```
hol4-hook H10: Resume <thm> added; insert `Finalise <thm>;` after the last
Resume block now (hol4-proving skill Gate 2).
```

Multiple:
```
hol4-hook H10: Resume blocks for <thm1>, <thm2> added without Finalise.
Insert `Finalise <thm>;` placeholders now (hol4-proving skill Gate 2).
```

## H14 — destructive git ops require `git ok` consent

**File**: `h14_git_destructive_consent.py`
**Event**: `PreToolUse`
**Matcher**: `Bash`
**Effect**: blocks (exit 2) destructive `git` invocations unless the literal
phrase `git ok` (case-insensitive) appears somewhere in the latest user
message in the session transcript.

### Destructive verb list

Matched after `git `:
`commit`, `push`, `stash`, `revert`, `reset`, `checkout`, `restore`, `clean`,
`rm`, `mv`, `pull`, `merge`, `rebase`, `cherry-pick`.

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
- A dispatcher that uses the same `suspend "Label"` on multiple arms
  (`>~ [pat_a] >- suspend "X" >~ [pat_b] >- suspend "X"` …). Each arm's
  residual gets tagged identically, and Resume sees them merged.
- A `>>` (THEN) distributing across multiple residual goals before
  `suspend "Label"`, bundling them.
- A `>~ [pat] >- suspend "Label"` whose pattern matches more than one goal.

Bundled goals cannot be decomposed cleanly with standard HOL tactics —
the user must split the dispatcher into per-arm labels (one label = one
goal) so each Resume body sees a single goal.

### What the reminder says

```
hol4-hook H16: goal display contains `⅋ᵣ` / `resconj` -- multiple
subgoals are bundled into one Resume body.

Cause is one of:
  - The parent dispatcher used the SAME `suspend "Label"` on MULTIPLE arms.
    ...
  - A `>>` (THEN) distributed over residual goals before `suspend "Label"`,
    bundling them.
  - A `>~ [pat] >- suspend "Label"` pattern matched and fired more than
    once because subsequent dispatcher arms have the same pattern shape.

Fix:
  - Split the suspended arms by giving each its OWN label
    (`suspend "Label_NONE"`, `suspend "Label_Break"`, ...), and write a
    Resume body per label. ...
```

### Limitations

- Triggers on any goal display containing the marker. A legitimate proof
  artifact that intentionally references `resconj` (e.g. a meta-discussion
  via `term_to_string`) would also fire — acceptable, since there's no
  legitimate reason to ship code containing the symbol.
- Same `tool_output`/`tool_response` / `result` / `output` / `response`
  field-name fallback as H6/H8; uses `ensure_ascii=False` so the U+214B
  marker survives dict serialisation.

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

## Installing the full suite

The scripts in this directory are dormant until wired into Claude Code's
`~/.claude/settings.json`. Schema reference:
<https://docs.claude.com/en/docs/claude-code/settings#hooks>.

### One-shot wiring (copy-paste)

Append (or merge) the following `hooks` block into `~/.claude/settings.json`.
If you already have a `hooks` key, merge by hand — JSON does not support
multiple `hooks` keys, and trailing commas are silently rejected (the entire
hooks block disappears with no warning if you slip one in).

```json
{
  "hooks": {
    "PreToolUse": [
      {
        "matcher": "Edit|Write|MultiEdit",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h1_banned_tactics.py"
          }
        ]
      },
      {
        "matcher": "Edit|Write|MultiEdit",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h10_resume_needs_finalise.py"
          }
        ]
      },
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h14_git_destructive_consent.py"
          }
        ]
      },
      {
        "matcher": "Edit|Write|MultiEdit",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h17_then_suspend.py"
          }
        ]
      },
      {
        "matcher": "mcp__hol4__hol_send|Edit|Write|MultiEdit",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h18_ban_lookup_suspension.py"
          }
        ]
      }
    ],
    "PostToolUse": [
      {
        "matcher": "mcp__hol4__hol_check_proof",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h6_check_proof_failure.py"
          }
        ]
      },
      {
        "matcher": "mcp__hol4__hol_state_at",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h8_state_at_replay_cost.py"
          }
        ]
      },
      {
        "matcher": "mcp__hol4__holmake",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h7_holmake_advisory.py"
          }
        ]
      },
      {
        "matcher": "mcp__hol4__hol_state_at|mcp__hol4__hol_send|mcp__hol4__hol_check_proof",
        "hooks": [
          {
            "type": "command",
            "command": "/home/yongkiam/hol4-mcp/hooks/h16_bundled_suspend_goals.py"
          }
        ]
      }
    ]
  }
}
```

Replace `/home/yongkiam/hol4-mcp` if your clone lives elsewhere.

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
for f in ~/hol4-mcp/hooks/h*.py; do
  python3 -c "import ast; ast.parse(open('$f').read())" && echo "ok: $f"
done

# Confirm settings.json is valid JSON
python3 -c "import json; json.load(open('$HOME/.claude/settings.json'))" \
  && echo "settings.json ok"
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
- Hook should be fast (default timeout 10 min, but set explicit `timeout` in
  settings.json — H1 uses 5s).

## Per-session state

Hooks needing cross-call state (H5, H7, H8) will use
`~/.claude/hook-state/<session_id>/` keyed by the `session_id` field on the
hook input. Cleanup: weekly `find ~/.claude/hook-state -mtime +7 -delete`.

## See also

- `~/.claude/skills/hol4-proving/SKILL.md` — the HOL4 proof-interaction rules these hooks enforce.
- `~/.claude/CLAUDE.md` — generic behavioural rules (editing/git — H14's source — memory-writing, working principles).
- `~/research/cakes/CLAUDE.md` — CakeML workspace orientation.
- `~/hol4-mcp/LOCAL_CHANGES.md` — local divergences of the running MCP server.
