# Bug: editing a `Definition` above the checkpoint leaves the session stale; forward replay then wedges with "Unknown identifier"

Status: **OPEN — to reproduce and fix.**

Two coupled defects observed in one session, both triggered by editing a
`Definition` (not a theorem) that sits *before* the cursor's current
position:

- **Defect A (silent staleness — the dangerous one):** after the edit,
  `hol_state_at` at a position *after* the Definition reports
  `file=changed` and returns a goal in ~140ms — but never re-executes the
  edited Definition. The in-heap constant stays the OLD version, and the
  file-change is *consumed* (the next call reports `file=unchanged`), so
  the session is permanently stale with no further signal. All `hol_send`
  probes (`EVAL`, fetching `<def>_def`) silently use the stale constant.
- **Defect B (wedged forward replay):** after navigating *backwards* to a
  position before the edited Definition (which succeeds), navigating
  forward again fails deterministically with
  `Error executing file content: Unknown identifier: mk_name` — where
  `mk_name` is a HOL **term-level constant** from an `Ancestors` theory
  (`cp_to_ilp`), bound and parseable in the live top-level at that very
  moment (verified via `hol_send`). The segment execution context is
  missing the file prelude's term grammar. The error reproduces on retry;
  the region is unreachable until session restart.

## Confirmed observation (cake-cp branch `cp_enc_new`, 2026-07-04)

Workdir: `~/research/cakes/cake-cp/examples/pseudo_bool/cp_encoding`.
File: `cp_to_ilp_primScript.sml`. Ancestors:
`pbc pbc_encode cp ilp cp_to_ilp int_bitwise int_bitwiseExtra`.
Layout at the time: a block of 9 new `Definition`s at lines ~529–653
(`mult_width` … `encode_mult`; the edited one is
`cencode_mult_body_def`, lines ~584–645), followed by
`Theorem encode_prim_constr_sem_1` (`Proof` at 682, first tactic 683).
`Theorem encode_max_sem_2` ends just above the block (~523).

Exact sequence (verbatim tool diagnostics):

1. Cold init: `hol_state_at(line=683)` — OK, goal shown.
   `[Timing: total=20942ms, replay=42ms, method=replay]`
   `[Cache: pos_before=(idx=0,uninit,hash=miss), target=(idx=0,partial), file=unchanged, replayed=0/3]`
2. `hol_send` EVALs of `cencode_mult` — OK, current definitions visible.
3. **Edit**: 3 lines changed inside `Definition cencode_mult_body_def`
   (lines 623–625; pure string-literal change — renamed 4 label tags).
4. `hol_state_at(line=683)` — OK, goal shown, **stale heap**:
   `[Timing: total=139ms, replay=47ms, method=replay]`
   `[Cache: pos_before=(idx=0,init,hash=match), target=(idx=0,partial), file=changed, replayed=0/3]`
   The Definition was NOT re-executed (139ms total; a re-execution of the
   prefix takes ~21s). Subsequent `EVAL` of the encoder still emits the
   OLD tags; `hol_send cencode_mult_body_def` shows the OLD rhs.
5. `hol_state_at(line=521)` (inside `encode_max_sem_2`, i.e. *before*
   the Definition block) — OK:
   `[Timing: total=239ms, replay=170ms]`
   `[Cache: pos_before=(idx=0,init,hash=match), target=(idx=1,partial), file=unchanged, replayed=1/3]`
   Note `file=unchanged`: step 4 absorbed the change into the stored
   snapshot without ever executing it.
6. `hol_state_at(line=683)` —
   `ERROR: Error executing file content: Unknown identifier: mk_name`.
   Retried: identical. Live top-level at the same moment: `hol_send
   "mk_name_def; cencode_mult_body_def;"` returns both (the latter stale),
   so the identifier IS available to the session's own parser — only the
   segment-replay context lacks it.

## Why it matters

- Defect A breaks the navigate-in-accurate-state guarantee *from the tool
  side*: the goal/probe state shown is computed against a constant that no
  longer matches the file, with `file=changed` reported once and then
  never again. Tactics and EVAL-based checks developed against it are
  validated against the wrong definition. (In this instance the edit was
  labels-only, so nothing semantic was miscarried — but only by luck.)
- Defect B makes the file region unreachable; recovery needs a session
  restart, which is deliberately friction-ful (H19 consent gate).

## Root-cause hypotheses (NOT yet verified — investigate in this order)

1. **Change-invalidation may skip or mishandle `Definition` items.**
   `hol_cursor.py:1005–1012` invalidates checkpoints for `self._theorems`
   with `proof_end_line >= start_line`. Check whether (a) Definition items
   carry correct `proof_end_line`s here, and (b) invalidation of the
   *downstream theorem's* checkpoint actually forces re-execution of the
   *gap content* (the Definitions) between the previous checkpoint and the
   target — the 139ms replay in step 4 suggests the target theorem was
   served from a still-live in-memory position (`pos_before idx=0,
   hash=match` computed against the pre-edit snapshot) rather than
   re-loaded.
2. **The file snapshot is updated even when nothing re-executed.** Step 5
   reporting `file=unchanged` right after step 4's `file=changed` shows
   the change was consumed unconditionally. If (1) decided "nothing to
   redo", the consume must not happen — otherwise the stale heap becomes
   undetectable.
3. **Segment execution context after a backward jump.** The
   `Unknown identifier` is raised by the HOL *term parser* inside
   re-executed file content (`_send_and_check`, `hol_cursor.py:1326`;
   message formatted at `:253`). The live top-level parses `mk_name`
   fine, so the forward segment was executed against a *different* state
   — most plausibly a restored PolyML SaveState checkpoint
   (`PolyML.SaveState.loadState`, `hol_cursor.py:736/:870/:934`) whose
   heap predates the file's `Ancestors` prelude execution.
4. **Cross-session stale on-disk checkpoint.** The workdir contains
   `cp_to_ilp_prim.encode_prim_constr_sem_1.dumpedheap` dated
   **2026-07-03 23:51** — from the *previous day's session*, before the
   Definition block existed and before the `Ancestors` line gained three
   theories. Today's cold init (step 1) did NOT refresh that file's
   mtime. If the backward/forward navigation (steps 5–6) restored this
   stale heap keyed by theorem name, that directly explains the missing
   grammar in step 6. Check how on-disk checkpoints are keyed/validated
   (content hash? session id?) and whether a leftover heap from an older
   file version can be adopted.

## Minimal repro to construct

Fixture `defEditScript.sml` (or reuse an existing fixture pair):

```
Theory defEdit  Ancestors <something exporting a constant used below>
Theorem t1: ... Proof ... QED            (* checkpoint anchor before *)
Definition d_def: d = «AAA» End          (* the Definition to edit *)
Theorem t2: ... Proof <tactics> QED      (* navigation target after *)
```

1. `hol_state_at` into `t2` (cold init).
2. Edit the string literal in `d_def` (`«AAA»` → `«BBB»`).
3. `hol_state_at` into `t2` again — assert the session's `d_def` rhs now
   shows `BBB` (Defect A: it shows `AAA`; diagnostics say `file=changed`,
   `replayed=0/…`, and a third call says `file=unchanged`).
4. `hol_state_at` into `t1`, then into `t2` — assert no
   `Error executing file content` (Defect B).
5. Cross-session variant for hypothesis 4: leave the on-disk
   `*.dumpedheap` from a run, change the file's `Ancestors`/Definitions,
   start a fresh session, repeat 1–4.

## Workaround (until fixed)

- After editing any `Definition` mid-session, do NOT trust `hol_send`
  probes or shown goals until the session demonstrably re-executed it:
  `hol_send "<def>_def"` and check the rhs matches the file. If stale,
  restart the session (`hol_stop` + fresh `hol_state_at`; H19 consent).
- Prefer completing Definition edits BEFORE the session's first navigation
  past them.

## References

- `hol4_mcp/hol_cursor.py:1005–1012` — change-point checkpoint invalidation loop.
- `hol4_mcp/hol_cursor.py:2196–2207` — `pos_hash_match` / `file_changed` diagnostics snapshot.
- `hol4_mcp/hol_cursor.py:1326` (`_send_and_check`) + `:253` — source of
  `Error executing file content: Unknown identifier: …`.
- `hol4_mcp/hol_cursor.py:663–740, 796–934` — PolyML SaveState checkpoint
  save/load (`saveChild`/`loadState`), on-disk `*.dumpedheap` naming.
- Concrete case: `~/research/cakes/cake-cp/examples/pseudo_bool/cp_encoding/cp_to_ilp_primScript.sml`
  (branch `cp_enc_new`, 2026-07-04), Definition `cencode_mult_body_def`
  lines ~584–645, targets `encode_prim_constr_sem_1:683` /
  `encode_max_sem_2:521`; stale heap
  `cp_to_ilp_prim.encode_prim_constr_sem_1.dumpedheap` (mtime 2026-07-03 23:51).
