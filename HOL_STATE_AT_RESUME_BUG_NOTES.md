# Bug: `hol_state_at` at a Resume position re-parses the goal lossily

Status: **RESOLVED**. See `hol4_mcp/hol_cursor.py:_setup_proof_goal` (Resume
branch) and `hol4_mcp/sml_helpers/tactic_prefix.sml:set_resume_goalfrag_json`.
Regression tests in `tests/test_verification.py`:
- `test_resume_goal_matches_marker_canonical` — strong invariant: the cursor's
  Resume goal matches `markerLib.set_suspended_goal` byte-for-byte under
  `term_to_string`.
- `test_resume_state_at_with_free_var_constant_clash` — concrete demonstration
  of the bug class: a free variable in the suspended goal whose name clashes
  with a constant of *different type* in the parse context. Under the old
  path this crashes with `Type constraint failure`; under the new path it
  succeeds.

The root cause described below remains valid. Bound-variable renaming was the
originally observed symptom; the broader bug class is "any term that doesn't
round-trip cleanly through term_to_string + Parse.Term will misbehave when
the cursor sets up the Resume goal." Renaming is the silent case; a type-
clash crash is the loud case.

## Symptom

For a `Resume thm[Label]:` block in a `*Script.sml` file, the goal shown by `hol_state_at` at the Resume's entry line uses **different bound-variable names** than the goal `markerLib.set_suspended_goal` produces from the same suspension. Both views are semantically (alpha) equivalent, but tactics in the Resume body are name-sensitive at the source level (e.g. `Cases_on \`v\`` vs `Cases_on \`v'\``), so the divergence silently breaks tactic development driven by `hol_state_at`.

The view that `set_suspended_goal` produces is the canonical one — it matches what Holmake actually runs the Resume body against.

## Confirmed observation (cake-while branch `loop-multiret`)

Workspace: `~/research/cakes/cake-while`. File: `pancake/proofs/crep_to_loopProofScript.sml`. Theorem: `ncompile_correct`. Suspension label: `Dec` (Resume header at line 2089).

In a single fresh HOL session (with `proofManagerLib.drop()` before each, so no contamination):

- `hol_state_at(line=2090, col=3)` returns the goal headed with `∀v' e prog s. ... evaluate (Dec v' e prog, s) ...`. Bound var is **primed `v'`**.
- `markerLib.set_suspended_goal {suspension_name = "ncompile_correct", label_name = "Dec"}; proofManagerLib.p ()` returns the goal headed with `∀v e prog s. ... evaluate (Dec v e prog, s) ...`. Bound var is **unprimed `v`**.

Holmake processes the Resume body against the unprimed view (since Holmake uses the suspension store). Therefore `set_suspended_goal`'s view is canonical; `hol_state_at`'s view is the outlier.

## Root cause

The divergence comes from a **string round-trip** in `hol_state_at`'s Resume setup path.

### Canonical (correct) path — `set_suspended_goal`

`markerLib.set_suspended_goal` (HOL4 `src/marker/markerLib.sml` near line 1269) does:

```sml
fun prim_set_suspended_goal tacmod {suspension_name, label_name} =
  case find_parent suspension_name of
    SOME (_, parent_thy, th) =>
      let val sths = lookup_resumption {parent_thy, parent_name=suspension_name, label=label_name}
      in
        proofManagerLib.new_goalstack
          (resumption_to_goal (extract_suspended_goal (th::sths) label_name))
          tacmod I
      end
```

It hands `proofManagerLib.new_goalstack` **terms** straight from the suspension store. No serialization, no renaming.

### hol_state_at path

For `Resume` blocks, `hol_state_at` ultimately calls `Cursor._setup_proof_goal` (`hol4-mcp/hol4_mcp/hol_cursor.py:1435`). That function does (lines 1454–1470):

```python
if thm.kind == "Resume":
    if thm.name not in self._resume_goals:
        return f"Failed to extract Resume goal for '{thm.name}'"
    rg = self._resume_goals[thm.name]
    asms = rg.get('asms', [])
    goal_str = rg.get('goal', '')
    if asms:
        asm_terms = ", ".join(
            f'Parse.Term [QUOTE "{escape_sml_string(a)}"]' for a in asms
        )
        gt_result = await self.session.send(
            f'proofManagerLib.set_goalfrag([{asm_terms}], '
            f'Parse.Term [QUOTE "{escape_sml_string(goal_str)}"]);',
            timeout=30
        )
    else:
        gt_result = await self.session.send(f'gf `{goal_str}`;', timeout=30)
```

The Resume goal is fetched as **strings** (the keys `'asms'` and `'goal'` in `_resume_goals`) and re-parsed via `Parse.Term [QUOTE ...]`. The strings were captured earlier via `_extract_resume_goal` (`hol_cursor.py:1026`), which calls the SML helper `extract_resume_goal_json` (`hol4-mcp/hol4_mcp/sml_helpers/tactic_prefix.sml:721`):

```sml
fun extract_resume_goal_json suspension_name label_name =
  let
    val (asms, concl) = resume_goal_terms suspension_name label_name
    fun typed_term_to_string t =
      Lib.with_flag (Globals.show_types, true) term_to_string t
    val json = "{\"asms\":" ^ json_string_array (map typed_term_to_string asms) ^
               ",\"goal\":" ^ json_string (typed_term_to_string concl) ^ "}"
  in
    print (json_ok json ^ "\n")
  end
```

So the term → string → term round-trip is `term_to_string` (HOL4 pretty-printer) on extraction, then `Parse.Term [QUOTE …]` (HOL4 parser) on entry.

### Why the round-trip renames

The HOL4 pretty-printer and parser are **not bound-variable-name preserving across a clashing context**:

- `term_to_string` (with `show_types=true`) prints terms with names chosen to disambiguate from anything in the current pretty-print scope, but the name preservation across a parse round-trip depends on the parse context being identical. It isn't.
- `Parse.Term [QUOTE "∀v. P v"]` parses fresh each time; the resulting bound variable name is whatever the parser picks given its current scope. If the current Parse context (which depends on session state — loaded theories, `add_user_printer` calls, in-scope free vars) already contains a free `v` of some type, the parser typically primes the bound var to `v'`. The semantics survive (alpha-equivalence); the print name drifts.

In our concrete case, by the time `hol_state_at` reaches the Resume[Dec] body, the session has loaded `crep_to_loopTheory`, `crepSemTheory`, etc., each of which contributes constants and overloads. Some of those contributions cause the parser to prime `v`. `set_suspended_goal` avoids the issue because it skips the parser entirely.

This is **not** a HOL4 kernel bug. It is an inevitable consequence of going through string-form Term parsing in a context where bound names can collide.

## Why it matters

- Resume bodies are name-sensitive at the source level. `Cases_on \`v\``, `qpat_x_assum \`FLOOKUP s.locals v = _\``, `last_x_assum (qspecl_then [\`ctxt with vars := ctxt.vars |+ (v, tmp); ...\`])` all parse `v` as an in-scope free variable. If the goal HOL gives the user has bound `v'` and **the parser sees no free `v` in scope at that point** (it's been bound), `Cases_on \`v\`` either silently does nothing or errors.
- Tactic chains developed against the `hol_state_at` view (primed) get persisted into the script. Holmake then runs them against the suspension-store view (unprimed). The two views differ → discharge fails.
- Cost on this branch: ~1 hour of confusion in a single session, plus a discarded set of `v → v'` renames across two large Resume bodies that had to be reverted.

## Fix sketch

Replace the string round-trip in `_setup_proof_goal`'s Resume branch with a direct `markerLib.set_suspended_goal` call. The fix is local to `hol4-mcp/hol4_mcp/hol_cursor.py:1454`.

### Proposed change (sketch — verify before committing)

```python
if thm.kind == "Resume":
    if not thm.suspension_name or thm.label_name is None:
        return f"Resume '{thm.name}' has no suspension info"
    susp = escape_sml_string(thm.suspension_name)
    label = escape_sml_string(thm.label_name)
    gt_result = await self.session.send(
        f'markerLib.set_suspended_goal '
        f'{{suspension_name = "{susp}", label_name = "{label}"}};',
        timeout=30
    )
```

Effects:
- Eliminates the term → string → term round-trip for the goal at Resume entry.
- The goal HOL exposes to subsequent `expandf` / `e()` / `hol_state_at`-driven replay is the canonical suspension-store goal. Matches what Holmake's Resume processing sees.
- `self._resume_goals` cache (used elsewhere — for invalidation tracking and the `Failed to extract Resume goal` error message) is unaffected. Keep `_extract_resume_goal` for that purpose; just don't re-parse from its strings when setting up the proof manager.

### What to NOT change

- `extract_resume_goal_json` SML helper: still useful for callers that genuinely want a JSON snapshot (e.g. `hol_check_proof`'s pre-flight, displaying goals in error messages). Leave its current term-to-string behavior alone; just stop using it to drive `proofManagerLib.set_goalfrag` for Resume entry.
- `verify_resume_json` SML helper: already does the right thing (it calls `resume_goal_terms` and feeds the result directly to `proofManagerLib.set_goalfrag` as **terms**). Don't touch.

### Open question

Does any other call site rely on `_resume_goals[name]['goal']` being a faithful term string? Likely fine — the existing extraction is already alpha-equivalent — but grep first:

```bash
grep -n '_resume_goals\b' hol4-mcp/hol4_mcp/*.py
```

## Validation plan

1. Build the minimal repro (see next section). Confirm BEFORE the fix that `hol_state_at` and `set_suspended_goal` diverge on it.
2. Apply the fix in `hol_cursor.py`.
3. Re-run the same repro. Confirm `hol_state_at` now shows the same bound-name view as `set_suspended_goal`.
4. Re-run the existing hol4-mcp test suite (`pytest tests/test_verification.py` and friends) — expect no regressions. The Resume-block tests there use `split_conj` (simple, no rename trigger), so they should keep passing.
5. Run the cake-while `loop-multiret` regression spot: `hol_state_at` at `pancake/proofs/crep_to_loopProofScript.sml:2090` should now return the same `∀v e prog s. …` view that `set_suspended_goal "ncompile_correct" "Dec"` returns.

## Minimal repro to construct

The existing `hol4-mcp/tests/fixtures/suspendScript.sml` (`split_conj`, `simple_suspend`) does NOT trigger the rename — neither has a parse-context clash for the bound names `p`, `q`. Construct a new fixture (e.g. `suspendRenameScript.sml`) that:

1. Loads some theory that introduces a free `v` or a constant `v` in the parse context (e.g. open `arithmeticTheory` and define `Definition v_def: v = (0:num) End`; then a `Theorem foo:` whose suspended goal binds a fresh `v`).
2. Has a `Theorem foo: ∀v. P v Proof strip_tac >- suspend "case1" QED` (or similar; the key is that the suspension store stores the term with bound `v`, and a subsequent parse of `term_to_string`-form of that term must rename to `v'`).
3. Provides a `Resume foo[case1]: ...` whose body uses `Cases_on \`v\``.
4. The test asserts `hol_state_at` at the Resume entry shows the same bound name as `markerLib.set_suspended_goal`. Before the fix, this assertion fails (primed vs unprimed); after the fix, it passes.

Crafting the exact clash that makes the parser prime can take some trial. An easier path: skip building a synthetic minimal and use the cake-while repro directly as a regression spot for now. The cake-while case is reproducible and reliable.

## Files to touch (after compact)

- `hol4-mcp/hol4_mcp/hol_cursor.py:1454` — main fix.
- `hol4-mcp/tests/fixtures/suspendRenameScript.sml` — new test fixture (optional but recommended).
- `hol4-mcp/tests/test_verification.py` — new test asserting hol_state_at agrees with set_suspended_goal on the rename fixture.

## References

- `hol4-mcp/hol4_mcp/hol_cursor.py:1026` — `_extract_resume_goal` (captures strings).
- `hol4-mcp/hol4_mcp/hol_cursor.py:1435` — `_setup_proof_goal` (re-parses strings).
- `hol4-mcp/hol4_mcp/sml_helpers/tactic_prefix.sml:706` — `resume_goal_terms` (returns canonical terms).
- `hol4-mcp/hol4_mcp/sml_helpers/tactic_prefix.sml:721` — `extract_resume_goal_json` (does the term-to-string serialization).
- HOL4 source: `src/marker/markerLib.sml` — `prim_set_suspended_goal`, `lookup_suspension`, `extract_suspended_goal`, `resumption_to_goal` (around lines 1098–1284 in the version used by cake-while; verify against your HOL4 checkout).
- Concrete cake-while case: `~/research/cakes/cake-while/pancake/proofs/crep_to_loopProofScript.sml:2089–2090` (Resume header) under branch `loop-multiret`. Theorem name `ncompile_correct`, label `Dec`.
