# `localfixes` branch

Local-only operating branch — **never push to remote**. Default checkout
for this clone. Each commit is one logical change; see `git log` /
`git show <sha>` for details.

| Commit  | Summary                                                          |
|---------|------------------------------------------------------------------|
| 91255af | SML step-plan fixes: nested `>-` in `>~` select-arm + `reverse TAC` preservation (PR #21) |
| 9a6771d | Regression tests for the SML fixes above (PR #21)                |
| efb689d | Monkey-patch mcp SDK `RequestResponder.cancel` (1.25.0 disconnect bug) |
| 83e42e2 | Emit `[Cache: ...]` diagnostics from `hol_state_at`              |
| e134b5c | Relax `hol_send` guidance — encourage exploration                |
| 69ee385 | Remove unused `hol_file_status` MCP tool                         |
| 011c5b2 | Bump default per-tactic timeout 5s → 60s                         |
| 714b941 | Failing tests demonstrating the parens-around-LT distribution bug |
| b43c34c | Fix parens-around-LT distribution bug + warning for nested cases |
| 67b6e2e | Append iteration-discipline warning to every non-OK `hol_check_proof` output (names `hol_state_at` and `hol_send` as the iteration tools) |
| 44d8fc5 | Fix Resume goal-setup to pull terms directly from the suspension store (no `term_to_string` → `Parse.Term` round-trip); adds `set_resume_goalfrag_json` SML helper and two regression tests |
| _new_  | Route file-replay (`verify_all_proofs`) Resume processing through canonical `markerLib.resume` so sub-suspends emitted inside Resume bodies register as resumption deltas. Adds `run_resume_canonical_json` SML helper and four regression tests (nested-Resume fixture). Symptom fixed: "No such label" when navigating into deeper Resume bodies after a file-level check |

## Untracked

- `LOCAL_CHANGES.md` — this file.
- `check_quotes.py` — personal one-off Unicode-quote-fixing utility.
- `HOL_STATE_AT_RESUME_BUG_NOTES.md` — investigation notes for the Resume
  goal-setup fix; kept for historical reference, see commit for the actual
  change.

## Upstreaming notes

- `91255af` + `9a6771d` — opened as PR #21 to upstream
  `HOL-Theorem-Prover/hol4-mcp`.
- `efb689d` should be obsoleted once mcp PR #2481 or #2493 merges.
- `83e42e2` is upstreamable as observability.
- `e134b5c`, `69ee385` are workflow opinions — discuss before upstreaming.
- `011c5b2` is personal preference for cake-while; do not upstream.
- `714b941` + `b43c34c` — try out locally first; if stable through the
  cake-while cleanup tasks, open as a separate PR. Has a documented
  trade-off (lose mid-arm navigation in parens-grouped LT chains).
- `67b6e2e` is a workflow opinion — discuss before upstreaming.
- The Resume goal-setup fix is a correctness fix (avoids a `Parse.Term`
  re-parse that crashes / silently renames under a clashing parse context).
  Upstreamable — discuss before opening a PR.
