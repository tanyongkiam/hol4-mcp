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
| d3d290b | Route file-replay (`verify_all_proofs`) Resume processing through canonical `markerLib.resume` so sub-suspends emitted inside Resume bodies register as resumption deltas. Adds `run_resume_canonical_json` SML helper and four regression tests (nested-Resume fixture). Symptom fixed: "No such label" when navigating into deeper Resume bodies after a file-level check |
| abccf27 | Report cheat-dependency oracles for store=false checks (`⚠ depends on cheat` marker) |
| 582f8cc | hol_state_at: report opaque multi-line step failures as a line range with cheat-bisection advice |
| c3a7712 | Hooks H19/H20/H22; citations retargeted to the hol4-proving skill |
| 379e054 | Diagnostics: auto-cheated deps NAMED with reasons (`[auto-cheated deps: ...]` in state_at/check_proof; `_failed_proofs` is now name→reason); chain-entry landing NOTE when the target is strictly inside a multi-line opaque step; timeout step attribution with source line span + shrink-the-lump advice; lost-suspension ancestor diagnosis (`diagnose_resume_failure`: chain listing, known-broken marking, replay-to-first-failure) |
| cfe858e | Information tools: `hol_search` (DB.find/DB.match via new `db_search_json` SML helper); `hol_goals` (goal count/headlines/slices, replaces `top_goals()` dumps); smart-quote diagnosis on parse-flavoured error paths (`hol4_mcp/quote_check.py`, `check_quotes.py` is now a shim) |
| 79b575f | Guard rails: RULE J server-side (`hol_start` refuses a second concurrent session unless `force=True`; `hol_file_init` refuses workdir switches — explicit `hol_stop` first); `hol_send` rejects `val gs/fs/rw/... = ...` shadow bindings |
| 4ed8a2a | Resume loading: unknown-label Resume blocks (silent no-ops in HOL) are detected at load and recorded as SKIPPED in `_failed_proofs`; the planned `skip_broken_resumes` flag was found unnecessary (broken Resume bodies are already auto-cheated canonically and downstream content stays reachable — see tests/test_p4_resume_navigation.py); mid-arm parens navigation documented infeasible-within-timebox in PARENS_NAVIGATION_NOTES.md |
| _docs_ | Server instructions + tool docstrings for the new tools, output lines, and guards (the commit adding this row) |
| f55138f | Replay diagnostics: soften raised-exception failure markers (no confident pin); `>>~-` step decomposer navigable; auto-cheated-deps reporting no longer grabs goal fragments / lists the target; per-theorem budget 60→120s |
| 9361e8b | `skip_prefix` navigation: bind prefix theorems by `cheat` (statement only) for instant cold-theory navigation. Cursor (`_cheat_skip_theorem`, `_skip_prefix`/`_skipped_thms`, `state_at(skip_prefix=…)`) + `skip_prefix` param on `hol_state_at`/`hol_goals` + `[prefix-skip mode ON…]` notice; tests + fixture |
| 4b34d84 | Invalidate stale auto-cheat verdicts (`_failed_proofs`) on file edit — a fixed Resume body stops reporting its first-load failure. A *broken* suspend/Resume chain reinits the session on edit so a fixed dispatcher re-registers orphaned children (`No such label`) without a manual restart. Unit + end-to-end regression tests |
| ff69e70 | Bound `state_at`/`hol_goals` navigation with an overall wall-clock timeout (`_state_at_bounded`; default 240s, `HOL_STATE_AT_TIMEOUT` / `--state-at-timeout` / per-call `timeout=`) — the per-tactic budget × prefix length could otherwise sum to a multi-hour hang. On expiry it SIGINTs HOL (recoverable) + resyncs the cursor (`mark_interrupted`) and returns a `TIMEOUT` result. Unit tests |

## Notes files

- `LOCAL_CHANGES.md` — this file (tracked since 37e03a0).
- `HOL_STATE_AT_RESUME_BUG_NOTES.md` — investigation notes for the Resume
  goal-setup fix; historical reference.
- `PARENS_NAVIGATION_NOTES.md` — why mid-arm navigation inside
  parens-grouped LT chains stays off (b43c34c trade-off), and the one
  feasible single-goal path if it's ever needed.

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
