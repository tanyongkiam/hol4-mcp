# Suspected target-independent MCP dependency discovery failure

Tool: holmake(workdir="cakeml/unverified/sexpr-bootstrap/x64/64", target="x64SexprTheory.dat", detach=True, jobs=1, heap_size=4096).
Expected: build named export and dependencies. Observed: preflight fails with `Holmake: Don’t star non-local script files`; no build starts. Same with target cake-sexpr-x64-64.
Server _build_claim runs `Holmake --json --dirs .` without target. Direct `Holmake --no_preexecs --no_action x64SexprTheory.dat` instead reaches graph scanning, then sandbox blocks writes of generated caches in the installed HOL tree. Direct build outcome still untested. No server repairs attempted.
The initial sandboxed write to the complaint inbox failed with OSError errno 30. A later escalated write saved this report to the designated inbox successfully.

A direct named-target dry run with sandbox escalation succeeds (exit 0); unlike MCP preflight it does not report a non-local starred script. Proceeding with direct named-target build as a task-scoped fallback.

The direct named-target build has successfully completed many theory files. The normal project scan consumes roughly 1.6 GiB in Holmake itself and scans outside the CakeML clone. A temporary restricted include closure with --no-project scans 99 directories and reduces the coordinator to roughly 130 MiB. Two workers now continue x64SexprTheory.dat; no upstream source changes or tool repairs were made.

The restricted --no-project build later failed when a generated theory loader omitted cross-directory ancestors: arm7_targetTheory.uo omitted asmPropsTheory even though the include directory was present. This is a limitation of the temporary nonstandard include strategy, not an upstream proof failure. Nine affected generated loaders were backed up under /tmp and removed for regeneration; all verified .dat theory data were retained. The export has resumed under the standard project configuration with two workers. No HOL source files were edited.
