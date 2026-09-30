Suspected: concurrent MCP operations can still interleave a proof session.

`_state_at_bounded` holds a cursor navigation lock, but `hol_check_proof` enters
and verifies the theorem without it; `hol_send` also bypasses this lock.
`_init_file_cursor` can replace/restart a cursor before that lock is acquired.
The per-send lock protects one pipe command, not an entire proof operation.
Expected: each operation receives its own proof state and interruptions recover
cleanly. Existing concurrent navigation tests cover two warm state_at calls;
add deterministic mixed-operation and cold-init regressions before changing
locking. No mixed-operation reproducer has been run yet.
