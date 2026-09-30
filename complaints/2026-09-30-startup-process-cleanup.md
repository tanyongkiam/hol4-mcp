Suspected: failed or cancelled HOL startup leaves an unregistered process.

`HOLSession.start` spawns before awaiting the initial prompt and loading helpers.
Neither it nor `hol_start` cleans up a spawned process if those awaits fail;
`__aenter__` failure also skips `__aexit__`. Expected: terminate/reap the process
and propagate the original failure, with no orphan or stale session entry.
Source inspection only so far; add timeout/cancellation regression tests and
a successful-retry control before fixing.
