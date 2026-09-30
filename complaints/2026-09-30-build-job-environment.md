Suspected: per-build job configuration does not honor the supplied environment.

`holmake(env={"HOL4_MCP_HOLMAKE_JOBS": "3"}, jobs=None)` computes parallelism
from `os.environ` before merging the supplied build environment. The child
receives the variable, but Holmake's `-j` is determined without it. Confirm
with a regression that observes actual worker concurrency or command options.
Expected precedence: explicit `jobs`, supplied environment, inherited setting,
then the documented default. A malformed inherited value also raises an
uncaught `ValueError` instead of an actionable configuration error.

These are source observations; before/after runtime tests remain outstanding.
