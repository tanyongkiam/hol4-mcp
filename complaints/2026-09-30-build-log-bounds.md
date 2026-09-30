Suspected: bounded build-log tools still read whole files into memory.

`hol_build_status(tail=2000)` calls `entry.log.read_bytes()` before slicing;
`hol_log(limit=1024)` and failed-build excerpts call `read_text()` before
truncating. A large translator/build log can therefore consume much more
memory than the requested excerpt. `hol_log` also counts characters while its
documented limit is bytes, unlike build status.

Expected: positive limits read only the needed tail, preserve diagnostic text,
and avoid whole-file allocation. Explicit unlimited requests may read all.
Static evidence is in `hol4_mcp/hol_mcp_server.py`; resource-bound regressions
and Unicode boundary cases still need to be added before repairing this.
