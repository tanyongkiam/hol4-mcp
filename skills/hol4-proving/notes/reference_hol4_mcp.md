---
name: reference_hol4_mcp
description: The running hol4-mcp server — install location, the local-only `localfixes` branch (don't upstream), and the pytest env mismatch. The copy under research/cakes is a dev repo, not the running version.
metadata:
  type: reference
---

# Install location
Running server: `/home/yongkiam/hol4-mcp/` (pip-installed; entry point `/home/linuxbrew/.linuxbrew/bin/hol4-mcp`). The copy at `/home/yongkiam/research/cakes/hol4-mcp/` is a dev repo, NOT the running version.

# `localfixes` branch — local-only, don't upstream
`~/hol4-mcp` runs the `localfixes` branch, carrying user-curated commits intentionally NOT in `origin/master` (navigation/timeout fixes, diagnostics, guidance text, SDK monkey-patch). Don't propose cherry-picking them or opening a PR unless the user explicitly asks. When behaviour depends on a local-only commit, rely on `~/hol4-mcp` being live — that (not GitHub) is the source of truth for the running MCP.

# ⚠ pytest env FastMCP ≠ runtime FastMCP
The pytest env has a newer `fastmcp` where `@mcp.tool()` returns a non-callable `FunctionTool` wrapper, so all tool-layer integration tests fail with `'FunctionTool' object is not callable` even though the RUNNING MCP works — env mismatch, NOT a code bug. To validate MCP changes under pytest, drive `FileProofCursor`/`HOLSession` directly or call pure module-level helpers (both bypass the tool layer). Real fix: pin fastmcp or keep the decorator name bound to the raw function.
