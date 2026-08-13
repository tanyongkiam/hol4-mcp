---
name: reference_hol4_mcp
description: The running hol4-mcp server — install location and the local-only `localfixes` branch (don't upstream). The copy under research/cakes is a dev repo, not the running version.
metadata:
  type: reference
---

# Install location
Running server: `/home/yongkiam/hol4-mcp/`, installed EDITABLE into the linuxbrew python behind the `/home/linuxbrew/.linuxbrew/bin/hol4-mcp` entry point — so an edit in that tree is live for the running server, no reinstall step. The copy at `/home/yongkiam/research/cakes/hol4-mcp/` is a dev repo, NOT the running version. Dev/test commands: `~/hol4-mcp/CLAUDE.md`.

# `localfixes` branch — local-only, don't upstream
`~/hol4-mcp` runs the `localfixes` branch, carrying user-curated commits intentionally NOT in `origin/master` (navigation/timeout fixes, diagnostics, guidance text, SDK monkey-patch). Don't propose cherry-picking them or opening a PR unless the user explicitly asks. When behaviour depends on a local-only commit, rely on `~/hol4-mcp` being live — that (not GitHub) is the source of truth for the running MCP.
