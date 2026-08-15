---
name: reference_hol4_mcp
description: The running hol4-mcp server — install location (editable, so edits are live) and the local-only `localfixes` branch (don't upstream).
metadata:
  type: reference
---

# Install location
`~/hol4-mcp` is the running server's source tree, installed EDITABLE — an edit there is live for the running server, no reinstall step. How it is launched (interpreter, entry point, launcher config) is machine-specific: don't record it here, read the MCP config if you ever need it. Dev/test commands: `~/hol4-mcp/CLAUDE.md`.

# `localfixes` branch — don't upstream
`~/hol4-mcp` runs the `localfixes` branch, carrying user-curated commits intentionally NOT in `origin/master` (navigation/timeout fixes, diagnostics, guidance text, SDK monkey-patch). It is pushed to `origin/localfixes` as a backup; that is not a step towards merging. Don't propose cherry-picking them or opening a PR unless the user explicitly asks. When behaviour depends on a local-only commit, rely on `~/hol4-mcp` being live — that (not GitHub) is the source of truth for the running MCP.
