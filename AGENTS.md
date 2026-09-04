# Development Notes for Codex

The package is installed editable into the Python environment that provides the
`hol4-mcp` executable, so source edits affect the running server without a
reinstall. Locate that interpreter rather than assuming a virtualenv path.

Run the suite with:

```bash
$PY -m pytest tests/ -q
```

The project requires FastMCP 3.x. Decorated tool functions remain directly
callable in tests; do not unwrap them through `.fn`.

The existing `hooks/h*.py` scripts and `hooks/install_hooks.py` are the Claude
Code integration. Keep their registration and `~/.claude` state contract
unchanged. Codex-specific translation and state isolation live under
`integrations/codex/`; its bundled wiring is `hooks/hooks.json`.

Before changing the HOL4 skill, hook policy, or MCP server guidance, read
`skills/hol4-proving/notes/reference_hol4_docs.md`. Before changing this local
server, also read `skills/hol4-proving/notes/reference_hol4_mcp.md` and preserve
the local-only branch policy documented there.
