# Development Notes

## Environment

Installed editable into the environment the `hol4-mcp` entry point runs on, so
an edit here is live for the running server — no reinstall step. That
environment is machine-specific; locate it rather than assuming a path (the
interpreter that can `import hol4_mcp`).

```bash
$PY -m pip install -e .
```

## Running tests

```bash
$PY -m pytest tests/ -q
```

Requires `pytest`, `pytest-asyncio` and `pytest-xdist` (for the `-n` in the
`pyproject` addopts) in that same environment.

## FastMCP

This project requires FastMCP >= 3.0. In 3.x, `@mcp.tool()` returns the
original function unchanged (no `.fn` unwrapping), so tool functions stay
directly callable in tests. Do not use `.fn` on tools.

## Hooks

`hooks/` holds the Claude Code hook suite and the HOL4 proof-interaction
skill it enforces (`skills/hol4-proving/`). Both are globally reachable, not
project-local — see `hooks/README.md` and
`skills/hol4-proving/notes/reference_hol4_docs.md` before editing either.
