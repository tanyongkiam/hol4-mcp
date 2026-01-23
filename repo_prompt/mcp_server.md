# MCP Server Recovery Prompt

## File: `hol_mcp_server.py`

FastMCP server providing HOL4 interaction tools. In-memory session registry.

## Dependencies

- fastmcp >= 2.0.0
- hol_session.py (HOLSession class)
- hol_cursor.py (ProofCursor class)

## Session Registry

```python
_sessions: dict[str, SessionEntry]  # name -> entry

@dataclass
class SessionEntry:
    session: HOLSession
    started: datetime
    workdir: Path
    cursor: ProofCursor | None
    holmake_env: dict | None  # cached env vars
```

In-memory only. Sessions survive across Claude context clears (handoffs) but not server restarts.

## Tools

### Session Management

```python
@mcp.tool()
def hol_start(workdir: str, name: str = "default") -> str:
    """Start or reconnect HOL session. Idempotent.

    If session exists and running: return top_goals()
    If session exists but dead: restart it
    If new: create session, start HOL, return greeting
    """

@mcp.tool()
def hol_sessions() -> str:
    """List active sessions: name, workdir, age, status (running/dead)"""

@mcp.tool()
def hol_send(session: str, command: str, timeout: int = 5) -> str:
    """Send SML command, return output. Max timeout 600s.

    Handles timeout by calling interrupt().
    """

@mcp.tool()
def hol_interrupt(session: str) -> str:
    """Send SIGINT to abort runaway tactic."""

@mcp.tool()
def hol_stop(session: str) -> str:
    """SIGTERM + wait. Removes from registry."""

@mcp.tool()
def hol_restart(session: str) -> str:
    """Stop + start. Preserves workdir."""
```

### Build

```python
@mcp.tool()
def holmake(workdir: str, target: str = None, env: dict = None, timeout: int = 90) -> str:
    """Run Holmake --qof in workdir.

    Args:
        env: Optional environment variables (e.g. {"MY_VAR": "/path"})
    Max timeout 1800s.
    On failure: return output + contents of .hol/logs/*.log
    Caches env vars for reuse.
    """

@mcp.tool()
def hol_log(workdir: str, theory: str, limit: int = 1024) -> str:
    """Read build log for a specific theory.

    Use after holmake failure to inspect errors in detail.
    Returns tail if truncated.
    """

@mcp.tool()
def hol_logs(workdir: str) -> str:
    """List available build logs with sizes and modification times."""
```

### Cursor Tools (Recommended Entry Point)

```python
@mcp.tool()
def hol_cursor_init(file: str, session: str = "default", workdir: str = None, start_at: str = None) -> str:
    """Initialize cursor-based workflow.

    1. Auto-start session if needed
    2. Parse file for theorems/cheats
    3. Load HOL context up to first cheat (or start_at if specified)
    4. Enter goaltree for first cheat
    5. Return top_goals() output

    Args:
        start_at: Optional theorem name to jump to instead of first cheat
    """

@mcp.tool()
def hol_cursor_goto(session: str, theorem_name: str) -> str:
    """Jump to specific theorem by name and enter goaltree.

    Drops current proof state before jumping.
    Use to skip ahead or go back to a different cheat.
    """

@mcp.tool()
def hol_cursor_complete(session: str) -> str:
    """Extract proof, drop goal, advance cursor to next cheat.

    Call when proof is done (no goals remaining). Returns proof script.
    Agent must splice proof into file, then call hol_cursor_reenter
    to set up goaltree for the next theorem.
    """

@mcp.tool()
def hol_cursor_status(session: str) -> str:
    """Show progress: file, position, current theorem, remaining cheats."""

@mcp.tool()
def hol_cursor_reenter(session: str) -> str:
    """Clears all proof state (via drop_all) and enters goaltree for current theorem.

    Use after hol_cursor_complete to set up the next theorem, or to retry
    a proof from scratch after exploring dead-end tactics.
    """
```

## Key Behaviors

1. **Idempotent hol_start**: Calling repeatedly is safe, returns current state
2. **Session names are explicit**: Not derived from directory
3. **Cursor is optional**: Can use hol_send directly for manual control
4. **holmake caches env**: Avoids repeated PATH discovery
5. **Timeout handling**: Long-running tactics get interrupted, not hung

## Reconstruction Notes

- Use FastMCP's `@mcp.tool()` decorator pattern
- Session registry is a module-level dict
- HOL subprocess owned by HOLSession, not MCP server
- Cursor stored in SessionEntry, created on cursor_init
