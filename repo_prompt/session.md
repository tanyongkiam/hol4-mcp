# HOL Session Recovery Prompt

## File: `hol_session.py`

Manages HOL4 subprocess with null-byte framing.

## HOLSession Class

```python
class HOLSession:
    workdir: Path
    process: subprocess.Popen | None
    pgid: int  # Process group ID for interrupt

    def __init__(self, workdir: Path):
        """Store workdir, don't start yet."""

    def start(self) -> str:
        """Spawn HOL subprocess.

        Command: hol --zero
        - --zero enables null-byte framing (commands/responses delimited by \0)
        - start_new_session=True for process group isolation
        - stdin/stdout as PIPE, stderr merged

        After spawn:
        1. Read initial greeting (until \0)
        2. Load etq.sml (tactic extraction helpers)
        3. Load .hol_init.sml if exists in workdir
        4. Return greeting
        """

    def send(self, command: str, timeout: float = 5.0) -> str:
        """Send SML command, return output.

        Protocol:
        1. Write command + \0 to stdin
        2. Read until \0 from stdout
        3. Return response (stripped)

        Timeout handling:
        - Use select() or threading for non-blocking read
        - On timeout: call interrupt(), return partial + timeout message
        """

    def interrupt(self) -> None:
        """Send SIGINT to process group.

        os.killpg(self.pgid, signal.SIGINT)
        """

    def stop(self) -> None:
        """Terminate session.

        1. Send SIGTERM to process group
        2. Wait for process exit
        3. Clean up file handles
        """

    @property
    def is_running(self) -> bool:
        """Check if process is alive: process.poll() is None"""
```

## Null-Byte Framing

HOL4's `--zero` mode uses `\0` as message delimiter:
- Send: `command\0`
- Receive: read until `\0` encountered

This is more reliable than line-based parsing for multi-line outputs.

## Helper Scripts

### etq.sml (Tactic Extraction)

Loaded at session start. Provides:
- `etq "tactic"` - Apply tactic in goaltree mode, record for extraction
- Enhanced `p()` - Print proof tree in format suitable for file splicing

Located in: `hol4_mcp/sml_helpers/etq.sml`

### .hol_init.sml

Optional per-project initialization. Loaded if exists in workdir.
Typically: `open` statements for project theories.

## Process Group Isolation

```python
process = subprocess.Popen(
    ["hol", "--zero"],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.STDOUT,
    cwd=str(workdir),
    start_new_session=True,  # Creates new process group
)
pgid = os.getpgid(process.pid)
```

This allows `os.killpg(pgid, SIGINT)` to interrupt HOL without affecting the Python process.

## Reconstruction Notes

- The key insight is null-byte framing with `--zero` flag
- Process group isolation is critical for interrupt handling
- etq.sml must be loaded for goaltree mode to work properly
- Goaltree has no rotate() - always works on leftmost goal. Use REVERSE tac or >- to control order.
- Timeout uses interrupt, not kill - allows HOL to recover
