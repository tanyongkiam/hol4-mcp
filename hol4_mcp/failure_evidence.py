"""Failure-only request/response evidence; no filesystem work on success."""
import json
from pathlib import Path
import tempfile


class FailureEvidence:
    def __init__(self):
        self.directory: Path | None = None
        self.sequence = 0
        self.latest: dict | None = None

    def record(self, command: str, response: str, kind: str, **metadata) -> None:
        self.sequence += 1
        entry = {"id": self.sequence, "kind": kind, **metadata}
        try:
            if self.directory is None:
                # Private, unpredictable directory; logs can contain project
                # source and are retained for diagnosis after session stop.
                self.directory = Path(tempfile.mkdtemp(prefix="hol4-mcp-evidence-"))
            path = self.directory / f"failure-{self.sequence}.json"
            with path.open("x", encoding="utf-8") as stream:
                json.dump({**entry, "command": command, "response": response},
                          stream, ensure_ascii=False)
            entry["path"] = str(path)
        except (OSError, ValueError, TypeError) as exc:
            # Diagnostics must never turn a failed log write into a different
            # proof result or hide the original exception.
            entry["log_error"] = str(exc)
        self.latest = entry
