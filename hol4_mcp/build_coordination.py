"""Coordinate MCP build dependency directories across server lifetimes.

Holmake locks competing writers, but can skip an existing partial dependency.
Read/read overlap is safe; a write/read or write/write overlap is refused.
Locks cover cooperating servers on the same host/user; undeclared outputs and
plain external Holmake processes remain outside this protocol.
"""

from dataclasses import dataclass, field
import fcntl
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import uuid


def _stamp(path):
    try:
        stat = path.stat()
        return stat.st_mtime_ns, stat.st_ctime_ns, stat.st_size, stat.st_ino
    except FileNotFoundError:
        return None


def _artifact_paths(path):
    """Graph names are logical; Poly/ML HOL stores generated files in objs.

    Keep both layouts for older HOL versions and ordinary shell recipes.
    sigobj files already have their physical names.
    """
    yield path.resolve()
    generated = path.suffix in {".uo", ".ui"} or (
        path.stem.endswith("Theory") and len(path.stem) > len("Theory")
        and path.suffix in {".sml", ".sig", ".dat"})
    already_physical = path.parent.name == "objs" and path.parent.parent.name == ".hol"
    if generated and path.parent.name != "sigobj" and not already_physical:
        yield (path.parent / ".hol" / "objs" / path.name).resolve()


@dataclass
class BuildClaim:
    workdir: Path
    reads: set[Path]
    outputs: set[Path]
    token: str = field(default_factory=lambda: uuid.uuid4().hex[:12])
    proc: object = None
    detached: bool = False
    before: dict = field(default_factory=dict)
    preflight_output: str = ""
    lock_fds: list[int] = field(default_factory=list)
    state_error: str = ""
    clean: bool = False

    @property
    def label(self):
        return f"{'job' if self.detached else 'build'}={self.token} workdir={self.workdir}"

    def release_locks(self):
        # Closing our copy preserves flock protection in an orphaned Holmake
        # process that inherited the same open file description via pass_fds.
        for fd in self.lock_fds:
            os.close(fd)
        self.lock_fds.clear()


def claim_from_graph(output: str, workdir: Path, target: str | None) -> BuildClaim:
    # Pre-exec commands may print before the graph. JSON itself starts in
    # column zero; dependency lists inside it never do.
    start = output.rfind("\n[") + 1
    nodes = json.loads(output[start:])
    if not isinstance(nodes, list) or any(
        not isinstance(node, dict) or not {"node_id", "target", "dependencies",
                                           "needs_rebuild", "command"} <= node.keys()
        for node in nodes
    ):
        raise ValueError("Holmake returned an unsupported dependency graph")
    graph = {node["node_id"]: node for node in nodes}
    nominal = {key: workdir / node["target"] for key, node in graph.items()}
    paths = {key: path.resolve() for key, path in nominal.items()}
    clean = target in {"clean", "cleanDeps", "cleanAll"}
    if target and not clean:
        requested = (workdir / target).resolve()
        roots = [key for key, path in paths.items() if path == requested]
        if not roots:
            roots = [key for key, path in paths.items() if path == Path(str(requested) + ".uo")]
        if not roots:
            raise ValueError(f"target {target!r} is absent from the dependency graph")
    else:
        roots = list(graph)
    selected = set()
    pending = roots[:]
    while pending:
        key = pending.pop()
        if key in selected:
            continue
        selected.add(key)
        pending.extend(graph[key]["dependencies"])
    reads = {path for key in selected for path in _artifact_paths(nominal[key])}
    outputs = {path for key in selected
               if graph[key]["command"] and graph[key]["needs_rebuild"]
               for path in _artifact_paths(nominal[key])}
    if clean:
        # Holmakefile CLINE_OPTIONS may make cleaning recursive. Reserve the
        # whole discovered closure so it cannot delete a peer's interfaces.
        outputs = {path for key in selected if graph[key]["command"]
                   for path in _artifact_paths(nominal[key])}
    claim = BuildClaim(workdir, reads, outputs)
    claim.clean = clean
    claim.preflight_output = output[:start]
    return claim


def _state_directory(path):
    directory = path.parent
    if directory.name == "objs" and directory.parent.name == ".hol":
        directory = directory.parent.parent
    # Native cleanAll removes .hol, including unfamiliar subdirectories.
    # Keep failure evidence outside it so cleaning cannot certify a surviving
    # arbitrary recipe output that was previously only partially written.
    return directory / ".hol4-mcp" / "build-state"


def _state_file(path, phase):
    digest = hashlib.sha256(str(path).encode()).hexdigest()
    return _state_directory(path) / f"{digest}.{phase}.json"


def _read_state(path, phase):
    try:
        data = json.loads(_state_file(path, phase).read_text())
    except FileNotFoundError:
        return None
    if not isinstance(data, dict) or not {"path", "stamp", "label", "token"} <= data.keys():
        raise ValueError(f"Invalid build coordination record for {path}")
    if data["path"] != str(path):
        raise ValueError(f"Mismatched build coordination record for {path}")
    return data


def _record_stamp(record):
    return tuple(record["stamp"]) if record["stamp"] is not None else None


def _write_state(path, phase, stamp, claim):
    destination = _state_file(path, phase)
    destination.parent.mkdir(parents=True, mode=0o700, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8",
                                         dir=destination.parent, delete=False) as stream:
            temporary = Path(stream.name)
            json.dump({"path": str(path), "stamp": stamp,
                       "label": claim.label, "token": claim.token}, stream)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, destination)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def _suspect(path):
    stamp = _stamp(path)
    if stamp is None:
        return None
    failed = _read_state(path, "failed")
    if failed is not None and stamp == _record_stamp(failed):
        return failed
    running = _read_state(path, "running")
    if running is not None and stamp != _record_stamp(running):
        # The lock is free, but the controller never certified completion.
        return running
    return None


def _lock_storage():
    # Coordination identity must not depend on a client's private TMPDIR.
    directory = Path("/tmp") / f"hol4-mcp-build-locks-{os.getuid()}"
    directory.mkdir(mode=0o700, exist_ok=True)
    info = directory.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_uid != os.getuid() or info.st_mode & 0o077:
        raise ValueError(f"Build lock directory is not private and owned by this user: {directory}")
    return directory


def _foreign_label(directory):
    # Atomic intent records are evidence for names, never evidence that a
    # process is still alive. Only failure to acquire flock proves overlap.
    try:
        records = _state_directory(directory / "placeholder").glob("*.running.json")
        labels = {json.loads(path.read_text())["label"] for path in records}
        return "; ".join(sorted(labels)) or "another MCP server's build"
    except (OSError, ValueError, KeyError):
        return "another MCP server's build"


class BuildClaims:
    def __init__(self):
        self.active: dict[str, BuildClaim] = {}

    def finish(self, claim):
        if claim.token not in self.active:
            return
        if claim.proc is not None and claim.proc.returncode is None:
            return  # Keep protection if killing/reaping the process failed.
        try:
            for path in claim.outputs:
                stamp = _stamp(path)
                failed = _read_state(path, "failed")
                if claim.proc is not None and claim.proc.returncode != 0:
                    if stamp is not None and stamp != claim.before.get(path):
                        _write_state(path, "failed", stamp, claim)
                elif failed is not None and stamp != _record_stamp(failed):
                    _state_file(path, "failed").unlink(missing_ok=True)
                running = _read_state(path, "running")
                if running is not None and running["token"] == claim.token:
                    _state_file(path, "running").unlink(missing_ok=True)
        except (OSError, ValueError) as exc:
            # Keep any unfinalized intent conservative, and always release
            # locks. State I/O failure must not strand a resource forever.
            claim.state_error = f"Build coordination state could not be finalized: {exc}"
            print(claim.state_error, file=sys.stderr)
        finally:
            self.active.pop(claim.token, None)
            claim.release_locks()

    def register(self, claim):
        read_dirs = {path.parent for path in claim.reads} | {claim.workdir}
        write_dirs = {path.parent for path in claim.outputs}
        if claim.clean:
            write_dirs |= read_dirs
        for previous in self.active.values():
            previous_reads = {path.parent for path in previous.reads} | {previous.workdir}
            previous_writes = {path.parent for path in previous.outputs}
            if previous.clean:
                previous_writes |= previous_reads
            overlap = (write_dirs & previous_reads) | (read_dirs & previous_writes)
            if overlap:
                return (f"ERROR: dependency overlap with {previous.label}: "
                        f"{', '.join(map(str, sorted(overlap)))}. No build was started. "
                        "Wait for the running build to finish, then retry; "
                        "hol_build_status reports detached jobs.")
        accepted = False
        try:
            storage = _lock_storage()
            for directory in sorted(read_dirs | write_dirs):
                digest = hashlib.sha256(str(directory).encode()).hexdigest()
                fd = os.open(storage / f"{digest}.lock",
                             os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
                claim.lock_fds.append(fd)
                mode = fcntl.LOCK_EX if directory in write_dirs else fcntl.LOCK_SH
                try:
                    fcntl.flock(fd, mode | fcntl.LOCK_NB)
                except BlockingIOError:
                    return (f"ERROR: dependency overlap with {_foreign_label(directory)}: "
                            f"{directory}. No build was started. Wait for the blocking "
                            "build to finish and retry; foreign job IDs belong to their "
                            "originating MCP server.")
            for path in sorted(claim.reads):
                record = _suspect(path)
                if record is not None and path not in claim.outputs:
                    return (f"ERROR: {record['label']} left a possibly partial or "
                            f"unverified artifact: {path}. No build was started. "
                            "Inspect/remove the failed output and rebuild its prerequisite "
                            "before retrying; existing files can otherwise be treated as up to date.")
            claim.before = {path: _stamp(path) for path in claim.outputs}
            for path in sorted(claim.outputs):
                previous = _suspect(path)
                if previous is not None:
                    # Preserve old suspicion before replacing an orphan's
                    # intent. A failed/no-op repair must not erase it.
                    _write_state(path, "failed", claim.before[path],
                                 _RecordOwner(previous["token"], previous["label"]))
                _write_state(path, "running", claim.before[path], claim)
            self.active[claim.token] = claim
            accepted = True
            return None
        finally:
            if not accepted:
                # No recipes have started. Remove only this proposal's intent;
                # retain preexisting failed/orphan evidence.
                try:
                    for path in claim.outputs:
                        running = _read_state(path, "running")
                        if running is not None and running["token"] == claim.token:
                            _state_file(path, "running").unlink(missing_ok=True)
                finally:
                    claim.release_locks()


@dataclass
class _RecordOwner:
    token: str
    label: str


build_claims = BuildClaims()
