"""Coordinate the dependency directories used by builds in one MCP server.

Holmake locks competing writers, but can skip an existing partial dependency.
Read/read overlap is safe; a write/read or write/write overlap is refused.
Undeclared outputs of arbitrary recipes and external Holmake processes remain
outside this registry's scope.
"""

from dataclasses import dataclass, field
import json
from pathlib import Path
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

    @property
    def label(self):
        return f"{'job' if self.detached else 'build'}={self.token} workdir={self.workdir}"


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
        outputs = reads.copy()
    claim = BuildClaim(workdir, reads, outputs)
    claim.preflight_output = output[:start]
    return claim


class BuildClaims:
    def __init__(self):
        self.active: dict[str, BuildClaim] = {}
        self.partial: dict[Path, tuple[tuple, str]] = {}

    def finish(self, claim):
        if claim.token not in self.active:
            return
        if claim.proc is not None and claim.proc.returncode is None:
            return  # Keep protection if killing/reaping the process failed.
        if claim.proc is not None and claim.proc.returncode != 0:
            for path in claim.outputs:
                stamp = _stamp(path)
                if stamp is not None and stamp != claim.before.get(path):
                    self.partial[path] = (stamp, claim.label)
        elif claim.proc is not None:
            for path in claim.outputs:
                previous = self.partial.get(path)
                if previous is not None and _stamp(path) != previous[0]:
                    self.partial.pop(path, None)
        self.active.pop(claim.token, None)

    def register(self, claim):
        # A reaper may not have run yet even though the process is terminal.
        for previous in list(self.active.values()):
            if previous.proc is not None and previous.proc.returncode is not None:
                self.finish(previous)
        for path, (stamp, label) in list(self.partial.items()):
            if _stamp(path) != stamp:
                del self.partial[path]
            elif path in claim.reads and path not in claim.outputs:
                return (f"ERROR: {label} left a possibly partial artifact: {path}. "
                        "No build was started. Inspect/remove the failed output and "
                        "rebuild its prerequisite before retrying; existing files "
                        "can otherwise be treated as up to date.")
        read_dirs = {path.parent for path in claim.reads} | {claim.workdir}
        write_dirs = {path.parent for path in claim.outputs}
        for previous in self.active.values():
            previous_reads = {path.parent for path in previous.reads} | {previous.workdir}
            previous_writes = {path.parent for path in previous.outputs}
            overlap = (write_dirs & previous_reads) | (read_dirs & previous_writes)
            if overlap:
                return (f"ERROR: dependency overlap with {previous.label}: "
                        f"{', '.join(map(str, sorted(overlap)))}. No build was started. "
                        "Wait for the running build to finish, then retry; "
                        "hol_build_status reports detached jobs.")
        claim.before = {path: _stamp(path) for path in claim.outputs}
        self.active[claim.token] = claim
        return None


build_claims = BuildClaims()
