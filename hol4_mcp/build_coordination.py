"""Coordinate MCP build dependency directories across server lifetimes.

Holmake locks competing writers, but can skip an existing partial dependency.
Read/read overlap is safe; a write/read or write/write overlap is refused.
Locks cover cooperating servers on the same host/user; undeclared outputs and
plain external Holmake processes remain outside this protocol.

When a build ends, each of its outputs is judged on its own: a job Holmake's
monitor reported as finished wrote complete files even if a later job failed.
A detached job also leaves a record of itself and, through its wrapper, the
exit status Holmake ends with, so a server started after the one that
launched it can report it, cancel it, and apply its outcome.
"""

from dataclasses import dataclass, field
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
import tempfile
import time
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
    # Outputs by the name Holmake's monitor prints for the job writing them,
    # and the outputs Holmake compiles in its own process (no job line).
    tags: dict = field(default_factory=dict)
    in_process: set = field(default_factory=set)

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
    tag_dirs = {}
    for key in selected:
        node = graph[key]
        if not (node["command"] and node["needs_rebuild"]):
            continue
        tag = job_tag(nominal[key], str(node["command"]))
        paths = set(_artifact_paths(nominal[key]))
        if tag is None:
            claim.in_process |= paths
        else:
            claim.tags.setdefault(tag, set()).update(paths)
            tag_dirs.setdefault(tag, set()).add(paths_dir(nominal[key]))
    for tag, dirs in tag_dirs.items():
        if len(dirs) > 1:
            del claim.tags[tag]   # the printed name alone cannot tell them apart
    return claim


def paths_dir(path):
    return path.resolve().parent


def job_tag(target: Path, command: str) -> str | None:
    """The name Holmake's monitor prints for the job that writes ``target``,
    or None when Holmake compiles it in its own process and prints nothing.
    One BIC_Build job writes a theory's .sml, .sig and .dat under the stem."""
    if command == "BIC_Compile":
        return None
    if command.startswith("BIC_Build"):
        return target.stem
    name = target.name
    return name[:-4] if name.endswith(".sml") else name


# Holmake's monitor, when stdout is not a terminal, prints one line as a job
# starts and one as it ends: `<tag> [dir] (<time>) [k/n] <verdict>`. The
# columns are space-padded; the padding can be absent (a long dir abuts the
# time, the counter abuts the verdict), and the dir may itself contain
# parentheses, as in `$(CAKEMLDIR)/...`.
_JOB_START_RE = re.compile(r"^Starting work on (\S+)\s*$")
_JOB_RESULT_RE = re.compile(
    r"^(?P<tag>\S+)(?:\s+\S*?)?\s*\([^)]*\)\s*(?:\[[^\]]*\])?\s*"
    r"(?P<verdict>OK|CHEATED|F-CHEAT|CACHED|RETRY|FAIL<[^>]*>)\s*$")
_SUCCESS_VERDICTS = {"OK", "CHEATED", "F-CHEAT", "CACHED"}
# A sequential build (-j1) has no monitor. After each theory script it ran
# successfully it prints `Holmake: [k/n] <thy>` (or `[↓m] <thy>` past 99
# theories), naming the job its monitor would print as `<thy>Theory`; shell
# command targets get no such line.
_J1_THEORY_DONE_RE = re.compile(r"^(?:Holmake: )?\[(?:\d+/\d+|↓\d+)\] (\S+)\s*$")


def completed_outputs(tags, in_process, output, returncode):
    """Outputs a build that did not succeed as a whole nevertheless finished.

    A monitored job's outputs are complete when its last line is a success
    verdict and no later start line reopened it; in a sequential build, a
    theory's are complete once its progress line follows. Holmake's in-process
    compiles are complete when Holmake exited of its own accord (a small
    positive status): it writes them one at a time and nothing interrupted
    it. A signal — cancellation, a timeout kill, a vanished controller —
    certifies nothing beyond the verdict lines.
    """
    state = {}
    for line in output.splitlines():
        start = _JOB_START_RE.match(line)
        if start:
            state[start.group(1)] = "started"
            continue
        result = _JOB_RESULT_RE.match(line)
        if result:
            state[result.group("tag")] = result.group("verdict")
            continue
        theory = _J1_THEORY_DONE_RE.match(line)
        if theory:
            state[theory.group(1) + "Theory"] = "OK"
    done = set()
    for tag, paths in tags.items():
        if state.get(tag) in _SUCCESS_VERDICTS:
            done.update(paths)
    if returncode is not None and 0 < returncode < 128:
        done.update(in_process)
    return done


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


def _suspect(path, adopt=True):
    stamp = _stamp(path)
    if stamp is None:
        return None
    failed = _read_state(path, "failed")
    if failed is not None and stamp == _record_stamp(failed):
        return failed
    running = _read_state(path, "running")
    if running is not None and stamp != _record_stamp(running):
        # The lock is free, but the controller never certified completion.
        # Its job may have left an exit status behind for us to apply.
        if adopt and adopt_finished_job(running["token"]):
            return _suspect(path, adopt=False)
        return running
    return None


# --- detached job records: survive the server that started the job ---------

_TOKEN_RE = re.compile(r"^[0-9a-f]{12}$")


def jobs_directory():
    directory = _lock_storage() / "jobs"
    directory.mkdir(mode=0o700, exist_ok=True)
    return directory


def _process_start(pid):
    """The kernel's start time of ``pid``, so a reused pid is not mistaken
    for the job; None where /proc is unavailable."""
    try:
        with open(f"/proc/{pid}/stat", encoding="utf-8", errors="replace") as stream:
            return stream.read().rsplit(")", 1)[1].split()[19]
    except (OSError, IndexError):
        return None


def job_record(claim, *, pid, target, log, exit_file, trace_note, started):
    return {
        "token": claim.token, "label": claim.label, "pid": pid,
        "process_start": _process_start(pid), "workdir": str(claim.workdir),
        "target": target, "log": str(log), "exit_file": str(exit_file),
        "trace_note": trace_note, "started": started,
        "outputs": [str(p) for p in claim.outputs],
        "before": {str(p): s for p, s in claim.before.items()},
        "tags": {t: sorted(str(p) for p in ps) for t, ps in claim.tags.items()},
        "in_process": sorted(str(p) for p in claim.in_process),
    }


def write_job(record):
    directory = jobs_directory()
    destination = directory / f"{record['token']}.json"
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=directory,
                                     delete=False) as stream:
        json.dump(record, stream)
        temporary = Path(stream.name)
    os.replace(temporary, destination)
    cutoff = time.time() - 7 * 24 * 3600
    for stale in directory.glob("*.json"):
        if stale != destination:
            try:
                data = json.loads(stale.read_text())
                if data.get("finalized") and data["finalized"]["at"] < cutoff:
                    stale.unlink()
            except (OSError, ValueError, KeyError, TypeError):
                pass


def read_job(token):
    if not _TOKEN_RE.match(token or ""):
        return None
    try:
        record = json.loads((jobs_directory() / f"{token}.json").read_text())
    except (OSError, ValueError):
        return None
    return record if isinstance(record, dict) and record.get("token") == token else None


def job_exit_status(record):
    """Holmake's exit status written by the job's wrapper, or None while it
    runs or if the wrapper itself was killed."""
    try:
        return int(Path(record["exit_file"]).read_text().strip())
    except (OSError, ValueError, KeyError):
        return None


def process_alive(record):
    pid = record.get("pid")
    if not pid:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        pass
    start = _process_start(pid)
    return start is None or record.get("process_start") in (None, start)


def finalize_job(record, returncode, output):
    """Apply a finished (or cancelled: ``returncode`` None) job's outcome to
    its outputs' coordination records, as its own server would have."""
    owner = _RecordOwner(record["token"], record["label"])
    outputs = [Path(p) for p in record["outputs"]]
    before = {Path(p): (tuple(s) if s is not None else None)
              for p, s in record["before"].items()}
    tags = {t: {Path(p) for p in ps} for t, ps in record["tags"].items()}
    in_process = {Path(p) for p in record["in_process"]}
    completed = (completed_outputs(tags, in_process, output, returncode)
                 if returncode else set())
    finalize(outputs, before, returncode, owner, completed)
    record["finalized"] = {"returncode": returncode, "at": time.time()}
    write_job(record)


def adopt_finished_job(token):
    """Finalize a job whose controller is gone but whose wrapper recorded
    Holmake's exit status. True when something was applied."""
    record = read_job(token)
    if record is None or record.get("finalized"):
        return False
    returncode = job_exit_status(record)
    if returncode is None:
        return False
    try:
        output = Path(record["log"]).read_text(encoding="utf-8", errors="replace")
    except (OSError, KeyError):
        output = ""
    try:
        finalize_job(record, returncode, output)
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"Build coordination state could not be finalized for job "
              f"{token}: {exc}", file=sys.stderr)
        return False
    return True


def record_finalized(token, returncode):
    """Note that the job's own server finalized it, so no adoption repeats it."""
    record = read_job(token)
    if record is not None and not record.get("finalized"):
        record["finalized"] = {"returncode": returncode, "at": time.time()}
        try:
            write_job(record)
        except OSError:
            pass


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


def finalize(outputs, before, returncode, owner, completed=frozenset()):
    """Record each output's fate once its build has ended.

    ``returncode`` None means cancelled or lost. An output the build did not
    finish is marked failed if it changed; one it did finish — the whole set
    on success, ``completed`` otherwise — sheds any stale failure record.
    """
    for path in outputs:
        stamp = _stamp(path)
        failed = _read_state(path, "failed")
        if returncode != 0 and path not in completed:
            if stamp is not None and stamp != before.get(path):
                _write_state(path, "failed", stamp, owner)
        elif failed is not None and stamp != _record_stamp(failed):
            _state_file(path, "failed").unlink(missing_ok=True)
        running = _read_state(path, "running")
        if running is not None and running["token"] == owner.token:
            _state_file(path, "running").unlink(missing_ok=True)


class BuildClaims:
    def __init__(self):
        self.active: dict[str, BuildClaim] = {}

    def finish(self, claim, output=""):
        """``output`` is the build's own stdout (the log, for a detached
        job): the verdict lines in it decide what a failed build finished."""
        if claim.token not in self.active:
            return
        if claim.proc is not None and claim.proc.returncode is None:
            return  # Keep protection if killing/reaping the process failed.
        try:
            returncode = claim.proc.returncode if claim.proc is not None else None
            completed = (completed_outputs(claim.tags, claim.in_process, output, returncode)
                         if returncode else set())
            finalize(claim.outputs, claim.before, returncode, claim, completed)
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
