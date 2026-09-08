"""Opt-in build-discovery tracing. Ordinary builds do not invoke a tracer."""
import json
import os
from pathlib import Path
import re
import shutil
import sys
import uuid


def build_failure_heading(returncode: int, output: str, traced: bool) -> str:
    if traced and re.search(r"^\S*strace:.*(?:PTRACE|ptrace|not permitted|not supported|invalid option|unrecognized option)", output, re.M):
        return ("ERROR: Discovery tracing failed or is unavailable in this execution "
                "environment. This is not a proof-failure verdict; inspect the "
                "tracer error and permissions before a diagnostic retry.")
    return f"Build failed (exit code {returncode})."


def traced_build(command: list[str], workdir: Path, enabled: bool,
                 environment: dict) -> tuple[list[str], str]:
    if not enabled:
        return command, ""
    tracer = shutil.which("strace", path=environment.get("PATH"))
    if sys.platform != "linux" or not tracer:
        raise ValueError("trace_discovery=True requires Linux and strace; no build was started")
    directory = workdir / ".hol"
    directory.mkdir(parents=True, exist_ok=True)
    trace = directory / f"mcp-discovery-{uuid.uuid4().hex[:12]}.log"
    try:
        namespace = os.readlink("/proc/self/ns/mnt")
    except OSError:
        namespace = "unavailable"
    metadata = trace.with_suffix(".json")
    with metadata.open("x", encoding="utf-8") as stream:
        json.dump({"command": command, "workdir": str(workdir),
                   "server_pid": os.getpid(), "mount_namespace": namespace}, stream)
    wrapped = [tracer, "-f", "--kill-on-exit", "-s", "4096", "-e",
               "trace=chdir,fchdir,openat,newfstatat,getdents64",
               "-o", str(trace), "--", *command]
    note = (f"[Discovery trace: {trace}; context: {metadata}; "
            f"mount namespace: {namespace}. Inspect failed syscalls and their "
            "paths; the last printed directory is not necessarily the failure. "
            "Tracing is opt-in and adds overhead.]")
    return wrapped, note
