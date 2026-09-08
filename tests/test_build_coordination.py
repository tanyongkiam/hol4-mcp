"""Exercise shared build behavior with the installed Holmake, not a mock lock."""
import asyncio
import re
import shlex
import sys

import pytest

from hol4_mcp import hol_mcp_server as srv


async def test_sibling_builds_share_native_artifact_lock(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    worker = shared / "writer.py"
    worker.write_text(
        "from pathlib import Path\nimport time\n"
        "guard = Path('writer-active')\n"
        "guard.mkdir()  # overlapping writers fail this test\n"
        "try:\n"
        " Path('ready').write_text('partial')\n"
        " time.sleep(.2)\n"
        " Path('ready').write_text('complete')\n"
        "finally:\n guard.rmdir()\n")
    python = shlex.quote(sys.executable)
    (shared / "Holmakefile").write_text(f"ready:\n\t{python} writer.py\n")
    branches = [tmp_path / "a", tmp_path / "b"]
    for branch in branches:
        branch.mkdir()
        (branch / "Holmakefile").write_text(
            "INCLUDES = ../shared\n"
            "result: ../shared/ready\n"
            "\t" + python + " -c \"from pathlib import Path; "
            "assert Path('../shared/ready').read_text() == 'complete'; "
            "Path('result').write_text('ok')\"\n")
    results = await asyncio.gather(*(
        srv.holmake(workdir=str(branch), target="result", timeout=30)
        for branch in branches))
    assert all("Build succeeded" in result for result in results), results
    assert (shared / ".hol" / "locks" / "ready.lock").exists()
    assert all((branch / "result").read_text() == "ok" for branch in branches)


async def test_cancelling_one_detached_build_does_not_kill_independent_job(tmp_path):
    python = shlex.quote(sys.executable)
    roots = [tmp_path / "cancelled", tmp_path / "independent"]
    job_ids = []
    for root in roots:
        root.mkdir()
        (root / "worker.py").write_text(
            "from pathlib import Path\nimport time\n"
            "Path('started').touch()\n"
            "while not Path('release').exists(): time.sleep(.01)\n"
            "Path('result').write_text('ok')\n")
        (root / "Holmakefile").write_text(f"result:\n\t{python} worker.py\n")
        result = await srv.holmake(workdir=str(root), target="result", detach=True)
        job_ids.append(re.search(r"job=(\S+)", result).group(1))
    try:
        async def ready():
            while not all((root / "started").exists() for root in roots):
                await asyncio.sleep(.01)
        await asyncio.wait_for(ready(), 10)
        cancelled = await srv.hol_build_status(job_ids[0], cancel=True)
        assert "cancelled" in cancelled, cancelled
        other = await srv.hol_build_status(job_ids[1])
        assert "running" in other, other
        (roots[1] / "release").touch()
        await asyncio.wait_for(srv._build_jobs[job_ids[1]].proc.wait(), 10)
        other = await srv.hol_build_status(job_ids[1])
        assert "Build succeeded" in other, other
    finally:
        for job in job_ids:
            await srv.hol_build_status(job, cancel=True)


async def test_build_does_not_delete_previous_or_peer_logs(tmp_path):
    logs = tmp_path / ".hol" / "logs"
    logs.mkdir(parents=True)
    prior = logs / "anotherTheory"
    prior.write_text("preserved diagnostic evidence")
    (tmp_path / "Holmakefile").write_text("result:\n\tfalse\n")
    result = await srv.holmake(workdir=str(tmp_path), target="result", timeout=10)
    assert "Build failed" in result, result
    assert prior.read_text() == "preserved diagnostic evidence"
    # An unchanged old failure must not be attributed to this request.
    assert "preserved diagnostic evidence" not in result


@pytest.mark.xfail(strict=True, reason=(
    "Holmake's per-target lock only serialises builders of the same target: a "
    "peer that starts after ../shared/ready already exists treats the partial "
    "file as up to date, skips the writer and reads it (open C13 race)"))
async def test_peer_starting_during_shared_write_waits_for_complete_artifact(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    python = shlex.quote(sys.executable)
    (shared / "writer.py").write_text(
        "from pathlib import Path\nimport time\n"
        "Path('ready').write_text('partial')\n"
        "Path('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "Path('ready').write_text('complete')\n")
    (shared / "Holmakefile").write_text(f"ready:\n\t{python} writer.py\n")
    job_ids = []
    try:
        for label in ("a", "b"):
            branch = tmp_path / label
            branch.mkdir()
            (branch / "Holmakefile").write_text(
                "INCLUDES = ../shared\nresult: ../shared/ready\n\t" + python +
                " -c \"from pathlib import Path; "
                "assert Path('../shared/ready').read_text() == 'complete'; "
                "Path('result').touch()\"\n")
            started = await srv.holmake(str(branch), target="result", detach=True)
            job_ids.append(re.search(r"job=(\S+)", started).group(1))
            if label == "a":
                async def wait_started():
                    while not (shared / "started").exists():
                        await asyncio.sleep(.01)
                await asyncio.wait_for(wait_started(), 10)
        # The second build must not treat the first writer's partial output
        # as an up-to-date dependency just because that file now exists.
        await asyncio.sleep(.15)
        peer = await srv.hol_build_status(job_ids[1])
        assert "running" in peer, peer
        (shared / "release").touch()
        for job in job_ids:
            await asyncio.wait_for(srv._build_jobs[job].proc.wait(), 10)
            status = await srv.hol_build_status(job)
            assert "Build succeeded" in status, status
    finally:
        (shared / "release").touch()
        for job in job_ids:
            await srv.hol_build_status(job, cancel=True)
