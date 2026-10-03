"""Exercise shared build behavior with the installed Holmake, not a mock lock."""
import asyncio
from pathlib import Path
import re
import shlex
import sys

import pytest

from hol4_mcp import hol_mcp_server as srv
from hol4_mcp.build_coordination import completed_outputs, job_tag


MONITOR_OUTPUT = """\
Scanning $(HOLDIR)/src/boss
Scanned 2 directories
Building 3 theory files
Starting work on aTheory
Starting work on bTheory
aTheory                                                  (3s)   [1/3]OK
bTheory                  ../other                       (12s)   [2/3]CHEATED
Starting work on cTheory
cTheory                                                  (1s)   RETRY
Starting work on cTheory
Starting work on dTheory
dTheory                                                  (0s)   FAIL<1>
Starting work on result
result                                                   (0s)   OK
"""


def test_completed_outputs_follows_the_monitor_verdicts():
    tags = {t: {Path(f"/w/{t}.dat")}
            for t in ("aTheory", "bTheory", "cTheory", "dTheory", "eTheory", "result")}
    compiled = {Path("/w/aTheory.uo")}
    done = completed_outputs(tags, compiled, MONITOR_OUTPUT, 1)
    assert done == {Path("/w/aTheory.dat"), Path("/w/bTheory.dat"),
                    Path("/w/result.dat"), Path("/w/aTheory.uo")}
    # A signal exit certifies verdict lines only, never the in-process compiles.
    for signalled in (-15, 143):
        done = completed_outputs(tags, compiled, MONITOR_OUTPUT, signalled)
        assert Path("/w/aTheory.dat") in done and Path("/w/aTheory.uo") not in done
    assert completed_outputs(tags, compiled, "", None) == set()


def test_job_tag_names_the_monitor_line():
    assert job_tag(Path("/w/fooTheory.dat"), "BIC_Build /w/foo") == "fooTheory"
    assert job_tag(Path("/w/fooTheory.sml"), "BIC_Build /w/foo") == "fooTheory"
    assert job_tag(Path("/w/fooTheory.uo"), "BIC_Compile") is None
    assert job_tag(Path("/w/result"), "touch result") == "result"
    assert job_tag(Path("/w/gen.sml"), "python gen.py") == "gen"


async def test_failed_build_keeps_the_prerequisite_its_monitor_reported_complete(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    python = shlex.quote(sys.executable)
    (shared / "Holmakefile").write_text(
        f"ready:\n\t{python} -c \"from pathlib import Path; Path('ready').write_text('complete')\"\n"
        f"broken: ready\n\t{python} -c \"from pathlib import Path; import sys; "
        "Path('broken').write_text('partial'); sys.exit(1)\"\n")
    result = await srv.holmake(str(shared), target="broken", timeout=30)
    assert "Build failed" in result, result
    assert (shared / "ready").read_text() == "complete"
    assert (shared / "broken").read_text() == "partial"

    def consumer(name, dependency):
        root = tmp_path / name
        root.mkdir()
        (root / "Holmakefile").write_text(
            f"INCLUDES = ../shared\nresult: ../shared/{dependency}\n\t{python} -c "
            f"\"from pathlib import Path; "
            f"Path('result').write_text(Path('../shared/{dependency}').read_text())\"\n")
        return root

    accepted = await srv.holmake(str(consumer("uses_ready", "ready")), target="result", timeout=30)
    assert "Build succeeded" in accepted, accepted
    refused = await srv.holmake(str(consumer("uses_broken", "broken")), target="result", timeout=30)
    assert refused.startswith("ERROR:") and "partial" in refused.lower(), refused


async def _wait_for_job_finished(job, timeout=10):
    async def finished():
        while srv._build_jobs[job].finished is None:
            await asyncio.sleep(.01)
    await asyncio.wait_for(finished(), timeout)


async def test_sibling_builds_do_not_consume_overlapping_writes(tmp_path):
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
    for branch, result in zip(branches, results):
        if "Build succeeded" not in result:
            assert result.startswith("ERROR:") and "overlap" in result.lower(), results
            result = await srv.holmake(workdir=str(branch), target="result", timeout=30)
            assert "Build succeeded" in result, result
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
        await _wait_for_job_finished(job_ids[1])
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


@pytest.mark.parametrize("detach", [False, True])
async def test_peer_starting_during_shared_write_is_refused_then_can_retry(tmp_path, detach):
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
            started = await srv.holmake(str(branch), target="result", detach=True if label == "a" else detach)
            if label == "b":
                assert started.startswith("ERROR:"), started
                assert "overlap" in started.lower() and job_ids[0] in started, started
                assert str(shared) in started, started
                assert not (branch / "result").exists()
                break
            job_ids.append(re.search(r"job=(\S+)", started).group(1))
            if label == "a":
                async def wait_started():
                    while not (shared / "started").exists():
                        await asyncio.sleep(.01)
                await asyncio.wait_for(wait_started(), 10)
        # No peer process may consume the first writer's partial output.
        (shared / "release").touch()
        for job in job_ids:
            await _wait_for_job_finished(job)
            status = await srv.hol_build_status(job)
            assert "Build succeeded" in status, status
        retried = await srv.holmake(str(tmp_path / "b"), target="result", timeout=10)
        assert "Build succeeded" in retried, retried
    finally:
        (shared / "release").touch()
        for job in job_ids:
            await srv.hol_build_status(job, cancel=True)


@pytest.mark.parametrize("artifact", ["ready", "ready.ui"])
async def test_cancelled_shared_writer_does_not_leave_silent_partial_dependency(tmp_path, artifact):
    shared = tmp_path / "shared"
    shared.mkdir()
    relative_output = f".hol/objs/{artifact}" if artifact.endswith(".ui") else artifact
    output = shared / relative_output
    python = shlex.quote(sys.executable)
    (shared / "writer.py").write_text(
        "from pathlib import Path\nimport time\n"
        f"output = Path({relative_output!r})\n"
        "output.parent.mkdir(parents=True, exist_ok=True)\n"
        "output.write_text('partial')\nPath('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        "output.write_text('complete')\n")
    (shared / "Holmakefile").write_text(f"{artifact}:\n\t{python} writer.py\n")
    peer = tmp_path / "peer"
    peer.mkdir()
    (peer / "Holmakefile").write_text(
        f"INCLUDES = ../shared\nresult: ../shared/{artifact}\n\t" + python +
        " -c \"from pathlib import Path; "
        f"Path('result').write_text(Path('../shared/{relative_output}').read_text())\"\n")
    started = await srv.holmake(str(shared), target=artifact, detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        async def wait_started():
            while not (shared / "started").exists():
                await asyncio.sleep(.01)
        await asyncio.wait_for(wait_started(), 10)
        cancelled = await srv.hol_build_status(job, cancel=True)
        assert "cancelled" in cancelled, cancelled
        assert srv._build_jobs[job].done.is_set()
        assert job not in srv.build_claims.active
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert result.startswith("ERROR:") and "partial" in result.lower(), result
        assert str(output) in result and job in result, result
        assert not (peer / "result").exists(), "a successful peer consumed partial content"
        if artifact == "ready":
            # Native clean does not remove an arbitrary recipe's output.
            # A successful clean must not certify unchanged partial content.
            cleaned = await srv.holmake(str(shared), target="cleanAll", timeout=10)
            assert "Build succeeded" in cleaned, cleaned
            result = await srv.holmake(str(peer), target="result", timeout=10)
            assert result.startswith("ERROR:") and "partial" in result.lower(), result
        # An explicit repair makes the dependency safe to use again.
        output.unlink()
        (shared / "release").touch()
        repaired = await srv.holmake(str(shared), target=artifact, timeout=10)
        assert "Build succeeded" in repaired, repaired
        result = await srv.holmake(str(peer), target="result", timeout=10)
        assert "Build succeeded" in result, result
        assert (peer / "result").read_text() == "complete"
    finally:
        (shared / "release").touch()
        await srv.hol_build_status(job, cancel=True)


async def test_independent_writers_share_read_only_dependency_in_parallel(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    (shared / "ready").write_text("complete")
    (shared / "Holmakefile").write_text("ready:\n\tfalse\n")
    python = shlex.quote(sys.executable)
    roots = [tmp_path / "a", tmp_path / "b"]
    jobs = []
    try:
        for root in roots:
            root.mkdir()
            (root / "worker.py").write_text(
                "from pathlib import Path\nimport time\n"
                "assert Path('../shared/ready').read_text() == 'complete'\n"
                "Path('started').touch()\n"
                "while not Path('release').exists(): time.sleep(.01)\n"
                "Path('result').touch()\n")
            (root / "Holmakefile").write_text(
                f"INCLUDES = ../shared\nresult: ../shared/ready\n\t{python} worker.py\n")
            result = await srv.holmake(str(root), target="result", detach=True)
            assert "Build started" in result, result
            jobs.append(re.search(r"job=(\S+)", result).group(1))
        async def both_started():
            while not all((root / "started").exists() for root in roots):
                await asyncio.sleep(.01)
        await asyncio.wait_for(both_started(), 10)
        for job in jobs:
            assert "running" in await srv.hol_build_status(job)
        for root in roots:
            (root / "release").touch()
        for job in jobs:
            await _wait_for_job_finished(job)
            assert "Build succeeded" in await srv.hol_build_status(job)
    finally:
        for root in roots:
            (root / "release").touch()
        for job in jobs:
            await srv.hol_build_status(job, cancel=True)


@pytest.mark.parametrize("detach", [False, True])
async def test_build_preexec_generates_rules_once_and_retains_diagnostics(tmp_path, detach):
    python = shlex.quote(sys.executable)
    (tmp_path / "prepare.py").write_text(
        "from pathlib import Path\n"
        "with Path('preexec-count').open('a') as log: log.write('run\\n')\n"
        "print('fixture preexec diagnostic')\n"
        "Path('Holmakefile').write_text('result:\\n\\ttouch result\\n')\n")
    (tmp_path / ".hol_preexec").write_text(f"{python} prepare.py\n")
    result = await srv.holmake(str(tmp_path), target="result", timeout=10, detach=detach)
    job = None
    try:
        if detach:
            assert "Build started" in result, result
            job = re.search(r"job=(\S+)", result).group(1)
            await _wait_for_job_finished(job)
            result = await srv.hol_build_status(job)
        assert "Build succeeded" in result, result
        assert "fixture preexec diagnostic" in result, result
        assert "=== Dependency discovery / preexec output ===" in result, result
        assert "=== Build output (preexec already ran; disabled below) ===" in result, result
        assert (tmp_path / "result").exists()
        assert (tmp_path / "preexec-count").read_text().splitlines() == ["run"]
    finally:
        if job:
            await srv.hol_build_status(job, cancel=True)


async def test_synchronous_budget_includes_dependency_preflight(tmp_path):
    python = shlex.quote(sys.executable)
    (tmp_path / ".hol_preexec").write_text(f"{python} -c 'import time; time.sleep(.7)'\n")
    (tmp_path / "Holmakefile").write_text(
        f"result:\n\t{python} -c 'import time; from pathlib import Path; "
        "time.sleep(.7); Path(\"result\").touch()'\n")
    result = await srv.holmake(str(tmp_path), target="result", timeout=1)
    assert "timed out" in result.lower(), result
    assert not (tmp_path / "result").exists(), "preflight silently extended the build budget"


async def test_detached_build_does_not_use_synchronous_timeout_for_preflight(tmp_path):
    python = shlex.quote(sys.executable)
    (tmp_path / ".hol_preexec").write_text(f"{python} -c 'import time; time.sleep(1.1)'\n")
    (tmp_path / "Holmakefile").write_text("result:\n\ttouch result\n")
    result = await srv.holmake(str(tmp_path), target="result", timeout=1, detach=True)
    job = None
    try:
        assert "Build started" in result, result
        job = re.search(r"job=(\S+)", result).group(1)
        await _wait_for_job_finished(job)
        assert "Build succeeded" in await srv.hol_build_status(job)
    finally:
        if job:
            await srv.hol_build_status(job, cancel=True)


async def test_recursive_clean_is_refused_while_peer_reads_shared_interfaces(tmp_path):
    shared = tmp_path / "shared"
    shared.mkdir()
    (shared / "ready.sig").write_text("signature Ready = sig val marker : int end\n")
    (shared / "ready.sml").write_text("structure Ready : Ready = struct val marker = 1 end\n")
    (shared / "Holmakefile").write_text("")
    built = await srv.holmake(str(shared), target="ready.uo", timeout=10)
    assert "Build succeeded" in built, built
    interface_path = shared / ".hol/objs/ready.ui"
    interface = interface_path.read_text()
    reader = tmp_path / "reader"
    reader.mkdir()
    python = shlex.quote(sys.executable)
    (reader / "worker.py").write_text(
        "from pathlib import Path\nimport time\n"
        "Path('started').touch()\n"
        "while not Path('release').exists(): time.sleep(.01)\n"
        f"assert Path('../shared/.hol/objs/ready.ui').read_text() == {interface!r}\n"
        "Path('result').touch()\n")
    (reader / "Holmakefile").write_text(
        f"INCLUDES = ../shared\nresult: ../shared/ready.ui\n\t{python} worker.py\n")
    cleaner = tmp_path / "cleaner"
    cleaner.mkdir()
    (cleaner / "Holmakefile").write_text(
        "CLINE_OPTIONS = --recursive-clean\nINCLUDES = ../shared\n"
        "result: ../shared/ready.ui\n\ttouch result\n")
    started = await srv.holmake(str(reader), target="result", detach=True)
    job = re.search(r"job=(\S+)", started).group(1)
    try:
        async def ready():
            while not (reader / "started").exists():
                await asyncio.sleep(.01)
        await asyncio.wait_for(ready(), 10)
        result = await srv.holmake(str(cleaner), target="cleanAll", timeout=10)
        assert result.startswith("ERROR:") and "overlap" in result.lower(), result
        assert job in result, result
        assert interface_path.read_text() == interface
        (reader / "release").touch()
        await _wait_for_job_finished(job)
        assert "Build succeeded" in await srv.hol_build_status(job)
    finally:
        (reader / "release").touch()
        await srv.hol_build_status(job, cancel=True)
