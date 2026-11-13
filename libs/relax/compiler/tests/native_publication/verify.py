# /// script
# requires-python = ">=3.11"
# ///
"""Offline Unix regression: uv run verify.py <relax binary> <new scratch directory>."""
import os
from pathlib import Path
import select
import shlex
import shutil
import signal
import subprocess
import sys

binary = str(Path(sys.argv[1]).resolve())
scratch = Path(sys.argv[2]).resolve()
scratch.mkdir(parents=True, exist_ok=True)
fixture = scratch / "fixture"
shutil.copytree(Path(__file__).parent, fixture, ignore=shutil.ignore_patterns("target", "Cargo.lock", "__pycache__"))
failed = scratch / "fail-link"
cc = scratch / "cc"
cc.write_text("#!/bin/sh\nfor arg do\ncase \"$arg\" in -shared|-dynamiclib) if [ -f " + shlex.quote(str(failed)) + " ]; then echo 'intentional native link failure' >&2; exit 1; fi;; esac\ndone\nexec /usr/bin/cc \"$@\"\n")
cc.chmod(0o755)
env = dict(os.environ, CC=str(cc), NATIVE_SALT="0", CARGO_NET_OFFLINE="true", CARGO_INCREMENTAL="0", CARGO_TARGET_DIR=str(scratch / "cargo"), RELAX_CACHE_DIR=str(scratch / "jit"))

def run(label, command, extra=None, success=True, output=None):
    result = subprocess.run(command, cwd=fixture, env=dict(env, **(extra or {})), capture_output=True, text=True, timeout=60)
    (scratch / (label + ".stdout")).write_text(result.stdout)
    (scratch / (label + ".stderr")).write_text(result.stderr)
    assert (result.returncode == 0) == success, f"{label}: exit {result.returncode}\n{result.stdout}\n{result.stderr}"
    if output is not None: assert result.stdout == output, f"{label}: {result.stdout!r}"
    return result

run("cargo-control", ["cargo", "test", "--release"])
ready = scratch / "ready"
release = scratch / "release"
for pipe in [ready, release]: os.mkfifo(pipe)
ready_fd = os.open(ready, os.O_RDWR | os.O_NONBLOCK)
release_fd = os.open(release, os.O_RDWR | os.O_NONBLOCK)
parent = subprocess.Popen([binary, "test", "--allow-c", "native-publication", "--test", "prepared"], cwd=fixture, env=dict(env, PREPARED_READY=str(ready), PREPARED_RELEASE=str(release), ARCHIVE_BIN=str(scratch / "archived-bin")), stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
try:
    assert select.select([ready_fd], [], [], 60)[0], "prepared test did not become ready"
    assert os.read(ready_fd, 1) == b"1"
    source = fixture / "cnative/value.c"
    initial = source.read_text()
    source.write_text(initial.replace("return 7", "return 9"))
    run("other-source", [binary, "test", "--allow-c", "native-publication", "--test", "prepared"], {"NATIVE_TEST_CASE": "edited"})
    source.write_text(initial)
    failed.touch()
    for attempt in [1, 2]:
        result = run(f"failed-refresh-{attempt}", [binary, "test", "--allow-c", "native-publication", "--test", "prepared"], {"NATIVE_SALT": "100", "NATIVE_TEST_CASE": "salted"}, success=False)
        assert "intentional native link failure" in result.stderr
    os.write(release_fd, b"1")
    stdout, stderr = parent.communicate(timeout=60)
    (scratch / "prepared.stdout").write_bytes(stdout)
    (scratch / "prepared.stderr").write_bytes(stderr)
    assert parent.returncode == 0, f"prepared binary: {stdout.decode(errors='replace')}\n{stderr.decode(errors='replace')}"
    assert b"1 passed; 0 failed" in stdout + stderr
    failed.unlink()
    run("recovered", [binary, "test", "--allow-c", "native-publication", "--test", "prepared"], {"NATIVE_SALT": "100", "NATIVE_TEST_CASE": "salted"})
    run("cargo-current", ["cargo", "run", "--release", "--quiet"], {"NATIVE_SALT": "100"}, output="107\n")
finally:
    os.close(ready_fd)
    os.close(release_fd)
    if parent.poll() is None:
        os.killpg(parent.pid, signal.SIGTERM)
        parent.wait(timeout=10)
