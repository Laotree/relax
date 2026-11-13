# /// script
# requires-python = ">=3.11"
# ///
"""Offline regression: uv run verify.py <relax binary> <scratch directory>."""
import os
import json
from pathlib import Path
import shutil
import select
import signal
import subprocess
import sys
import time

binary = str(Path(sys.argv[1]).resolve())
scratch = Path(sys.argv[2]).resolve()
scratch.mkdir(parents=True, exist_ok=True)
fixture = scratch / "fixture"
shutil.copytree(Path(__file__).parent, fixture,
                ignore=shutil.ignore_patterns("target", "Cargo.lock", "__pycache__"))
cc = scratch / "prepared-cc"
cc.write_text("#!/bin/sh\nif [ \"$1\" = --version ]; then printf 'prepared compiler\\n'; exit 0; fi\nexec cc \"$@\"\n")
cc.chmod(0o755)
env = dict(os.environ, CARGO_NET_OFFLINE="true", CARGO_INCREMENTAL="0", CC=str(cc), CHILD_NATIVE_TOKEN="required",
           CARGO_TARGET_DIR=str(scratch / "cargo"), RELAX_CACHE_DIR=str(scratch / "jit"))
for label, command in [("cargo", ["cargo", "test", "--release"]),
                       ("relax", [binary, "test", "--allow-c", "child-native-fixture"])]:
    result = subprocess.run(command, cwd=fixture, env=env, capture_output=True, text=True)
    (scratch / (label + ".stdout")).write_text(result.stdout)
    (scratch / (label + ".stderr")).write_text(result.stderr)
    assert result.returncode == 0, f"{label}: {result.stdout}\n{result.stderr}"
    assert "4 passed; 0 failed" in result.stdout + result.stderr

for mode in ["--nested", "--shell-nested"]:
    for label, command in [("cargo", ["cargo", "run", "--release", "--quiet", "--", mode]),
                           ("relax", [binary, "run", "--allow-c", "--quiet", "child-native-fixture", "--", mode])]:
        result = subprocess.run(command, cwd=fixture, env=env, capture_output=True, text=True)
        (scratch / (label + mode + ".stdout")).write_text(result.stdout)
        (scratch / (label + mode + ".stderr")).write_text(result.stderr)
        assert result.returncode == 0, result.stderr
        assert result.stdout == "5\n", result.stdout

def native_live_control(expected):
    result = subprocess.run(["cargo", "run", "--release", "--quiet", "--", "--live-native", "--once"],
                            cwd=fixture, env=env, capture_output=True, text=True)
    assert result.returncode == 0 and result.stdout == expected, (result.stdout, result.stderr)

native_live_control("5:0:0\n")
with (scratch / "live-native.stderr").open("w") as stderr:
    child = subprocess.Popen([binary, "run", "--allow-c", "--quiet", "child-native-fixture", "--", "--live-native"],
                             cwd=fixture, env=env, stdout=subprocess.PIPE, stderr=stderr, start_new_session=True)
    def live_line():
        assert select.select([child.stdout], [], [], 60)[0], "native relaunch did not produce output"
        value = child.stdout.readline()
        with (scratch / "live-native.stdout").open("ab") as output:
            output.write(value)
        return value
    try:
        assert live_line() == b"5:0:0\n"
        for file, old, new in [(fixture / "build.rs", "const VERSION: u8 = 0;", "const VERSION: u8 = 2;"),
                               (fixture / "cnative/build.rs", "const DELTA: i32 = 0;", "const DELTA: i32 = 2;")]:
            file.write_text(file.read_text().replace(old, new))
        native_live_control("7:2:2\n")
        deadline = time.monotonic() + 60
        while True:
            pending = subprocess.run([binary, "inspect", str(child.pid), "session", "pending", "--json"], env=env, capture_output=True, text=True)
            if any(json.loads(line).get("restart_pending", 0) > 0 for line in pending.stdout.splitlines()):
                break
            assert time.monotonic() < deadline, (pending.stdout, pending.stderr)
            time.sleep(.1)
        result = subprocess.run([binary, "inspect", str(child.pid), "session", "relaunch", "--json"], env=env, capture_output=True, text=True)
        (scratch / "live-native-relaunch.stdout").write_text(result.stdout)
        (scratch / "live-native-relaunch.stderr").write_text(result.stderr)
        # Terminal relaunch execs before replying, so the inspect socket may close. The
        # changed program output below, rather than that acknowledgement, proves restart.
        assert result.returncode == 0 or (result.returncode == 2 and "connection closed by the peer" in result.stderr), (result.returncode, result.stdout, result.stderr)
        assert live_line() == b"7:2:2\n", "relaunch reused stale native outputs or runtime build variables"
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
