# /// script
# requires-python = ">=3.11"
# ///
"""Offline Unix regression: uv run verify.py <relax binary> <new scratch directory>."""
import json
import os
from pathlib import Path
import select
import shlex
import shutil
import signal
import subprocess
import sys
import time

binary = str(Path(sys.argv[1]).resolve())
scratch = Path(sys.argv[2]).resolve()
scratch.mkdir(parents=True)
fixture = scratch / "fixture"
shutil.copytree(Path(__file__).parent, fixture,
                ignore=shutil.ignore_patterns("target", "Cargo.lock", "host", "__pycache__"))
gone = scratch / "compiler-gone"
cc = scratch / "cc"
cc.write_text("#!/bin/sh\nif [ -f " + shlex.quote(str(gone)) + " ]; then echo 'compiler unavailable after parent preparation' >&2; exit 42; fi\nexec /usr/bin/cc \"$@\"\n")
cc.chmod(0o755)
env = dict(os.environ, CC=str(cc), COMPILER_GONE=str(gone), CARGO_NET_OFFLINE="true",
           CARGO_TARGET_DIR=str(scratch / "cargo"), RELAX_CACHE_DIR=str(scratch / "jit"))
for label, command in [
    ("cargo-run", ["cargo", "run", "--release", "--quiet"]),
    ("cargo-test", ["cargo", "test", "--release"]),
    ("relax-run", [binary, "run", "--allow-c", "--quiet", "self-native-receipt"]),
    ("relax-test", [binary, "test", "--allow-c", "self-native-receipt"]),
]:
    gone.unlink(missing_ok=True)
    result = subprocess.run(command, cwd=fixture, env=env, capture_output=True, text=True)
    (scratch / (label + ".stdout")).write_text(result.stdout)
    (scratch / (label + ".stderr")).write_text(result.stderr)
    assert result.returncode == 0, f"{label}: {result.stdout}\n{result.stderr}"
    if label.endswith("run"):
        assert result.stdout == "ok\n", result.stdout
    else:
        assert "2 passed; 0 failed" in result.stdout + result.stderr

gone.unlink()
host_source = Path(__file__).parent / "host"
host_env = dict(env, CARGO_TARGET_DIR=str(scratch / "host-tool"))
host_build = subprocess.run(["cargo", "build", "--release", "--manifest-path", str(host_source / "Cargo.toml")],
                            env=host_env, capture_output=True, text=True)
(scratch / "host-build.stderr").write_text(host_build.stderr)
assert host_build.returncode == 0, host_build.stderr
host_fixture = scratch / "hosted"
shutil.copytree(Path(__file__).parent, host_fixture,
                ignore=shutil.ignore_patterns("target", "Cargo.lock", "host", "__pycache__"))
host_env = dict(env, LIVE_REENTERED="1", RELAX_CACHE_DIR=str(scratch / "hosted-jit"))
host_env.pop("RELAX_RUN_NATIVE", None)
prepared = subprocess.run([binary, "run", "--allow-c", "--quiet", "self-native-receipt", "--", "--live-native", "--once"],
                          cwd=host_fixture, env=host_env, capture_output=True, text=True)
assert prepared.returncode == 0 and prepared.stdout == "7\n", (prepared.stdout, prepared.stderr)
receipts = list((scratch / "hosted-jit").glob("native-scripts-*.json"))
assert len(receipts) == 1, receipts
host_env["RELAX_RUN_NATIVE"] = str(receipts[0])
hosted = subprocess.run([str(scratch / "host-tool/release/self-native-host"), "receipt-hosted", str(host_fixture)],
                        cwd=host_fixture, env=host_env, capture_output=True, text=True)
(scratch / "hosted.stdout").write_text(hosted.stdout)
(scratch / "hosted.stderr").write_text(hosted.stderr)
assert hosted.returncode == 0 and hosted.stdout == "7\n9\n", f"hosted relaunch kept stale native build: {hosted.stdout!r}\n{hosted.stderr}"

with (scratch / "live.stderr").open("w") as stderr:
    child = subprocess.Popen([binary, "run", "--allow-c", "--quiet", "self-native-receipt", "--", "--live-native"],
                             cwd=fixture, env=env, stdout=subprocess.PIPE, stderr=stderr, start_new_session=True)
    def live_line():
        assert select.select([child.stdout], [], [], 60)[0], "native relaunch produced no output"
        value = child.stdout.readline()
        with (scratch / "live.stdout").open("ab") as output:
            output.write(value)
        return value
    try:
        assert live_line() == b"7\n"
        source = fixture / "cnative/build.rs"
        source.write_text(source.read_text().replace("const SALT: i32 = 0;", "const SALT: i32 = 2;"))
        native = subprocess.run(["cargo", "run", "--release", "--quiet", "--", "--live-native", "--once"],
                                cwd=fixture, env=env, capture_output=True, text=True)
        assert native.returncode == 0 and native.stdout == "9\n", (native.stdout, native.stderr)
        deadline = time.monotonic() + 60
        while True:
            pending = subprocess.run([binary, "inspect", str(child.pid), "session", "pending", "--json"],
                                     env=env, capture_output=True, text=True)
            if any(json.loads(line).get("restart_pending", 0) > 0 for line in pending.stdout.splitlines()):
                break
            assert time.monotonic() < deadline, (pending.stdout, pending.stderr)
            time.sleep(.1)
        result = subprocess.run([binary, "inspect", str(child.pid), "session", "relaunch", "--json"],
                                env=env, capture_output=True, text=True)
        assert result.returncode == 0 or (result.returncode == 2 and "connection closed by the peer" in result.stderr), (result.returncode, result.stdout, result.stderr)
        assert live_line() == b"9\n", "explicit relaunch reused the prepared native build"
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
