# /// script
# requires-python = ">=3.11"
# ///
"""uv run verify.py <relax binary> <new scratch directory>; Unix only."""
import os
from pathlib import Path
import select
import shutil
import signal
import subprocess
import sys

runner = str(Path(sys.argv[1]).resolve())
scratch = Path(sys.argv[2]).resolve()
fixture = scratch / "fixture"
shutil.copytree(Path(__file__).parent, fixture,
                ignore=shutil.ignore_patterns("target", "Cargo.lock", "__pycache__"))
env = dict(os.environ, CARGO_NET_OFFLINE="true", RELAX_CACHE_DIR=str(scratch / "jit"),
           CARGO_TARGET_DIR=str(scratch / "cargo"))
native = subprocess.run(["cargo", "run", "--release", "--quiet", "--", "--once"],
                        cwd=fixture, env=env, capture_output=True, text=True)
assert native.returncode == 0 and native.stdout == "1\n", (native.stdout, native.stderr)
with (scratch / "relax.stderr").open("w") as stderr:
    child = subprocess.Popen([runner, "run", "--quiet", "live-exec"], cwd=fixture,
                             env=env, stdout=subprocess.PIPE, stderr=stderr, start_new_session=True)
    def line(message):
        assert select.select([child.stdout], [], [], 60)[0], message
        value = child.stdout.readline()
        with (scratch / "live.stdout").open("ab") as output:
            output.write(value)
        return value
    try:
        assert line("self-exec did not reach main") == b"1\n"
        source = fixture / "src/main.rs"
        source.write_text(source.read_text().replace("fn value() -> usize { 1 }", "fn value() -> usize { 2 }"))
        assert line("self-exec no longer observes live source edits") == b"2\n"
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
