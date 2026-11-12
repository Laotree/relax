#!/usr/bin/env python3
"""Run on a build node: verify.py <relax binary> <scratch directory>.

`helper`'s build script calls `cnative::answer()` — a C crate it build-depends on. The script runs
as its own `relax run --units … build-script-build` child, which resolves the same native package
but cannot compute the parent's cache key from its smaller unit graph. Before the receipt, the
child refused `cnative` ("built only with --allow-c") and the script never produced its OUT_DIR
file; a flagless check then failed on the missing include.

The fixture proves the whole path: one `--allow-c` run builds the native library and writes the
receipt, and a later `relax check` without the flag compiles the script from it.

Needs cargo and the system C toolchain (like `allow_c`); the only registry dependency is `cc`.
"""
import os
from pathlib import Path
import shutil
import subprocess
import sys

binary = str(Path(sys.argv[1]).resolve())
scratch = Path(sys.argv[2]).resolve()
scratch.mkdir(parents=True, exist_ok=True)
fixture = scratch / "fixture"
shutil.copytree(Path(__file__).parent, fixture,
                ignore=shutil.ignore_patterns("target", "Cargo.lock", "__pycache__"))
env = dict(os.environ, CARGO_INCREMENTAL="0", CARGO_NET_OFFLINE="true",
           CARGO_TARGET_DIR=str(scratch / "cargo"),
           MAKEPAD_RUN_CACHE_DIR=str(scratch / "jit"))


def run(label, args, success=True):
    result = subprocess.run(args, cwd=fixture, env=env, capture_output=True, text=True)
    (scratch / (label + ".stdout")).write_text(result.stdout)
    (scratch / (label + ".stderr")).write_text(result.stderr)
    assert (result.returncode == 0) == success, (
        f"{label}: exit {result.returncode}\n{result.stdout}\n{result.stderr}")
    return result


baseline = run("cargo", ["cargo", "run", "--release", "--quiet", "-p", "app"])
assert baseline.stdout.strip() == "42", baseline.stdout

# One --allow-c run builds cnative with cargo and leaves the receipt for its script children.
first = run("run", [binary, "run", "--allow-c", "app"])
assert first.stdout == baseline.stdout, f"native/JIT fixture output differs from cargo: {first.stderr}"
assert "building native dependencies with cargo" in first.stderr, "cold native build was not exercised"

# The flagless check's build-script child must compile from the receipt, not refuse cnative.
cached = run("check", [binary, "check", "app"])
assert "0 errors" in cached.stderr, cached.stderr
assert ".rs: build script failed" not in cached.stderr, cached.stderr
assert "built only with `--allow-c`" not in cached.stderr, cached.stderr
print("PASS receipt: a build script's own child run compiles from the parent's native outputs")

# Warm --allow-c stays one message, and no cargo run.
warm = run("run-again", [binary, "run", "--allow-c", "app"])
assert warm.stdout == baseline.stdout, warm.stderr
assert "building native dependencies with cargo" not in warm.stderr, "the warm run rebuilt native code"
print("PASS warm: the second --allow-c run reuses the native build")
