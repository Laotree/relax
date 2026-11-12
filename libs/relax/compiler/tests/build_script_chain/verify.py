#!/usr/bin/env python3
"""Run on a build node: verify.py <relax binary> <scratch directory>.

`app`'s build script uses `helper_a`'s, which uses `helper_b`'s: three build scripts on one
build-dependency chain, each a legitimate step (cargo's build graph is acyclic). A pure-Rust
chain, so it runs offline anywhere with cargo and no C toolchain.

Before the fix, relax refused depth 3 as "build scripts nest 3 deep (a script that runs itself
again?)" and cargo's output never appeared.
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
assert "scan=b" in baseline.stdout, baseline.stdout

relaxed = run("relax", [binary, "run", "app"])
assert relaxed.stdout == baseline.stdout, "three-level build-script chain differs from cargo"
assert "nest" not in relaxed.stderr, f"the chain was refused as a loop: {relaxed.stderr}"
assert "build script failed" not in relaxed.stderr, relaxed.stderr
print("PASS chain: app -> helper_a -> helper_b build scripts run, and the output matches cargo")
