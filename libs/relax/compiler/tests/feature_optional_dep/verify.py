#!/usr/bin/env python3
"""Run on a build node: verify.py <relax binary> <scratch directory>.

`wrapper` has an optional dependency `extra` and an explicit feature of the same name that hides
the implicit one (`extra = ["dep:extra"]`). Its `fast` feature asks for `extra/boost`: cargo reads
a strong `x/f` as also enabling the package's feature `x` (which is why `num`'s default features
can use `num-rational`'s `BigRational`), so `cfg(feature = "extra")` holds and `boosted()`
compiles. Relax used to switch the dependency on without enabling the feature, so the app saw no
`boosted` and failed with E0425.

A pure-Rust fixture: no registry dependencies, so it runs offline anywhere with cargo.
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

relaxed = run("relax", [binary, "run", "app"])
assert relaxed.stdout == baseline.stdout, (
    f"a strong `extra/boost` did not enable the feature `extra`: {relaxed.stderr}")
assert "boosted" not in relaxed.stderr, relaxed.stderr
print("PASS optional dependency: a strong `x/f` enables the package's explicit feature `x`")
