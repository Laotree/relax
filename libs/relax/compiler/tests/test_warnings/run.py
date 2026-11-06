#!/usr/bin/env python3
"""`makepad test` prints the warnings of the code under test, as `cargo test` does: run.py
/absolute/path/to/makepad.

src/t.rs's test has an unused import, an unused `let` and an unused `Result`: `cargo test` prints
3 warnings (the JIT printed none). The unused import is not judged by test runs yet (they record no
import uses): each run's summary line says so (check.rs TEST_UNCHECKED), and the other 2 print.
1. A first run prints the 2 and the summary.
2. An unchanged rerun (its check is stored whole) prints them again, as cargo replays a fresh
   crate's warnings.
3. A run after an edit elsewhere in the crate checks it again and prints them.
4. `makepad test --live`: the first verdict's check prints them, and a save that adds an unused
   `let` to the test prints the test's warnings with its patch line, the new one among them.
Prints "test_warnings: ok" or "test_warnings: FAILED (...)"."""
import os
from pathlib import Path
import shutil
import signal
import subprocess as sp
import sys
import tempfile
import time

binary = str(Path(sys.argv[1]).resolve())
here = Path(__file__).resolve().parent
WANT = ["warning: unused variable: `unused`", "warning: unused `Result` that must be used",
         "makepad test: 2 warnings (unused_imports, "]


def fail(why, out=""):
    print("test_warnings: FAILED (%s)" % why)
    print("\n".join(out.splitlines()[-30:]))
    sys.exit(1)


def missing(out, want):
    return [w for w in want if not any(w in line for line in out.splitlines())]


with tempfile.TemporaryDirectory(prefix="test-warnings-") as tmp:
    pkg = Path(tmp) / "pkg"
    pkg.mkdir()
    shutil.copy(here / "Cargo.toml", pkg / "Cargo.toml")
    shutil.copytree(here / "src", pkg / "src")
    env = dict(os.environ, MAKEPAD_RUN_CACHE_DIR=str(Path(tmp) / "cache"))

    def run(step):
        p = sp.run([binary, "test", "test-warnings"], cwd=pkg, env=env, stdout=sp.PIPE, stderr=sp.STDOUT, text=True)
        out = p.stdout
        if p.returncode != 0 or "test result: ok. 1 passed" not in out:
            fail("%s: the test did not pass" % step, out)
        if missing(out, WANT):
            fail("%s: no %s" % (step, ", ".join(missing(out, WANT))), out)
        n = sum(1 for line in out.splitlines() if ": warning: " in line)
        if n != 2:
            fail("%s: %d warnings, want 2" % (step, n), out)

    run("first run")
    run("unchanged rerun")
    lib = pkg / "src" / "lib.rs"
    lib.write_text(lib.read_text().replace("x / 2", "x >> 1"))
    run("run after an edit of lib.rs")

    log = Path(tmp) / "live.log"
    with open(log, "w") as f:
        p = sp.Popen([binary, "test", "--live", "test-warnings"], cwd=pkg, env=env, stdout=f, stderr=sp.STDOUT, start_new_session=True)
    try:
        def wait(cond, secs):
            end = time.time() + secs
            while time.time() < end:
                if cond(log.read_text(errors="replace")):
                    return True
                if p.poll() is not None:
                    return cond(log.read_text(errors="replace"))
                time.sleep(0.2)
            return False
        if not wait(lambda out: any(line.startswith("testverdict group=0") for line in out.splitlines()), 300):
            fail("--live: no first verdict", log.read_text(errors="replace"))
        out = log.read_text(errors="replace")
        if missing(out, WANT):
            fail("--live: the first check printed no %s" % ", ".join(missing(out, WANT)), out)
        t = pkg / "src" / "t.rs"
        time.sleep(1.1)
        t.write_text(t.read_text().replace("    let unused = 3;\n", "    let unused = 3;\n    let unused2 = 4;\n"))
        if not wait(lambda out: "t.rs: patched" in out and "unused variable: `unused2`" in out, 60):
            fail("--live: the save's patch line came without the new `let`'s warning", log.read_text(errors="replace"))
        lines = log.read_text(errors="replace").splitlines()
        at = next(i for i, line in enumerate(lines) if "t.rs: patched" in line)
        gone = missing("\n".join(lines[at + 1:at + 6]), ["warning: unused variable: `unused2`", "warning: unused variable: `unused`", "warning: unused `Result` that must be used"])
        if gone:
            fail("--live: after the patch line, no %s" % ", ".join(gone), "\n".join(lines))
    finally:
        try:
            os.killpg(p.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            p.wait(timeout=10)
        except sp.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
print("test_warnings: ok")
