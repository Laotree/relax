#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""A const's unused panic path does not restart unrelated edits; its value dependencies do."""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

runner = str(Path(sys.argv[1]).resolve())
with tempfile.TemporaryDirectory(prefix="live-const-panic-") as tmp:
    root = Path(tmp)
    pkg = root / "pkg"
    shutil.copytree(Path(__file__).parent / "pkg", pkg)
    env = dict(os.environ, TMPDIR=str(root), RELAX_PANIC_PARK="0")
    with (root / "run.log").open("w") as log:
        process = subprocess.Popen([runner, "test", "--live", "live-const-example", "--lib"],
                                   cwd=pkg, env=env, stdout=log, stderr=log, start_new_session=True)
        try:
            def query(*args):
                result = subprocess.run([runner, "inspect", *map(str, args), "--json"], env=env,
                                        capture_output=True, text=True, timeout=90, check=True)
                return [json.loads(line) for line in result.stdout.splitlines()]
            pid = None
            deadline = time.monotonic() + 300
            while time.monotonic() < deadline:
                runs = [r for r in query("list") if r.get("app") == "live-const-example"]
                if runs:
                    assert len(runs) == 1, runs
                    pid = runs[0]["pid"]
                    break
                assert process.poll() is None, "live session exited before discovery"
                time.sleep(0.05)
            assert pid is not None, "no inspect endpoint"

            def event(since):
                rows = query(pid, "watch", "on=testverdict,patchrefused", f"since={since}", "timeout_s=30")
                return next(r for r in rows if r.get("event") in ("testverdict", "patchrefused"))

            initial_rows = query(pid, "watch", "on=testverdict", "since=0", "timeout_s=30")
            initial = next(r for r in initial_rows if r.get("event") == "testverdict")
            assert initial["passed"] == 1 and initial["failed"] == 0, initial
            source = pkg / "src/lib.rs"
            base = source.read_text()
            source.write_text(base.replace("usize { 1 }", "usize { 2 }"))
            failed = event(initial["seq"])
            assert failed["event"] == "testverdict", f"unused panic path forced a restart: {failed}"
            assert not failed["restarted"] and failed["failures"] == ["result"], failed
            source.write_text(base)
            recovered = event(failed["seq"])
            assert recovered["event"] == "testverdict" and not recovered["restarted"], recovered
            assert recovered["passed"] == 1 and recovered["failed"] == 0, recovered
            source.write_text(base.replace("return i + 3", "return i + 4"))
            dependency = event(recovered["seq"])
            assert dependency["event"] == "patchrefused" and dependency["outcome"] == "restart", dependency
            print("live_const_panic: PASS (unrelated body patched, failure, recovery, const dependency restart)")
        except BaseException:
            print((root / "run.log").read_text(), file=sys.stderr)
            raise
        finally:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
