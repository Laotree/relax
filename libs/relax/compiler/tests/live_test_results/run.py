#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Run with `uv run run.py <relax binary>`. Read live test results without terminal parsing."""
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
fixture = Path(__file__).parent / "pkg"

with tempfile.TemporaryDirectory(prefix="live-test-results-") as tmp:
    root = Path(tmp)
    pkg = root / "pkg"
    shutil.copytree(fixture, pkg)
    source = pkg / "src/lib.rs"
    with source.open("a") as f:
        for i in range(320):
            f.write(f"\n#[test]\nfn extra_{i:03}() {{ assert_eq!(2 + 2, 4); }}\n")
    env = dict(os.environ, TMPDIR=str(root), RELAX_PANIC_PARK="0")
    with (root / "run.log").open("w") as log:
        process = subprocess.Popen(
            [runner, "test", "--live", "live-verdict-example", "--lib", "--", "--skip", "filtered"],
            cwd=pkg, env=env, stdout=log, stderr=log, start_new_session=True,
        )
        try:
            deadline = time.monotonic() + 300
            pid = None
            while time.monotonic() < deadline:
                listed = subprocess.run([runner, "inspect", "list", "--json"], env=env,
                                        capture_output=True, text=True, check=True)
                entries = [json.loads(line) for line in listed.stdout.splitlines()]
                runs = [entry for entry in entries if entry.get("app") == "live-verdict-example"]
                if runs:
                    assert len(runs) == 1, runs
                    pid = runs[0]["pid"]
                    break
                assert process.poll() is None, "live session exited before discovery"
                time.sleep(0.05)
            assert pid is not None, "live session did not publish an inspect endpoint"

            def watch(kind, since):
                answer = subprocess.run(
                    [runner, "inspect", str(pid), "watch", f"on={kind}", f"since={since}",
                     "timeout_s=30", "--json"],
                    env=env, capture_output=True, text=True, check=True, timeout=45,
                )
                events = [json.loads(line) for line in answer.stdout.splitlines()]
                event = next((e for e in events if e.get("event") == kind), None)
                assert event is not None, f"missing {kind}: {events}"
                return event

            def results(event):
                assert "results" in event, "testverdict omits the individual results query"
                answer = subprocess.run(
                    [runner, "inspect", str(pid), *event["results"].split(), "--json"],
                    env=env, capture_output=True, text=True, check=True, timeout=30,
                )
                rows = [json.loads(line) for line in answer.stdout.splitlines()]
                header = next(r for r in rows if "test_count" in r)
                assert header == {"group": event["group"], "test_count": 324}, header
                tests = [r for r in rows if "name" in r]
                assert len(tests) == 324, tests
                return {t["name"]: (t["status"], t["ran"]) for t in tests}

            initial = watch("testverdict", 0)
            assert results(initial) == {
                "value_is_one": ("passed", True),
                "independent": ("passed", True),
                "ignored": ("ignored", False),
                "filtered": ("filtered", False),
                **{f"extra_{i:03}": ("passed", True) for i in range(320)},
            }, initial
            base = source.read_text()
            source.write_text(base.replace("{ 1 }", "{ 2 }"))
            failed = watch("testverdict", initial["seq"])
            assert failed["group"] > initial["group"] and not failed["restarted"], failed
            assert any(path.endswith("src/lib.rs") for path in failed["edit"]), failed
            assert results(failed) == {
                "value_is_one": ("failed", True),
                "independent": ("passed", False),
                "ignored": ("ignored", False),
                "filtered": ("filtered", False),
                **{f"extra_{i:03}": ("passed", False) for i in range(320)},
            }, failed
            stale = subprocess.run(
                [runner, "inspect", str(pid), "test-results", f"group={initial['group']}", "full=1", "--json"],
                env=env, capture_output=True, text=True, timeout=30,
            )
            stale_rows = [json.loads(line) for line in stale.stdout.splitlines()]
            assert any("test results are for group" in r.get("err", "") for r in stale_rows), stale_rows
            assert not any("name" in r for r in stale_rows), stale_rows
            source.write_text(base.replace("{ 1 }", "{ missing_symbol() }"))
            refused = watch("patchrefused", failed["seq"])
            assert any("missing_symbol" in reason for reason in refused["reasons"]), refused
            source.write_text(base)
            recovered = watch("testverdict", refused["seq"])
            assert results(recovered)["value_is_one"] == ("passed", True), recovered
            assert recovered["failed"] == 0, recovered
            print("live_test_results: PASS (324 results, default verdict limit, affected failure, stale group, build refusal, recovery)")
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
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
