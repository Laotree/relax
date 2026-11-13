#!/usr/bin/env python3
"""Failed required scripts must not admit/replay a passing check verdict.

Run with an absolute path to the Relax runner. Uses only std and a temporary
workspace; rustc/Cargo is the oracle for the failing build script.
"""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile

binary = str(Path(sys.argv[1]).resolve())
std = str(Path(__file__).resolve().parents[2] / 'std')
root = Path(tempfile.mkdtemp(prefix='relax-check-script-'))
(root / 'src').mkdir()
(root / 'Cargo.toml').write_text(
    '[package]\nname="script-status"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
(root / 'src/lib.rs').write_text('pub fn answer() -> u32 { 42 }\n')
healthy = 'fn main() { println!("cargo:rustc-cfg=script_ran"); }\n'
broken = 'fn main() { panic!("required-script-failure-probe"); }\n'
env = dict(os.environ, CARGO_NET_OFFLINE='true', RELAX_OFFLINE='1', RELAX_STD=std,
           RELAX_CACHE_DIR=str(root / 'cache'), CARGO_TARGET_DIR=str(root / 'native-target'))


def run(name, command):
    p = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        output, _ = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        output, _ = p.communicate()
        raise AssertionError(f'{name} timed out:\n{output}')
    finally:
        # A script/native tier must not outlive the command this regression owned.
        try:
            os.killpg(p.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    (root / f'{name}.log').write_text(output)
    print(f'{name}: exit={p.returncode}\n{output}', flush=True)
    return p.returncode, output


print(f'check_script_failure evidence: {root}', flush=True)
results = []
(root / 'build.rs').write_text(healthy)
for name in ['healthy-cold', 'healthy-warm']:
    rc, _ = run(name, [binary, 'check', 'script-status'])
    results.append((name, rc == 0))
(root / 'build.rs').write_text(broken)
rc, text = run('native-failure', ['cargo', 'check', '--offline', '--release'])
results.append(('native-failure', rc == 101 and 'required-script-failure-probe' in text))
for name in ['failure-after-green', 'failure-repeat']:
    rc, text = run(name, [binary, 'check', 'script-status'])
    results.append((name, rc != 0 and 'required-script-failure-probe' in text))
(root / 'build.rs').write_text(healthy)
rc, _ = run('recovery', [binary, 'check', 'script-status'])
results.append(('recovery', rc == 0))
assert all(ok for _, ok in results), results
print('check_script_failure: ok (healthy cold/warm, failure after green/repeat, recovery)')
