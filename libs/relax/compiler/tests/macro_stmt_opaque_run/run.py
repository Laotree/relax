#!/usr/bin/env python3
"""A generated body must retain NtStmt bounds on the lazy `relax run` path.

Single-file `relax test` parses bodies eagerly, so it cannot guard this path.
Run with an absolute path to the release Relax runner; only std is required.
"""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile

binary = str(Path(sys.argv[1]).resolve())
std = str(Path(__file__).resolve().parents[2] / 'std')
root = Path(tempfile.mkdtemp(prefix='relax-stmt-lazy-'))
(root / 'src').mkdir()
(root / 'Cargo.toml').write_text(
    '[package]\nname="opaque-stmt-run"\nversion="0.0.0"\nedition="2021"\n[workspace]\n')
(root / 'src/main.rs').write_text('''
macro_rules! generated_function {
    ($name:ident, $value:ident, $s:stmt) => {
        fn $name() -> u32 {
            let mut $value = 0u32;
            $s
            $value
        }
    };
}
generated_function!(generated, value, value += 3);
fn main() { println!("generated={}", generated()); }
''')
env = dict(os.environ, CARGO_NET_OFFLINE='true', RELAX_OFFLINE='1', RELAX_STD=std,
           RELAX_CACHE_DIR=str(root / 'cache'), CARGO_TARGET_DIR=str(root / 'target'))


def run(name, command):
    p = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        stdout, stderr = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        stdout, stderr = p.communicate()
        raise AssertionError(f'{name} timed out:\n{stdout}\n{stderr}')
    finally:
        try:
            os.killpg(p.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    (root / f'{name}.stdout').write_text(stdout)
    (root / f'{name}.stderr').write_text(stderr)
    print(f'{name}: exit={p.returncode}\n{stdout}\n{stderr}', flush=True)
    return p.returncode, stdout, stderr


print(f'macro_stmt_opaque_run evidence: {root}', flush=True)
rc, stdout, stderr = run('native-build', [os.environ.get('RUSTC', 'rustc'),
                                      '--edition=2021', '-O', 'src/main.rs', '-o', 'native'])
assert rc == 0, stderr
rc, stdout, stderr = run('native-run', [str(root / 'native')])
assert rc == 0 and stdout == 'generated=3\n', (rc, stdout, stderr)
for name in ['jit-initial', 'jit-repeat']:
    rc, stdout, stderr = run(name, [binary, 'run', '--quiet', 'opaque-stmt-run'])
    assert rc == 0 and stdout == 'generated=3\n', (name, rc, stdout, stderr)
print('macro_stmt_opaque_run: ok (native oracle, lazy generated body initial/repeat)')
