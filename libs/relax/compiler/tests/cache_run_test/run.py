# /// script
# requires-python = ">=3.11"
# ///
"""run.py <runner> <scratch root>: run and test must share a cache correctly."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

if len(sys.argv) != 3:
    raise SystemExit(__doc__)
runner = str(Path(sys.argv[1]).resolve())
root = Path(sys.argv[2]).resolve()
root.mkdir(parents=True, exist_ok=True)
with tempfile.TemporaryDirectory(prefix='cache-run-test-', dir=root) as temporary:
    scratch = Path(temporary)
    fixture = scratch / 'fixture'
    shutil.copytree(Path(__file__).resolve().parent, fixture,
                    ignore=shutil.ignore_patterns('target', 'Cargo.lock', '__pycache__'))
    env = dict(os.environ, CARGO_NET_OFFLINE='true', CARGO_INCREMENTAL='0',
               CARGO_HOME=str(scratch / 'cargo-home'), CARGO_TARGET_DIR=str(scratch / 'cargo'))
    Path(env['CARGO_HOME']).mkdir()
    def run(label, command, cache=None):
        child_env = dict(env)
        if cache is not None:
            child_env['RELAX_CACHE_DIR'] = str(scratch / cache)
        result = subprocess.run(command, cwd=fixture, env=child_env, capture_output=True, text=True)
        print(label, result.returncode, flush=True)
        print(result.stdout, end='', flush=True)
        print(result.stderr, end='', file=sys.stderr, flush=True)
        assert result.returncode == 0, f'{label}: exit {result.returncode}'
        return result
    run('lock', ['cargo', 'generate-lockfile', '--offline'])
    native = run('rustc', ['cargo', 'test', '--release', '--locked'])
    assert 'test result: ok. 1 passed' in native.stdout, 'native control did not execute'
    cold = run('fresh-test', [runner, 'test', 'cc'], 'fresh')
    assert 'test result: ok. 1 passed' in cold.stdout, 'fresh JIT control did not execute'
    output = run('run', [runner, 'run', '--quiet', '--silent', 'cc'], 'shared')
    assert output.stdout == '[7, 7, 7]\n', f'run output: {output.stdout!r}'
    warm = run('test-after-run', [runner, 'test', 'cc'], 'shared')
    assert 'test result: ok. 1 passed' in warm.stdout, 'shared JIT test did not execute'
    reverse = run('run-after-test', [runner, 'run', '--quiet', '--silent', 'cc'], 'fresh')
    assert reverse.stdout == '[7, 7, 7]\n', f'reverse run output: {reverse.stdout!r}'
