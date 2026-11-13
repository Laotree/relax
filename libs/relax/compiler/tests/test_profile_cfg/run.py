# /// script
# requires-python = ">=3.11"
# ///
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

runner = str(Path(sys.argv[1]).resolve())
here = Path(__file__).resolve().parent
cases = [
    ("default", "", [], "debug,dep-debug,build-debug,macro-debug,host-dep-debug", "debug_only"),
    ("optimized test", "[profile.test]\nopt-level = 3\n", [], "debug,dep-debug,build-debug,macro-debug,host-dep-debug", "debug_only"),
    ("disabled", "[profile.test]\ndebug-assertions = false\n", [], "", "release_only"),
    ("inherited", "[profile.dev]\ndebug-assertions = false\n", [], "", "release_only"),
    ("root override", "[profile.test]\ndebug-assertions = false\n[profile.test.package.test-profile-cfg]\ndebug-assertions = true\n", [], "debug,build-debug", "debug_only"),
    ("dependency override", '[profile.test.package.profile-dep]\ndebug-assertions = false\n', [], "debug,build-debug,macro-debug", "debug_only"),
    ("wildcard override", '[profile.test.package."*"]\ndebug-assertions = false\n', [], "debug,build-debug", "debug_only"),
    ("build override", "[profile.test.build-override]\ndebug-assertions = false\n", [], "debug,dep-debug", "debug_only"),
    ("release", "", ["--release"], "", "release_only"),
    ("release override", "[profile.release]\ndebug-assertions = true\n", ["--release"], "debug,dep-debug,build-debug,macro-debug,host-dep-debug", "debug_only"),
    ("custom", '[profile.checked]\ninherits = "release"\ndebug-assertions = true\n', ["--profile", "checked"], "debug,dep-debug,build-debug,macro-debug,host-dep-debug", "debug_only"),
    ("native custom", '[profile.checked]\ninherits = "release"\ndebug-assertions = true\n', ["--profile", "checked"], "debug,dep-debug,build-debug,macro-debug,host-dep-debug,native", "debug_only"),
    ("native custom equals", '[profile.checked]\ninherits = "release"\ndebug-assertions = true\n', ["--profile=checked"], "debug,dep-debug,build-debug,macro-debug,host-dep-debug,native", "debug_only"),
]

with tempfile.TemporaryDirectory(prefix="test-profile-cfg-") as tmp:
    pkg = Path(tmp) / "pkg"
    shutil.copytree(here, pkg)
    manifest = (here / "Cargo.toml").read_text()
    env = dict(os.environ, RELAX_CACHE_DIR=str(Path(tmp) / "cache"))
    for label, profile, flags, features, selected in cases:
        (pkg / "Cargo.toml").write_text(manifest + "\n" + profile)
        native_flags = ["--allow-c"] if "native" in features.split(",") else []
        for command in (["cargo", "test", "--lib"], [runner, "test", *native_flags, "test-profile-cfg", "--lib"]):
            result = subprocess.run(command + flags + ["--features", features], cwd=pkg, env=env,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(f"{label}: {' '.join(command)}\n{result.stdout}", flush=True)
            other = "release_only" if selected == "debug_only" else "debug_only"
            assert result.returncode == 0, f"{label}: {command[0]} failed"
            assert f"test {selected} ... ok" in result.stdout, f"{label}: missing {selected}"
            assert f"test {other} ..." not in result.stdout, f"{label}: selected {other}"
            assert "2 passed; 0 failed" in result.stdout, f"{label}: wrong test count"
print("test_profile_cfg: ok")
