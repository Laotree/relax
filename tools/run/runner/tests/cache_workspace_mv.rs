//! The cache reuse gates for Target B (issue #170, PR #176): a rebuild at the same path must
//! reuse every store, and after the identity logicalization a workspace copied to a new path must
//! reuse them too. The second test is ignored until that change lands; it is the progress bar.
use std::path::{Path, PathBuf};
use std::process::Command;

fn tmp(tag: &str) -> PathBuf {
    let d = std::env::temp_dir().join(format!("relax-mv-{}-{}", tag, std::process::id()));
    let _ = std::fs::remove_dir_all(&d);
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn write_pkg(dir: &Path) {
    std::fs::create_dir_all(dir.join("src")).unwrap();
    std::fs::write(dir.join("Cargo.toml"), "[package]\nname = \"tbapp\"\nversion = \"0.1.0\"\nedition = \"2021\"\n").unwrap();
    std::fs::write(dir.join("src/main.rs"), "fn value() -> u32 { 41 + 1 }\nfn main() { println!(\"{}\", value()); }\n").unwrap();
}

fn run(bin: &Path, pkg: &Path, cache: &Path) -> String {
    let out = Command::new(bin)
        .arg("run")
        .arg("tbapp")
        .current_dir(pkg)
        .env("RELAX_CACHE_DIR", cache)
        .env("RELAX_SHARED_CACHE", "off")
        .output()
        .expect("run relax");
    assert!(out.status.success(), "relax run failed: {}", String::from_utf8_lossy(&out.stderr));
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stores(cache: &Path) -> usize {
    std::fs::read_dir(cache.join("cache"))
        .map(|rd| rd.flatten().filter(|e| e.file_name().to_string_lossy().contains(".rcs")).count())
        .unwrap_or(0)
}

/// The control for the `mv` progress test: the same path builds once, and the second run reuses
/// every store. A future `mv` failure can then be read as "identities not logical yet" rather
/// than "the cache is broken".
#[test]
fn a_rebuild_at_the_same_path_recompiles_nothing() {
    let bin = Path::new(env!("CARGO_BIN_EXE_relax"));
    let pkg = tmp("same");
    let cache = tmp("same-cache");
    write_pkg(&pkg);
    assert_eq!(run(bin, &pkg, &cache).trim(), "42");
    let first = stores(&cache);
    assert!(first > 0, "the first run wrote stores");
    assert_eq!(run(bin, &pkg, &cache).trim(), "42");
    assert_eq!(stores(&cache), first, "a rebuild at the same path added stores");
    let _ = std::fs::remove_dir_all(&pkg);
    let _ = std::fs::remove_dir_all(&cache);
}

/// Progress bar for the identity logicalization (#176): copy the workspace to a new path and the
/// second run must reuse every store. Ignored until that change lands.
#[test]
#[ignore = "identity logicalization pending (#176): keys still name the worktree"]
fn a_workspace_copied_to_a_new_path_recompiles_nothing() {
    let bin = Path::new(env!("CARGO_BIN_EXE_relax"));
    let pkg = tmp("mv-a");
    let cache = tmp("mv-cache");
    write_pkg(&pkg);
    assert_eq!(run(bin, &pkg, &cache).trim(), "42");
    let first = stores(&cache);
    let moved = pkg.with_file_name(format!("{}-moved", pkg.file_name().unwrap().to_string_lossy()));
    let _ = std::fs::remove_dir_all(&moved);
    std::fs::create_dir_all(&moved).unwrap();
    write_pkg(&moved);
    assert_eq!(run(bin, &moved, &cache).trim(), "42");
    assert_eq!(stores(&cache), first, "a workspace copied to a new path added stores");
    let _ = std::fs::remove_dir_all(&pkg);
    let _ = std::fs::remove_dir_all(&moved);
    let _ = std::fs::remove_dir_all(&cache);
}
