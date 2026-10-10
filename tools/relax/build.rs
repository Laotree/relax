//! The loader's build: RELAX_PROVENANCE (build_stamp.rs: content hashes of the packages this
//! binary compiles, never git state) and the source identity of each provided crate.
use std::path::PathBuf;

#[path = "base/src/json.rs"]
#[allow(dead_code)]
mod json;
#[path = "base/src/srchash.rs"]
mod srchash;
#[path = "build_stamp.rs"]
mod build_stamp;
use build_stamp::vfs;

/// The crates this binary provides (src/main.rs registers them).
const PROVIDED: &[&str] = &[
    "relax-provided-fixture",
    "makepad-live-id",
    "makepad-script",
    "makepad-script-std",
    "makepad-script-census",
    "makepad-script-compute",
    "makepad-shader",
    "makepad-tween-script",
    "makepad-script-audio-aot",
];

fn main() {
    // Windows: Relax runs the program's main on the process's main thread; give it the 8 MiB
    // macOS and Linux main threads have (a PE's default reserve is 1-2 MiB)
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("windows") {
        if std::env::var("CARGO_CFG_TARGET_ENV").as_deref() == Ok("msvc") {
            println!("cargo:rustc-link-arg-bins=/STACK:8388608");
        } else {
            println!("cargo:rustc-link-arg-bins=-Wl,--stack,8388608");
        }
    }
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=build_stamp.rs");
    let dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let g = build_stamp::graph(&dir);
    // the loader's closure holds the provided crates' closures: their files are watched here
    println!("cargo:rustc-env=RELAX_PROVENANCE={}", g.provenance(&dir, ""));
    // RELAX_SRC_<crate>: the source identity (srchash.rs) of each provided crate as this build
    // compiles it (its resolved features and dependencies)
    // RELAX_PROVIDED: `<package>=<feature>,..;..`, each provided crate with the features this
    // build compiles it with (`relax host-gen` reads it with them; `host-shims` only selects the
    // shim file itself)
    let mut provided = Vec::new();
    for name in PROVIDED {
        let root = g.pkgs.iter().position(|p| p.name == *name).unwrap_or_else(|| panic!("{} is not a dependency", name));
        println!("cargo:rustc-env=RELAX_SRC_{}={:016x}", name.replace('-', "_"), srchash::closure_hash(&g.pkgs, root));
        let mut features: Vec<&str> = g.pkgs[root].features.iter().map(String::as_str).filter(|f| *f != "host-shims").collect();
        features.sort();
        provided.push(format!("{}={}", name, features.join(",")));
    }
    println!("cargo:rustc-env=RELAX_PROVIDED={}", provided.join(";"));
}
