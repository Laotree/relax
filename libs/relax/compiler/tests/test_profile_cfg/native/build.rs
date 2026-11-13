use std::process::Command;

fn main() {
    let out = std::env::var("OUT_DIR").unwrap();
    let source = format!("{out}/probe.c");
    let object = format!("{out}/probe.o");
    let archive = format!("{out}/libprofile_native.a");
    std::fs::write(&source, "int profile_value(void) { return 7; }\n").unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    assert!(Command::new(cc).args(["-fPIC", "-c", &source, "-o", &object]).status().unwrap().success());
    assert!(Command::new("ar").args(["crs", &archive, &object]).status().unwrap().success());
    println!("cargo:rustc-link-search=native={out}");
    println!("cargo:rustc-link-lib=static=profile_native");
}
