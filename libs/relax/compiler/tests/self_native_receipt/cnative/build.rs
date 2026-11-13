use std::process::Command;
const SALT: i32 = 0;
fn main() {
    println!("cargo:rerun-if-changed=value.c");
    let salt = SALT;
    println!("cargo:rustc-env=NATIVE_SALT={salt}");
    let source = std::fs::read_to_string("value.c").unwrap();
    println!("cargo:rustc-env=NATIVE_SOURCE={}", if source.contains("return 7") { 7 } else { 9 });
    let out = std::env::var("OUT_DIR").unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());
    assert!(Command::new(cc).args(["-fPIC", "-c", "value.c", &format!("-DSALT={salt}"), "-o", &format!("{out}/value.o")]).status().unwrap().success());
    assert!(Command::new("ar").args(["crs", &format!("{out}/libcnative.a"), &format!("{out}/value.o")]).status().unwrap().success());
    println!("cargo:rustc-link-search=native={out}");
    println!("cargo:rustc-link-lib=static=cnative");
}
