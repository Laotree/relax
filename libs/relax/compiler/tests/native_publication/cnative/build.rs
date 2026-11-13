use std::process::Command;
fn main() {
    println!("cargo:rerun-if-changed=value.c");
    println!("cargo:rerun-if-env-changed=NATIVE_SALT");
    let salt: i32 = std::env::var("NATIVE_SALT").unwrap_or_else(|_| "0".into()).parse().unwrap();
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
