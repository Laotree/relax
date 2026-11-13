// Compiles csrc/*.c with the system C compiler ($CC or cc) into one static library in OUT_DIR, one
// member per file, as the cc crate would, and links it.
use std::process::Command;
fn main() {
    let out = std::env::var("OUT_DIR").unwrap();
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let lib = format!("{out}/libacu.a");
    let _ = std::fs::remove_file(&lib);
    let mut ar = Command::new("ar");
    ar.args(["crs", &lib]);
    for name in ["used", "unused", "needed", "helper"] {
        let obj = format!("{out}/{name}.o");
        assert!(Command::new(&cc).args(["-O2", "-fPIC", "-c", &format!("csrc/{name}.c"), "-o", &obj]).status().expect("cc").success(), "cc failed");
        ar.arg(&obj);
        println!("cargo:rerun-if-changed=csrc/{name}.c");
    }
    assert!(ar.status().expect("ar").success(), "ar failed");
    println!("cargo:rustc-link-search=native={out}");
    println!("cargo:rustc-link-lib=static=acu");
}
