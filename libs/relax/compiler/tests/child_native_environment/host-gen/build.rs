fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(nested_home_configured)");
    if std::path::Path::new(&std::env::var_os("HOME").unwrap()).file_name().is_some_and(|s| s == "configured-home") {
        println!("cargo:rustc-cfg=nested_home_configured");
    }
}
