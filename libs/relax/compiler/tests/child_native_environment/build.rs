const VERSION: u8 = 0;
fn main() {
    assert!(std::process::Command::new("rustdoc").arg("--version").output().unwrap().status.success());
    assert!(host_gen::configured(), "nested build script lost Cargo HOME configuration");
    println!("cargo:rustc-check-cfg=cfg(home_configured)");
    if std::path::Path::new(&std::env::var_os("HOME").unwrap()).file_name().is_some_and(|s| s == "configured-home") {
        println!("cargo:rustc-cfg=home_configured");
    }
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(fixture_built)");
    println!("cargo:rustc-cfg=fixture_built");
    println!("cargo:rustc-env=CHILD_FIXTURE_BUILD=prepared");
    println!("cargo:rustc-env=ROOT_VERSION={VERSION}");
}
