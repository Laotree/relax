fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-env=APP_SCAN={}", helper_a::scan());
}
