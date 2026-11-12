fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-env=HELPER_A={}", helper_b::scan());
}
