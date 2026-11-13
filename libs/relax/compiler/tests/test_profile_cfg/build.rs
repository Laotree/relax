fn main() {
    println!("cargo:rustc-env=BUILD_DEBUG={}", cfg!(debug_assertions));
}
