fn main() {
    cc::Build::new().file("csrc/answer.c").compile("cnative");
    println!("cargo:rerun-if-changed=csrc/answer.c");
}
