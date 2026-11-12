fn main() {
    // a build script that calls into a native crate: it runs as its own `relax run` child, so it
    // needs the native outputs and library the parent built (native.rs `write_receipt`)
    let out = std::env::var("OUT_DIR").unwrap();
    std::fs::write(
        std::path::Path::new(&out).join("generated.rs"),
        format!("pub const GENERATED: i32 = {};\n", cnative::answer()),
    ).unwrap();
}
