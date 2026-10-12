//! `relax`: the plain-Rust command line (no embedder registrations).
fn main() {
    let _phase = relax_compiler::zone_alloc::compiler();
    relax_compiler::clock::mark_process_start();
    let args: Vec<String> = std::env::args_os().map(|a| a.to_string_lossy().into_owned()).collect();
    // a build script's RUSTC (Relax itself) asked for its version
    if relax_compiler::relax_as_rustc() {
        return;
    }
    // a child started in a virtual folder of a git repository run gets the mount table
    if let Err(e) = relax_compiler::vfs::mount_from_env() {
        eprintln!("makepad: RELAX_VFS: {e}");
        std::process::exit(2);
    }
    let sess = relax_compiler::session_from_env(&args);
    relax_compiler::cli_main(&sess);
}
