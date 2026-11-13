//! std::process: Command, Child, Stdio, exit/abort/id. The OS half is selected here:
//! process_unix.rs (posix_spawnp / fork+exec) or process_windows.rs (CreateProcessW) or process_web.rs (none); all expose
//! the same public API.

#[cfg(unix)]
#[path = "process_unix.rs"]
mod imp;
#[cfg(windows)]
#[path = "process_windows.rs"]
mod imp;
#[cfg(target_family = "wasm")]
#[path = "process_web.rs"]
mod imp;

pub use imp::*;

/// Whether `word`, the first argument of a spawn of the loader's executable, is one of the
/// loader's commands (the run fact RELAX_SELF_EXEC_COMMANDS, from the runner's command list):
/// `$RELAX_LOADER run [flags] <package> ...` or `... app <id>` starts another program, `... export`
/// asks for a source tree, `... check <dir>` and `... test` check or test a package, and so on;
/// those run as written. Any other spawn of it runs this program again (`self_exec_args`). A host
/// that states no list (one older than this std) gets every spawn of the loader run as written:
/// a missing list never turns a loader command into a re-run of this program, which could start
/// itself without end.
#[cfg(any(unix, windows))]
fn loader_command(word: &crate::ffi::OsStr) -> bool {
    match crate::env::host_var_os("RELAX_SELF_EXEC_COMMANDS") {
        Some(words) => words.as_encoded_bytes().split(|&b| b == 0x1f).any(|w| w == word.as_encoded_bytes()),
        None => true,
    }
}
