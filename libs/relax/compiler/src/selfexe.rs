//! The program's own executable under the JIT: a hard link of the loader in this run's own folder,
//! `<run dir>/exe/<pid>/<name>` (`<name>.exe` on Windows), which the program's argv[0] and
//! std::env::current_exe() name. A spawn of that path runs this program again (std
//! process_unix.rs / process_windows.rs `self_exec_args`: RELAX_SELF_EXEC starts with it); a spawn
//! of the loader by any other name (RELAX_LOADER, an installed `makepad`) runs the loader's command
//! line as written, whatever its first word. A hard link, not a symlink or a copy: canonicalize
//! keeps its name, the OS runs it as the loader (the same file, so the same code signature on
//! macOS), and it takes no space beyond a directory entry while the loader file exists.
//!
//! The folder also holds the run's command line (`LINE`, RELAX_SELF_EXEC's value), so a launch of
//! the link that did not come through Relax std's spawn (`sh -c "exec $EXE ..."`, a C library's
//! exec) runs this program again too: the loader started by that path finds the line beside
//! itself (`relaunched`), as std's spawn would have put it before the arguments.
//!
//! The folder goes when the run exits (os::proc::exit); a run that did not get there (killed)
//! leaves it, and the next run's `link` removes the folders of processes that are gone. They
//! matter: a link keeps an old loader's blocks alive after cargo replaces the binary.
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

static OWN_DIR: OnceLock<PathBuf> = OnceLock::new();

/// This process's link to `loader`, named `name` (a package or binary name), made once; the
/// reason when the run dir's file system cannot hold it (another volume than the loader's).
pub fn link(loader: &Path, name: &str) -> Result<PathBuf, String> {
    let root = crate::dirs::relax_dir().join("exe");
    sweep(&root);
    let dir = root.join(std::process::id().to_string());
    // an exec of the program's own executable is this process going on (its pid) in a new image,
    // which runs from the link in this folder: that link is its own executable still (removing
    // the folder took the file it runs from, the new link found no loader, and a spawn of
    // current_exe() failed: not found, 11-13)
    if dir.canonicalize().is_ok_and(|d| loader.starts_with(d)) {
        let _ = OWN_DIR.set(dir);
        return Ok(loader.to_path_buf());
    }
    // a folder under this pid is a gone process's (pids are reused)
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    let _ = OWN_DIR.set(dir.clone());
    let name: String = name.chars().map(|c| if c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.' { c } else { '_' }).collect();
    let file = if cfg!(windows) { format!("{name}.exe") } else { name };
    let link = dir.join(file);
    std::fs::hard_link(loader, &link).map_err(|e| format!("hard link {} of {}: {e}", link.display(), loader.display()))?;
    link.canonicalize().map_err(|e| format!("{}: {e}", link.display()))
}

/// The command line beside the link: a name no link has (`link` keeps a name's letters, digits,
/// `-`, `_` and `.`).
const LINE: &str = "+self-exec";

/// Writes this run's command line (RELAX_SELF_EXEC's words, up to and with `--`) beside its link.
pub fn set_line(words: &[String]) -> Result<(), String> {
    let dir = OWN_DIR.get().ok_or("no link was made")?;
    std::fs::write(dir.join(LINE), words.join("\u{1f}")).map_err(|e| format!("{}: {e}", dir.join(LINE).display()))
}

/// A launch of a run's link whose arguments do not start with the run's command line (Relax std's
/// spawn and exec put it after argv[0], an exec without the `--silent` at its index 2): `args`
/// with that line after argv[0], as std's spawn gives them. None for any other launch of the
/// loader. (The arguments, not RELAX_SELF_EXEC, tell: a C library's exec passes this process's
/// own environment, which names it, with the program's arguments alone.)
pub fn relaunched(args: &[Vec<u8>]) -> Option<Vec<Vec<u8>>> {
    let exe = std::env::current_exe().ok()?;
    let line = std::fs::read(exe.parent()?.join(LINE)).ok()?;
    let mut out: Vec<Vec<u8>> = line.split(|&b| b == 0x1f).map(<[u8]>::to_vec).collect();
    let rest = args.get(1..).unwrap_or_default();
    let mut unsilenced = out[1..].to_vec();
    if unsilenced.get(1).is_some_and(|w| w == b"--silent") {
        unsilenced.remove(1);
    }
    if rest.starts_with(&out[1..]) || rest.starts_with(&unsilenced) {
        return None;
    }
    out[0] = args.first()?.clone();
    out.extend(rest.iter().cloned());
    Some(out)
}

/// Removes this process's folder (os::proc::exit). On Windows the link of a re-run that still
/// runs from it stays; the next run's sweep takes it.
pub fn remove() {
    if let Some(d) = OWN_DIR.get() {
        let _ = std::fs::remove_dir_all(d);
    }
}

/// The folders of processes that are gone.
fn sweep(root: &Path) {
    let Ok(entries) = std::fs::read_dir(root) else { return };
    for e in entries.flatten() {
        let Some(pid) = e.file_name().to_str().and_then(|s| s.parse::<u32>().ok()) else { continue };
        if pid != std::process::id() && !alive(pid) {
            let _ = std::fs::remove_dir_all(e.path());
        }
    }
}

#[cfg(unix)]
fn alive(pid: u32) -> bool {
    extern "C" {
        fn kill(pid: i32, sig: i32) -> i32;
    }
    const EPERM: i32 = 1;
    let signalled = unsafe { kill(pid as i32, 0) } == 0;
    signalled || std::io::Error::last_os_error().raw_os_error() == Some(EPERM)
}

#[cfg(windows)]
fn alive(pid: u32) -> bool {
    #[link(name = "kernel32")]
    extern "system" {
        fn OpenProcess(access: u32, inherit: i32, pid: u32) -> *mut core::ffi::c_void;
        fn GetExitCodeProcess(process: *mut core::ffi::c_void, code: *mut u32) -> i32;
        fn CloseHandle(handle: *mut core::ffi::c_void) -> i32;
    }
    const PROCESS_QUERY_LIMITED_INFORMATION: u32 = 0x1000;
    const STILL_ACTIVE: u32 = 259;
    unsafe {
        let h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, 0, pid);
        if h.is_null() {
            // another user's process is there, only not ours to query
            const ERROR_ACCESS_DENIED: i32 = 5;
            return std::io::Error::last_os_error().raw_os_error() == Some(ERROR_ACCESS_DENIED);
        }
        let mut code = 0u32;
        let running = GetExitCodeProcess(h, &mut code) != 0 && code == STILL_ACTIVE;
        CloseHandle(h);
        running
    }
}
