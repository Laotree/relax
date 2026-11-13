//! The program's executable under the JIT: a hard link of the loader in this run's own folder,
//! `<run dir>/exe/<pid>/<name>` (tests in `deps/`, `.exe` on Windows). argv[0] and current_exe()
//! name it. Its `.relax-exec` file holds the real loader's command line: an external launcher
//! can run it without std's self-exec rewrite. A spawn of RELAX_LOADER still runs the loader's
//! command line as written. Hard links survive canonicalize, keep the loader's code signature
//! on macOS, and take no space beyond a directory entry while the loader file exists.
//!
//! The folder goes when the run exits (os::proc::exit); a run that did not get there (killed)
//! leaves it, and the next run's `link` removes the folders of processes that are gone. They
//! matter: a link keeps an old loader's blocks alive after cargo replaces the binary.
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

static OWN_DIR: OnceLock<PathBuf> = OnceLock::new();

pub enum Kind { Program, Test }

pub struct Executable {
    pub program: PathBuf,
    pub loader: PathBuf,
}

/// This process's link to `loader`, named `name` (a package or binary name), made once; the
/// reason when the run dir's file system cannot hold it (another volume than the loader's).
pub fn link(loader: &Path, name: &str, kind: Kind) -> Result<Executable, String> {
    let root = crate::dirs::relax_dir().join("exe");
    sweep(&root);
    let dir = root.join(std::process::id().to_string());
    let raw = dir.join(format!(".loader{}", std::env::consts::EXE_SUFFIX));
    let reexec = raw.canonicalize().ok().as_deref() == Some(loader);
    if reexec {
        // exec keeps the pid: this loader's directory is still live.
        (|| -> std::io::Result<()> {
            for entry in std::fs::read_dir(&dir)? {
                let entry = entry?;
                if entry.path() == raw { continue; }
                if entry.file_type()?.is_dir() { std::fs::remove_dir_all(entry.path())?; }
                else { std::fs::remove_file(entry.path())?; }
            }
            Ok(())
        })().map_err(|e| format!("{}: {e}", dir.display()))?;
    } else {
        // a folder under this pid is a gone process's (pids are reused)
        let _ = std::fs::remove_dir_all(&dir);
    }
    let artifacts = match kind { Kind::Program => dir.clone(), Kind::Test => dir.join("deps") };
    std::fs::create_dir_all(&artifacts).map_err(|e| format!("{}: {e}", artifacts.display()))?;
    let name: String = name.chars().map(|c| if c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.' { c } else { '_' }).collect();
    let file = if cfg!(windows) { format!("{name}.exe") } else { name };
    let link = artifacts.join(file);
    std::fs::hard_link(loader, &link).map_err(|e| format!("hard link {} of {}: {e}", link.display(), loader.display()))?;
    if !reexec {
        std::fs::hard_link(loader, &raw).map_err(|e| format!("hard link {} of {}: {e}", raw.display(), loader.display()))?;
    }
    let executable = Executable {
        program: link.canonicalize().map_err(|e| format!("{}: {e}", link.display()))?,
        loader: raw.canonicalize().map_err(|e| format!("{}: {e}", raw.display()))?,
    };
    let _ = OWN_DIR.set(dir);
    Ok(executable)
}

fn command_file(exe: &Path) -> PathBuf {
    let mut name = exe.as_os_str().to_os_string();
    name.push(".relax-exec");
    PathBuf::from(name)
}

/// The real loader and its command line, before the program's arguments. External launchers
/// cannot use std's self-exec rewrite, so the executable carries the same replay on disk.
pub fn save(exe: &Path, args: &[String]) -> std::io::Result<()> {
    std::fs::write(command_file(exe), args.join("\0"))
}

/// A hard link's replay, if this is a program executable rather than the loader itself.
pub fn command(exe: &Path) -> std::io::Result<Option<Vec<String>>> {
    match std::fs::read_to_string(command_file(exe)) {
        Ok(text) => Ok(Some(text.split('\0').map(str::to_string).collect())),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

/// Cargo's package binaries beside deps/, for tests that discover them from current_exe().
pub fn bins(env: &[(String, String)], package_dir: &str, package: &str) -> std::io::Result<()> {
    let Some(dir) = OWN_DIR.get() else { return Ok(()) };
    let loader = dir.join(format!(".loader{}", std::env::consts::EXE_SUFFIX));
    let run_dir = std::path::absolute(crate::dirs::relax_dir())?;
    for (key, _) in env {
        let Some(name) = key.strip_prefix("CARGO_BIN_EXE_") else { continue };
        let exe = dir.join(format!("{name}{}", std::env::consts::EXE_SUFFIX));
        std::fs::hard_link(&loader, &exe)?;
        save(&exe, &[
            loader.display().to_string(), "run".into(), "--quiet".into(), "--silent".into(),
            "--no-live".into(), "--run-dir".into(), run_dir.display().to_string(),
            "--workspace-dir".into(), package_dir.into(), package.into(),
            "--bin".into(), name.into(), "--".into(),
        ])?;
    }
    Ok(())
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
