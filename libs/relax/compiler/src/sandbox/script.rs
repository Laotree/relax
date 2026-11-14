//! A confined build script's run: under a Host whose compile-time policy is Sandboxed, a script
//! whose closure holds a registry or git package runs its program unit whole as twins, in one
//! arena of the `build-script` domain, entered as the macro world's bridge is (pmhost.rs
//! `call_confined`). The script reaches nothing of the host but this domain's entries:
//! - the environment its parent gave (progenv `given_value`), as arena copies;
//! - its exit handlers, recorded in the arena and called in it (`call_in_arena`);
//! - `exit`, which runs them and ends the run as an exit does.
//!
//! The domain's table has no form that keeps a host function (`entry` returns a replacement or
//! nothing), so no host function's result reaches the script unless an entry made it: every
//! pointer an entry hands back lies in the arena (`ret_arena`), and every pointer it is given is
//! read inside the arena's window. A host address masked into the window would read the arena's
//! bytes at that offset (a flaky crash, garbage): an entry's mistake gives the script NULL.
//!
//! A fault of the script's code ends the child (its masked accesses stay in the window: the
//! process is the boundary), said as the script's (`fault_note`); a panic ends it with 101 after
//! its exit handlers ran (stdout's tail).

use super::*;
use crate::program::DefId;

/// The build-script domain: no fuel (a script's time is the person's to end), the clean-up of
/// the masks always (its twins never tier up).
pub const SCRIPT_DOMAIN: Domain = Domain { name: "build-script", allow: script_allow, fuel: false, clean_up: true };

/// The script arena's module number (the macro world's is u32::MAX).
const SCRIPT_MODULE: u32 = u32::MAX - 1;

/// The confined script's arena (its window base; 0: no confined script in this process).
static ARENA_BASE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The domain's entries as `Allow` sees them: every one a replacement (`entry`).
fn script_allow(name: &str) -> Option<Option<(&'static str, u64)>> {
    entry(name).map(Some)
}

/// The domain's entries: a C name and its replacement. The type has no kept form.
fn entry(name: &str) -> Option<(&'static str, u64)> {
    macro_rules! e {
        ($f:ident) => {
            (stringify!($f), $f as *const () as u64)
        };
    }
    Some(match name {
        "getenv" => e!(sc_getenv),
        "relax_env_snapshot" => e!(sc_env_snapshot),
        "relax_host_getenv" => e!(sc_host_getenv),
        "relax_pm_getenv" => e!(sc_pm_getenv),
        "atexit" => e!(sc_atexit),
        "exit" => e!(sc_exit),
        #[cfg(unix)]
        _ => return files::entry(name),
        #[cfg(not(unix))]
        _ => return None,
    })
}

/// The folders a confined script reaches, as its parent gives them (absolute paths).
pub struct Roots {
    /// folders it reads (its package's source)
    pub read: Vec<Vec<u8>>,
    /// folders it reads and writes (OUT_DIR)
    pub write: Vec<Vec<u8>>,
    /// folders inside those it never reaches (the run's target folder, Relax's cache)
    pub excluded: Vec<Vec<u8>>,
    /// its current folder at the start (the manifest folder, as cargo starts a script)
    pub cwd: Vec<u8>,
}

const ENAMETOOLONG: i32 = if cfg!(target_vendor = "apple") { 63 } else { 36 };

/// A C string of the script's (`p`), copied out of its window: at most 4096 bytes before the NUL
/// (ENAMETOOLONG), never past the window (EFAULT).
fn c_str(p: u64) -> Result<Vec<u8>, i32> {
    // (an unmapped page of the arena faults as the script's own read would: contained)
    let _safe = crate::jit::FaultSafe::enter();
    let pm = m(p);
    if pm == 0 {
        return Err(EFAULT);
    }
    let mut out = Vec::new();
    loop {
        if !fits(pm, out.len() as u64 + 1) {
            return Err(EFAULT);
        }
        let b = unsafe { *((pm + out.len() as u64) as *const u8) };
        if b == 0 {
            return Ok(out);
        }
        out.push(b);
        if out.len() >= 4096 {
            return Err(ENAMETOOLONG);
        }
    }
}

/// Writes `v` through the script's out pointer `p` (false: out of its window).
fn put_u64(p: u64, v: u64) -> bool {
    let _safe = crate::jit::FaultSafe::enter();
    let pm = arena_ptr(p, 8);
    if pm == 0 {
        return false;
    }
    unsafe { std::ptr::write_unaligned(pm as *mut u64, v) };
    true
}

// ------------------------------------------------------------------ environment

/// (arena base, name, its value's NUL-ended arena copy): made at the name's first ask, kept for
/// the arena's life (C's `getenv` contract: a script's own FFI may hold two results)
static INTERNED: Mutex<Vec<(u64, Vec<u8>, u64)>> = Mutex::new(Vec::new());

fn interned(name: &[u8], value: &[u8]) -> u64 {
    let Some(a) = cur_arena() else { return 0 };
    let mut g = INTERNED.lock().unwrap_or_else(|e| e.into_inner());
    if let Some(&(_, _, p)) = g.iter().find(|(b, n, _)| *b == a.base && n == name) {
        return ret_arena(p);
    }
    let p = sb_malloc(value.len() as u64 + 1);
    if p == 0 {
        return 0;
    }
    unsafe {
        std::ptr::copy_nonoverlapping(value.as_ptr(), p as *mut u8, value.len());
        *((p + value.len() as u64) as *mut u8) = 0;
    }
    g.push((a.base, name.to_vec(), p));
    ret_arena(p)
}

/// `getenv`: the names the script's parent gave, nothing of this process's environment.
extern "C" fn sc_getenv(name: u64) -> u64 {
    let Ok(n) = c_str(name) else { return 0 };
    match relax_base::progenv::given_value(&n) {
        Some(v) => interned(&n, &v),
        None => 0,
    }
}

/// std's `vars_os`: the given set, encoded (std copies it under its lock).
extern "C" fn sc_env_snapshot(out: u64, out_len: u64) {
    let b = relax_base::progenv::given_wire();
    let p = ret_arena(give(&b));
    if put_u64(out, p) {
        put_u64(out_len, if p == 0 { 0 } else { b.len() as u64 });
    }
}

/// std's plumbing reads: none of the host's values reach the script.
extern "C" fn sc_host_getenv(_name: u64) -> u64 {
    0
}

/// The proc-macro environment call: not set (a script reads its environment through `getenv`).
extern "C" fn sc_pm_getenv(_key: u64, _len: u64, _out: u64, _out_len: u64) -> i32 {
    1
}

// ------------------------------------------------------------------ exit

/// (arena base, a handler's fn value as the script gave it): `atexit`'s list, last first
static EXITS: Mutex<Vec<(u64, u64)>> = Mutex::new(Vec::new());
/// the handlers ran (a second `exit`, from inside one, goes straight to the end)
static EXITED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

extern "C" fn sc_atexit(f: u64) -> i32 {
    let Some(a) = cur_arena() else { return -1 };
    EXITS.lock().unwrap_or_else(|e| e.into_inner()).push((a.base, f));
    0
}

/// Calls the current arena's exit handlers, last registered first, until none is left (one a
/// handler registers runs too); a handler that panics is reported and the next one runs.
fn run_exit_handlers() {
    let Some(a) = cur_arena() else { return };
    EXITED.store(true, std::sync::atomic::Ordering::SeqCst);
    loop {
        let next = {
            let mut g = EXITS.lock().unwrap_or_else(|e| e.into_inner());
            let i = g.iter().rposition(|(b, _)| *b == a.base);
            i.map(|i| g.remove(i).1)
        };
        let Some(f) = next else { break };
        call_in_arena(f, 0);
    }
}

extern "C" fn sc_exit(code: i32) {
    if !EXITED.load(std::sync::atomic::Ordering::SeqCst) {
        run_exit_handlers();
    }
    end(code)
}

/// The run's end as an exit ends it (jit.rs `recorded_exit`).
fn end(code: i32) -> ! {
    #[cfg(unix)]
    if let Some(f) = crate::jit::loader_symbol(b"exit") {
        let f: extern "C" fn(i32) -> ! = unsafe { std::mem::transmute(f) };
        f(code)
    }
    std::process::exit(code)
}

// ------------------------------------------------------------------ files

/// The file entries: paths go to the broker's walk (broker.rs), fds are the broker's table.
#[cfg(unix)]
mod files {
    use super::super::broker::{c, last_errno, Broker, Fd, Opened};
    use super::*;
    use std::ffi::{c_int, c_void};
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};

    /// The broker of this process's confined script (one per child).
    pub(super) static BROKER: Mutex<Option<Broker>> = Mutex::new(None);

    pub(super) fn entry(name: &str) -> Option<(&'static str, u64)> {
        macro_rules! e {
            ($f:ident) => {
                (stringify!($f), $f as *const () as u64)
            };
        }
        Some(match name {
            "open" => e!(sc_open),
            "close" => e!(sc_close),
            "read" => e!(sc_read),
            "write" => e!(sc_write),
            "pread" => e!(sc_pread),
            "pwrite" => e!(sc_pwrite),
            "lseek" => e!(sc_lseek),
            "fstat" => e!(sc_fstat),
            "stat" => e!(sc_stat),
            "lstat" => e!(sc_lstat),
            "fsync" => e!(sc_fsync),
            "ftruncate" => e!(sc_ftruncate),
            "fchmod" => e!(sc_fchmod),
            "flock" => e!(sc_flock),
            "isatty" => e!(sc_isatty),
            "fcntl" => e!(sc_fcntl),
            "chmod" => e!(sc_chmod),
            "mkdir" => e!(sc_mkdir),
            "rmdir" => e!(sc_rmdir),
            "unlink" => e!(sc_unlink),
            "rename" => e!(sc_rename),
            "readlink" => e!(sc_readlink),
            "realpath" => e!(sc_realpath),
            "getcwd" => e!(sc_getcwd),
            "chdir" => e!(sc_chdir),
            _ => return None,
        })
    }

    extern "C" {
        #[link_name = "read"]
        fn host_read(fd: c_int, buf: *mut c_void, n: usize) -> isize;
        #[link_name = "write"]
        fn host_write(fd: c_int, buf: *const c_void, n: usize) -> isize;
        #[link_name = "pread"]
        fn host_pread(fd: c_int, buf: *mut c_void, n: usize, off: i64) -> isize;
        #[link_name = "pwrite"]
        fn host_pwrite(fd: c_int, buf: *const u8, n: usize, off: i64) -> isize;
        #[link_name = "lseek"]
        fn host_lseek(fd: c_int, off: i64, whence: c_int) -> i64;
        #[cfg_attr(all(target_vendor = "apple", target_arch = "x86_64"), link_name = "fstat$INODE64")]
        #[cfg_attr(not(all(target_vendor = "apple", target_arch = "x86_64")), link_name = "fstat")]
        fn host_fstat(fd: c_int, buf: *mut u8) -> c_int;
        #[link_name = "fsync"]
        fn host_fsync(fd: c_int) -> c_int;
        #[link_name = "ftruncate"]
        fn host_ftruncate(fd: c_int, len: i64) -> c_int;
        #[link_name = "fchmod"]
        fn host_fchmod(fd: c_int, mode: ModeT) -> c_int;
        #[link_name = "flock"]
        fn host_flock(fd: c_int, op: c_int) -> c_int;
        #[link_name = "isatty"]
        fn host_isatty(fd: c_int) -> c_int;
        #[link_name = "fcntl"]
        fn host_fcntl(fd: c_int, cmd: c_int, ...) -> c_int;
    }
    #[cfg(target_vendor = "apple")]
    type ModeT = u16;
    #[cfg(not(target_vendor = "apple"))]
    type ModeT = u32;

    /// An entry's failure: the script's errno, -1.
    fn fail(e: i32) -> i64 {
        set_errno(e)
    }

    /// The broker's answer, or EACCES when this process has none (fail closed).
    fn with<T>(f: impl FnOnce(&mut Broker) -> Result<T, i32>) -> Result<T, i32> {
        match BROKER.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
            Some(b) => f(b),
            None => Err(c::EACCES),
        }
    }

    /// What one of the script's fds is on the host.
    enum On {
        Null,
        Std(RawFd),
        File(RawFd, bool),
    }

    fn on(fd: i32) -> Result<On, i32> {
        with(|b| {
            Ok(match b.fd(fd).ok_or(c::EBADF)? {
                Fd::Null => On::Null,
                Fd::Std(h) => On::Std(*h),
                Fd::File { fd, write } => On::File(fd.as_raw_fd(), *write),
            })
        })
    }

    /// `r` as an entry's result: a host failure is the script's errno.
    fn host(r: i64) -> i64 {
        if r < 0 {
            fail(last_errno())
        } else {
            r
        }
    }

    /// A buffer of the script's: its arena address, or EFAULT.
    fn buf(p: u64, n: u64) -> Result<u64, i32> {
        if n > WINDOW {
            return Err(EFAULT);
        }
        match arena_ptr(p, n) {
            0 => Err(EFAULT),
            a => Ok(a),
        }
    }

    fn path_then(p: u64, f: impl FnOnce(&mut Broker, &[u8]) -> Result<i64, i32>) -> i64 {
        let r = c_str(p).and_then(|p| with(|b| f(b, &p)));
        r.unwrap_or_else(fail)
    }

    fn open_in(path: u64, flags: i32, mode: u32) -> i32 {
        path_then(path, |b, p| {
            let fd = match b.open(p, flags, mode)? {
                Opened::Null => Fd::Null,
                Opened::File { fd, write } => Fd::File { fd, write },
            };
            Ok(b.add_fd(fd, 0) as i64)
        }) as i32
    }

    // the variadic ones (open, fcntl): the next argument is in the next register, except on
    // Apple's arm64, where variadic arguments go on the stack past the eight argument registers
    #[cfg(not(all(target_vendor = "apple", target_arch = "aarch64")))]
    extern "C" fn sc_open(path: u64, flags: i32, mode: u32) -> i32 {
        open_in(path, flags, mode)
    }
    #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
    extern "C" fn sc_open(path: u64, flags: i32, _2: u64, _3: u64, _4: u64, _5: u64, _6: u64, _7: u64, mode: u32) -> i32 {
        open_in(path, flags, mode)
    }

    extern "C" fn sc_close(fd: i32) -> i32 {
        // (a Std fd's entry goes; the child's own stdout stays open)
        match with(|b| b.take_fd(fd).ok_or(c::EBADF)) {
            Ok(_) => 0,
            Err(e) => fail(e) as i32,
        }
    }

    extern "C" fn sc_read(fd: i32, p: u64, n: u64) -> i64 {
        let r = on(fd).and_then(|o| {
            Ok(match o {
                On::Null => 0,
                On::Std(_) => return Err(c::EBADF),
                On::File(h, _) => host(unsafe { host_read(h, buf(p, n)? as *mut c_void, n as usize) } as i64),
            })
        });
        r.unwrap_or_else(fail)
    }

    extern "C" fn sc_write(fd: i32, p: u64, n: u64) -> i64 {
        let r = on(fd).and_then(|o| {
            Ok(match o {
                On::Null => n as i64,
                On::Std(h) | On::File(h, _) => host(unsafe { host_write(h, buf(p, n)? as *const c_void, n as usize) } as i64),
            })
        });
        r.unwrap_or_else(fail)
    }

    extern "C" fn sc_pread(fd: i32, p: u64, n: u64, off: i64) -> i64 {
        let r = on(fd).and_then(|o| match o {
            On::File(h, _) => Ok(host(unsafe { host_pread(h, buf(p, n)? as *mut c_void, n as usize, off) } as i64)),
            _ => Err(c::ESPIPE),
        });
        r.unwrap_or_else(fail)
    }

    extern "C" fn sc_pwrite(fd: i32, p: u64, n: u64, off: i64) -> i64 {
        let r = on(fd).and_then(|o| match o {
            On::File(h, _) => Ok(host(unsafe { host_pwrite(h, buf(p, n)? as *const u8, n as usize, off) } as i64)),
            _ => Err(c::ESPIPE),
        });
        r.unwrap_or_else(fail)
    }

    extern "C" fn sc_lseek(fd: i32, off: i64, whence: i32) -> i64 {
        let r = on(fd).and_then(|o| match o {
            On::Null => Ok(0),
            On::Std(_) => Err(c::ESPIPE),
            On::File(h, _) => Ok(host(unsafe { host_lseek(h, off, whence) })),
        });
        r.unwrap_or_else(fail)
    }

    /// Writes a stat into the script's `struct stat` at `out`.
    fn put_stat(st: &[u8], out: u64) -> Result<i64, i32> {
        let a = buf(out, st.len() as u64)?;
        unsafe { std::ptr::copy_nonoverlapping(st.as_ptr(), a as *mut u8, st.len()) };
        Ok(0)
    }

    extern "C" fn sc_fstat(fd: i32, out: u64) -> i32 {
        let r = on(fd).and_then(|o| {
            let h = match o {
                On::Null => with(|b| Ok(b.null.as_raw_fd()))?,
                On::Std(h) | On::File(h, _) => h,
            };
            let mut st = [0u8; 160];
            if unsafe { host_fstat(h, st.as_mut_ptr()) } != 0 {
                return Err(last_errno());
            }
            put_stat(&st[..c::STAT_SIZE], out)
        });
        r.unwrap_or_else(fail) as i32
    }

    extern "C" fn sc_stat(path: u64, out: u64) -> i32 {
        path_then(path, |b, p| put_stat(b.stat(p, true)?.bytes(), out)) as i32
    }

    extern "C" fn sc_lstat(path: u64, out: u64) -> i32 {
        path_then(path, |b, p| put_stat(b.stat(p, false)?.bytes(), out)) as i32
    }

    /// An fd call on a file the walk opened (`write`: under a write root, else EPERM).
    fn file_call(fd: i32, write: bool, f: impl FnOnce(RawFd) -> c_int) -> i32 {
        let r = on(fd).and_then(|o| match o {
            On::File(h, w) if w || !write => Ok(host(f(h) as i64)),
            On::File(..) => Err(c::EPERM),
            _ => Err(c::EINVAL),
        });
        r.unwrap_or_else(fail) as i32
    }

    extern "C" fn sc_fsync(fd: i32) -> i32 {
        file_call(fd, false, |h| unsafe { host_fsync(h) })
    }

    extern "C" fn sc_ftruncate(fd: i32, len: i64) -> i32 {
        file_call(fd, true, |h| unsafe { host_ftruncate(h, len) })
    }

    extern "C" fn sc_fchmod(fd: i32, mode: u32) -> i32 {
        file_call(fd, true, |h| unsafe { host_fchmod(h, (mode & 0o7777) as ModeT) })
    }

    extern "C" fn sc_flock(fd: i32, op: i32) -> i32 {
        file_call(fd, false, |h| unsafe { host_flock(h, op) })
    }

    extern "C" fn sc_isatty(fd: i32) -> i32 {
        match on(fd) {
            Ok(On::Std(h)) => unsafe { host_isatty(h) },
            Ok(_) => {
                fail(c::ENOTTY);
                0
            }
            Err(e) => {
                fail(e);
                0
            }
        }
    }

    fn fcntl_in(fd: i32, cmd: i32, arg: u64) -> i32 {
        let r = on(fd).and_then(|o| match cmd {
            c::F_GETFD => Ok(c::FD_CLOEXEC as i64),
            c::F_SETFD => Ok(0),
            c::F_GETFL => match o {
                On::Null => Ok(c::O_RDWR as i64),
                On::Std(h) | On::File(h, _) => Ok(host(unsafe { host_fcntl(h, c::F_GETFL) } as i64)),
            },
            c::F_SETFL => match o {
                On::File(h, _) => Ok(host(unsafe { host_fcntl(h, c::F_SETFL, (arg as c_int) & (c::O_NONBLOCK | c::O_APPEND)) } as i64)),
                _ => Err(c::EINVAL),
            },
            c::F_DUPFD | c::F_DUPFD_CLOEXEC => {
                let copy = match o {
                    On::Null => Fd::Null,
                    On::Std(h) => Fd::Std(h),
                    On::File(h, write) => {
                        let d = unsafe { host_fcntl(h, c::F_DUPFD_CLOEXEC, 0 as c_int) };
                        if d < 0 {
                            return Err(last_errno());
                        }
                        Fd::File { fd: unsafe { OwnedFd::from_raw_fd(d) }, write }
                    }
                };
                with(|b| Ok(b.add_fd(copy, (arg as u32).min(i32::MAX as u32) as usize) as i64))
            }
            _ => Err(c::EINVAL),
        });
        r.unwrap_or_else(fail) as i32
    }
    #[cfg(not(all(target_vendor = "apple", target_arch = "aarch64")))]
    extern "C" fn sc_fcntl(fd: i32, cmd: i32, arg: u64) -> i32 {
        fcntl_in(fd, cmd, arg)
    }
    #[cfg(all(target_vendor = "apple", target_arch = "aarch64"))]
    extern "C" fn sc_fcntl(fd: i32, cmd: i32, _2: u64, _3: u64, _4: u64, _5: u64, _6: u64, _7: u64, arg: u64) -> i32 {
        fcntl_in(fd, cmd, arg)
    }

    extern "C" fn sc_chmod(path: u64, mode: u32) -> i32 {
        path_then(path, |b, p| b.chmod(p, mode).map(|()| 0)) as i32
    }

    extern "C" fn sc_mkdir(path: u64, mode: u32) -> i32 {
        path_then(path, |b, p| b.mkdir(p, mode).map(|()| 0)) as i32
    }

    extern "C" fn sc_rmdir(path: u64) -> i32 {
        path_then(path, |b, p| b.remove(p, true).map(|()| 0)) as i32
    }

    extern "C" fn sc_unlink(path: u64) -> i32 {
        path_then(path, |b, p| b.remove(p, false).map(|()| 0)) as i32
    }

    extern "C" fn sc_rename(from: u64, to: u64) -> i32 {
        let r = c_str(from).and_then(|a| c_str(to).and_then(|t| with(|b| b.rename(&a, &t))));
        match r {
            Ok(()) => 0,
            Err(e) => fail(e) as i32,
        }
    }

    extern "C" fn sc_readlink(path: u64, out: u64, size: u64) -> i64 {
        path_then(path, |b, p| {
            let t = b.readlink(p)?;
            let n = t.len().min(size as usize);
            let a = buf(out, n as u64)?;
            unsafe { std::ptr::copy_nonoverlapping(t.as_ptr(), a as *mut u8, n) };
            Ok(n as i64)
        })
    }

    /// `s` and a NUL into the script's buffer `out` of `size` bytes, or a new heap block when
    /// `out` is NULL (the script frees it): its address.
    fn put_path(s: &[u8], out: u64, size: u64, too_long: i32) -> Result<u64, i32> {
        let n = s.len() as u64 + 1;
        let a = if out == 0 {
            match sb_malloc(n) {
                0 => return Err(ENOMEM),
                a => a,
            }
        } else {
            if n > size {
                return Err(too_long);
            }
            buf(out, n)?
        };
        unsafe {
            std::ptr::copy_nonoverlapping(s.as_ptr(), a as *mut u8, s.len());
            *((a + s.len() as u64) as *mut u8) = 0;
        }
        Ok(ret_arena(a))
    }

    const ENOMEM: i32 = 12;
    #[cfg(target_vendor = "apple")]
    const PATH_MAX: u64 = 1024;
    #[cfg(not(target_vendor = "apple"))]
    const PATH_MAX: u64 = 4096;

    extern "C" fn sc_realpath(path: u64, out: u64) -> u64 {
        let r = c_str(path).and_then(|p| with(|b| b.realpath(&p))).and_then(|s| put_path(&s, out, PATH_MAX, c::ENAMETOOLONG));
        r.unwrap_or_else(|e| {
            fail(e);
            0
        })
    }

    extern "C" fn sc_getcwd(out: u64, size: u64) -> u64 {
        let r = with(|b| Ok(b.cwd())).and_then(|s| put_path(&s, out, size, c::ERANGE));
        r.unwrap_or_else(|e| {
            fail(e);
            0
        })
    }

    extern "C" fn sc_chdir(path: u64) -> i32 {
        path_then(path, |b, p| b.chdir(p).map(|()| 0)) as i32
    }
}

// ------------------------------------------------------------------ the run

/// Runs the program of a confined build script (`main_def` of crate `root`) as twins in the
/// script's arena, reaching the folders of `roots` only; its exit code.
pub unsafe fn run_main(up: *mut Unit, root: u32, main_def: DefId, roots: &Roots) -> i32 {
    let package = relax_base::progenv::given_value(b"CARGO_PKG_NAME").map_or_else(|| "a package".to_string(), |v| String::from_utf8_lossy(&v).into_owned());
    let name = format!("the confined build script of {package}");
    if cfg!(windows) {
        eprintln!("relax: {name} cannot run here: confined build scripts need arena windows, which Windows does not have yet (it runs under bare `relax`)");
        return 1;
    }
    // a constructor table would run before main as the platform's start code runs it: the
    // confined run calls none
    match crate::sections::constructor_paths(up, root) {
        Ok(v) if v.is_empty() => {}
        Ok(v) => {
            eprintln!("relax: {name} links constructors ({}), which a confined run does not call: it runs under bare `relax`", v.join(", "));
            return 1;
        }
        Err(e) => {
            eprintln!("relax: {e}");
            return 1;
        }
    }
    #[cfg(unix)]
    match super::broker::Broker::new(roots) {
        Ok(b) => *files::BROKER.lock().unwrap_or_else(|e| e.into_inner()) = Some(b),
        Err(e) => {
            eprintln!("relax: {name} cannot run confined: {e}");
            return 1;
        }
    }
    #[cfg(not(unix))]
    let _ = roots;
    let setup = confine_unit(up, SCRIPT_DOMAIN, &[]).and_then(|()| new_arena(up, SCRIPT_MODULE, &name, (HEAP_END - HEAP_BASE) as u64, 0));
    let arena = match setup {
        Ok(a) => a,
        Err(e) => {
            eprintln!("relax: {name} cannot run confined: {e}");
            return 1;
        }
    };
    // main's twin, or std's start of a main that returns a value with main's twin as its fn value
    let target = crate::owner::call(crate::owner::Class::Program, || -> Result<(u64, u64), String> {
        let u = &mut *up;
        let main_id = u.fn_id(FnKey::Inst(main_def, Vec::new()));
        let (t, arg) = match crate::run::lang_start_slot(u, main_def)? {
            None => (twin(up, main_id), 0),
            Some(start) => (twin(up, start), fn_value(up, main_id)?),
        };
        Ok(((*up).entry(t), arg))
    });
    let (entry, arg) = match target {
        Ok(t) => t,
        Err(e) => {
            eprintln!("relax: {e}");
            return 1;
        }
    };
    let _program = crate::os::program_thread();
    let depth = entry_depth();
    let saved = save();
    if enter_arena(&arena).is_err() {
        eprintln!("relax: {name}: its arena cannot be entered");
        return 1;
    }
    ARENA_BASE.store(arena.base, std::sync::atomic::Ordering::SeqCst);
    let code = match crate::jit::call_jit(up, entry, arg) {
        Ok(_) => 0,
        Err(p) => {
            // (the frames it unwound are gone: the arena is entered again for its exit handlers)
            entry_recover(depth);
            restore(saved);
            eprintln!("relax: main {}: {}", p.kind, p.message);
            if enter_arena(&arena).is_err() {
                return 101;
            }
            101
        }
    };
    run_exit_handlers();
    leave();
    code
}

/// A fault while a confined script runs: (the script's, what to say). The script's when it hit
/// its arena's window or guards from its own code; anything else is Relax's.
pub(crate) fn fault_note(u: &Unit, info: &crate::jit::PanicInfo) -> Option<(bool, String)> {
    let base = ARENA_BASE.load(std::sync::atomic::Ordering::SeqCst);
    if base == 0 {
        return None;
    }
    let in_window = info.fault_addr.wrapping_sub(base - GUARD) < WINDOW + 2 * GUARD;
    let twin_pc = info.frames.first().is_some_and(|pc| {
        let slot = u.code.read().unwrap_or_else(|e| e.into_inner()).slot_at(*pc);
        slot.is_some_and(|s| (s as usize) < u.fns.len() && matches!(u.fns[s as usize].key, FnKey::Sandbox(_)))
    });
    Some(if in_window && twin_pc {
        let off = info.fault_addr.wrapping_sub(base);
        (true, format!("relax: the confined build script faulted inside its arena ({} at {}): it failed, as a script that crashes fails", info.kind, describe_window_offset(off)))
    } else {
        (false, format!("relax: a fault outside the confined build script's arena ({} at {:#x}): a Relax bug, not the script's (report follows)", info.kind, info.fault_addr))
    })
}
