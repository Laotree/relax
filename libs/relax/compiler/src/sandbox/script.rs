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
        _ => return None,
    })
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

// ------------------------------------------------------------------ the run

/// Runs the program of a confined build script (`main_def` of crate `root`) as twins in the
/// script's arena; its exit code.
pub unsafe fn run_main(up: *mut Unit, root: u32, main_def: DefId) -> i32 {
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
