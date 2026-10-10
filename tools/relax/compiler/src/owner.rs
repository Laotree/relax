//! Unit calls (local/agent_state/fast-rust/JIT_THREADS.md): every step that reads or changes a
//! unit's mutable state is one call -- a region with a class saying whose work it is. They run
//! under the unit lock (jit::lock_unit, re-entrant) for now; the owner thread takes them over.

/// Whose work a unit call is.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Class {
    /// asked by a pure job (a constant's value for a type check, code tables for a report)
    Job = 0,
    /// a back end's result (store, install)
    Finish = 1,
    /// the program's main thread
    Main = 2,
    /// other program threads, patches, the run's own foreground needs
    App = 3,
    /// speculation, tiers, seeds, teardown, completion, monitors: gives way to the others
    Background = 4,
}

/// A program thread's class: Main on the program's main thread, App elsewhere.
pub fn program_class() -> Class {
    if crate::jit::MAIN_TID.load(std::sync::atomic::Ordering::Relaxed) == crate::os::thread::current() { Class::Main } else { Class::App }
}

/// Is this thread inside a unit call (it may read and change the unit)?
pub fn is_owner() -> bool {
    crate::jit::lock_depth() > 0
}

/// Releases the lock levels taken since `depth` when dropped (also when the call unwinds).
struct Hold(u32);
impl Drop for Hold {
    fn drop(&mut self) {
        crate::jit::unlock_to(self.0);
    }
}

fn take(class: Class, quick: bool) -> Hold {
    let depth = crate::jit::lock_depth();
    if quick {
        crate::jit::lock_unit_quick();
    } else if class == Class::Background {
        crate::jit::lock_bg();
    } else {
        crate::jit::lock_unit();
    }
    Hold(depth)
}

/// Runs `f` as a unit call and returns its result.
#[track_caller]
pub fn call<R>(class: Class, f: impl FnOnce() -> R) -> R {
    let _h = take(class, false);
    f()
}

/// `call` for work that reads no slot identity (the startup identities stay encoded).
#[track_caller]
pub fn call_quick<R>(class: Class, f: impl FnOnce() -> R) -> R {
    let _h = take(class, true);
    f()
}

/// `call`, unless it cannot start within `ms` (None).
#[track_caller]
pub fn call_within<R>(_class: Class, ms: u64, f: impl FnOnce() -> R) -> Option<R> {
    let depth = crate::jit::lock_depth();
    let t0 = std::time::Instant::now();
    while !crate::jit::try_lock_unit() {
        if t0.elapsed().as_millis() as u64 >= ms {
            return None;
        }
        std::thread::sleep(std::time::Duration::from_micros(200));
    }
    let _h = Hold(depth);
    Some(f())
}
