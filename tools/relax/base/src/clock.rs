//! Clocks of the front end's statistics: CPU time of the calling thread (compile-time numbers
//! robust to machine load) and a process-wide monotonic wall clock.

// Share the clock with the optimiser: build and pass totals must use the same Windows
// cycle calibration (and Unix thread CPU clock).
pub use relax_codegen::cpu_ns;

/// Wall time in ns since the first call of it in this process.
pub fn wall_ns() -> u64 {
    static T0: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    T0.get_or_init(std::time::Instant::now).elapsed().as_nanos() as u64
}

// Why this thread is working (type-checking bodies, parsing lazily): RELAX_TYCK_STATS /
// RELAX_LAZY_STATS attribute their numbers by it.
thread_local! { pub static TYS_ORIGIN: std::cell::Cell<&'static str> = const { std::cell::Cell::new("?") }; }

/// Names why this thread type-checks bodies until the guard drops (the previous name is
/// restored): RELAX_TYCK_STATS / RELAX_LAZY_STATS attribute checks and lazy parses by it.
pub fn origin(o: &'static str) -> OriginGuard {
    OriginGuard(TYS_ORIGIN.with(|c| c.replace(o)))
}

pub struct OriginGuard(&'static str);

impl Drop for OriginGuard {
    fn drop(&mut self) {
        TYS_ORIGIN.with(|c| c.set(self.0));
    }
}

/// When `relax run` started (its boot timeline and reports count from here).
static T0: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();

/// Starts the run clock (once; later calls keep the first time).
pub fn mark_start() {
    let _ = T0.set(std::time::Instant::now());
}

/// Milliseconds since `mark_start` (0 before it).
pub fn ms_since_start() -> f64 {
    T0.get().map(|t| t.elapsed().as_secs_f64() * 1e3).unwrap_or(0.0)
}

// Separate from the historical run/phase clock: includes loader setup before cmd_run.
// Each executable marks this at entry, so child launches never inherit their parent's origin.
static PROCESS_START: std::sync::OnceLock<(std::time::SystemTime, std::time::Instant)> = std::sync::OnceLock::new();

pub fn mark_process_start() {
    PROCESS_START.get_or_init(|| (std::time::SystemTime::now(), std::time::Instant::now()));
}

/// Epoch seconds at executable entry, for an in-process program's first-present clock.
pub fn process_start_epoch() -> f64 {
    mark_process_start();
    PROCESS_START.get().unwrap().0.duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_secs_f64()
}

pub fn ms_since_process_start() -> f64 {
    mark_process_start();
    PROCESS_START.get().unwrap().1.elapsed().as_secs_f64() * 1e3
}
