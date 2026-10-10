//! Opt-in work counts at first present; no wall-clock comparisons on shared hosts.
use std::sync::{OnceLock, atomic::{AtomicU64, Ordering}};

static ENABLED: OnceLock<bool> = OnceLock::new();
static COUNTS: [AtomicU64; 7] = [const { AtomicU64::new(0) }; 7];
pub const NORMALIZE: usize = 0;
pub const NORMALIZE_SKIPPED: usize = 1;
pub const IMPL_GOALS: usize = 2;
pub const IMPL_PROBES: usize = 3;
pub const IMPL_REJECTED: usize = 4;
pub const RECURSION_SCANS: usize = 5;
pub const ENV_INTERNS: usize = 6;

#[inline]
pub fn count(kind: usize) {
    if *ENABLED.get_or_init(|| std::env::var_os("RELAX_SOLVER_WORK_TRACE").is_some()) {
        COUNTS[kind].fetch_add(1, Ordering::Relaxed);
    }
}

pub fn report() {
    if !*ENABLED.get_or_init(|| std::env::var_os("RELAX_SOLVER_WORK_TRACE").is_some()) { return; }
    let names = ["normalize", "normalize_skipped", "impl_goals", "impl_probes", "impl_rejected", "recursion_scans", "env_interns"];
    for (name, count) in names.iter().zip(&COUNTS) {
        eprintln!("relax-solver-work: {name}={}", count.load(Ordering::Relaxed));
    }
}
