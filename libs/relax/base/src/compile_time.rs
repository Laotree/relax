//! What third-party packages' compile-time code may do: one policy per process, chosen by the
//! entry point (relax-runner Host `compile_time_code`), read by the proc-macro host
//! (relax-compiler pmhost.rs) and by the build-script runs (relax-front unitgraph.rs).

/// What compile-time code of third-party packages may do (proc macros and build scripts).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Policy {
    /// it runs as host code with the person's rights, as cargo runs it (bare `relax`)
    Open,
    /// code whose closure includes a registry or git package runs confined (`makepad run`)
    Sandboxed,
}

/// 0 = Sandboxed (the default when no entry point chose), 1 = Open
static POLICY: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

/// The entry point's policy, before any crate graph loads.
pub fn set_policy(p: Policy) {
    POLICY.store((p == Policy::Open) as u8, std::sync::atomic::Ordering::Relaxed);
}

pub fn policy() -> Policy {
    if POLICY.load(std::sync::atomic::Ordering::Relaxed) == 1 { Policy::Open } else { Policy::Sandboxed }
}
