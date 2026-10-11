//! Compilation inputs shared by every compiler layer.
pub mod options;
pub mod phase;
pub mod sip;
pub mod gen_local;
pub use options::{Options, RuntimeOptions};

/// memlane swap: forget the compiler generation's state held in this crate's statics;
/// called with every compiler thread quiesced, right before the old generation is destroyed.
pub fn zone_reset() {
    sip::zone_reset();
}

#[test]
fn zone_reset_fresh_process() {
    const CHILD: &str = "RELAX_ZONE_RESET_TEST_CHILD";
    if std::env::var_os(CHILD).is_some() {
        zone_reset();
        zone_reset();
        return;
    }
    // Other tests use these statics; the reset and its empty-state assertions need isolation.
    let status = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "zone_reset_fresh_process"])
        .env(CHILD, "1")
        .status().unwrap();
    assert!(status.success());
}

/// Immutable compiler and execution policy for one driver invocation.
/// rustc: compiler/rustc_session/src/session.rs:90-93.
#[derive(Default)]
pub struct Session {
    pub options: Options,
    pub runtime: RuntimeOptions,
}
