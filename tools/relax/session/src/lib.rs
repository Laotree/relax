//! Compilation inputs shared by every compiler layer.
pub mod options;
pub mod phase;
pub mod sip;
pub use options::{Options, RuntimeOptions};

/// Immutable compiler and execution policy for one driver invocation.
/// rustc: compiler/rustc_session/src/session.rs:90-93.
#[derive(Default)]
pub struct Session {
    pub options: Options,
    pub runtime: RuntimeOptions,
}
