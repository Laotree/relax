//! CEF re-executes this loader for apps hosted by Relax. Share the std-only
//! entry with standalone apps without adding a makepad-cef dependency.
#[path = "../../../libs/cef/src/subprocess.rs"]
mod subprocess;

pub use subprocess::run_helper_if_subprocess as subprocess;
