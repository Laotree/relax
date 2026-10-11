//! CEF re-executes this loader for apps hosted by Relax. Share the std-only
//! entry with standalone apps without adding a makepad-cef dependency.
#[path = "../../../libs/cef/src/subprocess.rs"]
mod subprocess;

pub use subprocess::run_helper_if_subprocess as subprocess;

/// The one `mallinfo` for libcef (libs/cef/src/malloc_compat.rs, root cause in its header),
/// exported from this executable (build.rs) so the dynamic linker binds libcef's import here.
#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[path = "../../../libs/cef/src/malloc_compat.rs"]
mod malloc_compat;

#[cfg(all(target_os = "linux", target_env = "gnu"))]
#[no_mangle]
pub extern "C" fn mallinfo() -> malloc_compat::Mallinfo {
    malloc_compat::saturating_mallinfo()
}
