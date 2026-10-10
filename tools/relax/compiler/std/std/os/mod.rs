//! std::os: raw C types; file descriptors and the unix extension traits (unix), handles and the
//! windows extension traits (windows).

#[cfg(unix)]
pub mod fd;
#[cfg(target_os = "linux")]
pub mod linux;
pub mod raw;
#[cfg(unix)]
pub mod unix;
#[cfg(windows)]
pub mod windows;
