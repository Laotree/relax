//! libmakepad.so: the Relax host as an Android shared library. The APK's host Activity
//! (dev.makepad.run.RunActivity) loads it and boots the packed app on the phone: the app's crate
//! graph is compiled by Relax from the source store in the APK, and the `Java_dev_makepad_android_*`
//! functions of makepad's Android backend (platform/src/os/linux/android) become the native methods
//! of `dev.makepad.android.MakepadNative`, registered by `RegisterNatives` (jni.rs). Nothing in
//! the host library is makepad: the app, the platform and its Android backend are all compiled
//! source.
//!
//! - [`boot`]: compile the exported functions of a package, from a checkout or a source archive.
//! - `jni` (Android): the Activity's natives, registration of the app's, the progress status.
//! - `logcat` (Android): the compiler's and the program's stdout/stderr lines go to logcat.
//! - `makepad_cli_main`: Relax's command line, for the APK's executable (build scripts run as it).

pub mod boot;
#[cfg(target_os = "android")]
mod jni;
#[cfg(target_os = "android")]
mod logcat;

/// The APK's executable (libmakepad_exe.so, android_exe) calls this with its own arguments: Relax
/// running itself again, which is what every build script is.
#[no_mangle]
pub extern "C" fn makepad_cli_main(argc: std::ffi::c_int, argv: *const *const std::ffi::c_char) {
    let args: Vec<Vec<u8>> = (0..argc.max(0) as usize)
        .map(|i| unsafe { std::ffi::CStr::from_ptr(*argv.add(i)) }.to_bytes().to_vec())
        .collect();
    #[cfg(target_os = "android")]
    jni::name_host_library();
    relax::run_with_args(args);
}
