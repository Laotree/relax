//! The host Activity's natives (dev.makepad.run.RunActivity) and the registration of the app's.
//!
//! `RunActivity.boot(..)` starts the boot on a thread of its own and returns: the UI thread never
//! waits for the compile. When Relax has compiled the exported functions of the package, the thread
//! binds every `native` method of `dev.makepad.android.MakepadNative` to the function of the same
//! JNI-mangled name (`RegisterNatives`; the method list, with signatures, is made by reflection in
//! Java), after telling the compiled platform which JavaVM it is in (`jni_on_load`).
//! The Java side starts MakepadActivity only when `status()` says "ready".

use crate::boot::{self, Boot, Source};
use crate::logcat;
use makepad_jni_sys as sys;
use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::path::PathBuf;
use std::sync::atomic::{AtomicPtr, Ordering};

static VM: AtomicPtr<sys::JavaVM> = AtomicPtr::new(std::ptr::null_mut());

#[link(name = "android")]
extern "C" {
    fn AAssetManager_fromJava(env: *mut sys::JNIEnv, asset_manager: sys::jobject) -> *mut c_void;
    fn AAssetManager_open(manager: *mut c_void, name: *const c_char, mode: c_int) -> *mut c_void;
    fn AAsset_openFileDescriptor64(asset: *mut c_void, start: *mut i64, length: *mut i64) -> c_int;
    fn AAsset_close(asset: *mut c_void);
}

extern "C" {
    fn dlopen(name: *const c_char, flags: c_int) -> *mut c_void;
    fn close(fd: c_int) -> c_int;
}

const RTLD_NOW: c_int = 2;
const RTLD_NOLOAD: c_int = 4;
/// AASSET_MODE_UNKNOWN
const ASSET_MODE_UNKNOWN: c_int = 0;

/// The packed source archive's name in the APK's assets.
const ARCHIVE_ASSET: &str = "relax-src.pack";
/// The package the APK runs and the compile's flags (cargo_makepad `android run-host` writes them
/// into assets/relax-host.conf: one `key=value` per line).
const CONF_ASSET: &str = "relax-host.conf";

#[no_mangle]
pub unsafe extern "system" fn JNI_OnLoad(vm: *mut sys::JavaVM, _: *mut c_void) -> sys::jint {
    VM.store(vm, Ordering::Release);
    sys::JNI_VERSION_1_6
}

/// Relax finds the host's exported functions through the library's own handle (see
/// os::proc::set_host_library); System.loadLibrary keeps the library out of the process-wide scope.
pub fn name_host_library() {
    let h = unsafe { dlopen(c"libmakepad.so".as_ptr(), RTLD_NOW | RTLD_NOLOAD) };
    relax_compiler::os::proc::set_host_library(h as *mut u8);
}

unsafe fn jstring_to_string(env: *mut sys::JNIEnv, s: sys::jstring) -> String {
    if s.is_null() {
        return String::new();
    }
    let get = (**env).GetStringUTFChars.unwrap();
    let release = (**env).ReleaseStringUTFChars.unwrap();
    let chars = get(env, s, std::ptr::null_mut());
    let out = CStr::from_ptr(chars).to_string_lossy().into_owned();
    release(env, s, chars);
    out
}

unsafe fn new_jstring(env: *mut sys::JNIEnv, s: &str) -> sys::jstring {
    let c = CString::new(s.replace('\0', " ")).unwrap();
    ((**env).NewStringUTF.unwrap())(env, c.as_ptr())
}

/// The JNI short name of a Java method (JNI spec, "Resolving Native Method Names").
fn mangle(name: &str) -> String {
    let mut out = String::new();
    for c in name.chars() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' => out.push(c),
            '_' => out.push_str("_1"),
            ';' => out.push_str("_2"),
            '[' => out.push_str("_3"),
            '.' | '/' => out.push('_'),
            c => out.push_str(&format!("_0{:04x}", c as u32)),
        }
    }
    out
}

/// A named asset of the APK as (file offset, length) of the APK file: it must be stored, not
/// compressed (AAsset gives no descriptor for a deflated one).
unsafe fn asset_range(manager: *mut c_void, name: &str) -> Result<(u64, u64), String> {
    let cname = CString::new(name).unwrap();
    let asset = AAssetManager_open(manager, cname.as_ptr(), ASSET_MODE_UNKNOWN);
    if asset.is_null() {
        return Err(format!("the APK has no asset {name}"));
    }
    let (mut start, mut len) = (0i64, 0i64);
    let fd = AAsset_openFileDescriptor64(asset, &mut start, &mut len);
    AAsset_close(asset);
    if fd < 0 {
        return Err(format!("asset {name} is compressed in the APK (it must be stored)"));
    }
    close(fd);
    Ok((start as u64, len as u64))
}

unsafe fn asset_text(manager: *mut c_void, name: &str) -> Result<String, String> {
    let cname = CString::new(name).unwrap();
    let asset = AAssetManager_open(manager, cname.as_ptr(), ASSET_MODE_UNKNOWN);
    if asset.is_null() {
        return Err(format!("the APK has no asset {name}"));
    }
    extern "C" {
        fn AAsset_getLength(asset: *mut c_void) -> i64;
        fn AAsset_read(asset: *mut c_void, buf: *mut c_void, count: usize) -> c_int;
    }
    let len = AAsset_getLength(asset) as usize;
    let mut buf = vec![0u8; len];
    let n = AAsset_read(asset, buf.as_mut_ptr() as *mut c_void, len);
    AAsset_close(asset);
    if n < 0 || n as usize != len {
        return Err(format!("cannot read asset {name}"));
    }
    String::from_utf8(buf).map_err(|_| format!("asset {name} is not UTF-8"))
}

struct Conf {
    package: String,
    cargo_flags: Vec<String>,
    /// environment of the process (`env=KEY=VALUE`: MAKEPAD_TRACE, SANDBOX_MUTE, ...)
    env: Vec<(String, String)>,
}

fn parse_conf(text: &str) -> Result<Conf, String> {
    let mut package = None;
    let mut cargo_flags = Vec::new();
    let mut env = Vec::new();
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let (k, v) = line.split_once('=').ok_or_else(|| format!("{CONF_ASSET}: bad line {line:?}"))?;
        match k {
            "package" => package = Some(v.to_string()),
            "flag" => cargo_flags.push(v.to_string()),
            "env" => {
                let (k, val) = v.split_once('=').ok_or_else(|| format!("{CONF_ASSET}: env wants KEY=VALUE, got {v:?}"))?;
                env.push((k.to_string(), val.to_string()));
            }
            _ => return Err(format!("{CONF_ASSET}: unknown key {k:?}")),
        }
    }
    Ok(Conf { package: package.ok_or_else(|| format!("{CONF_ASSET}: no package"))?, cargo_flags, env })
}

/// `RunActivity.boot(Class nativeClass, String natives, String apkPath, String filesDir, String cacheDir,
/// String libDir, AssetManager assets)`: `natives` is one `name:signature` line per native method of
/// MakepadNative. Returns at once; `status()` follows the boot.
#[no_mangle]
pub unsafe extern "system" fn Java_dev_makepad_run_RunActivity_boot(
    env: *mut sys::JNIEnv,
    _: sys::jclass,
    native_class: sys::jclass,
    natives: sys::jstring,
    apk_path: sys::jstring,
    files_dir: sys::jstring,
    cache_dir: sys::jstring,
    lib_dir: sys::jstring,
    assets: sys::jobject,
) {
    static STARTED: std::sync::Once = std::sync::Once::new();
    let mut first = false;
    STARTED.call_once(|| first = true);
    if !first {
        return;
    }
    logcat::redirect_stdio();
    let new_global = (**env).NewGlobalRef.unwrap();
    let native_class = new_global(env, native_class) as usize;
    let assets = new_global(env, assets);
    let manager = AAssetManager_fromJava(env, assets) as usize;
    let natives = jstring_to_string(env, natives);
    let apk = PathBuf::from(jstring_to_string(env, apk_path));
    let files = PathBuf::from(jstring_to_string(env, files_dir));
    let cache = jstring_to_string(env, cache_dir);
    let lib_dir = PathBuf::from(jstring_to_string(env, lib_dir));
    boot::set_state("starting", String::new());
    let spawned = std::thread::Builder::new().name("relax-boot".into()).stack_size(64 << 20).spawn(move || {
        let result = boot_thread(manager as *mut c_void, &natives, &apk, &files, &cache, &lib_dir, native_class as sys::jclass);
        match result {
            Ok(()) => boot::set_state("ready", String::new()),
            Err(e) => {
                logcat::log(&format!("boot failed: {e}"));
                boot::set_state("failed", e);
            }
        }
        // the thread that booted the program stays (Relax names it the main thread)
        loop {
            std::thread::park();
        }
    });
    if let Err(e) = spawned {
        boot::set_state("failed", format!("cannot start the boot thread: {e}"));
    }
}

fn boot_thread(
    manager: *mut c_void,
    natives: &str,
    apk: &std::path::Path,
    files: &std::path::Path,
    cache: &str,
    lib_dir: &std::path::Path,
    native_class: sys::jclass,
) -> Result<(), String> {
    name_host_library();
    let relax_home = files.join("relax");
    std::fs::create_dir_all(&relax_home).map_err(|e| format!("{}: {e}", relax_home.display()))?;
    // an Android app has no HOME and /tmp is not its own
    std::env::set_var("HOME", files);
    std::env::set_var("TMPDIR", cache);
        std::env::set_var("RELAX_HOME", &relax_home);
    if let Some(mb) = boot::memory_budget_mb() {
        std::env::set_var("RELAX_MEM_BUDGET_MB", mb.to_string());
    }
    let conf = parse_conf(&unsafe { asset_text(manager, CONF_ASSET)? })?;
    for (k, v) in &conf.env {
        std::env::set_var(k, v);
    }
    let (offset, len) = unsafe { asset_range(manager, ARCHIVE_ASSET)? };
    let b = Boot {
        package: conf.package,
        cargo_flags: conf.cargo_flags,
        exports: vec!["Java_dev_makepad_android_".to_string(), "jni_on_load".to_string()],
        source: Source::Archive { file: apk.to_path_buf(), offset, len },
        exe: lib_dir.join("libmakepad_exe.so"),
    };
    logcat::log(&format!("booting {} from {} at {offset}+{len}", b.package, apk.display()));
    let exports = boot::boot(&b)?;
    logcat::log(&format!("{} exported functions compiled", exports.len()));
    unsafe { bind(&exports, natives, native_class) }
}

/// Tells the compiled platform its JavaVM, then registers the natives.
unsafe fn bind(exports: &[(String, u64)], natives: &str, native_class: sys::jclass) -> Result<(), String> {
    let vm = VM.load(Ordering::Acquire);
    if vm.is_null() {
        return Err("JNI_OnLoad did not run".to_string());
    }
    let Some((_, on_load)) = exports.iter().find(|(s, _)| s == "jni_on_load") else {
        return Err("the program has no jni_on_load (makepad_android_state)".to_string());
    };
    let on_load: extern "C" fn(*mut c_void) = std::mem::transmute(*on_load as usize);
    on_load(vm as *mut c_void);

    let mut env: *mut sys::JNIEnv = std::ptr::null_mut();
    let attach = (**vm).AttachCurrentThread.unwrap();
    if attach(vm, &mut env, std::ptr::null_mut()) != 0 {
        return Err("cannot attach the boot thread to the JVM".to_string());
    }
    let mut methods: Vec<sys::JNINativeMethod> = Vec::new();
    let mut missing = Vec::new();
    for line in natives.lines().filter(|l| !l.is_empty()) {
        let (name, sig) = line.split_once(':').ok_or_else(|| format!("bad native method line {line:?}"))?;
        let symbol = format!("Java_dev_makepad_android_MakepadNative_{}", mangle(name));
        match exports.iter().find(|(s, _)| *s == symbol) {
            Some((_, addr)) => methods.push(sys::JNINativeMethod {
                name: CString::new(name).unwrap().into_raw(),
                signature: CString::new(sig).unwrap().into_raw(),
                fnPtr: *addr as usize as *mut c_void,
            }),
            None => missing.push(name.to_string()),
        }
    }
    if !missing.is_empty() {
        logcat::log(&format!("natives without a compiled function ({}): {}", missing.len(), missing.join(", ")));
    }
    let register = (**env).RegisterNatives.unwrap();
    if register(env, native_class, methods.as_ptr(), methods.len() as sys::jint) != 0 {
        return Err("RegisterNatives failed".to_string());
    }
    logcat::log(&format!("registered {} natives", methods.len()));
    Ok(())
}

/// `RunActivity.status()`: "state|phase|loaded|total|error" (error last: it may hold anything).
#[no_mangle]
pub unsafe extern "system" fn Java_dev_makepad_run_RunActivity_status(env: *mut sys::JNIEnv, _: sys::jclass) -> sys::jstring {
    let s = boot::status();
    new_jstring(env, &format!("{}|{}|{}|{}|{}", s.state, s.phase, s.loaded, s.total, s.error.replace('\n', " ")))
}
