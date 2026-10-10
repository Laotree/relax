//! CEF's subprocesses of a program running on this loader (Linux, Windows). makepad-cef names
//! the browser process's own executable as CEF's subprocess, and under Relax that executable is
//! this loader: CEF starts it again with `--type=gpu-process ..` (renderer, utility, zygote).
//! The loader then runs what makepad-cef's `bootstrap()` runs in a natively built app:
//! `cef_execute_process` from the libcef the browser process loaded (MAKEPAD_CEF_LIBRARY, which
//! makepad-cef sets before it starts CEF and its subprocesses inherit), with no app object,
//! exactly as the macOS helper does. Nothing is compiled for it.

use std::ffi::{c_char, c_int, c_void, CString};

/// The ABI version makepad-cef asks libcef for (makepad-cef native.rs CEF_API_VERSION).
const CEF_API_VERSION: c_int = 13800;

/// Some(exit code) when this process is a CEF subprocess; None otherwise.
pub fn subprocess() -> Option<i32> {
    if !std::env::args_os().skip(1).any(|a| a.to_string_lossy().starts_with("--type=")) {
        return None;
    }
    let lib = std::env::var_os("MAKEPAD_CEF_LIBRARY")?;
    Some(match run(&lib) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("makepad: CEF subprocess: {e}");
            1
        }
    })
}

type ApiHash = unsafe extern "C" fn(c_int, c_int) -> *const c_char;

#[cfg(unix)]
fn run(lib: &std::ffi::OsStr) -> Result<i32, String> {
    use std::os::unix::ffi::OsStrExt;
    #[repr(C)]
    struct MainArgs {
        argc: c_int,
        argv: *mut *mut c_char,
    }
    type ExecuteProcess = unsafe extern "C" fn(*const MainArgs, *mut c_void, *mut c_void) -> c_int;
    extern "C" {
        fn dlopen(filename: *const c_char, flag: c_int) -> *mut c_void;
        fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
        fn dlerror() -> *const c_char;
    }
    const RTLD_NOW: c_int = 2;
    let path = CString::new(lib.as_bytes()).map_err(|e| e.to_string())?;
    unsafe {
        let h = dlopen(path.as_ptr(), RTLD_NOW);
        if h.is_null() {
            let e = dlerror();
            return Err(format!("dlopen {}: {}", lib.to_string_lossy(), if e.is_null() { "?".into() } else { std::ffi::CStr::from_ptr(e).to_string_lossy() }));
        }
        let hash = dlsym(h, c"cef_api_hash".as_ptr());
        let exec = dlsym(h, c"cef_execute_process".as_ptr());
        if hash.is_null() || exec.is_null() {
            return Err("libcef lacks cef_api_hash / cef_execute_process".into());
        }
        let hash: ApiHash = std::mem::transmute(hash);
        if hash(CEF_API_VERSION, 0).is_null() {
            return Err("cef_api_hash returned null".into());
        }
        // argv as this process got it (CEF parses its switches from it)
        let args: Vec<CString> = std::env::args_os().map(|a| CString::new(a.as_bytes()).unwrap_or_default()).collect();
        let mut ptrs: Vec<*mut c_char> = args.iter().map(|a| a.as_ptr() as *mut c_char).collect();
        ptrs.push(std::ptr::null_mut());
        let main_args = MainArgs { argc: args.len() as c_int, argv: ptrs.as_mut_ptr() };
        let exec: ExecuteProcess = std::mem::transmute(exec);
        Ok(exec(&main_args, std::ptr::null_mut(), std::ptr::null_mut()))
    }
}

#[cfg(windows)]
fn run(lib: &std::ffi::OsStr) -> Result<i32, String> {
    use std::os::windows::ffi::OsStrExt;
    // Windows CEF reads its switches from GetCommandLineW itself; it takes the module instance
    #[repr(C)]
    struct MainArgs {
        instance: *mut c_void,
    }
    type ExecuteProcess = unsafe extern "C" fn(*const MainArgs, *mut c_void, *mut c_void) -> c_int;
    #[link(name = "kernel32")]
    extern "system" {
        fn LoadLibraryExW(name: *const u16, file: *mut c_void, flags: u32) -> *mut c_void;
        fn GetProcAddress(module: *mut c_void, name: *const c_char) -> *mut c_void;
        fn GetModuleHandleW(name: *const u16) -> *mut c_void;
        fn GetLastError() -> u32;
    }
    let wide: Vec<u16> = lib.encode_wide().chain(std::iter::once(0)).collect();
    unsafe {
        // libcef.dll's own folder first for its dependents (chrome_elf.dll sits beside it): a plain
        // LoadLibraryW searches the exe's folder -- the loader's -- and fails with error 126
        // (LOAD_LIBRARY_SEARCH_DLL_LOAD_DIR | LOAD_LIBRARY_SEARCH_DEFAULT_DIRS)
        let h = LoadLibraryExW(wide.as_ptr(), std::ptr::null_mut(), 0x0000_0100 | 0x0000_1000);
        if h.is_null() {
            return Err(format!("LoadLibraryEx {}: error {}", lib.to_string_lossy(), GetLastError()));
        }
        let hash = GetProcAddress(h, c"cef_api_hash".as_ptr());
        let exec = GetProcAddress(h, c"cef_execute_process".as_ptr());
        if hash.is_null() || exec.is_null() {
            return Err("libcef lacks cef_api_hash / cef_execute_process".into());
        }
        let hash: ApiHash = std::mem::transmute(hash);
        if hash(CEF_API_VERSION, 0).is_null() {
            return Err("cef_api_hash returned null".into());
        }
        let main_args = MainArgs { instance: GetModuleHandleW(std::ptr::null()) };
        let exec: ExecuteProcess = std::mem::transmute(exec);
        Ok(exec(&main_args, std::ptr::null_mut(), std::ptr::null_mut()))
    }
}
