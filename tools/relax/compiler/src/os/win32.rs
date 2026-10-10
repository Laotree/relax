//! The Win32 API surface the runtime's Windows halves use: small explicit `extern "system"`
//! declarations hard-linked against kernel32 (no bindings crate), and the x64 CONTEXT record.

#![allow(non_snake_case, clippy::upper_case_acronyms)]

pub type HANDLE = isize;

#[link(name = "kernel32")]
extern "system" {
    // memory
    pub fn VirtualAlloc(addr: *mut u8, size: usize, kind: u32, protect: u32) -> *mut u8;
    pub fn VirtualFree(addr: *mut u8, size: usize, kind: u32) -> i32;
    pub fn VirtualProtect(addr: *mut u8, size: usize, protect: u32, old: *mut u32) -> i32;
    pub fn FlushInstructionCache(process: HANDLE, addr: *const u8, size: usize) -> i32;
    // errors
    pub fn GetLastError() -> u32;
    pub fn SetLastError(e: u32);
    // processes, threads
    pub fn GetCurrentProcess() -> HANDLE;
    pub fn GetCurrentThread() -> HANDLE;
    pub fn GetThreadPriority(thread: HANDLE) -> i32;
    pub fn ReadProcessMemory(process: HANDLE, addr: *const u8, buf: *mut u8, size: usize, read: *mut usize) -> i32;
    pub fn GetCurrentThreadId() -> u32;
    pub fn OpenThread(access: u32, inherit: i32, id: u32) -> HANDLE;
    pub fn DuplicateHandle(src_process: HANDLE, src: HANDLE, dst_process: HANDLE, dst: *mut HANDLE, access: u32, inherit: i32, options: u32) -> i32;
    pub fn CloseHandle(h: HANDLE) -> i32;
    pub fn SuspendThread(t: HANDLE) -> u32;
    pub fn ResumeThread(t: HANDLE) -> u32;
    pub fn GetThreadContext(t: HANDLE, ctx: *mut Context) -> i32;
    pub fn SetThreadContext(t: HANDLE, ctx: *const Context) -> i32;
    pub fn GetCurrentThreadStackLimits(low: *mut usize, high: *mut usize);
    pub fn SetThreadStackGuarantee(size: *mut u32) -> i32;
    pub fn SetThreadPriority(t: HANDLE, priority: i32) -> i32;
    pub fn GetThreadDescription(t: HANDLE, desc: *mut *mut u16) -> i32;
    pub fn LocalFree(p: *mut u8) -> *mut u8;
    pub fn TerminateProcess(p: HANDLE, code: u32) -> i32;
    // sampler timer
    pub fn CreateWaitableTimerExW(attrs: *const u8, name: *const u16, flags: u32, access: u32) -> HANDLE;
    pub fn SetWaitableTimer(timer: HANDLE, due: *const i64, period: i32, callback: Option<unsafe extern "system" fn(*mut u8, u32, u32)>, arg: *mut u8, resume: i32) -> i32;
    pub fn WaitForSingleObject(handle: HANDLE, ms: u32) -> u32;
    // thread-local storage
    pub fn TlsAlloc() -> u32;
    pub fn TlsGetValue(index: u32) -> *mut u8;
    pub fn TlsSetValue(index: u32, v: *mut u8) -> i32;
    // exceptions
    pub fn AddVectoredExceptionHandler(first: u32, handler: extern "system" fn(*mut ExceptionPointers) -> i32) -> *mut u8;
    pub fn SetUnhandledExceptionFilter(filter: Option<extern "system" fn(*mut ExceptionPointers) -> i32>) -> usize;
    // modules
    pub fn LoadLibraryA(name: *const u8) -> HANDLE;
    pub fn GetModuleHandleExW(flags: u32, name: *const u16, module: *mut HANDLE) -> i32;
    pub fn GetModuleFileNameW(module: HANDLE, name: *mut u16, size: u32) -> u32;
    // stdio (fault diagnostics)
    pub fn GetStdHandle(which: u32) -> HANDLE;
    pub fn WriteFile(h: HANDLE, buf: *const u8, n: u32, written: *mut u32, overlapped: *mut u8) -> i32;
    pub fn GetProcAddress(module: HANDLE, name: *const u8) -> *mut u8;
    pub fn K32EnumProcessModules(process: HANDLE, modules: *mut HANDLE, bytes: u32, needed: *mut u32) -> i32;
    // power
    pub fn GetSystemPowerStatus(status: *mut SystemPowerStatus) -> i32;
}

pub const MEM_COMMIT: u32 = 0x1000;
pub const MEM_RESERVE: u32 = 0x2000;
pub const MEM_RELEASE: u32 = 0x8000;
pub const MEM_DECOMMIT: u32 = 0x4000;
pub const PAGE_NOACCESS: u32 = 0x01;
pub const PAGE_READWRITE: u32 = 0x04;
pub const PAGE_EXECUTE_READWRITE: u32 = 0x40;

pub const THREAD_SUSPEND_RESUME: u32 = 0x0002;
pub const THREAD_GET_CONTEXT: u32 = 0x0008;
pub const THREAD_SET_CONTEXT: u32 = 0x0010;
pub const THREAD_QUERY_LIMITED_INFORMATION: u32 = 0x0800;
pub const DUPLICATE_SAME_ACCESS: u32 = 0x2;

pub const EXCEPTION_CONTINUE_EXECUTION: i32 = -1;
pub const EXCEPTION_CONTINUE_SEARCH: i32 = 0;

/// winnt.h EXCEPTION_RECORD (x64)
#[repr(C)]
pub struct ExceptionRecord {
    pub code: u32,
    pub flags: u32,
    pub record: *mut ExceptionRecord,
    pub address: *mut u8,
    pub n_params: u32,
    pub info: [usize; 15],
}

#[repr(C)]
pub struct ExceptionPointers {
    pub record: *mut ExceptionRecord,
    pub context: *mut Context,
}

/// winnt.h CONTEXT (AMD64): 0x4d0 bytes, 16-aligned. The fields the runtime reads and writes are
/// accessed by their offsets.
#[repr(C, align(16))]
pub struct Context(pub [u8; 0x4d0]);

pub const CONTEXT_AMD64: u32 = 0x0010_0000;
pub const CONTEXT_CONTROL: u32 = CONTEXT_AMD64 | 0x1;
pub const CONTEXT_INTEGER: u32 = CONTEXT_AMD64 | 0x2;

// offsets in CONTEXT: P1Home..P6Home 0x00, ContextFlags 0x30, MxCsr 0x34, Seg* 0x38, EFlags 0x44,
// Dr0-7 0x48, Rax 0x78, Rcx 0x80, Rdx 0x88, Rbx 0x90, Rsp 0x98, Rbp 0xa0, Rsi 0xa8, Rdi 0xb0,
// R8-R15 0xb8.., Rip 0xf8
pub const CTX_FLAGS: usize = 0x30;
pub const CTX_RSP: usize = 0x98;
pub const CTX_RBP: usize = 0xa0;
pub const CTX_RSI: usize = 0xa8;
pub const CTX_RDI: usize = 0xb0;
pub const CTX_RIP: usize = 0xf8;

impl Context {
    pub fn new(flags: u32) -> Box<Context> {
        let mut c = Box::new(Context([0; 0x4d0]));
        c.0[CTX_FLAGS..CTX_FLAGS + 4].copy_from_slice(&flags.to_le_bytes());
        c
    }
    pub fn get(&self, off: usize) -> u64 {
        u64::from_le_bytes(self.0[off..off + 8].try_into().unwrap())
    }
    pub fn set(&mut self, off: usize, v: u64) {
        self.0[off..off + 8].copy_from_slice(&v.to_le_bytes());
    }
}

#[repr(C)]
#[derive(Default)]
pub struct SystemPowerStatus {
    pub ac_line_status: u8,
    pub battery_flag: u8,
    pub battery_life_percent: u8,
    pub system_status_flag: u8,
    pub battery_life_time: u32,
    pub battery_full_life_time: u32,
}

#[link(name = "winmm")]
extern "system" {
    pub fn timeBeginPeriod(ms: u32) -> u32;
    pub fn timeEndPeriod(ms: u32) -> u32;
}

pub const CREATE_WAITABLE_TIMER_HIGH_RESOLUTION: u32 = 0x2;
pub const TIMER_MODIFY_STATE: u32 = 0x2;
pub const SYNCHRONIZE: u32 = 0x0010_0000;
