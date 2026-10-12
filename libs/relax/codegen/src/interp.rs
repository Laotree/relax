//! Threaded interpreter backend for RIR (research prototype: platforms without writable and
//! executable memory).
//!
//! A function's RIR is lowered into a stream of 64-bit words: each instruction is the address
//! of a precompiled native handler followed by its operands (frame cell indices packed four to a
//! word, immediates, absolute branch targets). Every handler ends by loading the next handler's
//! address and calling it in tail position with the VM state in argument registers
//! (`pc`, frame pointer, context), so a sequence of RIR instructions runs as a chain of
//! indirect jumps between small native functions, with no dispatch loop and no runtime code.
//!
//! The boundary with native code is the backends' own ABI (AAPCS64 registers for Relax calls,
//! `cabi::plan` for C calls):
//! - interpreted -> native: `relax_interp_call`, one precompiled routine that loads x0-x7,
//!   q0-q7, x8 and the stack arguments from a buffer, calls the target and stores the result
//!   registers back. It serves every signature.
//! - native -> interpreted: a fixed pool of precompiled entry thunks (`movz w17, #k; b common`).
//!   Each interpreted function owns one pool index; the common entry spills the argument
//!   registers and calls `relax_interp_enter(k, regs, incoming stack args)`. A slot's code is a
//!   jump to its pool thunk, so native callers, function pointers and vtables reach it unchanged.
//! - interpreted -> interpreted: a call site resolves its target (table word, thunk or pool
//!   thunk) to the callee's interpreter code once (inline cache) and runs it on the same
//!   interpreter stack without leaving the interpreter.
//!
//! Selection: `MAKEPAD_RUN_INTERP=all` or a comma list of name substrings (`MAKEPAD_RUN_INTERP_SKIP` for
//! exclusions). Functions using operations this prototype does not cover stay native (counted:
//! `MAKEPAD_RUN_INTERP_STATS=1` prints a summary at exit).
//! Not covered: unwinding through interpreted frames (a panic below one cuts back to the
//! recovery point without running the interpreted frames' cleanups), most lane-typed vector
//! ops (`VX`, `VX3`), x86-only instructions.

#![allow(clippy::missing_safety_doc)]

use crate::cabi::{self, ArgPlan, PLoc, RetPlan};
use crate::rir::*;
use std::sync::atomic::{AtomicPtr, AtomicU64, AtomicUsize, Ordering};

pub type H = unsafe extern "C" fn(*const u64, *mut u64, *mut Cx);

/// Number of entry thunks in the pool (each 8 bytes of code, in the binary's text).
pub const POOL: usize = 32768;

/// Per-thread interpreter state; its address is the third handler argument.
#[repr(C)]
pub struct Cx {
    /// results of the last return: x0, x1, then q0, q1 (two words each)
    pub ret: [u64; 6],
    /// first free word of this thread's interpreter stack
    pub top: *mut u64,
    pub limit: *mut u64,
    /// this thread's thread-local block (0 = not asked yet)
    pub tls_block: u64,
    /// dispatch counts (builds with MAKEPAD_RUN_INTERP_COUNT set at compile time): handlers run,
    /// interpreted -> interpreted calls, interpreted -> native calls, native -> interpreted entries
    pub n: [u64; 4],
}

/// Count dispatches and calls (a build-time switch: the counting costs time in every handler).
const COUNT: bool = option_env!("MAKEPAD_RUN_INTERP_COUNT").is_some();
/// counting builds: dispatches per handler, and the RIR operation each handler was emitted for
static HIST: std::sync::Mutex<Vec<(u64, u64)>> = std::sync::Mutex::new(Vec::new());
static HNAMES: std::sync::Mutex<Vec<(u64, String)>> = std::sync::Mutex::new(Vec::new());
thread_local! {
    static THIST: std::cell::RefCell<std::collections::HashMap<u64, u64>> = std::cell::RefCell::new(std::collections::HashMap::new());
}
#[inline(never)]
fn hist_note(h: u64) {
    THIST.with(|t| *t.borrow_mut().entry(h).or_insert(0) += 1);
}
fn hist_flush() {
    THIST.with(|t| {
        let mut g = HIST.lock().unwrap_or_else(|e| e.into_inner());
        for (h, n) in t.borrow_mut().drain() {
            match g.iter_mut().find(|x| x.0 == h) {
                Some(x) => x.1 += n,
                None => g.push((h, n)),
            }
        }
    });
}
static COUNTS: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];

pub struct IFunc {
    pub code: Box<[u64]>,
    /// frame size in words (cells, stack slots, aggregate buffers), a multiple of 8
    pub frame_words: usize,
    /// (cell, class) per parameter in ABI order
    pub params: Vec<(u32, Cls)>,
    /// C ABI body: its plan and, per aggregate parameter passed in registers, the frame byte
    /// offset of the buffer it is rebuilt in; the result buffer (register-returned aggregate)
    pub cplan: Option<(Box<CSig>, cabi::Plan, Vec<u32>, u32)>,
    pub name: String,
}

// ---------------------------------------------------------------- precompiled glue

#[cfg(target_vendor = "apple")]
macro_rules! gsym {
    ($s:literal) => {
        concat!("_", $s)
    };
}
#[cfg(not(target_vendor = "apple"))]
#[allow(unused_macros)] // only the aarch64 asm below uses it
macro_rules! gsym {
    ($s:literal) => {
        $s
    };
}

#[cfg(target_arch = "aarch64")]
std::arch::global_asm!(
    ".text",
    ".p2align 3",
    concat!(".globl ", gsym!("relax_interp_pool")),
    concat!(gsym!("relax_interp_pool"), ":"),
    ".set rip_k, 0",
    ".rept 32768",
    "  movz w17, #rip_k",
    "  b 2f",
    ".set rip_k, rip_k + 1",
    ".endr",
    // common entry: x17 = pool index. Spill x0-x7, q0-q7, x8; call relax_interp_enter(k,
    // regs, caller's stack arguments); load the result registers from the buffer.
    "2:",
    "  stp x29, x30, [sp, #-16]!",
    "  mov x29, sp",
    "  sub sp, sp, #208",
    "  stp x0, x1, [sp, #0]",
    "  stp x2, x3, [sp, #16]",
    "  stp x4, x5, [sp, #32]",
    "  stp x6, x7, [sp, #48]",
    "  stp q0, q1, [sp, #64]",
    "  stp q2, q3, [sp, #96]",
    "  stp q4, q5, [sp, #128]",
    "  stp q6, q7, [sp, #160]",
    "  str x8, [sp, #192]",
    "  mov w0, w17",
    "  mov x1, sp",
    "  add x2, x29, #16",
    "  bl {enter}",
    "  ldp x0, x1, [sp, #0]",
    "  ldp q0, q1, [sp, #64]",
    "  mov sp, x29",
    "  ldp x29, x30, [sp], #16",
    "  ret",
    "",
    // relax_interp_call(target, regs, stack, nstack_words)
    ".p2align 2",
    concat!(".globl ", gsym!("relax_interp_call")),
    concat!(gsym!("relax_interp_call"), ":"),
    "  stp x29, x30, [sp, #-16]!",
    "  mov x29, sp",
    "  stp x19, x20, [sp, #-16]!",
    "  mov x19, x0",
    "  mov x20, x1",
    "  lsl x9, x3, #3",
    "  add x9, x9, #15",
    "  and x9, x9, #-16",
    "  sub sp, sp, x9",
    "  mov x10, #0",
    "3:",
    "  cmp x10, x3",
    "  b.ge 4f",
    "  ldr x11, [x2, x10, lsl #3]",
    "  str x11, [sp, x10, lsl #3]",
    "  add x10, x10, #1",
    "  b 3b",
    "4:",
    "  ldp q0, q1, [x20, #64]",
    "  ldp q2, q3, [x20, #96]",
    "  ldp q4, q5, [x20, #128]",
    "  ldp q6, q7, [x20, #160]",
    "  ldr x8, [x20, #192]",
    "  ldp x0, x1, [x20, #0]",
    "  ldp x2, x3, [x20, #16]",
    "  ldp x4, x5, [x20, #32]",
    "  ldp x6, x7, [x20, #48]",
    "  blr x19",
    "  stp x0, x1, [x20, #0]",
    "  stp q0, q1, [x20, #64]",
    "  sub sp, x29, #16",
    "  ldp x19, x20, [sp], #16",
    "  ldp x29, x30, [sp], #16",
    "  ret",
    "",
    // relax_interp_tls(glue): the backends' tls_slow glue returns the block in x16
    ".p2align 2",
    concat!(".globl ", gsym!("relax_interp_tls")),
    concat!(gsym!("relax_interp_tls"), ":"),
    "  stp x29, x30, [sp, #-16]!",
    "  mov x29, sp",
    "  blr x0",
    "  mov x0, x16",
    "  ldp x29, x30, [sp], #16",
    "  ret",
    enter = sym relax_interp_enter,
);

extern "C" {
    static relax_interp_pool: u8;
    fn relax_interp_call(target: u64, regs: *mut u64, stack: *const u64, nstack: u64);
    fn relax_interp_tls(glue: u64) -> u64;
}

fn pool_base() -> u64 {
    unsafe { &relax_interp_pool as *const u8 as u64 }
}

/// Register buffer layout shared by the glue: x0-x7 words 0..8, q0-q7 words 8..24, x8 word 24.
const RB_Q: usize = 8;
const RB_X8: usize = 24;
const RB_WORDS: usize = 26;

static FUNCS: [AtomicPtr<IFunc>; POOL] = [const { AtomicPtr::new(std::ptr::null_mut()) }; POOL];
static NEXT: AtomicUsize = AtomicUsize::new(0);
static TLS_GLUE: AtomicU64 = AtomicU64::new(0);
static SLOTS: AtomicUsize = AtomicUsize::new(0);
/// MAKEPAD_RUN_INTERP_TRACE: every entry and native call to stderr (debugging the prototype)
static TRACE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

// ---------------------------------------------------------------- statistics

pub static N_INTERP: AtomicU64 = AtomicU64::new(0);
pub static N_REFUSED: AtomicU64 = AtomicU64::new(0);
pub static N_WORDS: AtomicU64 = AtomicU64::new(0);
pub static N_INSTS: AtomicU64 = AtomicU64::new(0);
pub static LOWER_NS: AtomicU64 = AtomicU64::new(0);
/// functions the machine-code backend compiled meanwhile: count, ns, code bytes, RIR insts
static NATIVE: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];

pub fn note_native(ns: u64, bytes: u64, insts: u64) {
    NATIVE[1].fetch_add(ns, Ordering::Relaxed);
    NATIVE[2].fetch_add(bytes, Ordering::Relaxed);
    NATIVE[3].fetch_add(insts, Ordering::Relaxed);
    if NATIVE[0].fetch_add(1, Ordering::Relaxed) % 2000 == 1999 {
        eprintln!("relax-native: {} fns compiled to machine code ({} RIR insts -> {} KB, backend {:.1} ms)", NATIVE[0].load(Ordering::Relaxed), NATIVE[3].load(Ordering::Relaxed), NATIVE[2].load(Ordering::Relaxed) / 1024, NATIVE[1].load(Ordering::Relaxed) as f64 / 1e6);
    }
}
static REFUSALS: std::sync::Mutex<Vec<(String, u64)>> = std::sync::Mutex::new(Vec::new());

fn refuse(why: &str) {
    N_REFUSED.fetch_add(1, Ordering::Relaxed);
    let mut g = REFUSALS.lock().unwrap_or_else(|e| e.into_inner());
    match g.iter_mut().find(|x| x.0 == why) {
        Some(x) => x.1 += 1,
        None => g.push((why.to_string(), 1)),
    }
}

extern "C" fn print_stats() {
    let g = REFUSALS.lock().unwrap_or_else(|e| e.into_inner());
    let mut v: Vec<_> = g.clone();
    v.sort_by(|a, b| b.1.cmp(&a.1));
    if COUNT {
        let c: Vec<u64> = COUNTS.iter().map(|x| x.load(Ordering::Relaxed)).collect();
        eprintln!("relax-interp counts: {} dispatches, {} interp->interp calls, {} interp->native calls, {} native->interp entries", c[0], c[1], c[2], c[3]);
        let names = HNAMES.lock().unwrap_or_else(|e| e.into_inner());
        let mut by: Vec<(String, u64)> = Vec::new();
        for (h, n) in HIST.lock().unwrap_or_else(|e| e.into_inner()).iter() {
            let name = names.iter().find(|x| x.0 == *h).map(|x| x.1.clone()).unwrap_or_else(|| format!("{:#x}", h));
            match by.iter_mut().find(|x| x.0 == name) {
                Some(x) => x.1 += n,
                None => by.push((name, *n)),
            }
        }
        by.sort_by(|a, b| b.1.cmp(&a.1));
        let total: u64 = by.iter().map(|x| x.1).sum::<u64>().max(1);
        eprintln!("relax-interp ops: {}", by.iter().take(24).map(|(n, c)| format!("{} {:.1}%", n, 100.0 * *c as f64 / total as f64)).collect::<Vec<_>>().join(", "));
    }
    eprintln!(
        "relax-interp: {} fns interpreted ({} RIR insts -> {} KB threaded code, lowered in {:.1} ms), {} stayed native{}",
        N_INTERP.load(Ordering::Relaxed),
        N_INSTS.load(Ordering::Relaxed),
        N_WORDS.load(Ordering::Relaxed) * 8 / 1024,
        LOWER_NS.load(Ordering::Relaxed) as f64 / 1e6,
        N_REFUSED.load(Ordering::Relaxed),
        v.iter().map(|(w, n)| format!("; {} x{}", w, n)).collect::<String>()
    );
}

struct Sel {
    all: bool,
    pats: Vec<String>,
    skip: Vec<String>,
}

fn selection() -> Option<&'static Sel> {
    static S: std::sync::OnceLock<Option<Sel>> = std::sync::OnceLock::new();
    S.get_or_init(|| {
        let v = std::env::var("MAKEPAD_RUN_INTERP").ok().filter(|v| !v.is_empty() && v != "0")?;
        let split = |s: &str| s.split(',').filter(|x| !x.is_empty()).map(|x| x.to_string()).collect::<Vec<_>>();
        let skip = std::env::var("MAKEPAD_RUN_INTERP_SKIP").map(|s| split(&s)).unwrap_or_default();
        if std::env::var_os("MAKEPAD_RUN_INTERP_STATS").is_some() {
            extern "C" {
                fn atexit(f: extern "C" fn()) -> i32;
            }
            unsafe {
                atexit(print_stats);
            }
        }
        TRACE.store(std::env::var_os("MAKEPAD_RUN_INTERP_TRACE").is_some(), Ordering::Relaxed);
        Some(Sel { all: v == "all", pats: if v == "all" { Vec::new() } else { split(&v) }, skip })
    })
    .as_ref()
}

/// The backends' hook: `Some(code)` when `f` runs in the interpreter -- the slot's code is then
/// a jump to the function's entry thunk.
pub fn maybe_compile(f: &Func, slots: SlotsPtr, syms: u64, sym_class: u64, tls_slow: u64) -> Option<Vec<u8>> {
    let sel = selection()?;
    // a pattern matches a name containing it; `=name` matches that name only
    let m = |p: &String| match p.strip_prefix('=') {
        Some(x) => f.name == x,
        None => f.name.contains(p.as_str()),
    };
    if !(sel.all || sel.pats.iter().any(m)) || sel.skip.iter().any(m) {
        return None;
    }
    if !cfg!(target_arch = "aarch64") {
        return None;
    }
    let t0 = std::time::Instant::now();
    let lowered = lower(f, slots, syms, sym_class);
    LOWER_NS.fetch_add(t0.elapsed().as_nanos() as u64, Ordering::Relaxed);
    let ifunc = match lowered {
        Ok(x) => x,
        Err(why) => {
            refuse(why);
            return None;
        }
    };
    let k = NEXT.fetch_add(1, Ordering::Relaxed);
    if k >= POOL {
        refuse("entry thunk pool exhausted");
        return None;
    }
    TLS_GLUE.store(tls_slow, Ordering::Relaxed);
    SLOTS.store(slots.0 as usize, Ordering::Relaxed);
    if N_INTERP.fetch_add(1, Ordering::Relaxed) % 2000 == 1999 && std::env::var_os("MAKEPAD_RUN_INTERP_STATS").is_some() {
        print_stats();
    }
    N_WORDS.fetch_add(ifunc.code.len() as u64, Ordering::Relaxed);
    N_INSTS.fetch_add(f.blocks.iter().map(|b| b.insts.len() as u64 + 1).sum::<u64>(), Ordering::Relaxed);
    FUNCS[k].store(Box::into_raw(Box::new(ifunc)), Ordering::Release);
    Some(crate::arm64::jump_to(pool_base() + 8 * k as u64))
}

// ---------------------------------------------------------------- thread state

const STACK_WORDS: usize = 8 << 20; // 64 MB of interpreter stack per thread (reserved lazily)

thread_local! {
    static CX: std::cell::UnsafeCell<Cx> = const { std::cell::UnsafeCell::new(Cx { ret: [0; 6], top: std::ptr::null_mut(), limit: std::ptr::null_mut(), tls_block: 0, n: [0; 4] }) };
}

#[inline(always)]
unsafe fn cx_ptr() -> *mut Cx {
    let cx = CX.with(|c| c.get());
    if (*cx).top.is_null() {
        // reserved address space, touched as frames reach it (not the program's allocator)
        extern "C" {
            fn mmap(addr: *mut std::ffi::c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut std::ffi::c_void;
        }
        #[cfg(target_vendor = "apple")]
        const MAP_ANON: i32 = 0x1000;
        #[cfg(not(target_vendor = "apple"))]
        const MAP_ANON: i32 = 0x20;
        let p = mmap(std::ptr::null_mut(), STACK_WORDS * 8, 3, 0x0002 | MAP_ANON, -1, 0) as *mut u64;
        assert!(!p.is_null() && p as isize != -1, "relax-interp: no memory for the interpreter stack");
        (*cx).top = p;
        (*cx).limit = p.add(STACK_WORDS);
    }
    cx
}

#[inline(never)]
#[cold]
fn overflow() -> ! {
    eprintln!("relax-interp: interpreter stack overflow");
    std::process::abort()
}

#[inline(always)]
unsafe fn run(f: &IFunc, fp: *mut u64, cx: *mut Cx) {
    let h: H = std::mem::transmute(f.code[0]);
    h(f.code.as_ptr(), fp, cx)
}

/// Native -> interpreted (the pool's common entry).
#[no_mangle]
unsafe extern "C" fn relax_interp_enter(k: u32, regs: *mut u64, stack: *const u8) {
    let f = &*FUNCS[k as usize].load(Ordering::Acquire);
    let cx = cx_ptr();
    if TRACE.load(Ordering::Relaxed) {
        eprintln!("interp: enter {} {} top {:p} regs {:x?}", k, f.name, (*cx).top, std::slice::from_raw_parts(regs, 4));
    }
    let fp = (*cx).top;
    let top = fp.add(f.frame_words);
    if top > (*cx).limit {
        overflow();
    }
    (*cx).top = top;
    match &f.cplan {
        None => {
            let (mut ni, mut nf, mut k) = (0usize, 0usize, 0usize);
            for &(cell, c) in &f.params {
                let dst = fp.add(cell as usize);
                if c == Cls::I {
                    if ni < 8 {
                        *dst = *regs.add(ni);
                        ni += 1;
                        continue;
                    }
                } else if nf < 8 {
                    *dst = *regs.add(RB_Q + 2 * nf);
                    if c == Cls::V128 {
                        *dst.add(1) = *regs.add(RB_Q + 2 * nf + 1);
                    }
                    nf += 1;
                    continue;
                }
                *dst = std::ptr::read_unaligned((stack as *const u64).add(k));
                k += 1;
            }
        }
        Some((sig, plan, bufs, retbuf)) => {
            let skip = sig.ret.is_some() as usize;
            if skip == 1 {
                let a = match plan.ret {
                    RetPlan::Indirect => *regs.add(RB_X8),
                    _ => fp as u64 + *retbuf as u64,
                };
                *fp.add(f.params[0].0 as usize) = a;
            }
            for (j, ap) in plan.args.iter().enumerate() {
                let dst = fp.add(f.params[skip + j].0 as usize);
                let read = |loc: PLoc, size: u32| -> u64 {
                    let v = match loc {
                        PLoc::Int(n) => *regs.add(n as usize),
                        PLoc::Flt(n) => *regs.add(RB_Q + 2 * n as usize),
                        PLoc::Stack(o) => std::ptr::read_unaligned(stack.add(o as usize) as *const u64),
                    };
                    if size >= 8 { v } else { v & ((1u64 << (8 * size)) - 1) }
                };
                match ap {
                    ArgPlan::Scalar(loc, size) => {
                        let mut v = read(*loc, *size);
                        if let (CArg::Scalar(Mem::Int(b, true)), true) = (&sig.args[j], *size < 8) {
                            v = ext(v, b * 8, true);
                        }
                        *dst = v;
                    }
                    ArgPlan::Parts(parts) => {
                        let buf = (fp as *mut u8).add(bufs[j] as usize);
                        for p in parts {
                            let v = read(p.loc, 8);
                            std::ptr::copy_nonoverlapping(&v as *const u64 as *const u8, buf.add(p.off as usize), p.size as usize);
                        }
                        *dst = buf as u64;
                    }
                    ArgPlan::ByRef(loc) => *dst = read(*loc, 8),
                    ArgPlan::Stack(off, _) => *dst = stack.add(*off as usize) as u64,
                }
            }
        }
    }
    if COUNT {
        (*cx).n[3] += 1;
    }
    run(f, fp, cx);
    if COUNT {
        for k in 0..4 {
            COUNTS[k].fetch_add((*cx).n[k], Ordering::Relaxed);
            (*cx).n[k] = 0;
        }
        hist_flush();
    }
    let r = &(*cx).ret;
    match &f.cplan {
        Some((_, plan, _, retbuf)) if matches!(plan.ret, RetPlan::Parts(_)) => {
            let RetPlan::Parts(parts) = &plan.ret else { unreachable!() };
            let buf = (fp as *const u8).add(*retbuf as usize);
            for p in parts {
                let mut v = 0u64;
                std::ptr::copy_nonoverlapping(buf.add(p.off as usize), &mut v as *mut u64 as *mut u8, p.size as usize);
                match p.loc {
                    PLoc::Int(n) => *regs.add(n as usize) = v,
                    PLoc::Flt(n) => {
                        *regs.add(RB_Q + 2 * n as usize) = v;
                        *regs.add(RB_Q + 2 * n as usize + 1) = 0;
                    }
                    PLoc::Stack(_) => {}
                }
            }
        }
        _ => {
            *regs = r[0];
            *regs.add(1) = r[1];
            for k in 0..4 {
                *regs.add(RB_Q + k) = r[2 + k];
            }
        }
    }
    (*cx).top = fp;
}

// ---------------------------------------------------------------- handlers

macro_rules! next {
    ($pc:expr, $fp:expr, $cx:expr) => {{
        let p: *const u64 = $pc;
        if COUNT {
            (*$cx).n[0] += 1;
            hist_note(*p);
        }
        let h: H = std::mem::transmute(*p);
        return h(p, $fp, $cx);
    }};
}

/// Cell `k` (0..4) of an operand word.
#[inline(always)]
unsafe fn c(fp: *mut u64, w: u64, k: u32) -> *mut u64 {
    fp.add(((w >> (16 * k)) & 0xffff) as usize)
}

#[inline(always)]
fn ext(v: u64, bits: u8, signed: bool) -> u64 {
    if bits >= 64 {
        v
    } else if signed {
        (((v << (64 - bits)) as i64) >> (64 - bits)) as u64
    } else {
        v & ((1u64 << bits) - 1)
    }
}

const OP_ADD: u8 = 0;
const OP_SUB: u8 = 1;
const OP_MUL: u8 = 2;
const OP_AND: u8 = 3;
const OP_OR: u8 = 4;
const OP_XOR: u8 = 5;
const OP_SHL: u8 = 6;
const OP_SHR: u8 = 7;
const OP_DIV: u8 = 8;
const OP_REM: u8 = 9;
const OP_MULHI: u8 = 10;
const OP_ROTL: u8 = 11;

fn iop_code(op: IOp) -> u8 {
    match op {
        IOp::Add => OP_ADD,
        IOp::Sub => OP_SUB,
        IOp::Mul => OP_MUL,
        IOp::And => OP_AND,
        IOp::Or => OP_OR,
        IOp::Xor => OP_XOR,
        IOp::Shl => OP_SHL,
        IOp::Shr => OP_SHR,
        IOp::Div => OP_DIV,
        IOp::Rem => OP_REM,
        IOp::MulHi => OP_MULHI,
        IOp::Rotl => OP_ROTL,
    }
}

/// The arm64 backend's semantics: 64-bit operation then re-extension to the type (W forms for
/// u32: shift amounts mod 32), division by zero gives 0, remainder by zero the dividend.
#[inline(always)]
fn ibin(op: u8, bits: u8, s: bool, a: u64, b: u64) -> u64 {
    if op == OP_ROTL {
        return if bits == 32 { (a as u32).rotate_left(b as u32 & 31) as u64 } else { a.rotate_left(b as u32 & 63) };
    }
    if bits == 32 && !s && op != OP_DIV && op != OP_REM && op != OP_MULHI {
        let (x, y) = (a as u32, b as u32);
        return match op {
            OP_ADD => x.wrapping_add(y),
            OP_SUB => x.wrapping_sub(y),
            OP_MUL => x.wrapping_mul(y),
            OP_AND => x & y,
            OP_OR => x | y,
            OP_XOR => x ^ y,
            OP_SHL => x << (y & 31),
            _ => x >> (y & 31),
        } as u64;
    }
    let r = match op {
        OP_ADD => a.wrapping_add(b),
        OP_SUB => a.wrapping_sub(b),
        OP_MUL => a.wrapping_mul(b),
        OP_AND => a & b,
        OP_OR => a | b,
        OP_XOR => a ^ b,
        OP_SHL => a << (b & 63),
        OP_SHR => {
            if s {
                ((a as i64) >> (b & 63)) as u64
            } else {
                a >> (b & 63)
            }
        }
        OP_DIV => {
            if b == 0 {
                0
            } else if s {
                (a as i64).wrapping_div(b as i64) as u64
            } else {
                a / b
            }
        }
        OP_REM => {
            if b == 0 {
                a
            } else if s {
                (a as i64).wrapping_rem(b as i64) as u64
            } else {
                a % b
            }
        }
        _ => {
            if s {
                (((a as i64 as i128) * (b as i64 as i128)) >> 64) as u64
            } else {
                (((a as u128) * (b as u128)) >> 64) as u64
            }
        }
    };
    if bits < 64 && op != OP_AND && op != OP_OR && op != OP_XOR {
        ext(r, bits, s)
    } else {
        r
    }
}

unsafe extern "C" fn h_ibin<const OP: u8, const B: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = ibin(OP, B, S, *c(fp, w, 1), *c(fp, w, 2));
    next!(pc.add(2), fp, cx)
}

unsafe extern "C" fn h_ibini<const OP: u8, const B: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = ibin(OP, B, S, *c(fp, w, 1), *pc.add(2));
    next!(pc.add(3), fp, cx)
}

fn pick_ibin<const B: u8, const S: bool>(op: u8, imm: bool) -> H {
    macro_rules! p {
        ($o:expr) => {
            if imm {
                h_ibini::<{ $o }, B, S> as H
            } else {
                h_ibin::<{ $o }, B, S> as H
            }
        };
    }
    match op {
        OP_ADD => p!(OP_ADD),
        OP_SUB => p!(OP_SUB),
        OP_MUL => p!(OP_MUL),
        OP_AND => p!(OP_AND),
        OP_OR => p!(OP_OR),
        OP_XOR => p!(OP_XOR),
        OP_SHL => p!(OP_SHL),
        OP_SHR => p!(OP_SHR),
        OP_DIV => p!(OP_DIV),
        OP_REM => p!(OP_REM),
        OP_MULHI => p!(OP_MULHI),
        _ => p!(OP_ROTL),
    }
}

/// Integer types the handlers are specialised for.
macro_rules! by_ty {
    ($it:expr, $f:ident, $($a:expr),*) => {
        match ($it.bits, $it.signed) {
            (64, true) => Some($f::<64, true>($($a),*)),
            (64, false) => Some($f::<64, false>($($a),*)),
            (32, true) => Some($f::<32, true>($($a),*)),
            (32, false) => Some($f::<32, false>($($a),*)),
            (16, true) => Some($f::<16, true>($($a),*)),
            (16, false) => Some($f::<16, false>($($a),*)),
            (8, true) => Some($f::<8, true>($($a),*)),
            (8, false) => Some($f::<8, false>($($a),*)),
            (1, false) => Some($f::<1, false>($($a),*)),
            _ => None,
        }
    };
}

unsafe extern "C" fn h_ineg<const B: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = ext((*c(fp, w, 1)).wrapping_neg(), B, S);
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_inot<const B: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = ext(!*c(fp, w, 1), B, S);
    next!(pc.add(2), fp, cx)
}
fn pick_ineg<const B: u8, const S: bool>() -> H {
    h_ineg::<B, S>
}
fn pick_inot<const B: u8, const S: bool>() -> H {
    h_inot::<B, S>
}
unsafe extern "C" fn h_conv_int<const B: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = ext(*c(fp, w, 1), B, S);
    next!(pc.add(2), fp, cx)
}
fn pick_conv_int<const B: u8, const S: bool>() -> H {
    h_conv_int::<B, S>
}

unsafe extern "C" fn h_ibit<const OP: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let a = *c(fp, w, 1);
    *c(fp, w, 0) = match OP {
        0 => a.count_ones() as u64,
        1 => a.leading_zeros() as u64,
        2 => a.trailing_zeros() as u64,
        3 => a.swap_bytes(),
        _ => a.reverse_bits(),
    };
    next!(pc.add(2), fp, cx)
}

const C_EQ: u8 = 0;
const C_NE: u8 = 1;
const C_LT: u8 = 2;
const C_LE: u8 = 3;
const C_GT: u8 = 4;
const C_GE: u8 = 5;

fn cond_code(c: Cond) -> u8 {
    match c {
        Cond::Eq => C_EQ,
        Cond::Ne => C_NE,
        Cond::Lt => C_LT,
        Cond::Le => C_LE,
        Cond::Gt => C_GT,
        Cond::Ge => C_GE,
    }
}

#[inline(always)]
fn icmp(cc: u8, s: bool, a: u64, b: u64) -> bool {
    if s {
        let (a, b) = (a as i64, b as i64);
        match cc {
            C_EQ => a == b,
            C_NE => a != b,
            C_LT => a < b,
            C_LE => a <= b,
            C_GT => a > b,
            _ => a >= b,
        }
    } else {
        match cc {
            C_EQ => a == b,
            C_NE => a != b,
            C_LT => a < b,
            C_LE => a <= b,
            C_GT => a > b,
            _ => a >= b,
        }
    }
}

unsafe extern "C" fn h_icmp<const CC: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = icmp(CC, S, *c(fp, w, 1), *c(fp, w, 2)) as u64;
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_icmpi<const CC: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = icmp(CC, S, *c(fp, w, 1), *pc.add(2)) as u64;
    next!(pc.add(3), fp, cx)
}
/// super-instruction: compare, keep the flag, branch on it ([h, d|a|b, then, else])
unsafe extern "C" fn h_icmp_br<const CC: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let t = icmp(CC, S, *c(fp, w, 1), *c(fp, w, 2));
    *c(fp, w, 0) = t as u64;
    next!(*pc.add(if t { 2 } else { 3 }) as *const u64, fp, cx)
}
/// [h, d|a, imm, then, else]
unsafe extern "C" fn h_icmpi_br<const CC: u8, const S: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let t = icmp(CC, S, *c(fp, w, 1), *pc.add(2));
    *c(fp, w, 0) = t as u64;
    next!(*pc.add(if t { 3 } else { 4 }) as *const u64, fp, cx)
}

fn pick_icmp(cc: u8, s: bool, kind: u8) -> H {
    macro_rules! p {
        ($c:expr, $s:expr) => {
            match kind {
                0 => h_icmp::<{ $c }, { $s }> as H,
                1 => h_icmpi::<{ $c }, { $s }> as H,
                2 => h_icmp_br::<{ $c }, { $s }> as H,
                _ => h_icmpi_br::<{ $c }, { $s }> as H,
            }
        };
    }
    macro_rules! q {
        ($s:expr) => {
            match cc {
                C_EQ => p!(C_EQ, $s),
                C_NE => p!(C_NE, $s),
                C_LT => p!(C_LT, $s),
                C_LE => p!(C_LE, $s),
                C_GT => p!(C_GT, $s),
                _ => p!(C_GE, $s),
            }
        };
    }
    if s {
        q!(true)
    } else {
        q!(false)
    }
}

// ---- floats: f32 in the low 32 bits of a cell

trait Fl: Copy {
    unsafe fn get(p: *const u64) -> Self;
    unsafe fn put(p: *mut u64, v: Self);
}
impl Fl for f32 {
    #[inline(always)]
    unsafe fn get(p: *const u64) -> f32 {
        f32::from_bits(*p as u32)
    }
    #[inline(always)]
    unsafe fn put(p: *mut u64, v: f32) {
        *p = v.to_bits() as u64
    }
}
impl Fl for f64 {
    #[inline(always)]
    unsafe fn get(p: *const u64) -> f64 {
        f64::from_bits(*p)
    }
    #[inline(always)]
    unsafe fn put(p: *mut u64, v: f64) {
        *p = v.to_bits()
    }
}

macro_rules! fbin_body {
    ($t:ty, $op:expr, $a:expr, $b:expr) => {{
        let (a, b): ($t, $t) = ($a, $b);
        match $op {
            0 => a + b,
            1 => a - b,
            2 => a * b,
            3 => a / b,
            4 => a.min(b),
            5 => a.max(b),
            6 => {
                if a < b {
                    a
                } else {
                    b
                }
            }
            _ => {
                if a > b {
                    a
                } else {
                    b
                }
            }
        }
    }};
}

unsafe extern "C" fn h_fbin32<const OP: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    f32::put(c(fp, w, 0), fbin_body!(f32, OP, f32::get(c(fp, w, 1)), f32::get(c(fp, w, 2))));
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_fbin64<const OP: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    f64::put(c(fp, w, 0), fbin_body!(f64, OP, f64::get(c(fp, w, 1)), f64::get(c(fp, w, 2))));
    next!(pc.add(2), fp, cx)
}

fn fop_code(op: FOp) -> u8 {
    match op {
        FOp::Add => 0,
        FOp::Sub => 1,
        FOp::Mul => 2,
        FOp::Div => 3,
        FOp::Min => 4,
        FOp::Max => 5,
        FOp::MinLt => 6,
        FOp::MaxGt => 7,
    }
}

fn pick_fbin(op: u8, d: bool) -> H {
    macro_rules! p {
        ($o:expr) => {
            if d {
                h_fbin64::<{ $o }> as H
            } else {
                h_fbin32::<{ $o }> as H
            }
        };
    }
    match op {
        0 => p!(0),
        1 => p!(1),
        2 => p!(2),
        3 => p!(3),
        4 => p!(4),
        5 => p!(5),
        6 => p!(6),
        _ => p!(7),
    }
}

macro_rules! fun_body {
    ($op:expr, $a:expr) => {{
        let a = $a;
        match $op {
            0 => -a,
            1 => a.abs(),
            2 => a.sqrt(),
            3 => a.floor(),
            4 => a.ceil(),
            5 => a.trunc(),
            6 => a.round_ties_even(),
            _ => a.round(),
        }
    }};
}
unsafe extern "C" fn h_fun32<const OP: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    f32::put(c(fp, w, 0), fun_body!(OP, f32::get(c(fp, w, 1))));
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_fun64<const OP: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    f64::put(c(fp, w, 0), fun_body!(OP, f64::get(c(fp, w, 1))));
    next!(pc.add(2), fp, cx)
}
fn pick_fun(op: FUn, d: bool) -> H {
    macro_rules! p {
        ($o:expr) => {
            if d {
                h_fun64::<{ $o }> as H
            } else {
                h_fun32::<{ $o }> as H
            }
        };
    }
    match op {
        FUn::Neg => p!(0),
        FUn::Abs => p!(1),
        FUn::Sqrt => p!(2),
        FUn::Floor => p!(3),
        FUn::Ceil => p!(4),
        FUn::Trunc => p!(5),
        FUn::RoundEven => p!(6),
        FUn::RoundAway => p!(7),
    }
}

macro_rules! fcmp_body {
    ($cc:expr, $a:expr, $b:expr) => {{
        let (a, b) = ($a, $b);
        match $cc {
            C_EQ => a == b,
            C_NE => a != b,
            C_LT => a < b,
            C_LE => a <= b,
            C_GT => a > b,
            _ => a >= b,
        }
    }};
}
unsafe extern "C" fn h_fcmp<const CC: u8, const D: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let t = if D { fcmp_body!(CC, f64::get(c(fp, w, 1)), f64::get(c(fp, w, 2))) } else { fcmp_body!(CC, f32::get(c(fp, w, 1)), f32::get(c(fp, w, 2))) };
    *c(fp, w, 0) = t as u64;
    next!(pc.add(2), fp, cx)
}
/// [h, d|a|b, then, else]
unsafe extern "C" fn h_fcmp_br<const CC: u8, const D: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let t = if D { fcmp_body!(CC, f64::get(c(fp, w, 1)), f64::get(c(fp, w, 2))) } else { fcmp_body!(CC, f32::get(c(fp, w, 1)), f32::get(c(fp, w, 2))) };
    *c(fp, w, 0) = t as u64;
    next!(*pc.add(if t { 2 } else { 3 }) as *const u64, fp, cx)
}
fn pick_fcmp(cc: u8, d: bool, br: bool) -> H {
    macro_rules! p {
        ($c:expr) => {
            match (d, br) {
                (true, false) => h_fcmp::<{ $c }, true> as H,
                (false, false) => h_fcmp::<{ $c }, false> as H,
                (true, true) => h_fcmp_br::<{ $c }, true> as H,
                (false, true) => h_fcmp_br::<{ $c }, false> as H,
            }
        };
    }
    match cc {
        C_EQ => p!(C_EQ),
        C_NE => p!(C_NE),
        C_LT => p!(C_LT),
        C_LE => p!(C_LE),
        C_GT => p!(C_GT),
        _ => p!(C_GE),
    }
}

/// d = (np ? -(a*b) : a*b) + (na ? -c : c), one rounding. [h, d|a|b|c, flags]
unsafe extern "C" fn h_fma<const D: bool>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let fl = *pc.add(2);
    if D {
        let (mut a, b, mut z) = (f64::get(c(fp, w, 1)), f64::get(c(fp, w, 2)), f64::get(c(fp, w, 3)));
        if fl & 1 != 0 {
            a = -a;
        }
        if fl & 2 != 0 {
            z = -z;
        }
        f64::put(c(fp, w, 0), a.mul_add(b, z));
    } else {
        let (mut a, b, mut z) = (f32::get(c(fp, w, 1)), f32::get(c(fp, w, 2)), f32::get(c(fp, w, 3)));
        if fl & 1 != 0 {
            a = -a;
        }
        if fl & 2 != 0 {
            z = -z;
        }
        f32::put(c(fp, w, 0), a.mul_add(b, z));
    }
    next!(pc.add(3), fp, cx)
}

/// conversions: [h, d|s, kind]
unsafe extern "C" fn h_conv(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let k = *pc.add(2);
    let s = c(fp, w, 1);
    let d = c(fp, w, 0);
    let kind = k & 0xff;
    let bits = ((k >> 8) & 0xff) as u8;
    let signed = (k >> 16) & 1 != 0;
    let f64_ = (k >> 17) & 1 != 0;
    match kind {
        // int -> float (from u64: unsigned)
        0 => {
            let unsigned64 = bits == 64 && !signed;
            let v = *s;
            if f64_ {
                f64::put(d, if unsigned64 { v as f64 } else { v as i64 as f64 })
            } else {
                f32::put(d, if unsigned64 { v as f32 } else { v as i64 as f32 })
            }
        }
        // float -> int, saturating, NaN -> 0 (Rust `as`)
        1 => {
            let x = if f64_ { f64::get(s) } else { f32::get(s) as f64 };
            *d = match (bits, signed) {
                (64, true) => x as i64 as u64,
                (64, false) => x as u64,
                (32, true) => x as i32 as i64 as u64,
                (32, false) => x as u32 as u64,
                (16, true) => x as i16 as i64 as u64,
                (16, false) => x as u16 as u64,
                (8, true) => x as i8 as i64 as u64,
                _ => x as u8 as u64,
            };
            // f32 sources convert exactly through f64
        }
        2 => f64::put(d, f32::get(s) as f64),
        3 => f32::put(d, f64::get(s) as f32),
        // bits -> float, float -> bits
        4 => *d = if f64_ { *s } else { *s & 0xffff_ffff },
        _ => *d = if f64_ { *s } else { *s & 0xffff_ffff },
    }
    next!(pc.add(3), fp, cx)
}

// ---- memory

/// K: 0 u8, 1 i8, 2 u16, 3 i16, 4 u32, 5 i32, 6 u64
#[inline(always)]
unsafe fn ld<const K: u8>(a: u64) -> u64 {
    match K {
        0 => *(a as *const u8) as u64,
        1 => *(a as *const i8) as i64 as u64,
        2 => std::ptr::read_unaligned(a as *const u16) as u64,
        3 => std::ptr::read_unaligned(a as *const i16) as i64 as u64,
        4 => std::ptr::read_unaligned(a as *const u32) as u64,
        5 => std::ptr::read_unaligned(a as *const i32) as i64 as u64,
        _ => std::ptr::read_unaligned(a as *const u64),
    }
}
#[inline(always)]
unsafe fn st<const Z: u8>(a: u64, v: u64) {
    match Z {
        1 => *(a as *mut u8) = v as u8,
        2 => std::ptr::write_unaligned(a as *mut u16, v as u16),
        4 => std::ptr::write_unaligned(a as *mut u32, v as u32),
        _ => std::ptr::write_unaligned(a as *mut u64, v),
    }
}
/// [h, d|base|-|- off<<32]
unsafe extern "C" fn h_load<const K: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let off = (w >> 32) as i32 as i64 as u64;
    *c(fp, w, 0) = ld::<K>((*c(fp, w, 1)).wrapping_add(off));
    next!(pc.add(2), fp, cx)
}
/// [h, base|src|off<<32]
unsafe extern "C" fn h_store<const Z: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let off = (w >> 32) as i32 as i64 as u64;
    st::<Z>((*c(fp, w, 0)).wrapping_add(off), *c(fp, w, 1));
    next!(pc.add(2), fp, cx)
}
/// [h, d|base|idx|sh, off]
unsafe extern "C" fn h_loadx<const K: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let a = (*c(fp, w, 1)).wrapping_add((*c(fp, w, 2)) << (w >> 48)).wrapping_add(*pc.add(2));
    *c(fp, w, 0) = ld::<K>(a);
    next!(pc.add(3), fp, cx)
}
/// [h, base|idx|src|sh, off]
unsafe extern "C" fn h_storex<const Z: u8>(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let a = (*c(fp, w, 0)).wrapping_add((*c(fp, w, 1)) << (w >> 48)).wrapping_add(*pc.add(2));
    st::<Z>(a, *c(fp, w, 2));
    next!(pc.add(3), fp, cx)
}
/// [h, d|slot offset in bytes << 32]
unsafe extern "C" fn h_slot_addr(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = fp as u64 + (w >> 32);
    next!(pc.add(2), fp, cx)
}
/// a symbol relative to a slot's frame: [h, d|base, off] load through a slot address in one op
unsafe extern "C" fn h_const(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = *pc.add(2);
    next!(pc.add(3), fp, cx)
}
/// [h, n, (cell, value) * n]: the function's constant cells, once per call
unsafe extern "C" fn h_preload(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let n = *pc.add(1) as usize;
    for k in 0..n {
        *fp.add(*pc.add(2 + 2 * k) as usize) = *pc.add(3 + 2 * k);
    }
    next!(pc.add(2 + 2 * n), fp, cx)
}
unsafe extern "C" fn h_mov(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = *c(fp, w, 1);
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_mov16(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = *c(fp, w, 1);
    *c(fp, w, 0).add(1) = *c(fp, w, 1).add(1);
    next!(pc.add(2), fp, cx)
}
/// [h, dst|src, size]
unsafe extern "C" fn h_copy(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    std::ptr::copy(*c(fp, w, 1) as *const u8, *c(fp, w, 0) as *mut u8, *pc.add(2) as usize);
    next!(pc.add(3), fp, cx)
}
/// [h, d|c|a|b]
unsafe extern "C" fn h_sel(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = if *c(fp, w, 1) != 0 { *c(fp, w, 2) } else { *c(fp, w, 3) };
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_sel16(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let s = if *c(fp, w, 1) != 0 { c(fp, w, 2) } else { c(fp, w, 3) };
    let (x, y) = (*s, *s.add(1));
    *c(fp, w, 0) = x;
    *c(fp, w, 0).add(1) = y;
    next!(pc.add(2), fp, cx)
}

#[inline(always)]
unsafe fn tls_block(cx: *mut Cx) -> u64 {
    if (*cx).tls_block == 0 {
        (*cx).tls_block = relax_interp_tls(TLS_GLUE.load(Ordering::Relaxed));
    }
    (*cx).tls_block
}
/// d = this thread's domain static block + value. [h, d, value]
unsafe extern "C" fn h_dom_addr(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let base = *(tls_block(cx) as *const u64);
    *c(fp, w, 0) = base.wrapping_add(*pc.add(2));
    next!(pc.add(3), fp, cx)
}
/// d = this thread's thread-local block + value. [h, d, value]
unsafe extern "C" fn h_tls_addr(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    *c(fp, w, 0) = tls_block(cx).wrapping_add(*pc.add(2));
    next!(pc.add(3), fp, cx)
}

// ---- atomics: [h, d|addr|src|new, mem code | op << 8 | volatile << 16]

#[inline(always)]
fn mem_code(m: Mem) -> u64 {
    match m {
        Mem::Int(1, false) => 0,
        Mem::Int(1, true) => 1,
        Mem::Int(2, false) => 2,
        Mem::Int(2, true) => 3,
        Mem::Int(4, false) => 4,
        Mem::Int(4, true) => 5,
        Mem::F32 => 4,
        _ => 6,
    }
}
#[inline(always)]
fn mem_ext(k: u64, v: u64) -> u64 {
    match k {
        0 => v as u8 as u64,
        1 => v as u8 as i8 as i64 as u64,
        2 => v as u16 as u64,
        3 => v as u16 as i16 as i64 as u64,
        4 => v as u32 as u64,
        5 => v as u32 as i32 as i64 as u64,
        _ => v,
    }
}

unsafe extern "C" fn h_atomic_load(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    use std::sync::atomic::*;
    let w = *pc.add(1);
    let k = *pc.add(2) & 0xff;
    let a = *c(fp, w, 1);
    let v = match k {
        0 | 1 => (*(a as *const AtomicU8)).load(Ordering::SeqCst) as u64,
        2 | 3 => (*(a as *const AtomicU16)).load(Ordering::SeqCst) as u64,
        4 | 5 => (*(a as *const AtomicU32)).load(Ordering::SeqCst) as u64,
        _ => (*(a as *const AtomicU64)).load(Ordering::SeqCst),
    };
    *c(fp, w, 0) = mem_ext(k, v);
    next!(pc.add(3), fp, cx)
}
unsafe extern "C" fn h_atomic_store(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    use std::sync::atomic::*;
    let w = *pc.add(1);
    let k = *pc.add(2) & 0xff;
    let (a, v) = (*c(fp, w, 0), *c(fp, w, 1));
    match k {
        0 | 1 => (*(a as *const AtomicU8)).store(v as u8, Ordering::SeqCst),
        2 | 3 => (*(a as *const AtomicU16)).store(v as u16, Ordering::SeqCst),
        4 | 5 => (*(a as *const AtomicU32)).store(v as u32, Ordering::SeqCst),
        _ => (*(a as *const AtomicU64)).store(v, Ordering::SeqCst),
    }
    next!(pc.add(3), fp, cx)
}

macro_rules! rmw {
    ($au:ty, $ai:ty, $ut:ty, $it:ty, $a:expr, $v:expr, $op:expr) => {{
        let au = &*($a as *const $au);
        let ai = &*($a as *const $ai);
        let v = $v;
        let o = Ordering::SeqCst;
        (match $op {
            0 => au.swap(v as $ut, o),
            1 => au.fetch_add(v as $ut, o),
            2 => au.fetch_sub(v as $ut, o),
            3 => au.fetch_and(v as $ut, o),
            4 => au.fetch_nand(v as $ut, o),
            5 => au.fetch_or(v as $ut, o),
            6 => au.fetch_xor(v as $ut, o),
            7 => ai.fetch_max(v as $it, o) as $ut,
            8 => ai.fetch_min(v as $it, o) as $ut,
            9 => au.fetch_max(v as $ut, o),
            _ => au.fetch_min(v as $ut, o),
        }) as u64
    }};
}

unsafe extern "C" fn h_atomic_rmw(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    use std::sync::atomic::*;
    let w = *pc.add(1);
    let x = *pc.add(2);
    let (k, op) = (x & 0xff, (x >> 8) & 0xff);
    let (a, v) = (*c(fp, w, 1), *c(fp, w, 2));
    let old = match k {
        0 | 1 => rmw!(AtomicU8, AtomicI8, u8, i8, a, v, op),
        2 | 3 => rmw!(AtomicU16, AtomicI16, u16, i16, a, v, op),
        4 | 5 => rmw!(AtomicU32, AtomicI32, u32, i32, a, v, op),
        _ => rmw!(AtomicU64, AtomicI64, u64, i64, a, v, op),
    };
    *c(fp, w, 0) = mem_ext(k, old);
    next!(pc.add(3), fp, cx)
}
unsafe extern "C" fn h_atomic_cas(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    use std::sync::atomic::*;
    let w = *pc.add(1);
    let k = *pc.add(2) & 0xff;
    let (a, e, n) = (*c(fp, w, 1), *c(fp, w, 2), *c(fp, w, 3));
    let o = Ordering::SeqCst;
    let old = match k {
        0 | 1 => (*(a as *const AtomicU8)).compare_exchange(e as u8, n as u8, o, o).unwrap_or_else(|x| x) as u64,
        2 | 3 => (*(a as *const AtomicU16)).compare_exchange(e as u16, n as u16, o, o).unwrap_or_else(|x| x) as u64,
        4 | 5 => (*(a as *const AtomicU32)).compare_exchange(e as u32, n as u32, o, o).unwrap_or_else(|x| x) as u64,
        _ => (*(a as *const AtomicU64)).compare_exchange(e, n, o, o).unwrap_or_else(|x| x),
    };
    *c(fp, w, 0) = mem_ext(k, old);
    next!(pc.add(3), fp, cx)
}
unsafe extern "C" fn h_fence(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    if *pc.add(1) != 0 {
        std::sync::atomic::compiler_fence(Ordering::SeqCst);
    } else {
        std::sync::atomic::fence(Ordering::SeqCst);
    }
    next!(pc.add(2), fp, cx)
}
/// [h, cell, write?]
unsafe extern "C" fn h_fpenv(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    #[cfg(target_arch = "aarch64")]
    {
        if *pc.add(2) != 0 {
            let v = *c(fp, w, 0);
            std::arch::asm!("msr fpcr, {}", in(reg) v);
        } else {
            let v: u64;
            std::arch::asm!("mrs {}, fpcr", out(reg) v);
            *c(fp, w, 0) = v;
        }
    }
    let _ = w;
    next!(pc.add(3), fp, cx)
}

// ---- 128-bit vectors (four 32-bit lanes; cells hold 16 bytes)

#[inline(always)]
unsafe fn vget(p: *const u64) -> [u32; 4] {
    std::ptr::read_unaligned(p as *const [u32; 4])
}
#[inline(always)]
unsafe fn vput(p: *mut u64, v: [u32; 4]) {
    std::ptr::write_unaligned(p as *mut [u32; 4], v)
}
#[inline(always)]
fn fl(x: u32) -> f32 {
    f32::from_bits(x)
}
#[inline(always)]
fn nan_min(a: f32, b: f32, max: bool) -> f32 {
    if a.is_nan() || b.is_nan() {
        return a + b;
    }
    if a == b {
        // signed zeros: min prefers -0, max +0
        return if max { f32::from_bits(a.to_bits() & b.to_bits()) } else { f32::from_bits(a.to_bits() | b.to_bits()) };
    }
    if (a < b) != max {
        a
    } else {
        b
    }
}

/// [h, d|a|b, op code]
unsafe extern "C" fn h_vbin(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let op = *pc.add(2);
    let (a, b) = (vget(c(fp, w, 1)), vget(c(fp, w, 2)));
    let mut r = [0u32; 4];
    for i in 0..4 {
        let (x, y) = (a[i], b[i]);
        r[i] = match op & 0xff {
            0 => (fl(x) + fl(y)).to_bits(),
            1 => (fl(x) - fl(y)).to_bits(),
            2 => (fl(x) * fl(y)).to_bits(),
            3 => (fl(x) / fl(y)).to_bits(),
            4 => nan_min(fl(x), fl(y), false).to_bits(),
            5 => nan_min(fl(x), fl(y), true).to_bits(),
            6 => if fl(x) < fl(y) { x } else { y },
            7 => if fl(x) > fl(y) { x } else { y },
            8 => x.wrapping_add(y),
            9 => x.wrapping_sub(y),
            10 => x.wrapping_mul(y),
            11 => x & y,
            12 => x | y,
            13 => x ^ y,
            14 => x & !y,
            15 => x.min(y),
            16 => if y >= 32 { 0 } else { x << y },
            17 => ((x as i32) >> y.min(31)) as u32,
            18 => if y >= 32 { 0 } else { x >> y },
            19 => if fcmp_body!(((op >> 8) & 0xff) as u8, fl(x), fl(y)) { u32::MAX } else { 0 },
            _ => if icmp(((op >> 8) & 0xff) as u8, true, x as i32 as i64 as u64, y as i32 as i64 as u64) { u32::MAX } else { 0 },
        };
    }
    vput(c(fp, w, 0), r);
    next!(pc.add(3), fp, cx)
}
fn vop_code(op: VOp) -> u64 {
    match op {
        VOp::FAdd | VOp::FAddIntel | VOp::FAddNeon => 0,
        VOp::FSub | VOp::FSubIntel | VOp::FSubNeon => 1,
        VOp::FMul | VOp::FMulIntel | VOp::FMulNeon => 2,
        VOp::FDiv | VOp::FDivIntel | VOp::FDivNeon => 3,
        VOp::FMinNeon => 4,
        VOp::FMaxNeon => 5,
        VOp::FMinLt => 6,
        VOp::FMaxGt => 7,
        VOp::IAdd => 8,
        VOp::ISub => 9,
        VOp::IMul => 10,
        VOp::And => 11,
        VOp::Or => 12,
        VOp::Xor => 13,
        VOp::AndNot => 14,
        VOp::UMin => 15,
        VOp::Shl => 16,
        VOp::ShrS => 17,
        VOp::ShrU => 18,
        VOp::FCmp(c) => 19 | (cond_code(c) as u64) << 8,
        VOp::ICmp(c) => 20 | (cond_code(c) as u64) << 8,
    }
}
/// [h, d|a, op code]
unsafe extern "C" fn h_vun(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let op = *pc.add(2);
    let a = vget(c(fp, w, 1));
    let mut r = [0u32; 4];
    for i in 0..4 {
        let x = a[i];
        r[i] = match op {
            0 => (-fl(x)).to_bits(),
            1 => fl(x).abs().to_bits(),
            2 => fl(x).sqrt().to_bits(),
            3 => fl(x).floor().to_bits(),
            4 => fl(x).ceil().to_bits(),
            5 => fl(x).trunc().to_bits(),
            6 => fl(x).round().to_bits(),
            7 => fl(x) as i32 as u32,
            8 => (x as i32 as f32).to_bits(),
            _ => (x as i32).wrapping_neg() as u32,
        };
    }
    vput(c(fp, w, 0), r);
    next!(pc.add(3), fp, cx)
}
fn vun_code(op: VUn) -> u64 {
    match op {
        VUn::FNeg => 0,
        VUn::FAbs => 1,
        VUn::FSqrt | VUn::FSqrtIntel | VUn::FSqrtNeon => 2,
        VUn::FFloor => 3,
        VUn::FCeil => 4,
        VUn::FTrunc => 5,
        VUn::FRoundAway => 6,
        VUn::FToI => 7,
        VUn::IToF => 8,
        VUn::INeg => 9,
    }
}
/// [h, d|m|a|b]
unsafe extern "C" fn h_vsel(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let (m, a, b) = (vget(c(fp, w, 1)), vget(c(fp, w, 2)), vget(c(fp, w, 3)));
    let mut r = [0u32; 4];
    for i in 0..4 {
        r[i] = (m[i] & a[i]) | (!m[i] & b[i]);
    }
    vput(c(fp, w, 0), r);
    next!(pc.add(2), fp, cx)
}
/// [h, d|a|b|c, flags]
unsafe extern "C" fn h_vfma(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let fl_ = *pc.add(2);
    let (a, b, z) = (vget(c(fp, w, 1)), vget(c(fp, w, 2)), vget(c(fp, w, 3)));
    let mut r = [0u32; 4];
    for i in 0..4 {
        let mut x = fl(a[i]);
        let mut y = fl(z[i]);
        if fl_ & 1 != 0 {
            x = -x;
        }
        if fl_ & 2 != 0 {
            y = -y;
        }
        r[i] = x.mul_add(fl(b[i]), y).to_bits();
    }
    vput(c(fp, w, 0), r);
    next!(pc.add(3), fp, cx)
}
/// [h, d|s]
unsafe extern "C" fn h_vsplat(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let x = *c(fp, w, 1) as u32;
    vput(c(fp, w, 0), [x; 4]);
    next!(pc.add(2), fp, cx)
}
/// [h, d, bits]
unsafe extern "C" fn h_vconst(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    vput(c(fp, w, 0), [*pc.add(2) as u32; 4]);
    next!(pc.add(3), fp, cx)
}
/// [h, d|v|lane|is_int]
unsafe extern "C" fn h_vextract(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let x = vget(c(fp, w, 1))[((w >> 32) & 3) as usize];
    *c(fp, w, 0) = if (w >> 48) != 0 { x as i32 as i64 as u64 } else { x as u64 };
    next!(pc.add(2), fp, cx)
}
/// [h, d|v|s|lane]
unsafe extern "C" fn h_vinsert(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let mut v = vget(c(fp, w, 1));
    v[((w >> 48) & 3) as usize] = *c(fp, w, 2) as u32;
    vput(c(fp, w, 0), v);
    next!(pc.add(2), fp, cx)
}
/// [h, d|base|off<<32]
unsafe extern "C" fn h_vload(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let a = (*c(fp, w, 1)).wrapping_add((w >> 32) as i32 as i64 as u64);
    let v = std::ptr::read_unaligned(a as *const [u32; 4]);
    vput(c(fp, w, 0), v);
    next!(pc.add(2), fp, cx)
}
/// [h, base|src|off<<32]
unsafe extern "C" fn h_vstore(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let a = (*c(fp, w, 0)).wrapping_add((w >> 32) as i32 as i64 as u64);
    std::ptr::write_unaligned(a as *mut [u32; 4], vget(c(fp, w, 1)));
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_vany(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let v = vget(c(fp, w, 1));
    *c(fp, w, 0) = (v.iter().any(|x| *x != 0)) as u64;
    next!(pc.add(2), fp, cx)
}
unsafe extern "C" fn h_vgather(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let base = *c(fp, w, 1);
    let idx = vget(c(fp, w, 2));
    let mut r = [0u32; 4];
    for i in 0..4 {
        r[i] = std::ptr::read_unaligned((base + 4 * idx[i] as u64) as *const u32);
    }
    vput(c(fp, w, 0), r);
    next!(pc.add(2), fp, cx)
}
/// [h, d|a|amount, op]
unsafe extern "C" fn h_vshift(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let w = *pc.add(1);
    let k = ((w >> 32) & 0xffff) as u32;
    let op = *pc.add(2);
    let mut v = vget(c(fp, w, 1));
    for x in v.iter_mut() {
        *x = match op {
            16 => if k >= 32 { 0 } else { *x << k },
            17 => ((*x as i32) >> k.min(31)) as u32,
            _ => if k >= 32 { 0 } else { *x >> k },
        };
    }
    vput(c(fp, w, 0), v);
    next!(pc.add(3), fp, cx)
}

// ---- control

unsafe extern "C" fn h_jump(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    next!(*pc.add(1) as *const u64, fp, cx)
}
/// [h, c, then, else]
unsafe extern "C" fn h_branch(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let t = *fp.add(*pc.add(1) as usize) != 0;
    next!(*pc.add(if t { 2 } else { 3 }) as *const u64, fp, cx)
}
unsafe extern "C" fn h_ret0(_pc: *const u64, _fp: *mut u64, _cx: *mut Cx) {}
/// [h, cell] one integer result
unsafe extern "C" fn h_ret_i(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    (*cx).ret[0] = *fp.add(*pc.add(1) as usize);
}
/// [h, n, (cell | class << 32) * n]
unsafe extern "C" fn h_ret(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let n = *pc.add(1) as usize;
    let (mut ni, mut nf) = (0usize, 0usize);
    for k in 0..n {
        let x = *pc.add(2 + k);
        let p = fp.add((x & 0xffff_ffff) as usize);
        match x >> 32 {
            0 => {
                (*cx).ret[ni] = *p;
                ni += 1;
            }
            cls => {
                (*cx).ret[2 + 2 * nf] = *p;
                (*cx).ret[3 + 2 * nf] = if cls == 3 { *p.add(1) } else { 0 };
                nf += 1;
            }
        }
    }
}
unsafe extern "C" fn h_trap(pc: *const u64, _fp: *mut u64, _cx: *mut Cx) {
    let what = match *pc.add(1) {
        0 => "unreachable code",
        _ => "unwinding resumed in interpreted code (not supported by the prototype)",
    };
    eprintln!("relax-interp: {}", what);
    std::process::abort();
}

// ---- calls

enum Target {
    /// a slot's table word (its current code)
    Table(u64),
    /// a function pointer in a cell
    Cell(u32),
    /// a fixed address (runtime entry, C symbol)
    Addr(u64),
}

/// The callee an inline cache found for a target word: (word, interpreted fn or null).
struct Ic {
    word: u64,
    f: *const IFunc,
}

struct CallDesc {
    target: Target,
    /// argument cells and classes (C calls: ABI vregs, result address first)
    args: Vec<(u32, Cls)>,
    rets: Vec<(u32, Cls)>,
    csig: Option<(Box<CSig>, cabi::Plan)>,
    /// words of the caller's frame: callee frames start past it
    frame_words: usize,
    ic: AtomicPtr<Ic>,
}

/// The interpreted function a native code address leads to: a pool thunk, a jump to one
/// (the slot's code), or a slot thunk whose table word is one of those.
unsafe fn decode(mut a: u64) -> *const IFunc {
    let pool = pool_base();
    for _ in 0..3 {
        if a >= pool && a < pool + 8 * POOL as u64 {
            return FUNCS[((a - pool) / 8) as usize].load(Ordering::Acquire);
        }
        if a == 0 || a & 3 != 0 {
            return std::ptr::null();
        }
        let w = std::slice::from_raw_parts(a as *const u32, 6);
        // movz x16, #i0; movk x16, #i1, lsl 16; movk #i2, lsl 32; movk #i3, lsl 48
        if w[0] & 0xFFE0_001F != 0xD280_0010 {
            return std::ptr::null();
        }
        let mut v = ((w[0] >> 5) & 0xffff) as u64;
        for k in 1..4 {
            if w[k] & 0xFFE0_001F != (0xF280_0010 | (k as u32) << 21) {
                return std::ptr::null();
            }
            v |= (((w[k] >> 5) & 0xffff) as u64) << (16 * k);
        }
        if w[4] == 0xD61F_0200 {
            // br x16: the slot's code is a jump to v
            a = v;
        } else if w[4] == 0xF940_0210 && w[5] == 0xD61F_0200 {
            // ldr x16, [x16]; br x16: a slot thunk through table word v
            a = *(v as *const u64);
        } else {
            return std::ptr::null();
        }
    }
    std::ptr::null()
}

#[inline(always)]
unsafe fn resolve(d: &CallDesc, word: u64) -> *const IFunc {
    let ic = d.ic.load(Ordering::Acquire);
    if !ic.is_null() && (*ic).word == word {
        return (*ic).f;
    }
    let f = decode(word);
    // the replaced cache entry is leaked (another thread may still read it)
    d.ic.store(Box::into_raw(Box::new(Ic { word, f })), Ordering::Release);
    f
}

/// [h, desc]
unsafe extern "C" fn h_call(pc: *const u64, fp: *mut u64, cx: *mut Cx) {
    let d = &*(*pc.add(1) as *const CallDesc);
    do_call(d, fp, cx);
    next!(pc.add(2), fp, cx)
}

/// Out of line: the handler that calls it keeps no frame, so its jump to the next handler stays
/// a tail call (an inlined call frame turned it into call + return: native stack growth per call).
#[inline(never)]
unsafe fn do_call(d: &CallDesc, fp: *mut u64, cx: *mut Cx) {
    let word = match d.target {
        Target::Table(t) => *(t as *const u64),
        Target::Cell(k) => *fp.add(k as usize),
        Target::Addr(a) => a,
    };
    let saved_top = (*cx).top;
    let fp2 = fp.add(d.frame_words);
    if d.csig.is_none() && !matches!(d.target, Target::Addr(_)) {
        let f = resolve(d, word);
        if !f.is_null() {
            // interpreted -> interpreted: same stack, arguments cell to cell
            if COUNT {
                (*cx).n[1] += 1;
            }
            let f = &*f;
            let top = fp2.add(f.frame_words);
            if top > (*cx).limit {
                overflow();
            }
            (*cx).top = top;
            for (k, &(cell, cls)) in d.args.iter().enumerate() {
                let dst = fp2.add(f.params[k].0 as usize);
                let src = fp.add(cell as usize);
                *dst = *src;
                if cls == Cls::V128 {
                    *dst.add(1) = *src.add(1);
                }
            }
            run(f, fp2, cx);
            (*cx).top = saved_top;
            let (mut ni, mut nf) = (0usize, 0usize);
            for &(cell, cls) in &d.rets {
                let dst = fp.add(cell as usize);
                if cls == Cls::I {
                    *dst = (*cx).ret[ni];
                    ni += 1;
                } else {
                    *dst = (*cx).ret[2 + 2 * nf];
                    if cls == Cls::V128 {
                        *dst.add(1) = (*cx).ret[3 + 2 * nf];
                    }
                    nf += 1;
                }
            }
            return;
        }
    }
    // interpreted -> native through the call glue; native code that calls back into the
    // interpreter starts its frames past this one
    (*cx).top = fp2;
    if COUNT {
        (*cx).n[2] += 1;
    }
    if TRACE.load(Ordering::Relaxed) {
        eprintln!("interp: native call {:#x} args {:?}", word, d.args.iter().map(|a| *fp.add(a.0 as usize)).collect::<Vec<_>>());
    }
    let mut regs = [0u64; RB_WORDS];
    let mut stack = [0u64; 32];
    let mut nstack = 0usize;
    match &d.csig {
        None => {
            let (mut ni, mut nf) = (0usize, 0usize);
            for &(cell, cls) in &d.args {
                let src = fp.add(cell as usize);
                if cls == Cls::I && ni < 8 {
                    regs[ni] = *src;
                    ni += 1;
                } else if cls != Cls::I && nf < 8 {
                    regs[RB_Q + 2 * nf] = *src;
                    if cls == Cls::V128 {
                        regs[RB_Q + 2 * nf + 1] = *src.add(1);
                    }
                    nf += 1;
                } else {
                    stack[nstack] = *src;
                    nstack += 1;
                }
            }
            relax_interp_call(word, regs.as_mut_ptr(), stack.as_ptr(), nstack as u64);
            let (mut ni, mut nf) = (0usize, 0usize);
            for &(cell, cls) in &d.rets {
                let dst = fp.add(cell as usize);
                if cls == Cls::I {
                    *dst = regs[ni];
                    ni += 1;
                } else {
                    *dst = regs[RB_Q + 2 * nf];
                    if cls == Cls::V128 {
                        *dst.add(1) = regs[RB_Q + 2 * nf + 1];
                    }
                    nf += 1;
                }
            }
        }
        Some((sig, plan)) => {
            let skip = sig.ret.is_some() as usize;
            let sbytes = stack.as_mut_ptr() as *mut u8;
            let put = |regs: &mut [u64; RB_WORDS], loc: PLoc, v: u64, size: u32| match loc {
                PLoc::Int(n) => regs[n as usize] = v,
                PLoc::Flt(n) => {
                    regs[RB_Q + 2 * n as usize] = v;
                    regs[RB_Q + 2 * n as usize + 1] = 0;
                }
                PLoc::Stack(o) => std::ptr::copy_nonoverlapping(&v as *const u64 as *const u8, sbytes.add(o as usize), size.min(8) as usize),
            };
            for (j, ap) in plan.args.iter().enumerate() {
                let v = *fp.add(d.args[skip + j].0 as usize);
                match ap {
                    ArgPlan::Scalar(loc, size) => put(&mut regs, *loc, v, *size),
                    ArgPlan::Parts(parts) => {
                        for p in parts {
                            let mut x = 0u64;
                            std::ptr::copy_nonoverlapping((v + p.off as u64) as *const u8, &mut x as *mut u64 as *mut u8, p.size as usize);
                            put(&mut regs, p.loc, x, p.size);
                        }
                    }
                    ArgPlan::ByRef(loc) => put(&mut regs, *loc, v, 8),
                    ArgPlan::Stack(off, size) => std::ptr::copy_nonoverlapping(v as *const u8, sbytes.add(*off as usize), *size as usize),
                }
            }
            nstack = (plan.stack_bytes as usize + 7) / 8;
            let ret_addr = if skip == 1 { *fp.add(d.args[0].0 as usize) } else { 0 };
            if matches!(plan.ret, RetPlan::Indirect) {
                regs[RB_X8] = ret_addr;
            }
            relax_interp_call(word, regs.as_mut_ptr(), stack.as_ptr(), nstack as u64);
            match &plan.ret {
                RetPlan::Parts(parts) => {
                    for p in parts {
                        let v = match p.loc {
                            PLoc::Int(n) => regs[n as usize],
                            PLoc::Flt(n) => regs[RB_Q + 2 * n as usize],
                            PLoc::Stack(_) => 0,
                        };
                        std::ptr::copy_nonoverlapping(&v as *const u64 as *const u8, (ret_addr + p.off as u64) as *mut u8, p.size as usize);
                    }
                }
                _ => {
                    let (mut ni, mut nf) = (0usize, 0usize);
                    for &(cell, cls) in &d.rets {
                        let dst = fp.add(cell as usize);
                        if cls == Cls::I {
                            let mut v = regs[ni];
                            if let Some(it) = sig.ret_narrow {
                                v = ext(v, it.bits, it.signed);
                            }
                            *dst = v;
                            ni += 1;
                        } else {
                            *dst = regs[RB_Q + 2 * nf];
                            nf += 1;
                        }
                    }
                }
            }
        }
    }
    (*cx).top = saved_top;
}

// ---------------------------------------------------------------- lowering RIR -> threaded code

struct Lw<'a> {
    f: &'a Func,
    code: Vec<u64>,
    /// (word index, block) to patch with the block's address
    fix: Vec<(usize, u32)>,
    cell: Vec<u32>,
    slot_off: Vec<u32>,
    frame_words: usize,
    /// counting builds: the RIR operation being lowered
    cur: String,
}

fn mem_load_kind(m: Mem) -> u8 {
    match m {
        Mem::Int(1, false) => 0,
        Mem::Int(1, true) => 1,
        Mem::Int(2, false) => 2,
        Mem::Int(2, true) => 3,
        Mem::Int(4, false) | Mem::F32 => 4,
        Mem::Int(4, true) => 5,
        _ => 6,
    }
}
fn mem_size(m: Mem) -> u8 {
    match m {
        Mem::Int(b, _) => b,
        Mem::F32 => 4,
        Mem::F64 => 8,
    }
}
fn pick_load(k: u8, x: bool) -> H {
    macro_rules! p {
        ($k:expr) => {
            if x {
                h_loadx::<{ $k }> as H
            } else {
                h_load::<{ $k }> as H
            }
        };
    }
    match k {
        0 => p!(0),
        1 => p!(1),
        2 => p!(2),
        3 => p!(3),
        4 => p!(4),
        5 => p!(5),
        _ => p!(6),
    }
}
fn pick_store(z: u8, x: bool) -> H {
    macro_rules! p {
        ($k:expr) => {
            if x {
                h_storex::<{ $k }> as H
            } else {
                h_store::<{ $k }> as H
            }
        };
    }
    match z {
        1 => p!(1),
        2 => p!(2),
        4 => p!(4),
        _ => p!(8),
    }
}

impl<'a> Lw<'a> {
    fn r(&self, v: VReg) -> u64 {
        self.cell[v.0 as usize] as u64
    }
    fn w4(&self, a: VReg, b: VReg, c: VReg, d: VReg) -> u64 {
        self.r(a) | self.r(b) << 16 | self.r(c) << 32 | self.r(d) << 48
    }
    fn w3(&self, a: VReg, b: VReg, c: VReg) -> u64 {
        self.r(a) | self.r(b) << 16 | self.r(c) << 32
    }
    fn w2(&self, a: VReg, b: VReg) -> u64 {
        self.r(a) | self.r(b) << 16
    }
    fn emit(&mut self, h: H, ws: &[u64]) {
        if COUNT {
            let mut g = HNAMES.lock().unwrap_or_else(|e| e.into_inner());
            if !g.iter().any(|x| x.0 == h as usize as u64) {
                g.push((h as usize as u64, self.cur.clone()));
            }
        }
        self.code.push(h as usize as u64);
        self.code.extend_from_slice(ws);
    }
    fn target(&mut self, b: u32) {
        self.fix.push((self.code.len(), b));
        self.code.push(0);
    }
    fn cls(&self, v: VReg) -> Cls {
        self.f.vregs[v.0 as usize]
    }
}

fn lower(f: &Func, slots: SlotsPtr, syms: u64, sym_class: u64) -> Result<IFunc, &'static str> {
    // frame: one cell per vreg (two for V128), then the stack slots, then C ABI buffers
    let mut cell = Vec::with_capacity(f.vregs.len());
    let mut n = 0u32;
    for c in &f.vregs {
        cell.push(n);
        n += if *c == Cls::V128 { 2 } else { 1 };
    }
    if n > 0xffff {
        return Err("more than 65535 frame cells");
    }
    let mut bytes = (n as u64 * 8 + 15) & !15;
    let mut slot_off = Vec::with_capacity(f.slots.len());
    for s in &f.slots {
        if s.align > 64 {
            return Err("stack slot aligned beyond 64 bytes");
        }
        let a = s.align.max(1) as u64;
        bytes = (bytes + a - 1) / a * a;
        slot_off.push(bytes as u32);
        bytes += s.size as u64;
    }
    // C ABI body: aggregates arriving in registers are rebuilt in the frame
    let mut cplan = None;
    if let Some(sig) = &f.cabi {
        let plan = cabi::plan(sig, cabi::HOST);
        let mut bufs = vec![0u32; plan.args.len()];
        for (j, ap) in plan.args.iter().enumerate() {
            if let ArgPlan::Parts(_) = ap {
                let CArg::Agg(agg) = &sig.args[j] else { return Err("C parameter pieces of a scalar") };
                let a = agg.align.max(8) as u64;
                bytes = (bytes + a - 1) / a * a;
                bufs[j] = bytes as u32;
                bytes += agg.size as u64;
            }
        }
        let mut retbuf = 0u32;
        if let (RetPlan::Parts(_), Some(agg)) = (&plan.ret, &sig.ret) {
            let a = agg.align.max(8) as u64;
            bytes = (bytes + a - 1) / a * a;
            retbuf = bytes as u32;
            bytes += agg.size as u64;
        }
        if f.params.len() != sig.args.len() + sig.ret.is_some() as usize {
            return Err("C body parameter count");
        }
        cplan = Some((sig.clone(), plan, bufs, retbuf));
    }
    if bytes >= 1 << 31 {
        return Err("frame too large");
    }
    let frame_words = (((bytes + 63) & !63) / 8) as usize;
    // Relax ABI: vectors past the eighth float register are not passed on the stack here
    if f.cabi.is_none() {
        let nf = f.params.iter().filter(|p| f.vregs[p.0 as usize] != Cls::I).count();
        if nf > 8 && f.params.iter().any(|p| f.vregs[p.0 as usize] == Cls::V128) {
            return Err("vector parameter on the stack");
        }
    }
    // a vreg whose every definition is the same integer constant (O1 leaves bounds-check flags
    // like this in non-SSA RIR): a branch on it is a jump
    let mut konst: Vec<Option<Option<i64>>> = vec![None; f.vregs.len()];
    if std::env::var_os("MAKEPAD_RUN_INTERP_NOFOLD").is_none() {
        for p in &f.params {
            konst[p.0 as usize] = Some(None);
        }
        for b in &f.blocks {
            for i in &b.insts {
                let mut defs: Vec<VReg> = Vec::new();
                let k = match i {
                    Inst::Iconst(d, v) => {
                        defs.push(*d);
                        Some(*v)
                    }
                    Inst::Fconst(d, bits, _) => {
                        defs.push(*d);
                        Some(*bits as i64)
                    }
                    Inst::Addr(d, sym) if SymClass::of(sym_class, sym.id) != SymClass::Domain => {
                        defs.push(*d);
                        Some(unsafe { sym.value(syms) } as i64)
                    }
                    Inst::FnAddr(d, id) => {
                        defs.push(*d);
                        Some(slots.callable(*id) as i64)
                    }
                    _ => {
                        defs_of(i, &mut defs);
                        None
                    }
                };
                for d in defs {
                    let e = &mut konst[d.0 as usize];
                    *e = match (*e, k) {
                        (None, Some(v)) => Some(Some(v)),
                        (Some(Some(a)), Some(v)) if a == v => Some(Some(a)),
                        _ => Some(None),
                    };
                }
            }
        }
    }
    let konst_of = |v: VReg| konst[v.0 as usize].flatten();
    // constant cells defined inside loops: written once on entry, their defining instructions
    // dropped (a constant on a straight path stays an instruction: preloading it would cost every
    // call). Loops in layout order: a back edge b -> t (t <= b) marks blocks t..=b.
    let mut in_loop = vec![false; f.blocks.len()];
    for (bi, b) in f.blocks.iter().enumerate() {
        for t in b.term.succs() {
            if (t as usize) <= bi {
                for x in in_loop.iter_mut().take(bi + 1).skip(t as usize) {
                    *x = true;
                }
            }
        }
    }
    let mut hoist = vec![false; f.vregs.len()];
    if std::env::var_os("MAKEPAD_RUN_INTERP_NOPRELOAD").is_none() {
        for (bi, b) in f.blocks.iter().enumerate() {
            if !in_loop[bi] {
                continue;
            }
            for i in &b.insts {
                if let Inst::Iconst(d, _) | Inst::Fconst(d, _, _) | Inst::Addr(d, _) | Inst::FnAddr(d, _) = i {
                    if konst[d.0 as usize].flatten().is_some() {
                        hoist[d.0 as usize] = true;
                    }
                }
            }
        }
    }
    let preload: Vec<(u32, u64)> = (0..f.vregs.len()).filter(|v| hoist[*v]).filter_map(|v| konst[v].flatten().map(|k| (v as u32, k as u64))).collect();
    let mut l = Lw { f, code: Vec::new(), fix: Vec::new(), cell, slot_off, frame_words, cur: String::new() };
    let mut block_at = vec![0usize; f.blocks.len()];
    if !preload.is_empty() {
        let mut ws = vec![preload.len() as u64];
        for (v, k) in &preload {
            ws.push(l.cell[*v as usize] as u64);
            ws.push(*k);
        }
        l.cur = "const preload (entry)".into();
        l.emit(h_preload, &ws);
    }
    let sym_val = |s: Sym| unsafe { s.value(syms) };
    for (bi, b) in f.blocks.iter().enumerate() {
        block_at[bi] = l.code.len();
        let ni = b.insts.len();
        // compare + branch on its flag: one super-instruction
        let fuse = match (&b.term, b.insts.last()) {
            (Term::Branch(cv, _, _), Some(Inst::ICmp(_, _, d, _, _) | Inst::ICmpI(_, _, d, _, _) | Inst::FCmp(_, _, d, _, _))) => d == cv,
            _ => false,
        };
        for (k, i) in b.insts.iter().enumerate() {
            if fuse && k == ni - 1 {
                break;
            }
            if let Inst::Iconst(d, _) | Inst::Fconst(d, _, _) | Inst::Addr(d, _) | Inst::FnAddr(d, _) = i {
                if hoist[d.0 as usize] {
                    continue;
                }
            }
            if COUNT {
                let d = format!("{:?}", i);
                l.cur = d.split(|c| c == ',' || c == ')').next().unwrap_or("").split("(VReg").next().unwrap_or("").to_string();
                if l.cur.starts_with("Call(") {
                    l.cur = "Call".into();
                }
                if matches!(i, Inst::Iconst(..) | Inst::Fconst(..) | Inst::FnAddr(..)) || matches!(i, Inst::Addr(_, s) if SymClass::of(sym_class, s.id) != SymClass::Domain) {
                    l.cur = "const (Iconst/Fconst/Addr/FnAddr)".into();
                }
                if matches!(i, Inst::Mov(..)) {
                    l.cur = "Mov".into();
                }
            }
            lower_inst(&mut l, i, slots, sym_class, &sym_val)?;
        }
        if COUNT {
            l.cur = if fuse { "cmp+Branch (fused)".into() } else { format!("{:?}", b.term).split('(').next().unwrap_or("").to_string() };
        }
        match &b.term {
            Term::Jump(t) => {
                if *t as usize != bi + 1 {
                    l.emit(h_jump, &[]);
                    l.target(*t);
                }
            }
            Term::Branch(cv, t, e) if !fuse && konst_of(*cv).is_some() => {
                let to = if konst_of(*cv) != Some(0) { *t } else { *e };
                if to as usize != bi + 1 {
                    l.emit(h_jump, &[]);
                    l.target(to);
                }
            }
            Term::Branch(cv, t, e) => {
                if fuse {
                    match b.insts.last().unwrap() {
                        Inst::ICmp(cc, s, d, a, bb) => {
                            let w = l.w3(*d, *a, *bb);
                            l.emit(pick_icmp(cond_code(*cc), *s, 2), &[w]);
                        }
                        Inst::ICmpI(cc, s, d, a, imm) => {
                            let w = l.w2(*d, *a);
                            l.emit(pick_icmp(cond_code(*cc), *s, 3), &[w, *imm as u64]);
                        }
                        Inst::FCmp(cc, d64, d, a, bb) => {
                            let w = l.w3(*d, *a, *bb);
                            l.emit(pick_fcmp(cond_code(*cc), *d64, true), &[w]);
                        }
                        _ => unreachable!(),
                    }
                } else {
                    let w = l.r(*cv);
                    l.emit(h_branch, &[w]);
                }
                l.target(*t);
                l.target(*e);
            }
            Term::Ret(vs) => {
                if vs.is_empty() {
                    l.emit(h_ret0, &[]);
                } else if vs.len() == 1 && l.cls(vs[0]) == Cls::I {
                    let w = l.r(vs[0]);
                    l.emit(h_ret_i, &[w]);
                } else {
                    let mut ws = vec![vs.len() as u64];
                    let (mut ni, mut nf) = (0, 0);
                    for v in vs {
                        let cls = l.cls(*v);
                        if cls == Cls::I {
                            ni += 1;
                        } else {
                            nf += 1;
                        }
                        let code = match cls {
                            Cls::I => 0u64,
                            Cls::F32 => 1,
                            Cls::F64 => 2,
                            Cls::V128 => 3,
                        };
                        ws.push(l.r(*v) | code << 32);
                    }
                    if ni > 2 || nf > 2 {
                        return Err("more than two results of a class");
                    }
                    l.emit(h_ret, &ws);
                }
            }
            // the call is the block's last instruction; the unwind edge is not taken by the
            // prototype (a panic below cuts back to the recovery point)
            Term::Invoke(t, _) => {
                if *t as usize != bi + 1 {
                    l.emit(h_jump, &[]);
                    l.target(*t);
                }
            }
            Term::Unreachable => l.emit(h_trap, &[0]),
            Term::Resume => l.emit(h_trap, &[1]),
        }
    }
    let mut code = l.code.into_boxed_slice();
    let base = code.as_ptr() as u64;
    for (at, b) in l.fix {
        code[at] = base + 8 * block_at[b as usize] as u64;
    }
    let params = f.params.iter().map(|p| (l.cell[p.0 as usize], f.vregs[p.0 as usize])).collect();
    Ok(IFunc { code, frame_words, params, cplan, name: f.name.clone() })
}

fn lower_inst(l: &mut Lw, i: &Inst, slots: SlotsPtr, sym_class: u64, sym_val: &dyn Fn(Sym) -> u64) -> Result<(), &'static str> {
    match i {
        Inst::Iconst(d, v) => {
            let w = l.r(*d);
            l.emit(h_const, &[w, *v as u64]);
        }
        Inst::Fconst(d, bits, _) => {
            let w = l.r(*d);
            l.emit(h_const, &[w, *bits]);
        }
        Inst::VConst(d, bits) => {
            let w = l.r(*d);
            l.emit(h_vconst, &[w, *bits as u64]);
        }
        Inst::Mov(d, a) => {
            let w = l.w2(*d, *a);
            l.emit(if l.cls(*d) == Cls::V128 { h_mov16 } else { h_mov }, &[w]);
        }
        Inst::IBin(op, it, d, a, b) => {
            let h = by_ty!(it, pick_ibin, iop_code(*op), false).ok_or("integer width")?;
            let w = l.w3(*d, *a, *b);
            l.emit(h, &[w]);
        }
        Inst::IBinI(op, it, d, a, imm) => {
            let h = by_ty!(it, pick_ibin, iop_code(*op), true).ok_or("integer width")?;
            let w = l.w2(*d, *a);
            l.emit(h, &[w, *imm as u64]);
        }
        Inst::INeg(it, d, a) => {
            let h = by_ty!(it, pick_ineg,).ok_or("integer width")?;
            let w = l.w2(*d, *a);
            l.emit(h, &[w]);
        }
        Inst::INot(it, d, a) => {
            let h = by_ty!(it, pick_inot,).ok_or("integer width")?;
            let w = l.w2(*d, *a);
            l.emit(h, &[w]);
        }
        Inst::IBit(op, d, a) => {
            let h: H = match op {
                BitOp::Popcnt => h_ibit::<0>,
                BitOp::Clz => h_ibit::<1>,
                BitOp::Ctz => h_ibit::<2>,
                BitOp::Bswap => h_ibit::<3>,
                BitOp::Rev => h_ibit::<4>,
            };
            let w = l.w2(*d, *a);
            l.emit(h, &[w]);
        }
        Inst::ICmp(cc, s, d, a, b) => {
            let w = l.w3(*d, *a, *b);
            l.emit(pick_icmp(cond_code(*cc), *s, 0), &[w]);
        }
        Inst::ICmpI(cc, s, d, a, imm) => {
            let w = l.w2(*d, *a);
            l.emit(pick_icmp(cond_code(*cc), *s, 1), &[w, *imm as u64]);
        }
        Inst::FBin(op, d64, d, a, b) => {
            let w = l.w3(*d, *a, *b);
            l.emit(pick_fbin(fop_code(*op), *d64), &[w]);
        }
        Inst::FUnary(op, d64, d, a) => {
            let w = l.w2(*d, *a);
            l.emit(pick_fun(*op, *d64), &[w]);
        }
        Inst::FCmp(cc, d64, d, a, b) => {
            let w = l.w3(*d, *a, *b);
            l.emit(pick_fcmp(cond_code(*cc), *d64, false), &[w]);
        }
        Inst::FMulAdd(np, na, d64, d, a, b, c) => {
            let w = l.w4(*d, *a, *b, *c);
            l.emit(if *d64 { h_fma::<true> } else { h_fma::<false> }, &[w, *np as u64 | (*na as u64) << 1]);
        }
        Inst::Conv(cv, d, s) => {
            let w = l.w2(*d, *s);
            match cv {
                Conv::IntToInt(it) => {
                    let h = by_ty!(it, pick_conv_int,).ok_or("integer width")?;
                    l.emit(h, &[w]);
                }
                _ => {
                    let k: u64 = match cv {
                        Conv::IntToF(from, to64) => (from.bits as u64) << 8 | (from.signed as u64) << 16 | (*to64 as u64) << 17,
                        Conv::FToInt(from64, to) => 1 | (to.bits as u64) << 8 | (to.signed as u64) << 16 | (*from64 as u64) << 17,
                        Conv::F32ToF64 => 2,
                        Conv::F64ToF32 => 3,
                        Conv::BitsToF(d64) => 4 | (*d64 as u64) << 17,
                        Conv::FToBits(d64) => 5 | (*d64 as u64) << 17,
                        Conv::IntToInt(_) => unreachable!(),
                    };
                    if let Conv::FToInt(_, to) = cv {
                        if !matches!(to.bits, 8 | 16 | 32 | 64) {
                            return Err("float to odd integer width");
                        }
                    }
                    l.emit(h_conv, &[w, k]);
                }
            }
        }
        Inst::Load(m, d, base, off) => {
            let w = l.w2(*d, *base) | (*off as u32 as u64) << 32;
            l.emit(pick_load(mem_load_kind(*m), false), &[w]);
        }
        Inst::Store(m, base, off, src) => {
            let w = l.w2(*base, *src) | (*off as u32 as u64) << 32;
            l.emit(pick_store(mem_size(*m), false), &[w]);
        }
        Inst::LoadX(m, d, base, idx, sh, off) => {
            let w = l.w3(*d, *base, *idx) | (*sh as u64) << 48;
            l.emit(pick_load(mem_load_kind(*m), true), &[w, *off as i64 as u64]);
        }
        Inst::StoreX(m, base, idx, sh, off, src) => {
            let w = l.w3(*base, *idx, *src) | (*sh as u64) << 48;
            l.emit(pick_store(mem_size(*m), true), &[w, *off as i64 as u64]);
        }
        Inst::SlotAddr(d, s) => {
            let w = l.r(*d) | (l.slot_off[*s as usize] as u64) << 32;
            l.emit(h_slot_addr, &[w]);
        }
        Inst::Addr(d, sym) => {
            let w = l.r(*d);
            if SymClass::of(sym_class, sym.id) == SymClass::Domain {
                l.emit(h_dom_addr, &[w, sym_val(*sym)]);
            } else {
                l.emit(h_const, &[w, sym_val(*sym)]);
            }
        }
        Inst::TlsAddr(d, sym) => {
            let w = l.r(*d);
            l.emit(h_tls_addr, &[w, sym_val(*sym)]);
        }
        Inst::FnAddr(d, id) => {
            let w = l.r(*d);
            l.emit(h_const, &[w, slots.callable(*id)]);
        }
        Inst::Copy(dst, src, size) => {
            let w = l.w2(*dst, *src);
            l.emit(h_copy, &[w, *size as u64]);
        }
        Inst::Sel(d, c, a, b) => {
            let w = l.w4(*d, *c, *a, *b);
            l.emit(if l.cls(*d) == Cls::V128 { h_sel16 } else { h_sel }, &[w]);
        }
        Inst::Call(callee, args, rets) => {
            let target = match callee {
                Callee::Fn(id) | Callee::CFn(id, _) => Target::Table(slots.table(*id)),
                Callee::Indirect(v) | Callee::CIndirect(v, _) => Target::Cell(l.cell[v.0 as usize]),
                Callee::Host(s) | Callee::CHost(s, _) => Target::Addr(sym_val(*s)),
            };
            let csig = match callee {
                Callee::CHost(_, s) | Callee::CIndirect(_, s) | Callee::CFn(_, s) => {
                    let plan = cabi::plan(s, cabi::HOST);
                    if plan.stack_bytes > 256 {
                        return Err("C call with more than 256 bytes of stack arguments");
                    }
                    Some((s.clone(), plan))
                }
                _ => None,
            };
            if csig.is_none() {
                let nf = args.iter().filter(|v| l.cls(**v) != Cls::I).count();
                let ni = args.len() - nf;
                if (nf > 8 && args.iter().any(|v| l.cls(*v) == Cls::V128)) || ni.saturating_sub(8) + nf.saturating_sub(8) > 32 {
                    return Err("call with vector or over 32 stack arguments");
                }
            }
            let (mut ri, mut rf) = (0, 0);
            for r in rets {
                if l.cls(*r) == Cls::I {
                    ri += 1
                } else {
                    rf += 1
                }
            }
            if ri > 2 || rf > 2 {
                return Err("call with more than two results of a class");
            }
            let d = Box::new(CallDesc {
                target,
                args: args.iter().map(|v| (l.cell[v.0 as usize], l.cls(*v))).collect(),
                rets: rets.iter().map(|v| (l.cell[v.0 as usize], l.cls(*v))).collect(),
                csig,
                frame_words: l.frame_words,
                ic: AtomicPtr::new(std::ptr::null_mut()),
            });
            l.emit(h_call, &[Box::into_raw(d) as u64]);
        }
        Inst::AtomicLoad(m, ord, d, a) => {
            let _ = ord;
            let w = l.w2(*d, *a);
            l.emit(h_atomic_load, &[w, mem_code(*m)]);
        }
        Inst::AtomicStore(m, _, a, s) => {
            let w = l.w2(*a, *s);
            l.emit(h_atomic_store, &[w, mem_code(*m)]);
        }
        Inst::AtomicRmw(op, m, _, d, a, s) => {
            let o: u64 = match op {
                RmwOp::Xchg => 0,
                RmwOp::Add => 1,
                RmwOp::Sub => 2,
                RmwOp::And => 3,
                RmwOp::Nand => 4,
                RmwOp::Or => 5,
                RmwOp::Xor => 6,
                RmwOp::Max => 7,
                RmwOp::Min => 8,
                RmwOp::UMax => 9,
                RmwOp::UMin => 10,
            };
            let w = l.w3(*d, *a, *s);
            l.emit(h_atomic_rmw, &[w, mem_code(*m) | o << 8]);
        }
        Inst::AtomicCas(m, _, _, d, a, e, n) => {
            let w = l.w4(*d, *a, *e, *n);
            l.emit(h_atomic_cas, &[w, mem_code(*m)]);
        }
        Inst::Fence(_, compiler_only) => l.emit(h_fence, &[*compiler_only as u64]),
        Inst::FpEnv(write, v) => {
            let w = l.r(*v);
            l.emit(h_fpenv, &[w, *write as u64]);
        }
        Inst::Cpuid(..) | Inst::Xgetbv(..) => return Err("x86 instruction"),
        Inst::VBin(op, d, a, b) => {
            let w = l.w3(*d, *a, *b);
            l.emit(h_vbin, &[w, vop_code(*op)]);
        }
        Inst::VUn(op, d, a) => {
            let w = l.w2(*d, *a);
            l.emit(h_vun, &[w, vun_code(*op)]);
        }
        Inst::VSel(d, m, a, b) => {
            let w = l.w4(*d, *m, *a, *b);
            l.emit(h_vsel, &[w]);
        }
        Inst::VFma(np, na, d, a, b, c) => {
            let w = l.w4(*d, *a, *b, *c);
            l.emit(h_vfma, &[w, *np as u64 | (*na as u64) << 1]);
        }
        Inst::VSplat(d, s) => {
            let w = l.w2(*d, *s);
            l.emit(h_vsplat, &[w]);
        }
        Inst::VShift(op, d, a, k) => {
            let w = l.w2(*d, *a) | (*k as u64) << 32;
            l.emit(h_vshift, &[w, vop_code(*op)]);
        }
        Inst::VExtract(d, v, lane) => {
            let w = l.w2(*d, *v) | (*lane as u64) << 32 | ((l.cls(*d) == Cls::I) as u64) << 48;
            l.emit(h_vextract, &[w]);
        }
        Inst::VInsert(d, v, lane, s) => {
            let w = l.w3(*d, *v, *s) | (*lane as u64) << 48;
            l.emit(h_vinsert, &[w]);
        }
        Inst::VLoad(d, base, off) => {
            let w = l.w2(*d, *base) | (*off as u32 as u64) << 32;
            l.emit(h_vload, &[w]);
        }
        Inst::VStore(base, off, src) => {
            let w = l.w2(*base, *src) | (*off as u32 as u64) << 32;
            l.emit(h_vstore, &[w]);
        }
        Inst::VAny(d, v) => {
            let w = l.w2(*d, *v);
            l.emit(h_vany, &[w]);
        }
        Inst::VGather(d, base, idx) => {
            let w = l.w3(*d, *base, *idx);
            l.emit(h_vgather, &[w]);
        }
        Inst::VX(..) | Inst::VX3(..) => return Err("lane-typed vector op"),
    }
    Ok(())
}

/// The vregs an instruction defines (its results).
fn defs_of(i: &Inst, out: &mut Vec<VReg>) {
    match i {
        Inst::Store(..) | Inst::StoreX(..) | Inst::Copy(..) | Inst::VStore(..) | Inst::AtomicStore(..) | Inst::Fence(..) => {}
        Inst::FpEnv(w, v) => {
            if !*w {
                out.push(*v)
            }
        }
        Inst::Call(_, _, rets) => out.extend_from_slice(rets),
        Inst::Cpuid(ds, _, _) => out.extend_from_slice(ds),
        Inst::Iconst(d, _) | Inst::Fconst(d, _, _) | Inst::SlotAddr(d, _) | Inst::Addr(d, _) | Inst::FnAddr(d, _) | Inst::TlsAddr(d, _) | Inst::VConst(d, _) => out.push(*d),
        Inst::Mov(d, _) | Inst::INeg(_, d, _) | Inst::INot(_, d, _) | Inst::IBit(_, d, _) | Inst::FUnary(_, _, d, _) | Inst::Conv(_, d, _) | Inst::IBinI(_, _, d, _, _) | Inst::ICmpI(_, _, d, _, _) | Inst::Load(_, d, _, _) | Inst::VUn(_, d, _) | Inst::VSplat(d, _) | Inst::VShift(_, d, _, _) | Inst::VExtract(d, _, _) | Inst::VLoad(d, _, _) | Inst::VAny(d, _) | Inst::AtomicLoad(_, _, d, _) | Inst::Xgetbv(d, _) => out.push(*d),
        Inst::IBin(_, _, d, _, _) | Inst::ICmp(_, _, d, _, _) | Inst::FBin(_, _, d, _, _) | Inst::FCmp(_, _, d, _, _) | Inst::VBin(_, d, _, _) | Inst::VGather(d, _, _) | Inst::VX(_, d, _, _) | Inst::AtomicRmw(_, _, _, d, _, _) | Inst::LoadX(_, d, _, _, _, _) => out.push(*d),
        Inst::VInsert(d, _, _, _) | Inst::Sel(d, _, _, _) | Inst::VX3(_, d, _, _, _) | Inst::VSel(d, _, _, _) | Inst::VFma(_, _, d, _, _, _) | Inst::FMulAdd(_, _, _, d, _, _, _) | Inst::AtomicCas(_, _, _, d, _, _, _) => out.push(*d),
    }
}
