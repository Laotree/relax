//! The boot progress line of `relax run` on a terminal: one line redrawn in place while the
//! program boots (phase, counts, time), replaced at first present by one summary line.
//!
//! How it stays out of the way: while the bar is up, fd 2 is a pipe. One small thread forwards
//! everything written to it (errors, warnings, the program's own stderr, [I] log lines) to the real
//! terminal, erasing the bar before each batch of lines and drawing it again after, so output
//! prints above the bar and nothing is garbled. The thread redraws at most ~20 times a second from
//! plain atomics (phase, crate counter, compiled functions); the compile path takes no lock and
//! does no extra work. At first present (jit.rs relax_first_present) fd 2 is the terminal again.
//! Off (no bar, today's plain lines): stderr not a terminal, `--quiet`, `--verbose`, NO_COLOR,
//! a launcher's report file, non-Unix.

use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicU8, Ordering};

pub static LOAD_DONE: AtomicU32 = AtomicU32::new(0);
pub static LOAD_TOTAL: AtomicU32 = AtomicU32::new(0);
static PHASE: AtomicU8 = AtomicU8::new(0);
static ACTIVE: AtomicBool = AtomicBool::new(false);
/// Item tracking (the bar, or --verbose's slowest lists) is on.
static TRACK: AtomicBool = AtomicBool::new(false);

// ---- what each compiling thread is on: one slot per thread, written without locks.
// A slot is a sequence number (odd while written), the start (ms since process start, +1) and
// the first 96 bytes of the name; the ticker reads it and drops a torn read.
const SLOTS: usize = 32;
const WORDS: usize = 12;
struct Slot {
    seq: AtomicU32,
    start: AtomicU64,
    len: AtomicU32,
    name: [AtomicU64; WORDS],
}
#[allow(clippy::declare_interior_mutable_const)]
const SLOT0: Slot = Slot { seq: AtomicU32::new(0), start: AtomicU64::new(0), len: AtomicU32::new(0), name: [const { AtomicU64::new(0) }; WORDS] };
static ITEMS: [Slot; SLOTS] = [SLOT0; SLOTS];
static NEXT_SLOT: AtomicU32 = AtomicU32::new(0);
thread_local! { static MY_SLOT: usize = NEXT_SLOT.fetch_add(1, Ordering::Relaxed) as usize % SLOTS; }
/// Items that took long enough to list: (what, name, ms).
static SLOW: std::sync::Mutex<Vec<(&'static str, String, f64)>> = std::sync::Mutex::new(Vec::new());
/// The crate being loaded and when it started.
static LOADING: std::sync::Mutex<(String, f64)> = std::sync::Mutex::new((String::new(), 0.0));

/// --verbose: keep the slowest-item lists too.
pub fn track_for_verbose() {
    TRACK.store(true, Ordering::Relaxed);
    VERBOSE_LIST.store(true, Ordering::Relaxed);
}

/// A thread starts compiling `name` (jit.rs compile_watch). One relaxed load when nothing tracks.
pub fn item_begin(name: &str) {
    if !TRACK.load(Ordering::Relaxed) {
        return;
    }
    let s = &ITEMS[MY_SLOT.try_with(|s| *s).unwrap_or(0)];
    let q = s.seq.load(Ordering::Relaxed);
    s.seq.store(q | 1, Ordering::Release);
    let b = name.as_bytes();
    let n = b.len().min(WORDS * 8);
    for (i, w) in s.name.iter().enumerate() {
        let mut v = [0u8; 8];
        let lo = i * 8;
        if lo < n {
            let hi = (lo + 8).min(n);
            v[..hi - lo].copy_from_slice(&b[lo..hi]);
        }
        w.store(u64::from_le_bytes(v), Ordering::Relaxed);
    }
    s.len.store(n as u32, Ordering::Relaxed);
    s.start.store(crate::clock::ms_since_process_start() as u64 + 1, Ordering::Relaxed);
    s.seq.store((q | 1).wrapping_add(1), Ordering::Release);
    let _ = name;
}

/// The thread is done with its item.
pub fn item_end() {
    if !TRACK.load(Ordering::Relaxed) {
        return;
    }
    let s = &ITEMS[MY_SLOT.try_with(|s| *s).unwrap_or(0)];
    let start = s.start.swap(0, Ordering::Relaxed);
    if start == 0 || !VERBOSE_LIST.load(Ordering::Relaxed) {
        return;
    }
    let ms = crate::clock::ms_since_process_start() - (start - 1) as f64;
    if ms >= 20.0 {
        if let Some(name) = read_slot(s) {
            SLOW.lock().unwrap().push(("fn", name, ms));
        }
    }
}
static VERBOSE_LIST: AtomicBool = AtomicBool::new(false);

fn read_slot(s: &Slot) -> Option<String> {
    let q = s.seq.load(Ordering::Acquire);
    if q & 1 == 1 {
        return None;
    }
    let n = (s.len.load(Ordering::Relaxed) as usize).min(WORDS * 8);
    let mut bytes = Vec::with_capacity(WORDS * 8);
    for w in &s.name {
        bytes.extend_from_slice(&w.load(Ordering::Relaxed).to_le_bytes());
    }
    if s.seq.load(Ordering::Acquire) != q {
        return None;
    }
    bytes.truncate(n);
    Some(String::from_utf8_lossy(&bytes).into_owned())
}

/// The longest-running item (name, ms so far) of any thread.
fn longest_item() -> Option<(String, f64)> {
    let now = crate::clock::ms_since_process_start();
    let mut best: Option<(String, f64)> = None;
    for s in ITEMS.iter() {
        let start = s.start.load(Ordering::Relaxed);
        if start == 0 {
            continue;
        }
        let ms = now - (start - 1) as f64;
        if best.as_ref().map_or(true, |b| ms > b.1) {
            if let Some(n) = read_slot(s) {
                best = Some((n, ms));
            }
        }
    }
    best
}

/// A crate starts loading (run.rs); the one before it is done.
pub fn crate_begin(name: &str) {
    if !TRACK.load(Ordering::Relaxed) {
        return;
    }
    crate_end();
    *LOADING.lock().unwrap() = (name.to_string(), crate::clock::ms_since_process_start());
}

pub fn crate_end() {
    if !TRACK.load(Ordering::Relaxed) {
        return;
    }
    let mut g = LOADING.lock().unwrap();
    if !g.0.is_empty() {
        let ms = crate::clock::ms_since_process_start() - g.1;
        if VERBOSE_LIST.load(Ordering::Relaxed) {
            SLOW.lock().unwrap().push(("crate", std::mem::take(&mut g.0), ms));
        }
        g.0.clear();
    }
}

/// --verbose, at the end: the five slowest crates (load) and functions (compile).
pub fn print_slowest() {
    if !VERBOSE_LIST.load(Ordering::Relaxed) {
        return;
    }
    crate_end();
    let mut v = SLOW.lock().unwrap();
    for (kind, title) in [("crate", "slowest crates (load)"), ("fn", "slowest functions (compile)")] {
        let mut l: Vec<_> = v.iter().filter(|x| x.0 == kind).collect();
        l.sort_by(|a, b| b.2.total_cmp(&a.2));
        if l.is_empty() {
            continue;
        }
        eprintln!("relax-run: {title}:");
        for (_, n, ms) in l.into_iter().take(5) {
            eprintln!("relax-run:   {ms:>9.1} ms  {n}");
        }
    }
    v.clear();
}

const LABELS: [&str; 10] = [
    "booting", "unit graph", "build scripts", "loading", "resolving", "signatures", "linking", "image", "starting", "compiling",
];

/// A boot phase finished (run.rs `phase`): the one that follows is shown. A no-op without a bar.
pub fn phase_done(name: &str) {
    if !ACTIVE.load(Ordering::Relaxed) {
        return;
    }
    let next = match name.split(" (").next().unwrap_or(name) {
        "provided sources" => 1,
        "unit graph" => 2,
        "build scripts" => 3,
        "load+parse" => 4,
        "resolve" => 5,
        "signatures" => 6,
        "link libraries" => 7,
        "image" => 8,
        _ => return,
    };
    PHASE.store(next, Ordering::Relaxed);
}

/// `main` is about to be called: functions compile until the first frame.
pub fn compiling() {
    PHASE.store(9, Ordering::Relaxed);
}

#[cfg(not(unix))]
pub fn start() {}
#[cfg(not(unix))]
pub fn finish(_summary: bool) {}

#[cfg(unix)]
pub use unix::{finish, start};

#[cfg(unix)]
mod unix {
    use super::*;
    use std::io::IsTerminal;
    use std::sync::Mutex;

    #[repr(C)]
    struct PollFd {
        fd: i32,
        events: i16,
        revents: i16,
    }
    extern "C" {
        fn pipe(fds: *mut i32) -> i32;
        fn dup(fd: i32) -> i32;
        fn dup2(a: i32, b: i32) -> i32;
        fn close(fd: i32) -> i32;
        fn read(fd: i32, buf: *mut u8, n: usize) -> isize;
        fn write(fd: i32, buf: *const u8, n: usize) -> isize;
        fn poll(fds: *mut PollFd, n: u64, ms: i32) -> i32;
        fn fcntl(fd: i32, cmd: i32, ...) -> i32;
        fn atexit(f: extern "C" fn()) -> i32;
    }
    #[cfg(target_os = "macos")]
    const O_NONBLOCK: i32 = 0x4;
    #[cfg(not(target_os = "macos"))]
    const O_NONBLOCK: i32 = 0x800;

    struct State {
        /// the real stderr (a dup of it)
        out: i32,
        read_fd: i32,
        /// our copy of the pipe's write end (fd 2 is the other); -1 once closed
        write_fd: i32,
        /// bytes of a line that has no newline yet
        partial: Vec<u8>,
        drawn: bool,
        last_draw_ms: f64,
    }
    static STATE: Mutex<Option<State>> = Mutex::new(None);

    fn out_all(fd: i32, mut b: &[u8]) {
        while !b.is_empty() {
            let n = unsafe { write(fd, b.as_ptr(), b.len()) };
            if n <= 0 {
                return;
            }
            b = &b[n as usize..];
        }
    }

    fn style(code: &str, s: &str) -> String {
        format!("\x1b[{code}m{s}\x1b[0m")
    }

    fn secs(ms: f64) -> String {
        format!("{:.1} s", ms / 1000.0)
    }

    /// `s` shortened to `n` chars with an ellipsis in the middle.
    fn cut(s: &str, n: usize) -> String {
        let c: Vec<char> = s.chars().collect();
        if c.len() <= n {
            return s.to_string();
        }
        let head = n / 2;
        let tail = n - head - 1;
        format!("{}\u{2026}{}", c[..head].iter().collect::<String>(), c[c.len() - tail..].iter().collect::<String>())
    }

    fn bar() -> String {
        let ms = crate::clock::ms_since_process_start() as f64;
        const SPIN: [&str; 10] = ["\u{280b}", "\u{2819}", "\u{2839}", "\u{2838}", "\u{283c}", "\u{2834}", "\u{2826}", "\u{2827}", "\u{2807}", "\u{280f}"];
        let spin = style("1;36", SPIN[(ms / 80.0) as usize % SPIN.len()]);
        let p = PHASE.load(Ordering::Relaxed) as usize;
        let label = LABELS[p.min(LABELS.len() - 1)];
        let mut text = style("1", &format!("{label:<9}"));
        match p {
            3 => {
                let (d, t) = (LOAD_DONE.load(Ordering::Relaxed), LOAD_TOTAL.load(Ordering::Relaxed));
                if t > 0 {
                    text.push_str(&format!(" {d}/{t} crates"));
                }
                let g = LOADING.lock().unwrap();
                if !g.0.is_empty() {
                    text.push_str(&format!(" {} {}", style("2", "\u{b7}"), cut(&g.0, 40)));
                }
            }
            9 => {
                let n = crate::jit::COMPILED_FNS.load(Ordering::Relaxed);
                if n >= 1000 {
                    text.push_str(&format!(" {:.1}k fns", n as f64 / 1000.0));
                } else {
                    text.push_str(&format!(" {n} fns"));
                }
                if let Some((name, ms)) = longest_item().filter(|x| x.1 > 500.0) {
                    text.push_str(&format!(" {} {} {}", style("2", "\u{b7}"), cut(&name, 40), style("2", &secs(ms))));
                }
            }
            _ => {}
        }
        let mut line = format!("{spin} {text} {} {}", style("2", "\u{b7}"), style("2", &secs(ms)));
        // never wider than a narrow terminal's line: the escape codes are cut with the text
        if line.len() > 400 {
            line.truncate(400);
        }
        line
    }

    fn erase(st: &mut State) {
        if st.drawn {
            out_all(st.out, b"\r\x1b[2K");
            st.drawn = false;
        }
    }

    fn draw(st: &mut State) {
        let b = bar();
        out_all(st.out, format!("\r\x1b[2K{b}").as_bytes());
        st.drawn = true;
        st.last_draw_ms = crate::clock::ms_since_process_start() as f64;
    }

    /// Reads what is in the pipe (nonblocking) and prints its whole lines above the bar.
    /// Returns false at end of input.
    fn pump(st: &mut State, flush_partial: bool) -> bool {
        let mut buf = [0u8; 8192];
        let mut open = true;
        let mut got = false;
        loop {
            let n = unsafe { read(st.read_fd, buf.as_mut_ptr(), buf.len()) };
            if n == 0 {
                open = false;
                break;
            }
            if n < 0 {
                break;
            }
            st.partial.extend_from_slice(&buf[..n as usize]);
            got = true;
        }
        let cut = if flush_partial { st.partial.len() } else { st.partial.iter().rposition(|&c| c == b'\n').map_or(0, |i| i + 1) };
        if cut > 0 {
            let mut chunk: Vec<u8> = st.partial.drain(..cut).collect();
            if flush_partial && chunk.last() != Some(&b'\n') {
                chunk.push(b'\n');
            }
            erase(st);
            out_all(st.out, &chunk);
            if ACTIVE.load(Ordering::Relaxed) && !flush_partial {
                draw(st);
            }
        }
        let _ = got;
        open
    }

    extern "C" fn at_exit() {
        // run's exit worker handles the terminal inside its cleanup budget. Do
        // not take STATE again on the exiting thread after that budget expired.
        if !crate::preempt::is_stopped() { finish(false); }
    }

    /// Puts the bar up when this run is on a terminal and nothing asks for plain output.
    pub fn start() {
        unsafe { std::env::remove_var("RELAX_RUN_PROGRESS") };
        let env = |k: &str| std::env::var_os(k).filter(|v| !v.is_empty());
        if !std::io::stderr().is_terminal()
            || env("NO_COLOR").is_some()
            || env("RELAX_REPORT_TO").is_some()
            || env("RELAX_SCRIPT_DEPTH").is_some()
            || ACTIVE.load(Ordering::Relaxed)
        {
            return;
        }
        let (mut fds, out) = ([0i32; 2], unsafe { dup(2) });
        if out < 0 || unsafe { pipe(fds.as_mut_ptr()) } != 0 {
            return;
        }
        unsafe {
            fcntl(fds[0], 4, fcntl(fds[0], 3, 0) | O_NONBLOCK);
        }
        if unsafe { dup2(fds[1], 2) } < 0 {
            return;
        }
        let mut st = State { out, read_fd: fds[0], write_fd: fds[1], partial: Vec::new(), drawn: false, last_draw_ms: 0.0 };
        PHASE.store(1, Ordering::Relaxed);
        TRACK.store(true, Ordering::Relaxed);
        draw(&mut st);
        *STATE.lock().unwrap() = Some(st);
        ACTIVE.store(true, Ordering::Relaxed);
        unsafe { std::env::set_var("RELAX_RUN_PROGRESS", "1") };
        unsafe { atexit(at_exit) };
        let _ = std::thread::Builder::new().name("relax-progress".into()).spawn(forward);
    }

    /// Forwards the pipe until every writer is gone; draws the bar while it is up.
    fn forward() {
        let rfd = match STATE.lock().unwrap().as_ref() {
            Some(s) => s.read_fd,
            None => return,
        };
        loop {
            let mut p = PollFd { fd: rfd, events: 1, revents: 0 };
            unsafe { poll(&mut p, 1, 50) };
            let mut g = STATE.lock().unwrap();
            let Some(st) = g.as_mut() else { return };
            if !pump(st, false) {
                // end of input: all writers closed (after finish)
                if !ACTIVE.load(Ordering::Relaxed) {
                    unsafe { close(st.read_fd) };
                    *g = None;
                }
                return;
            }
            if ACTIVE.load(Ordering::Relaxed) && crate::clock::ms_since_process_start() as f64 - st.last_draw_ms >= 50.0 {
                draw(st);
            }
        }
    }

    /// Takes the bar down and gives fd 2 back its terminal. `summary`: first present, print the
    /// ready line. Idempotent.
    pub fn finish(summary: bool) {
        let mut g = STATE.lock().unwrap();
        let Some(st) = g.as_mut() else { return };
        if !ACTIVE.swap(false, Ordering::Relaxed) {
            return;
        }
        let _ = pump(st, true);
        erase(st);
        if summary {
            let pkg = std::env::var("RELAX_RUN_PACKAGE").unwrap_or_else(|_| "program".to_string());
            let cache = match std::env::var("RELAX_RUN_CACHE").as_deref() {
                Ok("warm") => " (warm)".to_string(),
                Ok("cold") => " (cold)".to_string(),
                _ => String::new(),
            };
            let ms = crate::clock::ms_since_process_start() as f64;
            let line = format!("{} {} ready in {}{}\n", style("1;32", "\u{2713}"), style("1;36", &pkg), secs(ms), style("2", &cache));
            out_all(st.out, line.as_bytes());
        }
        unsafe {
            dup2(st.out, 2);
            close(st.write_fd);
        }
        st.write_fd = -1;
        // the forwarder drains what children that still hold the pipe write, then ends
        if !summary {
            let _ = pump(st, true);
        }
    }
}
