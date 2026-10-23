// Code reclamation (MEMRECLAIM.DESIGN.md): a sandbox code space is reused only when no thread can
// still run in it. A thread parked inside a module (in a host call it made) blocks the reuse of
// the space its frames are in -- however long it stays -- while other threads keep calling and
// editing modules; once it has returned the reuse goes ahead, and every result stays right.
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

pub static PARKED: AtomicBool = AtomicBool::new(false);
pub static RELEASE: AtomicBool = AtomicBool::new(false);

/// Part of the host's API the parker module calls: waits until the test lets it go.
pub fn host_park(x: u64) -> u64 {
    PARKED.store(true, Ordering::SeqCst);
    while !RELEASE.load(Ordering::SeqCst) {
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    x
}

fn quick_src(k: u64) -> String {
    format!("pub fn quick(x: u64) -> u64 {{ let mut a = x; for i in 0..8u64 {{ a = a.wrapping_mul(3).wrapping_add(i + {k}); }} a }}\n")
}

fn quick_want(x: u64, k: u64) -> u64 {
    let mut a = x;
    for i in 0..8u64 {
        a = a.wrapping_mul(3).wrapping_add(i + k);
    }
    a
}

/// A recycle now; Err while the proof refuses it.
fn recycle() -> Result<[u64; 8], String> {
    std::relax::sandbox_stats(true)
}

#[test]
fn reclaim_threads() {
    use std::relax::Module;
    let parker = Module::load_source("parker", "parker.rs", "pub fn parked(x: u64) -> u64 { test_crate::host_park(x) + 1 }\n", &["test_crate"]).unwrap();
    let parked: fn(u64) -> u64 = parker.get("parked").unwrap();
    let worker = Module::load_source("worker", "worker.rs", &quick_src(1), &[]).unwrap();
    let quick: fn(u64) -> u64 = worker.get("quick").unwrap();
    assert_eq!(quick(5), quick_want(5, 1));

    // T parks inside the module: its frames are in the active space (space 0)
    let t = std::thread::spawn(move || parked(41));
    while !PARKED.load(Ordering::SeqCst) {
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    // other threads call module code all along (they enter and leave many times); one module
    // each: concurrent calls into one module's arena share its shadow stack (as guard_threads)
    let stop = Arc::new(AtomicBool::new(false));
    let bad = Arc::new(AtomicU64::new(0));
    let calls = Arc::new(AtomicU64::new(0));
    let mut hammers = Vec::new();
    let mut own = Vec::new();
    for h in 0..3u64 {
        let (stop, bad, calls) = (stop.clone(), bad.clone(), calls.clone());
        let m = Module::load_source(&format!("hammer{}", h), &format!("hammer{}.rs", h), &quick_src(1), &[]).unwrap();
        let quick: fn(u64) -> u64 = m.get("quick").unwrap();
        own.push(m);
        hammers.push(std::thread::spawn(move || {
            let mut x = h;
            while !stop.load(Ordering::SeqCst) {
                let r = quick(x);
                // the module text is 1 throughout (edits go to another module)
                if r != quick_want(x, 1) {
                    if bad.fetch_add(1, Ordering::SeqCst) < 5 {
                        eprintln!("reclaim_threads: bad quick({}) = {} want {}", x, r, quick_want(x, 1));
                    }
                }
                calls.fetch_add(1, Ordering::Relaxed);
                x = x.wrapping_add(7);
            }
        }));
    }
    // recycle 1: the live twins move to the never-used space 1 (nothing to prove)
    let first = recycle();
    // recycle 2 would reuse space 0, where T still is: refused, as often as asked
    let mut refused_while_parked = true;
    let mut edits = 0;
    for k in 0..20u64 {
        let side = Module::load_source(&format!("side{}", k), &format!("side{}.rs", k), &quick_src(k), &[]).unwrap();
        let f: fn(u64) -> u64 = side.get("quick").unwrap();
        refused_while_parked &= f(3) == quick_want(3, k);
        side.replace(&quick_src(k + 100)).unwrap();
        refused_while_parked &= f(3) == quick_want(3, k + 100);
        side.unload();
        edits += 1;
        refused_while_parked &= recycle().is_err();
    }
    let refused = std::relax::sandbox_stats(false).unwrap()[6];
    // (under MAKEPAD_RUN_RECLAIM_STRESS background recycles may have used the fresh space already)
    let stress = std::env::var("MAKEPAD_RUN_RECLAIM_STRESS").is_ok_and(|v| v != "0");
    println!("out first recycle (fresh space): {}", first.is_ok() || stress);
    println!("out parked thread blocks reuse: {}", refused_while_parked && refused >= 20 && edits == 20);
    // T returns through its old frames (the space was never reused under it)
    RELEASE.store(true, Ordering::SeqCst);
    let r = t.join().unwrap();
    println!("out parked call returns: {}", r == 42);
    // now the reuse goes ahead; the hammer threads only delay it while one is inside since the
    // last stamp (no timeout: retried until done)
    let mut reused = 0;
    let mut tries = 0u64;
    while reused < 10 {
        tries += 1;
        if recycle().is_ok() {
            reused += 1;
        } else {
            std::thread::yield_now();
        }
    }
    stop.store(true, Ordering::SeqCst);
    for h in hammers {
        h.join().unwrap();
    }
    let s = std::relax::sandbox_stats(false).unwrap();
    eprintln!("reclaim_threads: bad {} quick(9) {} want {}", bad.load(Ordering::SeqCst), quick(9), quick_want(9, 1));
    eprintln!("reclaim_threads: {} hammer calls, {} recycle tries for 10 reuses, stats {:?}", calls.load(Ordering::SeqCst), tries, s);
    println!("out reuse after it left: {}", reused == 10);
    println!("out results under recycles: {}", bad.load(Ordering::SeqCst) == 0 && quick(9) == quick_want(9, 1));
    for m in own {
        m.unload();
    }
    worker.unload();
    parker.unload();
}
