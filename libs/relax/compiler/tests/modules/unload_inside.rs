// Arena reclamation (MEMRECLAIM.REVIEW F2): unloading a module while a thread is still inside it
// (parked in a host call the module made) must not free its window under that thread. The thread
// resumes, uses its heap and shadow frames, and returns the right value; the window is freed
// once it has left. Meanwhile other threads race calls into a module being unloaded and
// reloaded: every call either runs fully or reports "unloaded", never touches a freed `Arena`.
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

const PARKER: &str = r#"
pub fn parked(x: u64) -> u64 {
    // heap and shadow-stack state that lives across the host call
    let v: Vec<u64> = (0..4096u64).map(|i| i ^ x).collect();
    let mut local = [0u64; 64];
    for i in 0..64 { local[i] = v[i * 7] + 1; }
    let back = test_crate::host_park(x);
    let mut s = back;
    for i in 0..64 { s = s.wrapping_add(local[i]); }
    for e in v.iter() { s = s.wrapping_add(*e); }
    // allocates again after the unload: the arena's heap is still its own
    let w = vec![s; 1000];
    w[999]
}
"#;

fn want(x: u64) -> u64 {
    let v: Vec<u64> = (0..4096u64).map(|i| i ^ x).collect();
    let mut s = x;
    for i in 0..64 { s = s.wrapping_add(v[i * 7] + 1); }
    for e in v.iter() { s = s.wrapping_add(*e); }
    s
}

#[test]
fn unload_inside() {
    use std::relax::Module;
    let parker = Module::load_source("parker", "parker.rs", PARKER, &["test_crate"]).unwrap();
    let parked: fn(u64) -> u64 = parker.get("parked").unwrap();
    let t = std::thread::spawn(move || parked(41));
    while !PARKED.load(Ordering::SeqCst) {
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    let before = std::relax::sandbox_stats(false).unwrap();
    parker.unload();
    // T is inside: the arena waits for it
    let during = std::relax::sandbox_stats(false).unwrap();
    println!("out unload while inside defers the free: {}", during[7] == before[7] + 1);
    // new arenas made meanwhile never land on the waiting window
    let mut others = Vec::new();
    for k in 0..8 {
        let m = Module::load_source(&format!("other{}", k), "other.rs", "pub fn f(x: u64) -> u64 { let v = vec![x; 512]; v.iter().sum() }", &[]).unwrap();
        let f: fn(u64) -> u64 = m.get("f").unwrap();
        assert_eq!(f(2), 1024);
        others.push(m);
    }
    for m in others {
        m.unload();
    }
    RELEASE.store(true, Ordering::SeqCst);
    let r = t.join();
    println!("out parked call returns through its window: {}", matches!(r, Ok(v) if v == want(41)));
    let after = std::relax::sandbox_stats(false).unwrap();
    println!("out freed once it left: {}", after[7] == 0);

    // calls racing unloads: never a crash, every completed call right
    let stop = Arc::new(AtomicBool::new(false));
    let slot = Arc::new(AtomicU64::new(0));
    let (ok, gone, bad) = (Arc::new(AtomicU64::new(0)), Arc::new(AtomicU64::new(0)), Arc::new(AtomicU64::new(0)));
    let mut callers = Vec::new();
    for c in 0..3u64 {
        let (stop, slot, ok, gone, bad) = (stop.clone(), slot.clone(), ok.clone(), gone.clone(), bad.clone());
        callers.push(std::thread::spawn(move || {
            let mut x = c;
            while !stop.load(Ordering::SeqCst) {
                let p = slot.load(Ordering::SeqCst);
                if p == 0 { std::thread::yield_now(); continue; }
                let f: fn(u64) -> u64 = unsafe { std::mem::transmute(p as usize) };
                match std::relax::guard(0, || f(x)) {
                    Ok(v) if v == x * 512 => { ok.fetch_add(1, Ordering::Relaxed); }
                    Ok(_) => { bad.fetch_add(1, Ordering::Relaxed); }
                    Err(_) => { gone.fetch_add(1, Ordering::Relaxed); }
                }
                x = x.wrapping_add(3) & 0xffff;
            }
        }));
    }
    for k in 0..40 {
        let m = Module::load_source(&format!("racy{}", k), "racy.rs", "pub fn f(x: u64) -> u64 { let v = vec![x; 512]; v.iter().sum() }", &[]).unwrap();
        let f: fn(u64) -> u64 = m.get("f").unwrap();
        slot.store(f as usize as u64, Ordering::SeqCst);
        std::thread::sleep(std::time::Duration::from_millis(5));
        m.unload();
    }
    stop.store(true, Ordering::SeqCst);
    for c in callers {
        c.join().unwrap();
    }
    let mut left = std::relax::sandbox_stats(false).unwrap()[7];
    for _ in 0..1000 {
        if left == 0 { break; }
        std::thread::sleep(std::time::Duration::from_millis(1));
        left = std::relax::sandbox_stats(false).unwrap()[7];
    }
    eprintln!("unload_inside: racing calls ok {} unloaded {} bad {}", ok.load(Ordering::SeqCst), gone.load(Ordering::SeqCst), bad.load(Ordering::SeqCst));
    println!("out racing unloads: {}", bad.load(Ordering::SeqCst) == 0 && ok.load(Ordering::SeqCst) > 0 && left == 0);
}
