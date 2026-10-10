//! Settling must be invisible to generated O1 code and to later closure rebuilds.
use super::*;

#[test]
fn settle_rebuild_pins_tier1_and_closure_history() {
    // Unit installs process-global runtime state. Cache fixtures in the same harness can
    // leave a reentrant unit lock behind; run this fixture in its own runtime process.
    const CHILD: &str = "RELAX_SETTLE_TEST_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "jit::settle_tests::settle_rebuild_pins_tier1_and_closure_history", "--test-threads=1"])
            .env(CHILD, "1").status().unwrap();
        assert!(status.success());
        return;
    }
    crate::borrowck::lazy::disable_gandalf();
    if std::env::var_os("RELAX_STD").is_none() {
        std::env::set_var("RELAX_STD", concat!(env!("CARGO_MANIFEST_DIR"), "/std"));
    }
    let dir = std::env::temp_dir().join(format!("relax-settle-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::env::set_var("RELAX_CACHE_DIR", dir.join("cache"));
    let path = dir.join("input.rs");
    let source = r#"
const fn width() -> usize { 3 }
const WIDTH: usize = width();
#[inline(never)]
fn apply(x: u32) -> u32 {
    let a = [x; WIDTH];
    a.iter().map(|v| *v + 7).sum::<u32>()
}
fn main() { let _ = apply(4); }
fn unrelated(x: u32) -> u32 { x + 1 }
"#.replace("let a =", &format!("{}let a =", "let _ = x; ".repeat(50)));
    std::fs::write(&path, &source).unwrap();
    let (prog, core, krate) = crate::load_with_std(&std::sync::Arc::new(crate::Session::default()), path.to_str().unwrap(), "settle_test", false).unwrap();
    let def = prog.defs.iter().enumerate().find_map(|(i, d)| {
        let id = DefId(i as u32);
        (d.krate == krate && prog.name(id) == "apply").then_some(id)
    }).unwrap();
    let mut tcx = Tcx::new();
    tcx.collect(&prog);
    assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
    let mut u = Unit::new(prog, tcx, core);
    let up = &mut *u as *mut Unit;
    lock_unit();
    let id = u.fn_id(FnKey::Inst(def, Vec::new()));
    let file = u.prog.def(def).file;
    let first = unsafe { compile_fn(up, id) }.unwrap();
    u.install(id, &first.0, &first.2, first.1.clone(), 0).unwrap();
    let mut cache = crate::cache::Cache::open(&u, crate::cache::Mode::On).unwrap();
    cache.record(&u, id, &first.0, &first.2, &first.1);
    assert!(cache.pending_bytes() > 0);
    let spill = cache.spill_take().unwrap();
    assert_eq!(cache.pending_bytes(), 0);
    unlock_unit();
    assert!(spill.write().unwrap() > 0);
    lock_unit();
    let mut verify = crate::cache::Cache::open(&u, crate::cache::Mode::Verify).unwrap();
    assert!(matches!(verify.lookup(&mut u, id), Some(_)), "verification must have a real disk entry");
    let rir = u.fns[id as usize].rir.as_ref().unwrap().dump();
    let calls = u.fns[id as usize].calls.clone();
    let late_body = clone_body(u.body_of(id, file).unwrap());
    let key = (def, Vec::new());
    assert!(u.front.built.contains(&key));
    publish_ahead(&u.front, key.clone(), u.tcx.collect_epoch.load(Ordering::SeqCst), late_body);
    assert!(!u.front.ahead.contains_key(&key), "a late ahead check has no remaining reader");
    let closure = u.fns.iter().enumerate().find_map(|(i, f)| {
        matches!(f.key, FnKey::Closure(_, _, p) if p == id).then_some(i as u32)
    }).unwrap();
    unsafe { build_rir(up, closure) }.unwrap();
    let closure_rir = u.fns[closure as usize].rir.as_ref().unwrap().dump();
    let c = unsafe { compile_fn(up, closure) }.unwrap();
    u.install(closure, &c.0, &c.2, c.1, 0).unwrap();
    assert!(u.fns[id as usize].rir.is_none(), "last closure reader releases its installed owner");
    assert!(!u.has_body(id, file));
    unsafe { build_rir(up, id) }.unwrap();
    let unrelated_def = u.prog.defs.iter().enumerate().find_map(|(i, d)| {
        let id = DefId(i as u32);
        (d.krate == krate && u.prog.name(id) == "unrelated").then_some(id)
    }).unwrap();
    let unrelated = u.fn_id(FnKey::Inst(unrelated_def, Vec::new()));
    let code = unsafe { compile_fn(up, unrelated) }.unwrap();
    u.install(unrelated, &code.0, &code.2, code.1, 0).unwrap();
    let saved_refs = std::mem::replace(&mut u.fns[id as usize].rir_refs, vec![unrelated].into_boxed_slice());
    // Pending and popped/in-flight O3 jobs both pin their input slots.
    TIER_QUEUE.lock().unwrap().push((id, Q_CALLS, wall_ns(), 0));
    TIER_ACTIVE.lock().unwrap().push(closure);
    let active = TierActive(closure);
    let generation = reclaim_generation();
    drop_completed_body(&mut u, id);
    drop_completed_body(&mut u, closure);
    unsafe { settle_drop(up) };
    assert!(u.fns[id as usize].rir.is_some());
    assert!(u.fns[closure as usize].rir.is_some());
    assert!(u.fns[unrelated as usize].rir.is_some(), "queued readers pin their known callee inputs too");
    u.fns[id as usize].rir_refs = saved_refs;
    TIER_QUEUE.lock().unwrap().clear();
    drop(active);
    assert!(reclaim_generation() > generation, "finishing the last reader must wake reclamation without a new install");
    // A suspended O1 front must keep all of its not-yet-snapshotted candidates.
    u.fns[id as usize].building = true;
    let saved_calls = std::mem::replace(&mut u.fns[id as usize].calls, vec![closure].into_boxed_slice());
    let checking = FRONT_RW.read().unwrap();
    let partial = unsafe { settle_drop(up) };
    assert!(partial.front_pending, "a busy ahead checker postpones only shared memo removal");
    assert!(u.fns[id as usize].rir.is_some());
    assert!(u.fns[closure as usize].rir.is_some(), "a suspended front pins its inline candidate");
    assert!(u.fns[unrelated as usize].rir.is_none(), "an unrelated completed body need not wait for that front");
    drop(checking);
    u.fns[id as usize].calls = saved_calls;
    u.fns[id as usize].building = false;
    u.fns[id as usize].inflight = true;
    unsafe { settle_drop(up) };
    assert!(u.fns[id as usize].rir.is_some());
    u.fns[id as usize].inflight = false;
    drop_completed_body(&mut u, id);
    assert!(u.fns[id as usize].rir.is_none(), "installation releases the completed slot immediately");
    assert!(!u.has_body(id, file));
    unsafe { build_rir(up, closure) }.unwrap();
    let retired = std::sync::Arc::downgrade(u.fns[closure as usize].rir.as_ref().unwrap());
    let mut dropped = unsafe { settle_drop(up) };
    assert!(dropped.fns >= 1);
    assert!(u.fns[id as usize].rir.is_none());
    assert!(u.fns[closure as usize].rir.is_none());
    assert!(retired.upgrade().is_some(), "unlinking must defer destruction until after unlocking");
    unlock_unit();
    dropped.release_rir();
    lock_unit();
    assert!(retired.upgrade().is_none(), "retired RIR must actually be released off the unit lock");
    assert_eq!(u.fns[id as usize].calls, calls);
    assert!(!u.has_body(id, file));
    // Rebuild the closure FIRST: its compiled parent no longer has a checked body or RIR.
    unsafe { build_rir(up, closure) }.unwrap();
    assert_eq!(u.fns[closure as usize].rir.as_ref().unwrap().dump(), closure_rir);
    let rebuilt = unsafe { compile_fn(up, id) }.unwrap();
    assert_eq!(u.fns[id as usize].rir.as_ref().unwrap().dump(), rir);
    assert_eq!(rebuilt.0, first.0, "O1 machine code changed after settle");
    assert!(verify.verify_entry(&u, id, &rebuilt.0, &rebuilt.2), "cache verify after settle");
    unsafe { settle_drop(up) };
    unlock_unit();
    assert!(unsafe { compile_tier1(up, id) }, "O3 must rebuild settled RIR");
    lock_unit();
    unsafe { settle_drop(up) };
    assert!(!u.has_body(id, file));
    unlock_unit();
    // Apply a real edit after eviction; old compiled closures still rebuild from old text.
    let outcome = unsafe { crate::reload::apply(up, vec![crate::reload::Edit {
        file, path: path.to_str().unwrap().to_string(), src: source.replace("*v + 7", "*v + 9").into_bytes(),
    }]) };
    assert_eq!(outcome.rung, crate::reload::Rung::Patch, "{:?}", outcome.lines);
    lock_unit();
    assert!(u.has_body(id, file), "reload must preserve the old closure owner");
    u.fns[closure as usize].rir = None;
    unsafe { build_rir(up, closure) }.unwrap();
    assert_eq!(u.fns[closure as usize].rir.as_ref().unwrap().dump(), closure_rir);
    // Unit normally lives to process exit; leak it here to avoid tearing down process-global
    // JIT workers from this test. The test process releases its executable reservation.
    std::mem::forget(u);
    unlock_unit();
    std::fs::remove_file(path).unwrap();
    // Keep the isolated cache for inspection; it lives under the OS temporary directory.
}
