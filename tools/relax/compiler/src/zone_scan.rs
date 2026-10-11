//! The kept-state scan (`RELAX_ZONE_CHECK=1`): a walk over the closed list of Unit state that
//! must survive the destruction of the compiler arena (memlane step 1b), counting every owned
//! heap allocation that lies inside that arena. A count above zero is a site that built kept
//! state in the compiler phase (it needs `zone_alloc::kept()` around the allocation).
//!
//! The list is the K class of the Unit (jit.rs, `Unit`): the compile state (C) is not walked.

use super::*;
use std::collections::{BTreeMap, HashSet};

/// Counts, per named field, the owned allocations that lie in the compiler arena.
pub(crate) struct Acc {
    counts: Vec<(&'static str, usize)>,
    cur: usize,
}

impl Acc {
    fn new() -> Acc {
        Acc { counts: Vec::new(), cur: 0 }
    }

    /// The following pointers are counted under `name`.
    pub(crate) fn field(&mut self, name: &'static str) {
        self.cur = match self.counts.iter().position(|c| c.0 == name) {
            Some(i) => i,
            None => {
                self.counts.push((name, 0));
                self.counts.len() - 1
            }
        };
    }

    /// An allocation the state owns.
    pub(crate) fn ptr<T: ?Sized>(&mut self, p: *const T) {
        if crate::zone_alloc::compiler_owns(p as *const u8) {
            self.counts[self.cur].1 += 1;
        }
    }

    pub(crate) fn vec<T>(&mut self, v: &Vec<T>) {
        if v.capacity() > 0 && std::mem::size_of::<T>() > 0 {
            self.ptr(v.as_ptr());
        }
    }

    pub(crate) fn string(&mut self, s: &String) {
        if s.capacity() > 0 {
            self.ptr(s.as_ptr());
        }
    }

    pub(crate) fn boxed<T: ?Sized>(&mut self, b: &Box<T>) {
        if std::mem::size_of_val(&**b) > 0 {
            self.ptr(&**b as *const T);
        }
    }

    pub(crate) fn arc<T: ?Sized>(&mut self, a: &std::sync::Arc<T>) {
        self.ptr(std::sync::Arc::as_ptr(a));
    }

    /// A hash map: each entry lies in the table's allocation (an entry reference is an address
    /// in it), then what the entry owns.
    pub(crate) fn map<K, V, S>(&mut self, m: &std::collections::HashMap<K, V, S>, mut deep: impl FnMut(&mut Acc, &K, &V)) {
        for (k, v) in m.iter() {
            if std::mem::size_of::<(K, V)>() > 0 {
                self.ptr(k as *const K);
            }
            deep(self, k, v);
        }
    }

    pub(crate) fn set<T, S>(&mut self, m: &HashSet<T, S>) {
        for k in m.iter() {
            if std::mem::size_of::<T>() > 0 {
                self.ptr(k as *const T);
            }
        }
    }

    /// A B-tree map: each key lies in its node's allocation.
    pub(crate) fn btree<K, V>(&mut self, m: &BTreeMap<K, V>, mut deep: impl FnMut(&mut Acc, &K, &V)) {
        for (k, v) in m.iter() {
            if std::mem::size_of::<K>() > 0 {
                self.ptr(k as *const K);
            }
            deep(self, k, v);
        }
    }
}

impl PcMap {
    fn scan(&self, acc: &mut Acc) {
        match &self.0 {
            PcBytes::Own(b) => {
                if !b.is_empty() {
                    acc.ptr(b.as_ptr());
                }
            }
            PcBytes::Mapped(_, f) => acc.pc_files(f),
        }
    }
}

impl Acc {
    fn pc_files(&mut self, f: &std::sync::Arc<PcFiles>) {
        self.arc(f);
        self.vec(&f.files);
        self.ptr(&*f.keep as *const (dyn std::any::Any + Send + Sync));
    }

    fn fn_key(&mut self, k: &FnKey) {
        match k {
            FnKey::Inst(_, a) => self.vec(a),
            FnKey::Shim(s) => self.vec(&s.args),
            _ => {}
        }
    }
}

/// Owned allocations of the kept state that lie in the compiler arena, per field (only fields
/// with a nonzero count are listed). Quiescent callers only (the owner thread at a settle).
pub(crate) fn kept_scan(u: &Unit) -> Vec<(&'static str, usize)> {
    let mut a = Acc::new();
    a.field("unit");
    a.ptr(u as *const Unit);
    a.field("slots");
    a.boxed(&u.slots);
    if let Ok(c) = u.code.try_read() {
        a.field("code.index");
        a.vec(&c.index);
        a.field("code.unwind");
        a.map(&c.unwind, |a, _, v| {
            a.vec(&v.saved);
            a.vec(&v.pads);
        });
        a.field("code.image_unwind");
        a.vec(&c.image_unwind);
        if let Some(f) = &c.image_keep {
            a.pc_files(f);
        }
    }
    a.field("fns");
    u.fns.alloc_ptrs(|p| a.ptr(p));
    for f in u.fns.iter() {
        a.field("fn.key");
        a.fn_key(&f.key);
        a.field("fn.name");
        a.string(&f.name);
        a.field("fn.pc_map");
        f.pc_map.scan(&mut a);
        a.field("fn.prev");
        a.vec(&f.prev);
        for p in &f.prev {
            p.2.scan(&mut a);
        }
        a.field("fn.retired");
        a.vec(&f.retired);
        for p in &f.retired {
            p.2.scan(&mut a);
        }
        a.field("fn.inlined_into");
        a.vec(&f.inlined_into);
    }
    a.field("fn_map");
    {
        let mut own = Vec::new();
        let mut keys = Vec::new();
        u.fn_map.scan(|p| own.push(p), |k, _| keys.push(k as *const FnKey));
        for p in own {
            a.ptr(p);
        }
        for k in keys {
            a.fn_key(unsafe { &*k });
        }
    }
    a.field("consts");
    a.map(&u.consts, |a, k, _| a.vec(&k.1));
    a.field("const_readers");
    if let Ok(g) = u.const_readers.try_lock() {
        a.map(&*g, |a, _, v| a.vec(v));
    }
    a.field("body_deps");
    a.map(&u.body_deps, |a, _, v| a.vec(v));
    a.field("statics");
    a.map(&u.statics, |_, _, _| {});
    a.field("static_spans");
    a.btree(&u.static_spans, |_, _, _| {});
    a.field("sites");
    if let Ok(g) = u.sites.try_lock() {
        a.vec(&g);
        for s in g.iter() {
            a.string(&s.msg);
        }
    }
    a.field("site_ix");
    if let Ok(g) = u.site_ix.try_lock() {
        a.map(&*g, |a, k, _| a.string(&k.2));
    }
    u.syms.scan(&mut a);
    a.field("start_order");
    a.vec(&u.start_order);
    a.field("vtables");
    {
        let mut own = Vec::new();
        u.vtables.scan(|p| own.push(p), |_, _| {});
        for p in own {
            a.ptr(p);
        }
    }
    a.field("locations");
    if let Ok(g) = u.locations.try_lock() {
        a.map(&*g, |a, k, _| a.string(&k.0));
    }
    a.field("lit_data");
    if let Ok(g) = u.lit_data.try_lock() {
        a.map(&*g, |a, k, _| a.vec(&k.0));
    }
    a.field("provided");
    a.vec(&u.provided);
    for (_, p) in &u.provided {
        a.string(&p.name);
        a.map(&p.shims, |a, k, _| a.string(k));
        a.map(&p.types, |a, k, _| a.string(k));
        a.map(&p.layouts, |a, k, _| a.string(k));
    }
    a.field("provided_types");
    a.map(&u.provided_types, |_, _, _| {});
    a.field("provided_shared");
    a.set(&u.provided_shared);
    a.field("missing_stubs");
    if let Ok(g) = u.missing_stubs.try_lock() {
        a.map(&*g, |a, k, _| a.string(k));
    }
    a.field("patch_log");
    a.vec(&u.patch_log);
    a.field("cold_users");
    a.map(&u.cold_users, |a, _, v| a.vec(v));
    a.field("retiers");
    a.map(&u.retiers, |_, _, _| {});
    a.field("frequency_profiles");
    a.map(&u.frequency_profiles, |a, _, p| a.map(&p.positions, |_, _, _| {}));
    a.field("errors");
    a.vec(&u.errors);
    for e in &u.errors {
        a.string(e);
    }
    a.field("stats.timeline");
    a.vec(&u.stats.timeline);
    a.field("stats.tier1_drop_why");
    a.btree(&u.stats.tier1_drop_why, |_, _, _| {});
    a.counts.retain(|c| c.1 > 0);
    a.counts
}

/// Whether `RELAX_ZONE_CHECK=1`.
pub(crate) fn enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("RELAX_ZONE_CHECK").map_or(false, |v| v == "1"))
}

/// The scan's result: the one-line report, and the total (for `inspect memory`).
pub(crate) fn report(u: &Unit) -> (usize, String) {
    let counts = kept_scan(u);
    let total: usize = counts.iter().map(|c| c.1).sum();
    let list: Vec<String> = counts.iter().map(|(n, c)| format!("{n}: {c}")).collect();
    (total, format!("relax-zone: kept scan: {total} pointers into the compiler arena [{}]", list.join(", ")))
}

static LAST: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(usize::MAX);

/// The total of the latest scan (None: the check is off or has not run).
pub(crate) fn last_total() -> Option<usize> {
    match LAST.load(std::sync::atomic::Ordering::Relaxed) {
        usize::MAX => None,
        n => Some(n),
    }
}

/// Runs the scan and prints its line (a settle's owner call; silent unless RELAX_ZONE_CHECK=1).
pub(crate) fn settle_check(u: &Unit) {
    if !enabled() {
        return;
    }
    let (total, line) = report(u);
    LAST.store(total, std::sync::atomic::Ordering::Relaxed);
    eprintln!("{line}");
}
