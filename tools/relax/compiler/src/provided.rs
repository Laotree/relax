//! Provided crates (local/plans/loader-core.md section 8): a crate rustc built into the binary
//! that runs Relax (the `relax` loader builds makepad-script into itself). Relax still loads
//! its source (types, signatures, generic and inline bodies) but binds its non-generic,
//! C-shaped fns to the compiled code: each such fn gets a bridge body (lower::bridge_func) with
//! Relax's own ABI that packs its arguments into one uniform C call,
//! `extern "C" fn(args: *const *mut u8, ret: *mut u8) -> u32`, of a shim `makepad host-gen`
//! generated into the crate (host_gen below). Callers, fn pointers and vtables need nothing
//! else: the slot is an ordinary Relax fn.
//!
//! A fn is bound when every parameter and the result are C-shaped (`trusted`): scalars,
//! pointers/references to the crate's own types or to trusted values, `&str`, slices of trusted
//! elements, `extern "C"` fn pointers, and the crate's `#[repr(C)]` / `#[repr(transparent)]` /
//! fieldless primitive-repr types. Other fns compile from source as before.
//!
//! Each shim is registered under the fn's key (its path as Relax names it) with a hash of its
//! signature as Relax sees it; a key whose hash differs is a boot error ("host shims are
//! stale: run makepad host-gen"), never a wrong call.

use crate::lang_items::LangItem;
use crate::program::{DefId, DefKind, Program, NO_DEF};
use crate::tcx::Tcx;
use crate::types::{TyId, TyKind};
use std::collections::HashMap;
use std::sync::Mutex;

/// A generated shim: arguments moved out of `args[i]`, the result written to `ret`; 0 = returned,
/// 1 = panicked (the message is then read with the crate's LastPanicFn).
pub type ShimFn = unsafe extern "C" fn(*const *mut u8, *mut u8) -> u32;
/// Writes the text of the last panic a shim caught on this thread: (ptr, len), valid until the
/// thread's next shim call.
pub type LastPanicFn = unsafe extern "C" fn(*mut *const u8, *mut usize);

/// A provided type rustc lays out (its fields are the crate's business): size, align, and
/// its `drop_in_place` when it needs drop.
pub type DropFn = unsafe extern "C" fn(*mut u8);

pub struct ProvidedCrate {
    /// the crate's name as Relax loads it (`makepad_script`)
    pub name: String,
    /// key -> (signature hash, shim)
    pub shims: HashMap<&'static str, (u64, ShimFn)>,
    /// opaque types by def path: (size, align, drop)
    pub types: HashMap<&'static str, (u64, u64, Option<DropFn>)>,
    /// trusted types by def path: rustc's (size, align), checked against Relax's at unit creation
    pub layouts: HashMap<&'static str, (u64, u64, &'static [u64])>,
    pub last_panic: LastPanicFn,
    /// the source identity rustc built it from (srchash.rs; the loader's build.rs)
    pub source: u64,
}

static REGISTRY: Mutex<Vec<ProvidedCrate>> = Mutex::new(Vec::new());

/// Registers a provided crate (before `cli_main`): its generated shim table
/// (`<crate>::__host_shims::SHIMS`) and panic-text accessor.
pub fn register(
    name: &str,
    shims: &'static [(&'static str, u64, ShimFn)],
    types: &'static [(&'static str, u64, u64, Option<DropFn>)],
    layouts: &'static [(&'static str, u64, u64, &'static [u64])],
    last_panic: LastPanicFn,
    source: u64,
) {
    let name = name.replace('-', "_");
    let shims = shims.iter().map(|(k, h, f)| (*k, (*h, *f))).collect();
    let types = types.iter().map(|(k, s, a, d)| (*k, (*s, *a, *d))).collect();
    let layouts = layouts.iter().map(|(k, s, a, o)| (*k, (*s, *a, *o))).collect();
    REGISTRY.lock().unwrap_or_else(|e| e.into_inner()).push(ProvidedCrate { name, shims, types, layouts, last_panic, source });
}

/// The registered crates whose source in the program is what the loader was built from
/// (check_sources); only they bind.
static MATCHED: Mutex<Vec<String>> = Mutex::new(Vec::new());

/// Compares each registered crate's source identity in the program's crate graph (`pkgs`:
/// the unit graph's packages, srchash.rs) with the loader's. A crate that differs (a dev edit,
/// another checkout or release, a patched dependency) is an error for the Splash VM; other
/// provided crates retain source fallback. Crates absent from the program need no binding.
pub fn check_sources(pkgs: &[crate::srchash::SrcPkg], quiet: bool) -> Result<(), String> {
    let reg = REGISTRY.lock().unwrap_or_else(|e| e.into_inner());
    let mut matched = MATCHED.lock().unwrap_or_else(|e| e.into_inner());
    matched.clear();
    for p in reg.iter() {
        let Some(root) = pkgs.iter().position(|k| k.name.replace('-', "_") == p.name) else { continue };
        let here = crate::srchash::closure_hash(pkgs, root);
        if here == p.source {
            matched.push(p.name.clone());
        } else if matches!(p.name.as_str(), "makepad_live_id" | "makepad_script" | "makepad_script_std" | "makepad_script_compute" | "makepad_script_census" | "makepad_tween_script" | "makepad_script_audio_aot") {
            matched.clear();
            return Err(format!("the Splash VM in this tree differs from the one built into relax: rebuild relax (cargo build --release -p relax) [{}: source {:016x}, loader {:016x}]", p.name, here, p.source));
        } else if !quiet {
            eprintln!("relax-run: {}: source differs from the loader's build ({:016x}, loader {:016x}): compiled from source", p.name, here, p.source);
        }
    }
    Ok(())
}

/// The registered crates as (crate index in `prog`, entry) whose source matched (check_sources);
/// crates not in the program are left out. Taken once per unit (Unit::new).
pub fn take_for(prog: &Program) -> Vec<(u32, ProvidedCrate)> {
    let matched = MATCHED.lock().unwrap_or_else(|e| e.into_inner());
    let mut out = Vec::new();
    for p in REGISTRY.lock().unwrap_or_else(|e| e.into_inner()).iter() {
        if !matched.contains(&p.name) {
            continue;
        }
        if let Some(i) = prog.crates.iter().position(|c| prog.syms.str(c.name) == p.name) {
            out.push((i as u32, ProvidedCrate { name: p.name.clone(), shims: p.shims.clone(), types: p.types.clone(), layouts: p.layouts.clone(), last_panic: p.last_panic, source: p.source }));
        }
    }
    out
}

/// Is crate `krate` of `prog` a registered provided crate?
fn is_provided(prog: &Program, krate: u32) -> bool {
    let name = prog.syms.str(prog.crates[krate as usize].name);
    REGISTRY.lock().unwrap_or_else(|e| e.into_inner()).iter().any(|p| p.name == name)
}

fn fnv(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// `#[repr(transparent)]` on an ADT (Relax's AdtT records repr(C)/int only; transparent lays
/// out as its one non-ZST field, which `trusted` checks).
fn is_transparent(prog: &Program, d: DefId) -> bool {
    let def = prog.def(d);
    let f = &prog.files[def.file as usize];
    f.ast.list(f.ast.item(def.item).attrs).iter().any(|a| {
        a.toks.hi > a.toks.lo && f.tok_text(a.toks.lo) == "repr" && (a.toks.lo + 1..a.toks.hi).any(|i| f.tok_text(i) == "transparent")
    })
}

/// Identity flags follow rustc_middle/src/ty/adt.rs:371; host layout checks remain required.
/// Is `t` the same bytes on both sides of the boundary (rustc-built crate, Relax-built caller)?
/// `krate` is the provided crate: pointers to its own types are opaque handles.
pub fn trusted(prog: &Program, tcx: &Tcx, krate: u32, t: TyId, depth: u32) -> bool {
    trusted_in(prog, tcx, krate, t, depth, false)
}

/// `field`: `t` is a field of a provided type, where a pointer to a trait object may pass
/// through (rustc stores and hands it back, never calls through it: the vtable is Relax's; the
/// VM's `host: &mut dyn ScriptHost`). As a bound fn's own parameter it may not.
fn trusted_in(prog: &Program, tcx: &Tcx, krate: u32, t: TyId, depth: u32, field: bool) -> bool {
    if depth > 8 {
        return false;
    }
    let tr = |t: TyId| trusted_in(prog, tcx, krate, t, depth + 1, false);
    // a pointer to the crate's own values (rustc made them: the pointer is a handle) or to
    // trusted ones
    let own_pub = |x: TyId| matches!(tcx.tys.kind(x), TyKind::Adt(d, a, _) if a.is_empty() && prog.def(*d).krate == krate && prog.def(*d).is_pub);
    let pointee = |x: TyId| match tcx.tys.kind(x) {
        TyKind::Str => true,
        // the crate's own public types as elements: rustc's stride (TYPES / LAYOUTS), read only
        // through the crate's fns
        TyKind::Slice(e) => tr(*e) || own_pub(*e),
        // generic ones too: the pointer is an address, their fields stay unread (lower.rs); so
        // are another provided crate's (rustc-built into the same binary: the census's &mut ScriptVm)
        TyKind::Adt(d, _, _) => prog.def(*d).krate == krate || is_provided(prog, prog.def(*d).krate) || tr(x),
        TyKind::Dyn(..) => field,
        _ => tr(x),
    };
    match tcx.tys.kind(t) {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Float(_) | TyKind::Never => true,
        // tuples: rustc's size checked through LAYOUTS (layout_deps)
        TyKind::Tuple(v) => v.iter().all(|x| tr(*x)),
        TyKind::Ref(_, x, _) | TyKind::Ptr(_, x) => pointee(*x),
        TyKind::FnPtr(_, _, header, _) => header.abi.is_c_like(),
        TyKind::Array(e, _) => tr(*e),
        TyKind::Adt(d, a, _) => {
            // Box<T> (global allocator): a pointer; both sides allocate with the system malloc
            if tcx.adts.get(d).is_some_and(|a| a.is_box()) {
                return a.len() <= 2 && a.first().is_some_and(|x| !matches!(tcx.tys.kind(*x), TyKind::Dyn(..)) && pointee(*x));
            }
            let std_crate = is_std(prog, prog.def(*d).krate);
            // Option<T>: rustc's layout (niche or tag), checked against host-gen's LAYOUTS
            // PhantomData<T>: zero-sized, the same on both sides
            if tcx.adts.get(d).is_some_and(|a| a.is_phantom_data()) {
                return true;
            }
            if tcx.lang_items.get(LangItem::Option) == Some(*d) && a.len() == 1 {
                return tr(a[0]);
            }
            if !a.is_empty() {
                return false;
            }
            let adt = match tcx.adts.get(d) {
                Some(x) => x,
                None => return false,
            };
            // std's own types: fieldless enums only (Ordering), checked against LAYOUTS;
            // other crates' plain data (LiveId, the math vectors): as the crate's own
            if std_crate && !(adt.is_enum && adt.variants.iter().all(|v| v.fields.is_empty())) {
                return false;
            }
            if adt.is_union {
                return false;
            }
            let fields_ok = |v: &crate::tcx::VariantT| v.fields.iter().all(|f| trusted_in(prog, tcx, krate, f.ty, depth + 1, true));
            if adt.is_enum {
                if adt.variants.iter().all(|v| v.fields.is_empty()) {
                    return true;
                }
                // repr(C) / repr(int) data enums: laid out by RFC 2195
                if adt.repr_c || adt.repr_int.is_some() {
                    return adt.variants.iter().all(fields_ok);
                }
                // Option-like over a reference: the null niche (rustc's guaranteed layout)
                let opt_like = adt.variants.len() == 2
                    && adt.variants.iter().filter(|v| v.fields.is_empty()).count() == 1
                    && adt.variants.iter().any(|v| v.fields.len() == 1 && matches!(tcx.tys.kind(v.fields[0].ty), TyKind::Ref(..)) && fields_ok(v));
                return opt_like;
            }
            // structs, any repr: Relax lays them out as rustc does (layout.rs); host-gen's
            // LAYOUTS table carries rustc's size/align and a mismatch makes the type opaque
            let _ = is_transparent;
            adt.variants.iter().all(fields_ok)
        }
        _ => false,
    }
}

fn is_std(prog: &Program, krate: u32) -> bool {
    matches!(prog.syms.str(prog.crates[krate as usize].name), "core" | "alloc" | "std")
}

/// Every type in `t` whose layout the bound fn relies on and that is not the crate's own
/// non-generic type (those are in LAYOUTS / TYPES already): std instances (Option<T>) and other
/// crates' types. host-gen emits rustc's size/align for each; Relax compares before binding.
pub fn layout_deps(prog: &Program, tcx: &Tcx, krate: u32, t: TyId, out: &mut Vec<TyId>) {
    match tcx.tys.kind(t) {
        TyKind::Ref(_, x, _) | TyKind::Ptr(_, x) => {
            // a pointer to the crate's own values is a handle; to others: their layout matters
            if !matches!(tcx.tys.kind(*x), TyKind::Adt(d, _, _) if prog.def(*d).krate == krate) {
                layout_deps(prog, tcx, krate, *x, out);
            }
        }
        TyKind::Slice(e) | TyKind::Array(e, _) => layout_deps(prog, tcx, krate, *e, out),
        TyKind::Tuple(v) if !v.is_empty() => {
            if !out.contains(&t) {
                out.push(t);
            }
            for x in v {
                layout_deps(prog, tcx, krate, *x, out);
            }
        }
        TyKind::Adt(d, a, _) => {
            if tcx.adts.get(d).is_some_and(|a| a.is_box()) {
                return;
            }
            if prog.def(*d).krate != krate || !a.is_empty() {
                if !out.contains(&t) {
                    out.push(t);
                }
            }
            for x in a {
                layout_deps(prog, tcx, krate, *x, out);
            }
        }
        _ => {}
    }
}

/// The key a shim is registered under: the fn's path as Relax names it, impls as
/// `<Self>` / `<Self as Trait>` with their types resolved.
pub fn key(prog: &Program, tcx: &Tcx, d: DefId) -> String {
    let mut parts = Vec::new();
    let mut cur = d;
    while cur != NO_DEF && parts.len() < 64 {
        let def = prog.def(cur);
        if def.kind == DefKind::Impl {
            let st = tcx.impl_self.get(&cur).map(|t| crate::typeck::ty_to_string(false, prog, tcx, *t)).unwrap_or_default();
            parts.push(match tcx.impl_trait.get(&cur) {
                Some(tr) => {
                    // the trait's arguments tell `From<f64>` from `From<bool>` apart
                    let targs = tcx.impl_trait_args.get(&cur).cloned().unwrap_or_default();
                    let a: Vec<String> = targs.iter().map(|t| crate::typeck::ty_to_string(false, prog, tcx, *t)).collect();
                    if a.is_empty() {
                        format!("<{} as {}>", st, prog.def_path(*tr))
                    } else {
                        format!("<{} as {}<{}>>", st, prog.def_path(*tr), a.join(", "))
                    }
                }
                None => format!("<{}>", st),
            });
            break;
        }
        parts.push(prog.syms.str(def.name).to_string());
        cur = def.parent;
    }
    parts.reverse();
    parts.join("::")
}

/// The host bridge key for Clone / PartialEq on an opaque type.
pub fn opaque_method_key(prog: &Program, d: DefId, method: &str) -> String {
    match method {
        "eq" => format!("<{} as PartialEq>::eq", prog.def_path(d)),
        _ => format!("<{} as Clone>::clone", prog.def_path(d)),
    }
}

/// The signature hash checked at bind time: parameter and result types as Relax sees them.
pub fn sig_hash(prog: &Program, tcx: &Tcx, d: DefId) -> u64 {
    let s = match tcx.fn_sig(prog, d) {
        Some(s) => s,
        None => return 0,
    };
    let mut text = String::new();
    for p in &s.params {
        text.push_str(&crate::typeck::ty_to_string(false, prog, tcx, *p));
        text.push(',');
    }
    text.push_str("->");
    text.push_str(&crate::typeck::ty_to_string(false, prog, tcx, s.ret));
    fnv(&text)
}

/// Why `d` (a fn of provided crate `krate`) is compiled from source instead of bound to a shim;
/// None: it is bound.
pub fn unbound_reason(prog: &Program, tcx: &Tcx, krate: u32, d: DefId, opaque: &dyn Fn(DefId) -> bool) -> Option<&'static str> {
    let def = prog.def(d);
    if !matches!(def.kind, DefKind::Fn | DefKind::AssocFn) {
        return Some("not a fn");
    }
    let s = tcx.fn_sig(prog, d)?;
    if s.n_generics > 0 {
        return Some("generic");
    }
    if s.header.abi.is_c_like() || s.header.c_variadic || s.track_caller {
        return Some("abi");
    }
    if crate::jit::inline_attrs(prog, d) & crate::opt::ATTR_ALWAYS != 0 {
        return Some("#[inline(always)]: compiled on the caller's side");
    }
    let parent = prog.def(def.parent);
    if parent.kind == DefKind::Trait {
        return Some("trait default body");
    }
    // Eq's derived assertion is a rustc-internal type-check helper, not a callable API.
    if parent.kind == DefKind::Impl
        && prog.syms.str(def.name) == "assert_fields_are_eq"
        && tcx.impl_trait.get(&def.parent).is_some_and(|t| prog.def_path(*t) == "core::cmp::Eq")
    {
        return Some("Eq assertion (compiler internal)");
    }
    // `Drop::drop` runs inside the type's drop shim (rustc refuses an explicit call, E0040)
    if parent.kind == DefKind::Impl && tcx.impl_trait.get(&def.parent).is_some_and(|t| tcx.lang_items.get(LangItem::Drop) == Some(*t)) {
        return Some("Drop::drop (in the drop shim)");
    }
    let crosses = |t: TyId| trusted(prog, tcx, krate, t, 0) || matches!(tcx.tys.kind(t), TyKind::Adt(d, a, _) if a.is_empty() && opaque(*d));
    if !s.params.iter().chain(std::iter::once(&s.ret)).all(|t| crosses(*t)) {
        return Some("signature not C-shaped");
    }
    None
}

/// Is ADT `d` of crate `krate` one host-gen lists as opaque (rustc's size/align, drop shim):
/// a public non-generic struct or enum that is not `trusted` by value.
pub fn opaque_candidate(prog: &Program, tcx: &Tcx, krate: u32, d: DefId) -> bool {
    let def = prog.def(d);
    if def.krate != krate || !def.is_pub || !matches!(def.kind, DefKind::Struct | DefKind::Enum) {
        return false;
    }
    match tcx.adts.get(&d) {
        Some(a) if a.n_generics == 0 && !a.is_union => {}
        _ => return false,
    }
    let t = tcx.tys.intern(TyKind::Adt(d, Vec::new(), crate::types::RegionArgsId::EMPTY));
    !trusted(prog, tcx, krate, t, 0)
}

/// Whether the root shim module can name this item (including restricted visibility).
fn root_visible(prog: &Program, d: DefId) -> bool {
    let def = prog.def(d);
    if def.parent == NO_DEF { return true; }
    let item = prog.files[def.file as usize].ast.item(def.item);
    prog.vis_module(def.file, def.scope, &item.vis)
        .is_none_or(|m| m == prog.crates[def.krate as usize].root_mod)
}

/// Preserve conditions on enclosing modules/items in the generated declarations and tables.
/// In particular, an ARM host's compute shims must still compile on x86.
fn item_cfg(prog: &Program, d: DefId) -> String {
    let mut attrs = std::collections::BTreeSet::new();
    let mut cur = d;
    while cur != NO_DEF {
        let def = prog.def(cur);
        if def.parent == NO_DEF { break; }
        let f = &prog.files[def.file as usize];
        for a in f.ast.list(f.ast.item(def.item).attrs) {
            if a.toks.hi > a.toks.lo && f.tok_text(a.toks.lo) == "cfg" {
                let text = (a.toks.lo..a.toks.hi).map(|i| f.tok_text(i)).collect::<Vec<_>>().join(" ");
                attrs.insert(format!("#[{text}]\n"));
            }
        }
        cur = def.parent;
    }
    attrs.into_iter().collect()
}

fn type_cfg(prog: &Program, tcx: &Tcx, t: TyId) -> String {
    match tcx.tys.kind(t) {
        TyKind::Adt(d, args, _) => {
            let mut out = item_cfg(prog, *d);
            for a in args { out.push_str(&type_cfg(prog, tcx, *a)); }
            out
        }
        TyKind::Ref(_, t, _) | TyKind::Ptr(_, t) | TyKind::Slice(t) | TyKind::Array(t, _) => type_cfg(prog, tcx, *t),
        TyKind::Tuple(ts) => ts.iter().map(|t| type_cfg(prog, tcx, *t)).collect(),
        _ => String::new(),
    }
}

/// Shim Rust path for fn `d` of crate `krate` (from inside the crate: `crate::...`), or None
/// when rustc cannot name it from the crate root (a private fn or module path).
fn rust_path(prog: &Program, tcx: &Tcx, krate: u32, d: DefId) -> Option<String> {
    let def = prog.def(d);
    if !def.is_pub || !root_visible(prog, d) {
        // impl methods of trait impls are callable through the trait
        let p = prog.def(def.parent);
        if !(p.kind == DefKind::Impl && tcx.impl_trait.contains_key(&def.parent)) {
            return None;
        }
    }
    let name = prog.syms.str(def.name).to_string();
    let parent = def.parent;
    if prog.def(parent).kind == DefKind::Impl {
        let st = tcx.impl_self.get(&parent)?;
        let st_path = rust_ty(prog, tcx, krate, *st)?;
        return Some(match tcx.impl_trait.get(&parent) {
            Some(tr) => {
                let mut tp = trait_path(prog, krate, *tr)?;
                let targs = tcx.impl_trait_args.get(&parent).cloned().unwrap_or_default();
                if !targs.is_empty() {
                    let a: Option<Vec<String>> = targs.iter().map(|t| rust_ty(prog, tcx, krate, *t)).collect();
                    tp = format!("{}<{}>", tp, a?.join(", "));
                }
                format!("<{} as {}>::{}", st_path, tp, name)
            }
            None => format!("<{}>::{}", st_path, name),
        });
    }
    Some(format!("{}::{}", item_path(prog, krate, parent)?, name))
}

/// A trait's path as rustc names it from inside crate `krate`: the crate's own public traits,
/// other crates' traits, and std traits in the modules whose path is the same in Relax's std and
/// rustc's (Relax's std is laid out differently elsewhere, e.g. `core::string`).
fn trait_path(prog: &Program, krate: u32, tr: DefId) -> Option<String> {
    let def = prog.def(tr);
    if !def.is_pub {
        return None;
    }
    let p = item_path(prog, krate, tr)?;
    let cname = prog.syms.str(prog.crates[def.krate as usize].name);
    if matches!(cname, "core" | "alloc" | "std") {
        const SAME: [&str; 12] = ["default", "clone", "ops", "cmp", "convert", "hash", "fmt", "iter", "borrow", "str", "any", "marker"];
        let rest = p.trim_start_matches("::").splitn(3, "::").collect::<Vec<_>>();
        if rest.len() < 3 || !SAME.contains(&rest[1]) {
            return None;
        }
        return Some(format!("::core::{}::{}", rest[1], rest[2]));
    }
    Some(p)
}

/// Is `d` reachable by its definition path from outside its crate (it and every enclosing
/// module public)?
fn nameable(prog: &Program, d: DefId) -> bool {
    let mut cur = d;
    while cur != NO_DEF {
        let def = prog.def(cur);
        if def.parent == NO_DEF {
            return true;
        }
        if !def.is_pub {
            return false;
        }
        cur = def.parent;
    }
    true
}

/// A module or item path from inside crate `krate` (`crate::a::b`, `::other::x`).
fn item_path(prog: &Program, krate: u32, d: DefId) -> Option<String> {
    let mut parts = Vec::new();
    let mut cur = d;
    while cur != NO_DEF && parts.len() < 64 {
        let def = prog.def(cur);
        if def.parent == NO_DEF {
            // the crate root module
            parts.push(if def.krate == krate { "crate".to_string() } else { format!("::{}", prog.syms.str(prog.crates[def.krate as usize].name)) });
            break;
        }
        if def.krate == krate && !root_visible(prog, cur) { return None; }
        parts.push(prog.syms.str(def.name).to_string());
        cur = def.parent;
    }
    parts.reverse();
    Some(parts.join("::"))
}

fn rust_ty(prog: &Program, tcx: &Tcx, krate: u32, t: TyId) -> Option<String> {
    match tcx.tys.kind(t) {
        // the crate's own public types only (other crates' paths may differ under rustc)
        TyKind::Adt(d, a, _) if a.is_empty() && prog.def(*d).krate == krate && prog.def(*d).is_pub => item_path(prog, krate, *d),
        TyKind::Adt(d, a, _) if a.len() == 1 && tcx.lang_items.get(LangItem::Option) == Some(*d) => {
            Some(format!("::core::option::Option<{}>", rust_ty(prog, tcx, krate, a[0])?))
        }
        TyKind::Adt(d, a, _) if a.is_empty() && tcx.lang_items.get(LangItem::OrderingEnum) == Some(*d) => {
            Some("::core::cmp::Ordering".to_string())
        }
        // another (non-std) crate's public type with a public module path
        TyKind::Adt(d, a, _) if a.is_empty() && !is_std(prog, prog.def(*d).krate) && nameable(prog, *d) => item_path(prog, krate, *d),
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str => Some(crate::typeck::ty_to_string(false, prog, tcx, t)),
        TyKind::Ref(m, x, _) => Some(format!("&{}{}", if *m { "mut " } else { "" }, rust_ty(prog, tcx, krate, *x)?)),
        TyKind::Slice(x) => Some(format!("[{}]", rust_ty(prog, tcx, krate, *x)?)),
        TyKind::Array(x, n) => Some(format!("[{}; {}]", rust_ty(prog, tcx, krate, *x)?, n.try_to_target_usize(&tcx.tys)?)),
        TyKind::Tuple(v) if v.is_empty() => Some("()".to_string()),
        TyKind::Tuple(v) => {
            let a: Option<Vec<String>> = v.iter().map(|x| rust_ty(prog, tcx, krate, *x)).collect();
            Some(format!("({},)", a?.join(", ")))
        }
        _ => None,
    }
}

/// `makepad host-gen`: the shim file of provided crate `krate` (included by the crate under
/// `#[cfg(feature = "host-shims")]`, see the crate's lib.rs). Returns (file text, report).
pub fn host_gen(prog: &Program, tcx: &Tcx, krate: u32) -> (String, String) {
    let mut fns: Vec<(String, u64, String, usize, bool, String)> = Vec::new();
    let mut why: HashMap<&'static str, usize> = HashMap::new();
    let mut unshaped: Vec<String> = Vec::new();
    let mut blockers: HashMap<String, usize> = HashMap::new();
    let mut dep_lays: Vec<(String, String, String)> = Vec::new();
    // the fns that get a shim: only they cross (a private fn with a C-shaped signature does not)
    let mut bound: std::collections::HashSet<DefId> = Default::default();
    for (i, def) in prog.defs.iter().enumerate() {
        let d = DefId(i as u32);
        if def.krate != krate || !matches!(def.kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let it = prog.files[def.file as usize].ast.item(def.item);
        let has_body = matches!(&it.kind, crate::ast::ItemKind::Fn(s, b, _) if b.is_some() || prog.files[def.file as usize].ast.fn_sig(*s).lazy_body.is_some());
        if !has_body {
            continue;
        }
        if let Some(r) = unbound_reason(prog, tcx, krate, d, &|a| opaque_candidate(prog, tcx, krate, a)) {
            *why.entry(r).or_default() += 1;
            if r == "signature not C-shaped" {
                unshaped.push(key(prog, tcx, d));
                if let Some(sg) = tcx.fn_sig(prog, d) {
                    let op = |a: DefId| opaque_candidate(prog, tcx, krate, a);
                    for t in sg.params.iter().chain(std::iter::once(&sg.ret)) {
                        let ok = trusted(prog, tcx, krate, *t, 0) || matches!(tcx.tys.kind(*t), TyKind::Adt(d2, a2, _) if a2.is_empty() && op(*d2));
                        if !ok {
                            *blockers.entry(crate::typeck::ty_to_string(false, prog, tcx, *t)).or_default() += 1;
                        }
                    }
                }
            }
            continue;
        }
        let path = match rust_path(prog, tcx, krate, d) {
            Some(p) => p,
            None => {
                *why.entry("not nameable from the crate root (private)").or_default() += 1;
                continue;
            }
        };
        let n = tcx.fn_sig(prog, d).map_or(0, |s| s.params.len());
        let never = tcx.fn_sig(prog, d).is_some_and(|s| matches!(tcx.tys.kind(s.ret), TyKind::Never));
        // the layouts this binding relies on must be nameable to be checked; else compiled from source
        let mut deps = Vec::new();
        if let Some(sg) = tcx.fn_sig(prog, d) {
            for t in sg.params.iter().chain(std::iter::once(&sg.ret)) {
                layout_deps(prog, tcx, krate, *t, &mut deps);
            }
        }
        let named: Option<Vec<(String, String, String)>> = deps.iter().map(|t| rust_ty(prog, tcx, krate, *t).map(|r| (crate::typeck::ty_to_string(false, prog, tcx, *t), r, type_cfg(prog, tcx, *t)))).collect();
        let Some(named) = named else {
            *why.entry("a type in the signature is not nameable for its layout check").or_default() += 1;
            continue;
        };
        dep_lays.extend(named);
        bound.insert(d);
        let mut cfg = item_cfg(prog, d);
        if let Some(sg) = tcx.fn_sig(prog, d) {
            for t in sg.params.iter().chain(std::iter::once(&sg.ret)) { cfg.push_str(&type_cfg(prog, tcx, *t)); }
        }
        fns.push((key(prog, tcx, d), sig_hash(prog, tcx, d), path, n, never, cfg));
    }
    fns.sort();
    fns.dedup_by(|a, b| a.0 == b.0);
    let mut out = String::new();
    out.push_str("// @generated by `makepad host-gen` (Relax provided crates, loader-core.md section 8). Do not edit.\n");
    out.push_str("// One C shim per bound fn: arguments moved out of args[i] (types inferred from the call),\n");
    out.push_str("// the result written to ret; 0 = returned, 1 = panicked (text: __host_last_panic).\n");
    out.push_str("#![allow(unused_unsafe, unused_variables, clippy::all)]\n\n");
    out.push_str("thread_local! { static LAST_PANIC: std::cell::RefCell<String> = const { std::cell::RefCell::new(String::new()) }; }\n\n");
    out.push_str("fn caught(p: Box<dyn std::any::Any + Send>) -> u32 {\n");
    out.push_str("    let msg = p.downcast_ref::<&str>().map(|s| s.to_string()).or_else(|| p.downcast_ref::<String>().cloned()).unwrap_or_else(|| \"panic\".to_string());\n");
    out.push_str("    LAST_PANIC.with(|l| *l.borrow_mut() = msg);\n    1\n}\n\n");
    out.push_str("pub unsafe extern \"C\" fn __host_last_panic(ptr: *mut *const u8, len: *mut usize) {\n");
    out.push_str("    LAST_PANIC.with(|l| { let l = l.borrow(); *ptr = l.as_ptr(); *len = l.len(); });\n}\n\n");
    for (i, (_, _, path, n, never, cfg)) in fns.iter().enumerate() {
        out.push_str(cfg);
        out.push_str(&format!("unsafe extern \"C\" fn s{}(a: *const *mut u8, r: *mut u8) -> u32 {{\n", i));
        let args: Vec<String> = (0..*n).map(|k| format!("std::ptr::read(*a.add({}) as *const _)", k)).collect();
        if *never {
            // diverges: returns only by panicking
            out.push_str(&format!(
                "    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| -> () {{ unsafe {{ {}({}) }} }})) {{ Ok(()) => 0, Err(p) => caught(p) }}\n}}\n",
                path,
                args.join(", ")
            ));
            continue;
        }
        out.push_str(&format!(
            "    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {{ {}({}) }})) {{ Ok(v) => {{ std::ptr::write(r as *mut _, v); 0 }} Err(p) => caught(p) }}\n}}\n",
            path,
            args.join(", ")
        ));
    }
    // opaque types: rustc's size/align and drop
    // opaque only what crosses (a type no bound fn reaches is Relax's alone)
    let crossing = crossing_types(prog, tcx, &[krate], &|d| bound.contains(&d));
    // Regions do not affect the opaque layout: signatures can carry non-empty lifetime
    // arguments even when a type has no type parameters (ScriptModuleRead, for example).
    let mut tys: Vec<(String, String, DefId)> = Vec::new();
    for (i, def) in prog.defs.iter().enumerate() {
        let d = DefId(i as u32);
        if def.krate == krate && opaque_candidate(prog, tcx, krate, d) && crossing.iter().any(|t| matches!(tcx.tys.kind(*t), TyKind::Adt(ad, args, _) if *ad == d && args.is_empty())) {
            if let Some(p) = item_path(prog, krate, d) {
                tys.push((prog.def_path(d), p, d));
            }
        }
    }
    tys.sort_by(|a, b| a.0.cmp(&b.0));
    tys.dedup_by(|a, b| a.0 == b.0);
    // Clone / PartialEq impls on host-owned opaque types.
    let mut opaque_trait_shims: Vec<(String, String, String)> = Vec::new();
    for (_, p, d) in &tys {
        for (&imp, &td) in &tcx.impl_trait {
            if !tcx.impl_self.get(&imp).is_some_and(|t| matches!(tcx.tys.kind(*t), TyKind::Adt(ad, aa, _) if *ad == *d && aa.is_empty())) { continue; }
            if tcx.lang_items.get(LangItem::Clone) == Some(td) {
                opaque_trait_shims.push((opaque_method_key(prog, *d, "clone"), format!("<{} as ::core::clone::Clone>::clone(std::ptr::read(*a.add(0) as *const _))", p), item_cfg(prog, *d)));
            } else if tcx.lang_items.get(LangItem::PartialEq) == Some(td)
                && tcx.impl_trait_args.get(&imp).is_some_and(|args| args.as_slice() == [tcx.impl_self[&imp]]) {
                opaque_trait_shims.push((opaque_method_key(prog, *d, "eq"), format!("<{} as ::core::cmp::PartialEq>::eq(std::ptr::read(*a.add(0) as *const _), std::ptr::read(*a.add(1) as *const _))", p), item_cfg(prog, *d)));
            }
        }
    }
    // Hash / Debug / Display of opaque types, derived or written: rustc's impl, reached from
    // Relax's std helpers (jit.rs provided_fmt_hash); bytes / text come back by callback
    let mut hasher_used = false;
    {
        let has = |d: DefId, path_end: &str| {
            tcx.impl_trait.iter().any(|(imp, tr)| prog.def(*imp).krate == krate && prog.def_path(*tr).ends_with(path_end) && tcx.impl_self.get(imp).is_some_and(|t| matches!(tcx.tys.kind(*t), TyKind::Adt(a, aa, _) if *a == d && aa.is_empty())))
        };
        for (_, p, d) in &tys {
            if has(*d, "hash::Hash") {
                hasher_used = true;
                opaque_trait_shims.push((
                    format!("<{} as Hash>::hash_into", prog.def_path(*d)),
                    format!("{{ let x: &{p} = std::ptr::read(*a.add(0) as *const &{p}); let st: *mut u8 = std::ptr::read(*a.add(1) as *const *mut u8); let w: unsafe extern \"C-unwind\" fn(*mut u8, *const u8, usize) = std::ptr::read(*a.add(2) as *const _); ::core::hash::Hash::hash(x, &mut __RelaxHasher(st, w)) }}"),
                    item_cfg(prog, *d),
                ));
            }
            let debug = has(*d, "fmt::Debug");
            let display = has(*d, "fmt::Display");
            if debug || display {
                let arms = format!(
                    "{}{}",
                    if debug { "0 => format!(\"{:?}\", x), 1 => format!(\"{:#?}\", x), " } else { "" },
                    if display { "_ => format!(\"{}\", x)," } else { "_ => unreachable!(), " }
                );
                opaque_trait_shims.push((
                    format!("<{} as Fmt>::fmt_into", prog.def_path(*d)),
                    format!("{{ let x: &{p} = std::ptr::read(*a.add(0) as *const &{p}); let mode: u8 = std::ptr::read(*a.add(1) as *const u8); let out: *mut u8 = std::ptr::read(*a.add(2) as *const *mut u8); let push: unsafe extern \"C-unwind\" fn(*mut u8, *const u8, usize) = std::ptr::read(*a.add(3) as *const _); let s: String = match mode {{ {arms} }}; push(out, s.as_ptr(), s.len()) }}"),
                    item_cfg(prog, *d),
                ));
            }
        }
    }
    if hasher_used {
        out.push_str("struct __RelaxHasher(*mut u8, unsafe extern \"C-unwind\" fn(*mut u8, *const u8, usize));\n");
        out.push_str("impl ::core::hash::Hasher for __RelaxHasher {\n    fn write(&mut self, b: &[u8]) { unsafe { (self.1)(self.0, b.as_ptr(), b.len()) } }\n    fn finish(&self) -> u64 { 0 }\n}\n\n");
    }
    opaque_trait_shims.sort();
    for (i, (_, call, cfg)) in opaque_trait_shims.iter().enumerate() {
        out.push_str(cfg);
        out.push_str(&format!(
            "unsafe extern \"C\" fn v{}(a: *const *mut u8, r: *mut u8) -> u32 {{\n    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {{ {} }})) {{ Ok(v) => {{ std::ptr::write(r as *mut _, v); 0 }} Err(p) => caught(p) }}\n}}\n",
            i, call
        ));
    }
    for (i, (_, p, d)) in tys.iter().enumerate() {
        out.push_str(&item_cfg(prog, *d));
        out.push_str(&format!(
            "unsafe extern \"C\" fn d{}(p: *mut u8) {{ let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {{ std::ptr::drop_in_place(p as *mut {}) }})); }}\n",
            i, p
        ));
    }
    out.push_str("\npub static TYPES: &[(&str, u64, u64, Option<unsafe extern \"C\" fn(*mut u8)>)] = &[\n");
    for (i, (k, p, d)) in tys.iter().enumerate() {
        out.push_str(&item_cfg(prog, *d));
        out.push_str(&format!(
            "    ({:?}, std::mem::size_of::<{p}>() as u64, std::mem::align_of::<{p}>() as u64, if std::mem::needs_drop::<{p}>() {{ Some(d{i}) }} else {{ None }}),\n",
            k
        ));
    }
    out.push_str("];\n");
    // trusted types: rustc's size/align, checked by Relax at unit creation
    // (key, rust path, field names for offset_of! -- empty: size/align only)
    let mut lays: Vec<(String, String, Vec<String>, String)> = Vec::new();
    let mut unchecked_offsets = 0usize;
    for (i, def) in prog.defs.iter().enumerate() {
        let d = DefId(i as u32);
        if def.krate != krate || !def.is_pub || !matches!(def.kind, DefKind::Struct | DefKind::Enum) {
            continue;
        }
        let adt = match tcx.adts.get(&d) {
            Some(a) if a.n_generics == 0 && !a.is_union => a,
            _ => continue,
        };
        if opaque_candidate(prog, tcx, krate, d) {
            continue;
        }
        if let Some(p) = item_path(prog, krate, d) {
            // a struct's field offsets too (rustc may reorder fields; Relax's layout must agree):
            // offset_of! from the shim module needs the fields visible there
            let mut names = Vec::new();
            if !adt.is_enum {
                let fs = &adt.variants[0].fields;
                if fs.iter().all(|f| f.is_pub) {
                    // tuple fields are named by index
                    names = fs.iter().enumerate().map(|(i, f)| {
                        let n = prog.syms.str(f.name);
                        if n.chars().next().is_some_and(|c| c.is_alphabetic() || c == '_') { n.to_string() } else { i.to_string() }
                    }).collect();
                } else if !fs.is_empty() {
                    unchecked_offsets += 1;
                }
            }
            lays.push((prog.def_path(d), p, names, item_cfg(prog, d)));
        }
    }
    // the types bound signatures rely on (keyed by Relax's type name, checked at bind time)
    lays.extend(dep_lays.into_iter().map(|(k, p, cfg)| (k, p, Vec::new(), cfg)));
    lays.sort();
    lays.dedup_by(|a, b| a.0 == b.0);
    out.push_str("\npub static LAYOUTS: &[(&str, u64, u64, &[u64])] = &[\n");
    for (k, p, names, cfg) in &lays {
        out.push_str(cfg);
        let offs: Vec<String> = names.iter().map(|n| format!("std::mem::offset_of!({p}, {n}) as u64")).collect();
        out.push_str(&format!("    ({:?}, std::mem::size_of::<{p}>() as u64, std::mem::align_of::<{p}>() as u64, &[{}]),\n", k, offs.join(", ")));
    }
    out.push_str("];\n");
    let _ = unchecked_offsets;
    out.push_str("\npub static SHIMS: &[(&str, u64, unsafe extern \"C\" fn(*const *mut u8, *mut u8) -> u32)] = &[\n");
    for (i, (k, h, _, _, _, cfg)) in fns.iter().enumerate() {
        out.push_str(cfg);
        out.push_str(&format!("    ({:?}, 0x{:016x}, s{}),\n", k, h, i));
    }
    for (i, (k, _, cfg)) in opaque_trait_shims.iter().enumerate() {
        out.push_str(cfg);
        out.push_str(&format!("    ({:?}, 0, v{}),\n", k, i));
    }
    out.push_str("];\n");
    let mut rep = format!("host-gen {}: {} fns bound, {} opaque types", prog.syms.str(prog.crates[krate as usize].name), fns.len(), tys.len());
    let mut w: Vec<_> = why.into_iter().collect();
    w.sort_by(|a, b| b.1.cmp(&a.1));
    for (r, n) in w {
        rep.push_str(&format!("; {} {}", n, r));
    }
    let mut bl: Vec<_> = blockers.into_iter().collect();
    bl.sort_by(|a, b| b.1.cmp(&a.1));
    for (t, n) in bl.iter().take(60) {
        rep.push_str(&format!("\n  blocking type ({} fns): {}", n, t));
    }
    unshaped.sort();
    for k in unshaped {
        rep.push_str(&format!("\n  not C-shaped (compiled from source; may not read the crate's opaque fields): {}", k));
    }
    (out, rep)
}

/// The types whose values cross between the provided crates' rustc code and Relax-compiled code:
/// reachable from the signatures of the bound fns (`bound`) through references, arrays, tuples,
/// type arguments and the fields of provided-crate types (and Option/Box/PhantomData). The walk
/// does not enter other std types: what a rustc-built Vec or String holds is reached only
/// through bound fns, whose signatures are roots themselves. Every other type of a provided
/// crate is made and laid out by Relax-compiled code alone (an inline shell's result, a type only
/// generic or unbound code builds): no opaque layout, no field guard.
pub fn crossing_types(prog: &Program, tcx: &Tcx, krates: &[u32], bound: &dyn Fn(DefId) -> bool) -> std::collections::HashSet<TyId> {
    let mut out = std::collections::HashSet::new();
    let mut stack: Vec<TyId> = Vec::new();
    for (i, def) in prog.defs.iter().enumerate() {
        if !krates.contains(&def.krate) || !matches!(def.kind, DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let d = DefId(i as u32);
        if !bound(d) {
            continue;
        }
        if let Some(sg) = tcx.fn_sig(prog, d) {
            stack.extend(sg.params.iter().copied());
            stack.push(sg.ret);
        }
    }
    while let Some(t) = stack.pop() {
        if out.len() > 200_000 || !out.insert(t) {
            continue;
        }
        match tcx.tys.kind(t) {
            TyKind::Adt(d, a, _) => {
                let k = prog.def(*d).krate;
                if krates.contains(&k) {
                    if let Some(adt) = tcx.adts.get(d) {
                        for (vi, v) in adt.variants.iter().enumerate() {
                            for fi in 0..v.fields.len() {
                                stack.push(tcx.field_ty(prog, crate::tcx::TypingEnv::fully_monomorphized(&prog), *d, vi as u32, fi as u32, a));
                            }
                        }
                    }
                    stack.extend(a.iter().copied());
                } else if tcx.lang_items.get(LangItem::Option) == Some(*d) || tcx.adts.get(d).is_some_and(|a| a.is_box() || a.is_phantom_data()) {
                    stack.extend(a.iter().copied());
                }
            }
            TyKind::Ref(_, x, _) | TyKind::Ptr(_, x) | TyKind::Slice(x) | TyKind::Array(x, _) => stack.push(*x),
            TyKind::Tuple(v) => stack.extend(v.iter().copied()),
            _ => {}
        }
    }
    out
}
