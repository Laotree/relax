//! Type-checked bodies of generic functions, instantiated by substitution.
//!
//! Relax type-checks every function instance (rustc checks a generic body once). Most generic
//! instances of a startup are tiny core bodies (`size_of::<T>`, `Box::new`, `Vec::push`, ...)
//! checked again for every T. When a generic fn's body checks without errors over its own
//! params, and none of its decisions looked at what a param is (no method, operator, index,
//! deref, call or cast whose subject is a param or a projection on one, no closures, no opaque
//! types, no constant requests), the instance body is that polymorphic body with the instance's
//! args substituted and projections normalized -- the same result the instance check gives.
//! The template is built at the second instance of a definition (a fn instantiated once gains
//! nothing) and kept per collect epoch. RELAX_TEMPLATES=0 turns it off.

use crate::ast::{ExprId, ExprKind};
use crate::program::{DefId, DefKind, Program};
use crate::tcx::Tcx;
use crate::typeck::{Body, Coerce, Local, MethodRes};
use crate::types::{TyId, TyKind};
use std::sync::Arc;

pub fn enabled(options: &crate::options::Options) -> bool {
    options.templates
}

/// The instance body of `def` with `args` from the definition's template, when there is one
/// (None: check the instance itself).
pub fn instance(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, def: DefId, args: &[TyId]) -> Option<Body> {
    let options = &prog.session.clone().options;
    let _mem = crate::memstat::tag(crate::memstat::Tag::Template);
    if args.is_empty() || !enabled(options) || args.iter().any(|a| !tcx.tys.is_concrete(*a)) {
        return None;
    }
    if !matches!(prog.def(def).kind, DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    let epoch = tcx.collect_epoch.load(std::sync::atomic::Ordering::SeqCst);
    let key = (def, epoch);
    let t = match tcx.templates.get(&key) {
        Some(t) => t,
        None => {
            // the first instance is checked as before; the second builds the template
            if !tcx.template_seen.contains(&key) {
                tcx.template_seen.insert(key, ());
                return None;
            }
            let t = build(cx, prog, tcx, def, args.len()).map(Arc::new);
            tcx.templates.insert(key, t.clone());
            t
        }
    }?;
    instantiate(cx, prog, tcx, &t, args)
}

fn build(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, def: DefId, n: usize) -> Option<Body> {
    let params: Vec<TyId> = (0..n as u32).map(|i| tcx.tys.intern(TyKind::Param(i))).collect();
    // a polymorphic check that asks for a constant is no template (its requests stay queued:
    // the queue is shared with other threads' checks, and evaluating the constant is harmless)
    let asked = cx.state.const_asked.get();
    let wait = cx.state.const_wait.get();
    let b = crate::typeck::check_fn_uncached(cx, prog, tcx, def, &params);
    cx.state.const_wait.set(wait);
    if tcx.has_blocked_consts() || cx.state.const_asked.get() != asked || !b.errors.is_empty() || !eligible(prog, tcx, &b) {
        return None;
    }
    Some(b)
}

/// A param (or a projection / opaque type over one) at the top of `t`, under references and
/// raw pointers: the subject of a decision the instance check makes by what the param is.
fn param_like(tcx: &Tcx, t: TyId) -> bool {
    let mut t = t;
    loop {
        match tcx.tys.kind(t) {
            TyKind::Ref(_, x, _) | TyKind::Ptr(_, x) => t = *x,
            TyKind::Param(_) | TyKind::Assoc(..) | TyKind::Opaque(..) | TyKind::Infer(_) | TyKind::Error => return true,
            _ => return false,
        }
    }
}

fn eligible(prog: &Program, tcx: &Tcx, b: &Body) -> bool {
    match why_not(prog, tcx, b) {
        None => true,
        Some(r) => {
            if why_on() {
                eprintln!("TEMPLATE-NO\t{}\t{}", r, prog.def_path(b.def));
            }
            false
        }
    }
}

fn why_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("RELAX_TEMPLATE_WHY").is_ok())
}

/// `p as *const U` / `p as usize` from a pointer: pointer casts typeck takes as they come
/// (lowering decides thin / fat from the instance's types); not when a pointee is a projection
/// or opaque type, or when the source is no pointer.
fn ptr_cast(tcx: &Tcx, from: TyId, to: TyId) -> bool {
    let pointee = |t: TyId| match tcx.tys.kind(t) {
        TyKind::Ptr(_, x) | TyKind::Ref(_, x, _) => Some(*x),
        _ => None,
    };
    let plain = |t: TyId| !matches!(tcx.tys.kind(t), TyKind::Assoc(..) | TyKind::Opaque(..) | TyKind::Infer(_) | TyKind::Error);
    match (pointee(from), tcx.tys.kind(to)) {
        (Some(a), TyKind::Ptr(_, b)) => plain(a) && plain(*b),
        (Some(a), TyKind::Int(_)) => plain(a),
        _ => false,
    }
}

fn why_not(prog: &Program, tcx: &Tcx, b: &Body) -> Option<&'static str> {
    if !b.closures.is_empty() || !b.closure_locals.is_empty() || !b.capture_by_value.is_empty() {
        return Some("closures");
    }
    let ast = &prog.files[b.file as usize].ast;
    for (i, &t) in b.expr_ty.iter().enumerate() {
        if tcx.tys.has_opaque(t) || tcx.tys.has_error(t) {
            return Some("opaque/error expr");
        }
        let e = b.expr_at(i);
        let subject: &[ExprId] = match &ast.expr(e).kind {
            ExprKind::MethodCall { recv, .. } => std::slice::from_ref(recv),
            ExprKind::Cast(x, _) if ptr_cast(tcx, b.ty(*x), t) => &[],
            ExprKind::Unary(_, x) | ExprKind::Cast(x, _) | ExprKind::Field(x, _) | ExprKind::TupleField(x, _) | ExprKind::Try(x) | ExprKind::Await(x) | ExprKind::Call(x, _) => std::slice::from_ref(x),
            ExprKind::Binary(_, l, r) | ExprKind::AssignOp(_, l, r) | ExprKind::Index(l, r) => {
                if param_like(tcx, b.ty(*l)) || param_like(tcx, b.ty(*r)) {
                    return Some("binary/index operand");
                }
                &[]
            }
            ExprKind::For(_, it, _, _) => std::slice::from_ref(it),
            ExprKind::Closure { .. } | ExprKind::Async(..) | ExprKind::Yield(_) => return Some("closure/async/yield"),
            _ => &[],
        };
        for s in subject {
            if param_like(tcx, b.ty(*s)) {
                return Some("subject");
            }
        }
        // a cast's target type too (`x as T` is no cast the template can decide)
        if let ExprKind::Cast(x, _) = &ast.expr(e).kind {
            if param_like(tcx, t) && !ptr_cast(tcx, b.ty(*x), t) {
                return Some("cast target");
            }
        }
    }
    if b.pat_ty.iter().any(|t| tcx.tys.has_opaque(*t) || tcx.tys.has_error(*t)) || tcx.tys.has_opaque(b.ret) {
        return Some("opaque pat/ret");
    }
    // trait methods / operators / derefs / indexing / iteration / `?` conversions resolved on a
    // param-like Self
    let trait_self_param = |d: DefId, args: &[TyId]| prog.def(prog.def(d).parent).kind == DefKind::Trait && args.first().map_or(true, |s| param_like(tcx, *s));
    if b.methods.values().chain(b.binops.values()).any(|m| trait_self_param(m.def, &m.args)) {
        return Some("trait method on param");
    }
    if b.ov_derefs.values().chain(b.ov_index.values()).chain(b.for_next.values()).any(|(d, a)| trait_self_param(*d, a)) {
        return Some("deref/index/next on param");
    }
    if b.for_into.values().any(|(d, a, _)| trait_self_param(*d, a)) {
        return Some("into_iter on param");
    }
    if b.try_conv.values().any(|c| c.as_ref().map_or(false, |(_, a)| a.iter().any(|t| tcx.has_param(*t)))) {
        return Some("try conv");
    }
    None
}

fn instantiate(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, t: &Body, args: &[TyId]) -> Option<Body> {
    let mut bad = false;
    let mut s = |x: TyId| -> TyId {
        if !tcx.has_param(x) {
            return x;
        }
        let y = tcx.tys.subst(x, args);
        let y = tcx.normalize(cx, prog, y);
        if tcx.tys.has_error(y) || tcx.tys.has_stuck_assoc(y) || tcx.tys.has_opaque(y) {
            bad = true;
        }
        y
    };
    let sv = |v: &[TyId], s: &mut dyn FnMut(TyId) -> TyId| -> Vec<TyId> { v.iter().map(|x| s(*x)).collect() };
    let mut b = Body {
        def: t.def,
        args: args.to_vec(),
        file: t.file,
        expr_lo: t.expr_lo,
        expr_ty: Vec::new(),
        pat_lo: t.pat_lo,
        pat_ty: Vec::new(),
        expr_lo2: t.expr_lo2,
        expr_n1: t.expr_n1,
        pat_lo2: t.pat_lo2,
        pat_n1: t.pat_n1,
        res: t.res.clone(),
        res_args: Default::default(),
        pat_res: t.pat_res.clone(),
        pat_local: t.pat_local.clone(),
        methods: Default::default(),
        binops: Default::default(),
        coerce: Default::default(),
        reborrows: t.reborrows.clone(),
        // Templates exclude closure bodies (why_not).
        min_captures: Default::default(),
        field_idx: t.field_idx.clone(),
        field_uses: t.field_uses.clone(),
        dependencies: t.dependencies.clone(),
        ov_derefs: Default::default(),
        ov_index: Default::default(),
        for_next: Default::default(),
        for_into: Default::default(),
        index_derefs: t.index_derefs.clone(),
        legacy_args: t.legacy_args.clone(),
        call_derefs: t.call_derefs.clone(),
        call_traits: t.call_traits.clone(),
        try_conv: Default::default(),
        pat_derefs: t.pat_derefs.clone(),
        pat_bind_ref: t.pat_bind_ref.clone(),
        pat_discriminant_reads: t.pat_discriminant_reads.clone(),
        locals: Vec::new(),
        param_pats: t.param_pats.clone(),
        ret: TyId(0),
        body: t.body,
        fmt_named: t.fmt_named.clone(),
        closures: t.closures.clone(),
        closure_locals: t.closure_locals.clone(),
        closure_expected_kinds: t.closure_expected_kinds.clone(),
        closure_sigs: t.closure_sigs.iter().map(|(e, sig)| (*e, crate::typeck::ClosureSignatures {
            bound: s(sig.bound), liberated: s(sig.liberated),
            annotation_eq: sig.annotation_eq.map(|(a, b)| (s(a), s(b))),
        })).collect(),
        inline_const_types: t.inline_const_types.iter().map(|(e, t)| (*e, s(*t))).collect(),
        capture_by_value: t.capture_by_value.clone(),
        capture_fields: t.capture_fields.clone(),
        struct_defaults: t.struct_defaults.clone(),
        errors: Vec::new(),
        param_env: None,
    };
    b.expr_ty = sv(&t.expr_ty, &mut s);
    b.pat_ty = sv(&t.pat_ty, &mut s);
    b.ret = s(t.ret);
    for (k, v) in &t.res_args {
        b.res_args.insert(*k, sv(v, &mut s));
    }
    let mr = |m: &MethodRes, s: &mut dyn FnMut(TyId) -> TyId| MethodRes { def: m.def, derefs: m.derefs, autoref: m.autoref, args: m.args.iter().map(|x| s(*x)).collect() };
    for (k, m) in &t.methods {
        b.methods.insert(*k, mr(m, &mut s));
    }
    for (k, m) in &t.binops {
        b.binops.insert(*k, mr(m, &mut s));
    }
    for (k, c) in &t.coerce {
        let c = match *c {
            Coerce::ToDyn(a, d) => Coerce::ToDyn(s(a), s(d)),
            Coerce::Upcast(a, d) => Coerce::Upcast(s(a), s(d)),
            c => c,
        };
        b.coerce.insert(*k, c);
    }
    for (k, (d, a)) in &t.ov_derefs {
        b.ov_derefs.insert(*k, (*d, sv(a, &mut s)));
    }
    for (k, (d, a)) in &t.ov_index {
        b.ov_index.insert(*k, (*d, sv(a, &mut s)));
    }
    for (k, (d, a)) in &t.for_next {
        b.for_next.insert(*k, (*d, sv(a, &mut s)));
    }
    for (k, (d, a, it)) in &t.for_into {
        let a = sv(a, &mut s);
        let it = s(*it);
        b.for_into.insert(*k, (*d, a, it));
    }
    for (k, c) in &t.try_conv {
        b.try_conv.insert(*k, c.as_ref().map(|(d, a)| (*d, sv(a, &mut s))));
    }
    for l in &t.locals {
        let ty = s(l.ty);
        b.locals.push(Local { name: l.name, ty, mutable: l.mutable, pat: l.pat });
    }
    if bad {
        return None;
    }
    Some(b)
}
