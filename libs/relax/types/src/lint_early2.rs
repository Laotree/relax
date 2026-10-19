//! Lints of rustc_lint / rustc_resolve that need more than the syntax of one node: they use the
//! lifetime resolution (`mismatched_lifetime_syntaxes`, `elided_lifetimes_in_paths`), the
//! macro definitions, or the source text between tokens. Check-only.

use crate::ast::*;
use crate::lint::{self, Level, Lint};
use crate::lint_early::W;
use crate::program::{DefId, DefKind, Program};
use crate::tcx::lifetime_resolve::{LifetimeRes, LifetimeResolution};
use crate::tcx::Tcx;
use std::sync::Arc;

pub const MISMATCHED_LIFETIME_SYNTAXES: Lint = lint::lint("mismatched_lifetime_syntaxes", Level::Warn, &[]);
pub const ELIDED_LIFETIMES_IN_PATHS: Lint = lint::lint("elided_lifetimes_in_paths", Level::Allow, &["rust_2018_idioms"]);

/// The lifetime resolution of a definition's signature and body.
pub(crate) fn names(prog: &Program, tcx: &Tcx, d: DefId) -> Arc<LifetimeResolution> { tcx.resolve_lifetime_names(prog, d) }

// ---------------------------------------------------------------- mismatched_lifetime_syntaxes

#[derive(Clone, Copy, PartialEq, Eq)]
enum Syntax { Implicit, Anonymous, Bound }

#[derive(Clone, Copy, PartialEq, Eq)]
enum Source { Reference, Path, Outlives, Precise }

#[derive(Clone, Copy, PartialEq, Eq)]
enum Cat { Hidden, Elided, Named }

#[derive(Clone, Copy)]
struct Info { res: LifetimeRes, cat: Cat, pos: u32 }

struct Collector<'a, 'b> {
    w: &'a W<'b>,
    names: &'a LifetimeResolution,
    out: Vec<Info>,
    /// argument position: `impl Trait` is an anonymous type parameter there, its bounds are not
    /// part of the type
    input: bool,
}

impl Collector<'_, '_> {
    fn push(&mut self, res: Option<LifetimeRes>, syntax: Syntax, source: Source, pos: u32) {
        let Some(res) = res else { return };
        // lifetimes that failed to resolve are reported elsewhere
        if matches!(res, LifetimeRes::Error | LifetimeRes::Infer) { return; }
        let cat = match (syntax, source) {
            (Syntax::Implicit, Source::Reference) | (Syntax::Anonymous, _) => Cat::Elided,
            (Syntax::Implicit, Source::Path) => Cat::Hidden,
            (Syntax::Bound, _) => Cat::Named,
            // `+ '_` is elided, `+ 'a` named; an implicit one cannot be written there
            (Syntax::Implicit, _) => return,
        };
        self.out.push(Info { res, cat, pos });
    }

    fn written(&mut self, lt: Ident, source: Source) {
        let syntax = if self.w.pf.text(lt) == "'_" { Syntax::Anonymous } else { Syntax::Bound };
        let res = self.names.named(lt.lo, lt.hi);
        self.push(res, syntax, source, lt.lo);
    }

    fn ty(&mut self, t: TyId) {
        let ast = self.w.ast;
        match *ast.ty(t) {
            Ty::Ref(lt, _, inner) => {
                match lt {
                    Some(l) => self.written(l, Source::Reference),
                    None => {
                        let pos = self.w.ty_start(t).unwrap_or(self.w.cur);
                        self.push(self.names.reference(t.0), Syntax::Implicit, Source::Reference, pos);
                    }
                }
                self.ty(inner);
            }
            Ty::Ptr(_, x) | Ty::Slice(x) | Ty::Array(x, _) | Ty::Paren(x) => self.ty(x),
            Ty::Tuple(l) => for &x in ast.list(l) { self.ty(x); },
            Ty::Fn(f) => {
                let f = *ast.fn_ptr(f);
                for &x in ast.list(f.params) { self.ty(x); }
                if let Some(r) = f.ret { self.ty(r); }
            }
            Ty::Path(p) => self.path(&p, t),
            Ty::ImplTrait(b) => if !self.input { self.bounds(b, t) },
            Ty::DynTrait(b, _) => self.bounds(b, t),
            Ty::Never | Ty::Infer | Ty::Mac(_) | Ty::ImplicitSelf | Ty::CVarArgs => {}
        }
    }

    fn bounds(&mut self, l: List<Bound>, owner: TyId) {
        let ast = self.w.ast;
        // the trait bounds first, the lifetime bound after them (intravisit TraitObject)
        for b in ast.list(l) {
            if let Bound::Trait { path, .. } = *b { self.path(&path, owner); }
        }
        for b in ast.list(l) {
            match *b {
                Bound::Lifetime(lt) => self.written(lt, Source::Outlives),
                Bound::Use(args) => {
                    if let Some(GenericArgs::Angle(l)) = ast.gargs(args) {
                        for a in ast.list(*l) { if let GenericArg::Lifetime(lt) = *a { self.written(lt, Source::Precise); } }
                    }
                }
                Bound::Trait { .. } => {}
            }
        }
    }

    fn path(&mut self, p: &Path, owner: TyId) {
        let ast = self.w.ast;
        if p.has_qself() {
            if let Some(q) = ast.qself(p) {
                self.ty(q.ty);
                if let Some(tp) = q.trait_path { self.path(&tp, owner); }
            }
        }
        for (i, seg) in ast.segs(p.segs).iter().enumerate() {
            // the hidden lifetimes come first in the lowered arguments
            let mut k = 0;
            while let Some(res) = self.names.path(p.segs.lo + i as u32, k) {
                let pos = self.w.ty_start(owner).unwrap_or(seg.name.lo);
                self.push(Some(res), Syntax::Implicit, Source::Path, pos);
                k += 1;
            }
            match ast.gargs(seg.args()) {
                Some(GenericArgs::Angle(l)) => {
                    for a in ast.list(*l) { if let GenericArg::Lifetime(lt) = *a { self.written(lt, Source::Path); } }
                    for a in ast.list(*l) { if let GenericArg::Type(t) = *a { self.ty(t); } }
                    for a in ast.list(*l) {
                        match *a {
                            GenericArg::Binding(_, _, t) => self.ty(t),
                            GenericArg::Constraint(_, b) => self.bounds(b, owner),
                            _ => {}
                        }
                    }
                }
                Some(GenericArgs::Paren(tys, ret)) => {
                    for &t in ast.list(*tys) { self.ty(t); }
                    if let Some(r) = ret { self.ty(*r); }
                }
                None => {}
            }
        }
    }
}

/// The position of the first token of a fn's parameter list (a `&self` receiver is the first
/// parameter).
fn params_start(w: &W, item: &Item) -> u32 {
    let pf = w.pf;
    let mut at = item.name.hi;
    let mut depth = 0i32;
    let n = pf.src_len;
    // generics: skip to the matching `>`
    loop {
        let b = pf.bytes(at.min(n), (at + 1).min(n));
        if b.is_empty() { return item.lo; }
        match b[0] {
            b'<' => depth += 1,
            b'>' => { depth -= 1; if depth <= 0 { at += 1; break; } }
            b'-' if pf.bytes(at + 1, (at + 2).min(n)) == b">" => at += 1,
            b'(' if depth == 0 => break,
            _ => {}
        }
        at += 1;
    }
    loop {
        let b = pf.bytes(at.min(n), (at + 1).min(n));
        if b.is_empty() { return item.lo; }
        if b[0] == b'(' { at += 1; break; }
        at += 1;
    }
    while let [c, ..] = pf.bytes(at.min(n), (at + 1).min(n)) {
        if matches!(c, b' ' | b'\t' | b'\n' | b'\r') { at += 1; } else { break; }
    }
    at
}

/// rustc_lint `LifetimeSyntax::check_fn_like`.
fn mismatched_lifetime_syntaxes(prog: &Program, tcx: &Tcx, d: DefId) {
    let def = prog.def(d);
    let pf = &prog.files[def.file as usize];
    let ast = &pf.ast;
    let item = *ast.item(def.item);
    let ItemKind::Fn(sig, _, _) = item.kind else { return };
    let sig = *ast.fn_sig(sig);
    // no output, or no input: nothing can disagree
    let Some(ret) = sig.ret else { return };
    if sig.self_param.is_none_or(|s| matches!(s, SelfParam::Value(_))) && ast.list(sig.params).is_empty() { return; }
    let names = names(prog, tcx, d);
    let mut w = W::new(prog, def.file, d);
    w.cur = item.lo;
    let mut outputs = Collector { w: &w, names: &names, out: Vec::new(), input: false };
    outputs.ty(ret);
    let outputs = outputs.out;
    if outputs.is_empty() { return; }
    let mut inputs = Collector { w: &w, names: &names, out: Vec::new(), input: true };
    match sig.self_param {
        Some(SelfParam::Ref(lt, _)) => match lt {
            Some(l) => inputs.written(l, Source::Reference),
            None => {
                let pos = params_start(&w, &item);
                inputs.push(names.self_reference(), Syntax::Implicit, Source::Reference, pos);
            }
        },
        Some(SelfParam::Typed(_, t)) => inputs.ty(t),
        _ => {}
    }
    for p in ast.list(sig.params) { inputs.ty(p.ty); }
    let inputs = inputs.out;
    // the groups, in the order of the output's lifetimes
    let mut keys: Vec<LifetimeRes> = Vec::new();
    for o in &outputs { if !keys.contains(&o.res) { keys.push(o.res); } }
    for key in keys {
        let ins: Vec<&Info> = inputs.iter().filter(|i| i.res == key).collect();
        let outs: Vec<&Info> = outputs.iter().filter(|i| i.res == key).collect();
        let Some(first) = ins.first() else { continue };
        if ins.iter().chain(outs.iter()).all(|i| i.cat == first.cat) { continue; }
        let count = |c: Cat| ins.iter().chain(outs.iter()).filter(|i| i.cat == c).count();
        let (hidden, elided, named) = (count(Cat::Hidden), count(Cat::Elided), count(Cat::Named));
        let msg = if named == 0 { "hiding a lifetime that's elided elsewhere is confusing" }
            else if elided == 0 { "hiding a lifetime that's named elsewhere is confusing" }
            else if hidden == 0 { "eliding a lifetime that's named elsewhere is confusing" }
            else { "hiding or eliding a lifetime that's named elsewhere is confusing" };
        // the primary spans: the hidden then the elided ones of the inputs, then of the outputs
        let pos = [&ins, &outs].iter().find_map(|side| {
            [Cat::Hidden, Cat::Elided].iter().find_map(|c| side.iter().find(|i| i.cat == *c).map(|i| i.pos))
        }).unwrap_or(item.lo);
        if lint::external(prog, def.file, pos) { continue; }
        lint::emit(prog, d, &MISMATCHED_LIFETIME_SYNTAXES, def.file, pos, msg);
    }
}

// ---------------------------------------------------------------- entry points

/// The definition-level passes of this file over one definition.
pub fn check_def_item(prog: &Program, tcx: &Tcx, d: DefId) {
    if matches!(prog.def(d).kind, DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn) {
        mismatched_lifetime_syntaxes(prog, tcx, d);
    }
}
