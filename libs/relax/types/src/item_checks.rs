//! Item-level checks of `makepad check` that need no body: duplicate definitions (E0428,
//! rustc_resolve build_reduced_graph / report_conflict) and recursive types without
//! indirection (E0072, rustc_ty_utils representability.rs).

use crate::program::{DefId, DefKind, Program, NO_DEF};
use crate::tcx::Tcx;
use crate::types::{TyId, TyKind};

/// The namespaces a definition takes in its module: (type, value).
fn namespaces(prog: &Program, d: DefId) -> (bool, bool) {
    let def = prog.def(d);
    match def.kind {
        DefKind::Mod | DefKind::Enum | DefKind::Union | DefKind::Trait | DefKind::TypeAlias => (true, false),
        // (foreign items are left out: an `extern` block inside a fn body is collected into the
        // enclosing module, not the body's block, so two bodies' declarations would collide)
        DefKind::Fn | DefKind::Const | DefKind::Static => (false, true),
        DefKind::Struct => {
            // tuple and unit structs also live in the value namespace
            let ast = &prog.files[def.file as usize].ast;
            let tuple_or_unit = ast.as_struct(&ast.item(def.item).kind).is_some_and(|s| !matches!(s.data, crate::ast::VariantData::Struct(_)));
            (true, tuple_or_unit)
        }
        _ => (false, false),
    }
}

/// E0428: two items of one module (or block) with the same name in the same namespace. The
/// second is reported, as rustc does ("the name `X` is defined multiple times").
pub fn duplicate_items(prog: &Program, own: &[bool]) -> Vec<String> {
    let mut seen: crate::fxhash::HashMap<(DefId, bool, u32), DefId> = Default::default();
    let mut errors = Vec::new();
    for i in 0..prog.defs.len() {
        let d = DefId(i as u32);
        let def = prog.def(d);
        if !own.get(def.krate as usize).copied().unwrap_or(false) || def.parent == NO_DEF { continue; }
        if prog.def(def.parent).kind != DefKind::Mod { continue; }
        // only items the module's source declares (not the compiler's own definitions)
        if prog.item_defs.get(&(def.file, def.item.0)) != Some(&d) { continue; }
        let name = prog.syms.str(def.name);
        if name == "_" || name.is_empty() { continue; }
        // a module file configured away by its own inner `#![cfg]` defines nothing
        if def.kind == DefKind::Mod {
            let m = &prog.mods[def.sub as usize];
            let attrs: Vec<crate::ast::Attr> = prog.files[m.file as usize].ast.root_attrs.iter().copied().collect();
            if m.file != def.file && !prog.active(m.file, &attrs) { continue; }
        }
        let (ty_ns, value_ns) = namespaces(prog, d);
        for (ns, on) in [(true, ty_ns), (false, value_ns)] {
            if !on { continue; }
            match seen.get(&(def.parent, ns, def.name)) {
                Some(&first) if first != d => {
                    let ast = &prog.files[def.file as usize].ast;
                    let pos = ast.item(def.item).name.lo;
                    let ns_name = if ns { "type" } else { "value" };
                    let module = if prog.block_owner.get(&prog.def(def.parent).sub).is_some() { "this block" } else { "this module" };
                    errors.push(prog.record_error(def.file, pos, "resolve", format!(
                        "E0428: the name `{}` is defined multiple times -- note: `{}` must be defined only once in the {} namespace of {}",
                        name, name, ns_name, module)));
                    break;
                }
                Some(_) => {}
                None => { seen.insert((def.parent, ns, def.name), d); }
            }
        }
    }
    errors
}

/// A query of rustc_ty_utils/src/representability.rs, the nodes of its cycle detection.
#[derive(Clone, PartialEq, Eq, Hash)]
enum ReprKey {
    /// `check_representability(adt)`
    Adt(DefId),
    /// `check_representability(field)`: the ADT, variant and field index
    Field(DefId, usize, usize),
    /// `check_representability_adt_ty(ty)`
    AdtTy(TyId),
}

struct Representability<'a> {
    tcx: &'a Tcx,
    /// the queries being computed, innermost last
    active: Vec<ReprKey>,
    done: crate::fxhash::HashSet<ReprKey>,
    /// the first cycle met: its queries, outermost first
    cycle: Option<Vec<ReprKey>>,
}

impl Representability<'_> {
    fn enter(&mut self, key: &ReprKey) -> bool {
        if self.cycle.is_some() || self.done.contains(key) { return false; }
        if let Some(at) = self.active.iter().position(|k| k == key) {
            self.cycle = Some(self.active[at..].to_vec());
            return false;
        }
        self.active.push(key.clone());
        true
    }

    fn leave(&mut self, key: ReprKey) {
        self.active.pop();
        if self.cycle.is_none() { self.done.insert(key); }
    }

    fn check_adt(&mut self, d: DefId) {
        let key = ReprKey::Adt(d);
        if !self.enter(&key) { return; }
        if let Some(adt) = self.tcx.adts.get(&d) {
            for (vi, v) in adt.variants.iter().enumerate() {
                for fi in 0..v.fields.len() { self.check_field(d, vi, fi); }
            }
        }
        self.leave(key);
    }

    fn check_field(&mut self, d: DefId, vi: usize, fi: usize) {
        let key = ReprKey::Field(d, vi, fi);
        if !self.enter(&key) { return; }
        let ty = self.tcx.adts[&d].variants[vi].fields[fi].ty;
        self.check_ty(ty);
        self.leave(key);
    }

    fn check_ty(&mut self, t: TyId) {
        match self.tcx.tys.kind(t).clone() {
            TyKind::Adt(..) => self.check_adt_ty(t),
            TyKind::Array(e, _) => self.check_ty(e),
            TyKind::Tuple(ts) => for x in self.tcx.tys.list(ts).to_vec() { self.check_ty(x); },
            _ => {}
        }
    }

    fn check_adt_ty(&mut self, t: TyId) {
        let key = ReprKey::AdtTy(t);
        if !self.enter(&key) { return; }
        let TyKind::Adt(d, args, _) = self.tcx.tys.kind(t).clone() else { unreachable!() };
        // the item itself is representable; its parameters may still cycle through a type argument
        self.check_adt(d);
        if self.cycle.is_none() {
            let used = self.params_in_repr(d, &mut Vec::new());
            for (i, a) in self.tcx.tys.list(args).to_vec().into_iter().enumerate() {
                if used.contains(&(i as u32)) { self.check_ty(a); }
            }
        }
        self.leave(key);
    }

    /// `params_in_repr`: the type parameters (by compact index) an ADT's fields hold by value.
    fn params_in_repr(&self, d: DefId, visiting: &mut Vec<DefId>) -> crate::fxhash::HashSet<u32> {
        let mut out = crate::fxhash::HashSet::default();
        if visiting.contains(&d) { return out; }
        visiting.push(d);
        if let Some(adt) = self.tcx.adts.get(&d) {
            for v in &adt.variants {
                for f in &v.fields { self.params_in_repr_ty(f.ty, &mut out, visiting); }
            }
        }
        visiting.pop();
        out
    }

    fn params_in_repr_ty(&self, t: TyId, out: &mut crate::fxhash::HashSet<u32>, visiting: &mut Vec<DefId>) {
        match self.tcx.tys.kind(t).clone() {
            TyKind::Adt(d, args, _) => {
                let inner = self.params_in_repr(d, visiting);
                for (i, a) in self.tcx.tys.list(args).to_vec().into_iter().enumerate() {
                    if inner.contains(&(i as u32)) { self.params_in_repr_ty(a, out, visiting); }
                }
            }
            TyKind::Array(e, _) => self.params_in_repr_ty(e, out, visiting),
            TyKind::Tuple(ts) => for x in self.tcx.tys.list(ts).to_vec() { self.params_in_repr_ty(x, out, visiting); },
            TyKind::Param(i) => { out.insert(i); }
            _ => {}
        }
    }
}

/// E0072: an ADT that contains itself by value (through fields, tuples, arrays and the
/// parameters other ADTs hold by value) has no finite size (rustc_ty_utils
/// representability.rs: a cycle among its queries; rustc_middle values.rs reports the ADTs of
/// the cycle once, at the first). The cycle is reported by the first of its ADTs.
pub fn representability(prog: &Program, tcx: &Tcx, d: DefId) -> Option<String> {
    let mut r = Representability { tcx, active: Vec::new(), done: Default::default(), cycle: None };
    r.check_adt(d);
    let cycle = r.cycle?;
    let mut items: Vec<DefId> = Vec::new();
    for k in &cycle {
        if let ReprKey::Field(a, _, _) = k { if !items.contains(a) { items.push(*a); } }
    }
    // reported once: by the first ADT of the cycle
    if items.first().is_none() || items.iter().min_by_key(|x| x.0) != Some(&d) || !items.contains(&d) { return None; }
    let at = items.iter().position(|x| *x == d).unwrap();
    items.rotate_left(at);
    let names: Vec<String> = items.iter().map(|x| format!("`{}`", prog.syms.str(prog.def(*x).name))).collect();
    let list = match names.len() {
        1 => names[0].clone(),
        2 => format!("{} and {}", names[0], names[1]),
        _ => format!("{} and {}", names[..names.len() - 1].join(", "), names[names.len() - 1]),
    };
    let def = prog.def(d);
    let ast = &prog.files[def.file as usize].ast;
    let pos = ast.item(def.item).name.lo;
    Some(prog.record_error(def.file, pos, "typeck", format!(
        "E0072: recursive type{} {} {} infinite size -- help: insert some indirection (e.g., a `Box`, `Rc`, or `&`) to break the cycle",
        if items.len() == 1 { "" } else { "s" }, list, if items.len() == 1 { "has" } else { "have" })))
}

/// rustc_hir_analysis wfcheck.rs check_impl: a trait impl's trait reference is well formed --
/// the trait's own where-clauses and supertraits hold for it, in the impl's environment
/// (`trait Foo: Send {}` + `impl Foo for Rc<i8> {}`: E0277 "`Rc<i8>` cannot be sent between
/// threads safely"). Ambiguous goals are left to the rest of the check.
pub fn impl_trait_wf(prog: &Program, tcx: &Tcx, imp: DefId) -> Vec<String> {
    use crate::consts::GenericArg;
    use crate::next_solver::{ClauseKind, Goal, PredicateKind};
    let Some(&td) = tcx.impl_trait.get(&imp) else { return Vec::new() };
    let def = prog.def(imp);
    let ast = &prog.files[def.file as usize].ast;
    if ast.as_impl(&ast.item(def.item).kind).is_some_and(|i| i.negative) { return Vec::new(); }
    let indices = tcx.generic_indices_of(prog, imp);
    let trait_ref = tcx.impl_trait_ref(prog, imp, &indices.identity_args(&tcx.tys));
    if trait_ref.args.iter().any(|a| matches!(*a, GenericArg::Type(t) if tcx.tys.has_error(t))) { return Vec::new(); }
    let env = tcx.param_env_id(prog, imp);
    let infcx = crate::infer::InferCtxt::for_item(tcx, prog, crate::tcx::TypingMode::non_body_analysis(), imp);
    let mut errors = Vec::new();
    for p in tcx.clauses_of(prog, td) {
        let p = tcx.instantiate_predicate(prog, td, &trait_ref.args, &p);
        let PredicateKind::Clause(ClauseKind::Trait(t)) = &p.kind else { continue };
        // the trait's own `Self: Trait` predicate holds through this impl
        if t.trait_ref.def_id == td { continue; }
        let tr = t.trait_ref.clone();
        let r = infcx.evaluate_obligation(prog, Goal { param_env: env, predicate: p.clone() });
        if r.may_apply() { continue; }
        let args: Vec<String> = tr.args.iter().map(|a| match a {
            GenericArg::Type(t) => crate::typeck::ty_to_string(false, prog, tcx, *t),
            GenericArg::Const(c) => tcx.tys.const_to_string(*c),
            GenericArg::Lifetime(_) => "'_".to_string(),
        }).collect();
        let name = prog.name(tr.def_id).to_string();
        let self_ty = args.first().cloned().unwrap_or_default();
        let msg = match name.as_str() {
            "Sized" => format!("the size for values of type `{}` cannot be known at compilation time", self_ty),
            "Send" => format!("`{}` cannot be sent between threads safely", self_ty),
            "Sync" => format!("`{}` cannot be shared between threads safely", self_ty),
            _ if args.len() > 1 => format!("the trait bound `{}: {}<{}>` is not satisfied", self_ty, name, args[1..].join(", ")),
            _ => format!("the trait bound `{}: {}` is not satisfied", self_ty, name),
        };
        errors.push(prog.record_error(def.file, ast.item(def.item).lo, "typeck", format!("E0277: {}", msg)));
    }
    errors
}

/// rustc_hir_analysis coherence/builtin.rs `visit_implementation_of_copy`: `impl Copy for T`
/// needs an ADT (E0206) whose every field is `Copy` (E0204) and that has no destructor (E0184).
pub fn copy_impl(prog: &Program, tcx: &Tcx, imp: DefId) -> Vec<String> {
    use crate::consts::GenericArg;
    use crate::next_solver::Goal;
    let Some(&td) = tcx.impl_trait.get(&imp) else { return Vec::new() };
    if tcx.copy_trait != Some(td) { return Vec::new(); }
    let def = prog.def(imp);
    let ast = &prog.files[def.file as usize].ast;
    let Some(item) = ast.as_impl(&ast.item(def.item).kind) else { return Vec::new() };
    if item.negative { return Vec::new(); }
    let indices = tcx.generic_indices_of(prog, imp);
    let trait_ref = tcx.impl_trait_ref(prog, imp, &indices.identity_args(&tcx.tys));
    let Some(GenericArg::Type(self_ty)) = trait_ref.args.first().copied() else { return Vec::new() };
    if tcx.tys.has_error(self_ty) { return Vec::new(); }
    let pos = ast.item(def.item).lo;
    let report = |code: &str, msg: &str| prog.record_error(def.file, pos, "typeck", format!("{}: {}", code, msg));
    let (adt, args) = match tcx.tys.kind(self_ty).clone() {
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Ptr(..) | TyKind::Never | TyKind::Ref(false, _, _) | TyKind::Array(..) => return Vec::new(),
        TyKind::Adt(d, args, _) => (d, tcx.tys.list(args).to_vec()),
        _ => return vec![report("E0206", "the trait `Copy` cannot be implemented for this type; type is not a structure or enumeration")],
    };
    let Some(def_adt) = tcx.adts.get(&adt) else { return Vec::new() };
    let env = tcx.param_env_id(prog, imp);
    let infcx = crate::infer::InferCtxt::for_item(tcx, prog, crate::tcx::TypingMode::non_body_analysis(), imp);
    for v in &def_adt.variants {
        for f in &v.fields {
            let ft = tcx.tys.subst(f.ty, &args);
            if tcx.tys.has_error(ft) { continue; }
            let predicate = crate::next_solver::collect::trait_predicate(td, vec![GenericArg::Type(ft)]);
            if !infcx.evaluate_obligation(prog, Goal { param_env: env, predicate }).may_apply() {
                return vec![report("E0204", "the trait `Copy` cannot be implemented for this type")];
            }
        }
    }
    if tcx.adt_destructor(adt).is_some() {
        return vec![report("E0184", "the trait `Copy` cannot be implemented for this type; the type has a destructor")];
    }
    Vec::new()
}

/// rustc_resolve late resolution of generic parameter ribs: a type or const parameter named
/// like an earlier one of the same list, or like one of the enclosing trait or impl, is E0403.
/// (Lifetime parameters are checked by the lifetime resolution.)
pub fn duplicate_generic_params(prog: &Program, d: DefId) -> Vec<String> {
    use crate::ast::GenericParamKind;
    let def = prog.def(d);
    let ast = &prog.files[def.file as usize].ast;
    let Some(g) = ast.kind_generics(&ast.item(def.item).kind) else { return Vec::new() };
    let f = &prog.files[def.file as usize];
    let mut outer: Vec<&str> = Vec::new();
    let parent = prog.def(def.parent);
    if def.parent != NO_DEF && matches!(parent.kind, DefKind::Trait | DefKind::Impl) {
        let pf = &prog.files[parent.file as usize];
        if let Some(pg) = pf.ast.kind_generics(&pf.ast.item(parent.item).kind) {
            for p in pf.ast.list(pg.params) {
                if !matches!(p.kind, GenericParamKind::Lifetime(_)) { outer.push(pf.text(p.name)); }
            }
        }
    }
    let mut errors = Vec::new();
    let mut seen: Vec<&str> = Vec::new();
    for p in ast.list(g.params) {
        if matches!(p.kind, GenericParamKind::Lifetime(_)) { continue; }
        let name = f.text(p.name);
        if seen.contains(&name) || outer.contains(&name) {
            errors.push(prog.record_error(def.file, p.name.lo, "resolve", format!("E0403: the name `{}` is already used for a generic parameter in this item's generic parameters", name)));
        }
        seen.push(name);
    }
    errors
}
