//! rustc_hir_analysis well-formedness checks of definitions that need no body:
//! constrained_generic_params.rs, impl_wf_check.rs (E0207), check/wfcheck.rs
//! `check_variances_for_type_defn` (E0392) and check/check.rs
//! `check_type_alias_type_params_are_used` (E0091).
use crate::ast::{GenericParamKind, ItemKind};
use crate::consts::{ConstKind, GenericArg};
use crate::fxhash::HashSet;
use crate::next_solver::{AliasTerm, ClauseKind, Predicate, PredicateKind, Term};
use crate::program::{DefId, DefKind, Program};
use crate::tcx::Tcx;
use crate::types::variance::{GenericIndices, V};
use crate::types::{AliasTy, AliasTyKind, RegionKind, TyId, TyKind};

/// A generic parameter by its index in the full generics list (lifetimes included).
type Parameter = u32;

struct Collector<'a> {
    tcx: &'a Tcx,
    indices: &'a GenericIndices,
    include_nonconstraining: bool,
    out: Vec<Parameter>,
}

impl Collector<'_> {
    fn ty(&mut self, t: TyId) {
        match self.tcx.tys.kind(t).clone() {
            // projections are not injective in general
            TyKind::Alias(_, AliasTy { kind: AliasTyKind::Projection { .. } | AliasTyKind::Inherent { .. } | AliasTyKind::Opaque { .. }, .. }) if !self.include_nonconstraining => {}
            TyKind::Param(i) => { if let Some(&full) = self.indices.types_consts.get(i as usize) { self.out.push(full); } }
            TyKind::Ref(_, t, r) => { self.region(r); self.ty(t); }
            TyKind::Ptr(_, t) | TyKind::Slice(t) => self.ty(t),
            TyKind::Array(t, len) => { self.ty(t); self.ct(len); }
            TyKind::Const(c) => self.ct(c),
            TyKind::Tuple(ts) => for &t in self.tcx.tys.list(ts) { self.ty(t); },
            TyKind::FnPtr(ps, ret, _, _) => { for &p in self.tcx.tys.list(ps) { self.ty(p); } self.ty(ret); }
            TyKind::Adt(_, ts, rs) | TyKind::FnDef(_, ts, rs) => {
                for &t in self.tcx.tys.list(ts) { self.ty(t); }
                for &r in self.tcx.tys.region_args(rs).iter() { self.region(r); }
            }
            TyKind::Alias(_, AliasTy { args, regions, .. }) => {
                for &t in self.tcx.tys.list(args) { self.ty(t); }
                for &r in self.tcx.tys.region_args(regions).iter() { self.region(r); }
            }
            TyKind::Dyn(_, ts, bindings, rs, r, _, _) => {
                self.region(r);
                for &t in self.tcx.tys.list(ts) { self.ty(t); }
                for &r in self.tcx.tys.region_args(rs).iter() { self.region(r); }
                for &(_, t, _) in self.tcx.tys.list(bindings) { self.ty(t); }
            }
            _ => {}
        }
    }

    fn region(&mut self, r: crate::types::RegionId) {
        if let RegionKind::ReEarlyParam(i) = self.tcx.tys.region_kind(r) { self.out.push(i); }
    }

    fn ct(&mut self, c: crate::consts::Const) {
        match self.tcx.tys.const_kind(c) {
            ConstKind::Alias(..) if !self.include_nonconstraining => {}
            ConstKind::Param(p) => { if let Some(&full) = self.indices.types_consts.get(p.index as usize) { self.out.push(full); } }
            ConstKind::Alias(_, alias) => for &arg in alias.args.iter() { self.arg(arg); },
            _ => {}
        }
    }

    fn arg(&mut self, a: GenericArg) {
        match a {
            GenericArg::Type(t) => self.ty(t),
            GenericArg::Const(c) => self.ct(c),
            GenericArg::Lifetime(r) => self.region(r),
        }
    }
}

impl Tcx {
    /// constrained_generic_params.rs `parameters_for` of a type.
    fn parameters_for_ty(&self, indices: &GenericIndices, t: TyId, include_nonconstraining: bool) -> Vec<Parameter> {
        let mut c = Collector { tcx: self, indices, include_nonconstraining, out: Vec::new() };
        c.ty(t);
        c.out
    }

    fn parameters_for_args(&self, indices: &GenericIndices, args: &[GenericArg], include_nonconstraining: bool) -> Vec<Parameter> {
        let mut c = Collector { tcx: self, indices, include_nonconstraining, out: Vec::new() };
        for &a in args { c.arg(a); }
        c.out
    }

    /// `identify_constrained_generic_params` / `setup_constraining_predicates`: parameters that a
    /// projection predicate `<..> = Term` fixes once all of its inputs are known.
    /// The trait an associated item belongs to.
    fn assoc_trait(&self, prog: &Program, item: DefId) -> DefId { prog.def(item).parent }

    fn identify_constrained_generic_params(&self, prog: &Program, indices: &GenericIndices, predicates: &[Predicate], impl_trait_ref: Option<&crate::next_solver::TraitRef>, input: &mut HashSet<Parameter>) {
        let mut remaining: Vec<&Predicate> = predicates.iter().filter(|p| matches!(&p.kind, PredicateKind::Clause(ClauseKind::Projection(_)))).collect();
        let mut changed = true;
        while changed {
            changed = false;
            let mut j = 0;
            while j < remaining.len() {
                let PredicateKind::Clause(ClauseKind::Projection(projection)) = &remaining[j].kind else { unreachable!() };
                let (inputs, same_trait) = match &projection.projection_term {
                    AliasTerm::Ty(alias) => {
                        let TyKind::Alias(_, a) = self.tys.kind(*alias).clone() else { j += 1; continue };
                        // (`prog` for the trait of the projected item)
                        let inputs: Vec<Parameter> = {
                            let mut c = Collector { tcx: self, indices, include_nonconstraining: true, out: Vec::new() };
                            c.ty(*alias);
                            c.out
                        };
                        // an attempt to project out an associated type of the impl's own trait ref
                        let same = impl_trait_ref.is_some_and(|tr| {
                            // the whole trait ref: type and const arguments, then lifetimes
                            let tc: Vec<TyId> = tr.args.iter().filter_map(|x| match *x {
                                GenericArg::Type(t) => Some(t),
                                GenericArg::Const(c) => Some(self.tys.intern(TyKind::Const(c))),
                                GenericArg::Lifetime(_) => None,
                            }).collect();
                            let lts: Vec<crate::types::RegionId> = tr.args.iter().filter_map(|x| if let GenericArg::Lifetime(r) = *x { Some(r) } else { None }).collect();
                            let regions = self.tys.region_args(a.regions);
                            tr.def_id == self.assoc_trait(prog, a.kind.def_id()) && self.tys.list(a.args).len() >= tc.len() && self.tys.list(a.args)[..tc.len()] == tc[..]
                                && regions.len() >= lts.len() && regions[..lts.len()] == lts[..]
                        });
                        (inputs, same)
                    }
                    AliasTerm::Const(_) => { j += 1; continue; }
                };
                if !same_trait && inputs.iter().all(|p| input.contains(p)) {
                    let determined = match &projection.term {
                        Term::Ty(t) => self.parameters_for_ty(indices, *t, false),
                        Term::Const(c) => { let mut col = Collector { tcx: self, indices, include_nonconstraining: false, out: Vec::new() }; col.ct(*c); col.out }
                    };
                    input.extend(determined);
                    remaining.swap_remove(j);
                    changed = true;
                } else { j += 1; }
            }
        }
    }

    /// impl_wf_check.rs `check_impl_wf`: every type and const parameter of an impl appears in the
    /// trait ref or self type, or is fixed by a projection predicate (E0207); a lifetime
    /// parameter too when an associated type's value uses it.
    pub fn check_impl_params_constrained(&self, prog: &Program, imp: DefId) -> Vec<String> {
        let Some(&self_ty) = self.impl_self.get(&imp) else { return Vec::new() };
        if self.tys.has_error(self_ty) { return Vec::new(); }
        let def = prog.def(imp);
        let ast = &prog.files[def.file as usize].ast;
        let Some(item) = ast.as_impl(&ast.item(def.item).kind) else { return Vec::new() };
        let indices = self.generic_indices_of(prog, imp).clone();
        let of_trait = self.impl_trait.contains_key(&imp);
        let trait_ref = of_trait.then(|| self.identity_impl_trait_ref(prog, imp));
        if let Some(tr) = &trait_ref {
            if tr.args.iter().any(|a| matches!(*a, GenericArg::Type(t) if self.tys.has_error(t))) { return Vec::new(); }
        }
        let mut input: HashSet<Parameter> = match &trait_ref {
            Some(tr) => self.parameters_for_args(&indices, &tr.args, false),
            None => self.parameters_for_ty(&indices, self_ty, false),
        }.into_iter().collect();
        let predicates = self.own_clauses_of(prog, imp).to_vec();
        self.identify_constrained_generic_params(prog, &indices, &predicates, trait_ref, &mut input);
        // lifetimes used by an associated type's value
        let mut in_assoc: HashSet<Parameter> = HashSet::default();
        let mut lifetimes_checked = false;
        let mut errors = Vec::new();
        for (index, p) in ast.list(item.generics.params).iter().enumerate() {
            let index = index as u32;
            let name = prog.files[def.file as usize].text(p.name);
            let what = match p.kind {
                GenericParamKind::Type(..) => "type",
                GenericParamKind::Const(..) => "const",
                GenericParamKind::Lifetime(_) => {
                    if !lifetimes_checked {
                        lifetimes_checked = true;
                        let state = crate::tcx::EvalState::new();
                        let cx = crate::tcx::EvalCx::new(prog, self, crate::tcx::TypingEnv::fully_monomorphized(prog), &state);
                        for &it in &prog.impls[def.sub as usize].items {
                            let d = prog.def(it);
                            if d.kind != DefKind::AssocTy { continue; }
                            if let Some(t) = self.impl_assoc_ty(&cx, prog, imp, d.name) {
                                in_assoc.extend(self.parameters_for_ty(&indices, t, true));
                            }
                        }
                    }
                    if in_assoc.contains(&index) && !input.contains(&index) { "lifetime" } else { continue }
                }
            };
            if matches!(p.kind, GenericParamKind::Lifetime(_)) { } else if input.contains(&index) { continue; }
            errors.push(prog.record_error(def.file, p.name.lo, "typeck", format!("E0207: the {} parameter `{}` is not constrained by the impl trait, self type, or predicates", what, name)));
        }
        errors
    }

    /// check_variances_for_type_defn: a parameter of a struct, enum or union that no field uses
    /// and no projection predicate constrains (E0392).
    pub fn check_type_defn_variances(&self, prog: &Program, d: DefId) -> Vec<String> {
        let def = prog.def(d);
        let ast = &prog.files[def.file as usize].ast;
        let Some(generics) = ast.kind_generics(&ast.item(def.item).kind) else { return Vec::new() };
        if generics.params.is_empty() { return Vec::new(); }
        let variances = self.variances_of(prog, d);
        let indices = self.generic_indices_of(prog, d).clone();
        let mut constrained: HashSet<Parameter> = variances.iter().enumerate().filter(|(_, v)| **v != V::Bi).map(|(i, _)| i as u32).collect();
        self.identify_constrained_generic_params(prog, &indices, self.own_clauses_of(prog, d), None, &mut constrained);
        // an error deep in a field type: the unused parameter is not reported
        if self.adts.get(&d).is_some_and(|adt| adt.variants.iter().any(|v| v.fields.iter().any(|f| self.tys.has_error(f.ty)))) { return Vec::new(); }
        let mut errors = Vec::new();
        for (index, p) in ast.list(generics.params).iter().enumerate() {
            if constrained.contains(&(index as u32)) || variances.get(index).is_none() { continue; }
            let what = match p.kind { GenericParamKind::Lifetime(_) => "lifetime", GenericParamKind::Type(..) => "type", GenericParamKind::Const(..) => "const" };
            let name = prog.files[def.file as usize].text(p.name);
            errors.push(prog.record_error(def.file, p.name.lo, "typeck", format!("E0392: {} parameter `{}` is never used", what, name)));
        }
        errors
    }

    /// The type a type alias is declared as, lowered afresh: its errors are the alias's own
    /// (rustc `type_of` of every item), `alias_ty` caches the first lowering for users.
    pub fn check_type_alias(&self, prog: &Program, d: DefId) -> Vec<String> {
        let def = prog.def(d);
        let ast = &prog.files[def.file as usize].ast;
        let ItemKind::TypeAlias(_) = ast.item(def.item).kind else { return Vec::new() };
        let Some(generics) = ast.kind_generics(&ast.item(def.item).kind) else { return Vec::new() };
        let state = crate::tcx::EvalState::new();
        state.errors.replace(Some(Vec::new()));
        let cx = crate::tcx::EvalCx::new(prog, self, crate::tcx::TypingEnv::fully_monomorphized(prog), &state);
        let ty = self.lower_alias_rhs(&cx, prog, d);
        let mut errors = state.errors.take().unwrap_or_default();
        if !errors.is_empty() || self.tys.has_error(ty) { return errors; }
        // check_type_alias_type_params_are_used: a type parameter the aliased type never
        // mentions (E0091)
        let indices = self.generic_indices_of(prog, d).clone();
        let used: HashSet<Parameter> = self.parameters_for_ty(&indices, ty, true).into_iter().collect();
        for (index, p) in ast.list(generics.params).iter().enumerate() {
            if matches!(p.kind, GenericParamKind::Type(..)) && !used.contains(&(index as u32)) {
                let name = prog.files[def.file as usize].text(p.name);
                errors.push(prog.record_error(def.file, p.name.lo, "typeck", format!("E0091: type parameter `{}` is never used", name)));
            }
        }
        errors
    }
}

/// rustc_hir_analysis check/wfcheck.rs `check_method_receiver` for a method that writes its
/// receiver type (`self: Box<Self>`): the receiver must be `Self` or reach it through the
/// autoderef chain, every step implementing `LegacyReceiver`. Where rustc would accept it with
/// `arbitrary_self_types` (a `Deref` chain) or `arbitrary_self_types_pointers` (raw pointers),
/// it reports the feature gate (E0658); otherwise E0307, or E0801 for a generic receiver.
/// A receiver or `Self` that mentions a projection or opaque type is not judged.
impl Tcx {
    pub fn check_method_receiver(&self, prog: &Program, m: DefId) -> Vec<String> {
        use crate::next_solver::{Goal, collect};
        let def = prog.def(m);
        if def.kind != DefKind::AssocFn { return Vec::new(); }
        let f = &prog.files[def.file as usize];
        let item = f.ast.item(def.item);
        let ItemKind::Fn(sig_id, _, _) = item.kind else { return Vec::new() };
        if !matches!(f.ast.fn_sig(sig_id).self_param, Some(crate::ast::SelfParam::Typed(..))) { return Vec::new(); }
        let parent = prog.def(def.parent);
        let self_ty = match parent.kind {
            DefKind::Impl => match self.impl_self.get(&def.parent) { Some(&t) => t, None => return Vec::new() },
            DefKind::Trait => self.tys.intern(TyKind::Param(0)),
            _ => return Vec::new(),
        };
        let Some(sig) = self.fn_sig(prog, m) else { return Vec::new() };
        let Some(&recv) = sig.params.first() else { return Vec::new() };
        let (recv, self_ty) = (self.tys.erase_regions(recv), self.tys.erase_regions(self_ty));
        for t in [recv, self_ty] {
            if self.tys.has_error(t) || self.tys.has_assoc(t) || self.tys.has_opaque(t) || self.tys.has_infer(t) { return Vec::new(); }
        }
        let Some(legacy) = self.lang_items.get(crate::lang_items::LangItem::LegacyReceiver) else { return Vec::new() };
        let env = self.param_env_id(prog, m);
        let parent_params = self.generic_indices_of(prog, def.parent).types_consts.len() as u32;
        // 0: neither feature, 1: arbitrary_self_types, 2: with pointers
        let valid = |level: u8| -> Result<(), bool> {
            let infcx = crate::infer::InferCtxt::for_item(self, prog, crate::tcx::TypingMode::non_body_analysis(), m);
            let same = |a: TyId, b: TyId| infcx.at(prog, env.clone()).eq(a, b).is_ok();
            if same(self_ty, recv) { return Ok(()); }
            let generic_param = |t: TyId| matches!(self.tys.kind(t), TyKind::Param(i) if *i >= parent_params);
            if generic_param(recv) { return Err(true); }
            let mut cur = recv;
            for _ in 0..32 {
                if generic_param(cur) { return Err(true); }
                if same(self_ty, cur) { return Ok(()); }
                if level == 0 {
                    let goal = Goal { param_env: env.clone(), predicate: collect::trait_predicate(legacy, vec![GenericArg::Type(cur)]) };
                    if !infcx.evaluate_obligation(prog, goal).must_apply_modulo_regions() { break; }
                }
                let next = match self.tys.kind(cur) {
                    TyKind::Ref(_, t, _) => Some(*t),
                    TyKind::Ptr(_, t) if level == 2 => Some(*t),
                    TyKind::Ptr(..) | TyKind::Error | TyKind::Infer(_) => None,
                    _ => crate::typeck::probe::overloaded_deref_ty(&infcx, prog, &env, cur),
                };
                let Some(next) = next else { break };
                cur = self.tys.erase_regions(next);
            }
            Err(false)
        };
        let Err(generic) = valid(0) else { return Vec::new() };
        let shown = crate::typeck::ty_to_string(false, prog, self, recv);
        let pos = self_param_pos(prog, def.file, item.lo, item.name.hi);
        let crate_features = prog.crates[def.krate as usize].features(prog);
        if !generic {
            if valid(1).is_ok() && !crate_features.has("arbitrary_self_types") && !crate_features.has("arbitrary_self_types_pointers") {
                return vec![prog.record_error(def.file, pos, "typeck", format!("E0658: `{}` cannot be used as the type of `self` without the `arbitrary_self_types` feature", shown))];
            }
            if valid(2).is_ok() && !crate_features.has("arbitrary_self_types_pointers") {
                return vec![prog.record_error(def.file, pos, "typeck", format!("E0658: `{}` cannot be used as the type of `self` without the `arbitrary_self_types_pointers` feature", shown))];
            }
        }
        if crate_features.has("arbitrary_self_types") || crate_features.has("arbitrary_self_types_pointers") {
            // (the features change which chains are valid; Relax does not model their errors)
            return Vec::new();
        }
        if generic {
            vec![prog.record_error(def.file, pos, "typeck", format!("E0801: invalid generic `self` parameter type: `{}`", shown))]
        } else {
            vec![prog.record_error(def.file, pos, "typeck", format!("E0307: invalid `self` parameter type: `{}`", shown))]
        }
    }
}

/// The position of the `self` of a method's parameter list (after its name).
fn self_param_pos(prog: &Program, file: u32, lo: u32, name_hi: u32) -> u32 {
    let f = &prog.files[file as usize];
    let b = f.bytes(name_hi, (name_hi + 400).min(f.src_len));
    b.windows(4).position(|w| w == b"self").map_or(lo, |i| name_hi + i as u32)
}
