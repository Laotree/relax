//! Item well-formedness: the trait obligations of rustc_hir_analysis/src/check/wfcheck.rs
//! (check_item, check_type_defn, check_item_fn / check_fn_or_method, check_impl,
//! check_where_clauses, check_associated_item, check_static_item). Region obligations are
//! the region checker's; every obligation here is registered in a fulfillment context under
//! the item's own parameter environment and reported when it cannot hold.
use crate::consts::GenericArg;
use crate::next_solver::fulfill::{NextSolverError, ObligationCause, ObligationCtxt, PredicateObligation};
use crate::next_solver::{collect, AliasTerm, ClauseKind, ClausePolarity, Goal, ParamEnvId, Predicate, PredicateKind, Term};
use crate::program::{DefId, DefKind, Program};
use crate::tcx::Tcx;
use crate::types::{TyId, TyKind};
use crate::ast::{self, ItemKind};

struct Wfcx<'a, 'tcx> {
    prog: &'a Program,
    tcx: &'a Tcx,
    infcx: &'a crate::infer::InferCtxt<'tcx>,
    ocx: ObligationCtxt<'a, 'tcx>,
    env: ParamEnvId,
    def: DefId,
}

impl<'a, 'tcx> Wfcx<'a, 'tcx> {
    fn register(&mut self, goal: Goal, pos: u32) {
        self.ocx.engine.register_predicate_obligation(self.infcx, PredicateObligation { goal, recursion_depth: 0, cause: ObligationCause { span: pos, body_id: self.def } });
    }

    fn goal(&self, kind: PredicateKind) -> Goal {
        Goal { param_env: self.env.clone(), predicate: Predicate::dummy(kind) }
    }

    /// wfcheck.rs WfCheckingCtxt::deeply_normalize. A type that cannot be normalized stays as
    /// written: its own well-formedness reports the unmet bound.
    fn normalize(&mut self, ty: TyId) -> TyId {
        if !self.tcx.tys.has_assoc(ty) { return ty; }
        let mut ocx = ObligationCtxt::new(self.infcx, self.prog);
        ocx.cause = ObligationCause { span: 0, body_id: self.def };
        ocx.deeply_normalize_ty(&self.env, ty).unwrap_or(ty)
    }

    /// WfCheckingCtxt::register_wf_obligation: the obligations that make `term` well formed
    /// (rustc_trait_selection wf.rs), expanded here so a failure names the unmet bound.
    fn register_wf(&mut self, ty: TyId, pos: u32) {
        if self.tcx.tys.has_error(ty) || !arity_ok(self.tcx, self.prog, ty) { return; }
        if let Ok(Some(goals)) = crate::next_solver::wf::unnormalized_obligations(self.infcx, self.prog, &self.env, Term::Ty(ty)) {
            for g in goals {
                // (constants are evaluated by their own check)
                if matches!(g.predicate.kind, PredicateKind::Clause(ClauseKind::ConstEvaluatable(_))) { continue; }
                self.register(g, pos);
            }
        }
    }

    fn register_bound(&mut self, ty: TyId, trait_def: Option<DefId>, pos: u32) {
        if self.tcx.tys.has_error(ty) { return; }
        let Some(td) = trait_def else { return };
        let goal = Goal { param_env: self.env.clone(), predicate: collect::trait_predicate(td, vec![GenericArg::Type(ty)]) };
        self.register(goal, pos);
    }

    fn sized(&mut self, ty: TyId, pos: u32) {
        let sized = self.tcx.lang_items.get(crate::lang_items::LangItem::Sized);
        self.register_bound(ty, sized, pos);
    }

    /// wf.rs clause_obligations: what makes one where-clause well formed.
    fn clause_obligations(&mut self, p: &Predicate, pos: u32) {
        let tys = &self.tcx.tys;
        let escaping = |t: TyId| tys.has_vars_bound_at_or_above(t, 0);
        match &p.kind {
            PredicateKind::Clause(ClauseKind::Trait(t)) => {
                if t.polarity == ClausePolarity::Negative { return; }
                let def = t.trait_ref.def_id;
                let args = &t.trait_ref.args;
                // wf.rs nominal_obligations: the trait's own predicates at these arguments
                // (the `Self: Sized`-like predicates of a `?Sized`-declaring trait included)
                if self.tcx.lang_items.get(crate::lang_items::LangItem::Sized) != Some(def) {
                    for q in self.tcx.clauses_of(self.prog, def) {
                        // (bounds on the supertraits' associated types, `Super<Assoc: Bound>`, are implied
                        // predicates rustc elaborates into the environment; this one's elaboration stops
                        // at `Self: Super`)
                        if matches!(&q.kind, PredicateKind::Clause(ClauseKind::Trait(u)) if matches!(u.trait_ref.args.first(), Some(GenericArg::Type(t)) if matches!(self.tcx.tys.kind(*t), TyKind::Alias(..)))) { continue; }
                        let q = self.tcx.instantiate_predicate(self.prog, def, args, &q);
                        if crate::next_solver::wf::predicate_has_escaping_bound_vars(tys, &q) { continue; }
                        // the trait's `Self: Trait` is the clause itself
                        if matches!(&q.kind, PredicateKind::Clause(ClauseKind::Trait(u)) if u.trait_ref.def_id == def) { continue; }
                        self.register(Goal { param_env: self.env.clone(), predicate: q }, pos);
                    }
                }
                for a in args {
                    if let GenericArg::Type(t) = a { if !escaping(*t) { self.register_wf(*t, pos); } }
                }
            }
            PredicateKind::Clause(ClauseKind::TypeOutlives(t, _)) => { if !escaping(*t) { self.register_wf(*t, pos); } }
            PredicateKind::Clause(ClauseKind::Projection(pc)) => {
                if let AliasTerm::Ty(a) = &pc.projection_term { if !escaping(*a) { self.register_wf(*a, pos); } }
                if let Term::Ty(t) = pc.term { if !escaping(t) { self.register_wf(t, pos); } }
            }
            PredicateKind::Clause(ClauseKind::ConstArgHasType(_, t)) => { if !escaping(*t) { self.register_wf(*t, pos); } }
            _ => {}
        }
    }

    /// wfcheck.rs check_where_clauses: every where-clause of the item (the parent's included) is
    /// well formed.
    fn check_where_clauses(&mut self, pos: u32) {
        for p in self.tcx.clauses_of(self.prog, self.def) {
            self.clause_obligations(&p, pos);
        }
    }

    /// wfcheck.rs check_false_global_bounds: a where-clause that mentions no parameter must hold
    /// (unless `trivial_bounds`); the clauses are elaborated, WellFormed ones left out.
    fn check_false_global_bounds(&mut self) {
        let d = self.prog.def(self.def);
        if self.prog.crates[d.krate as usize].feature_enabled(self.prog, "trivial_bounds") { return; }
        // type aliases bounds are ignored
        if d.kind == DefKind::TypeAlias { return; }
        let pos = self.prog.files[d.file as usize].ast.item(d.item).lo;
        let tys = &self.tcx.tys;
        for p in self.tcx.clauses_of(self.prog, self.def) {
            for p in self.tcx.supertraits(self.prog, p) {
                if matches!(p.kind, PredicateKind::Clause(ClauseKind::WellFormed(_))) { continue; }
                let flags = p.flags(tys);
                let local = crate::types::TypeFlags::HAS_PARAM.bits() | crate::types::TypeFlags::HAS_ANY_INFER.bits() | crate::types::TypeFlags::HAS_PLACEHOLDER.bits() | crate::types::TypeFlags::HAS_BOUND_VARS.bits() | crate::types::TypeFlags::HAS_ALIAS.bits();
                if flags & local != 0 || !p.bound_vars.is_empty() { continue; }
                // the trait's own `Self: Trait` of a trait definition is not a user bound
                if let PredicateKind::Clause(ClauseKind::Trait(t)) = &p.kind { if t.trait_ref.def_id == self.def { continue; } }
                self.register(Goal { param_env: ParamEnvId::EMPTY, predicate: p }, pos);
            }
        }
    }

    /// Solve what was registered; an obligation that cannot hold is an error. Ambiguity is
    /// left to the rest of the check.
    fn finish(mut self, file: u32) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for e in self.ocx.try_evaluate_obligations() {
            let (code, o) = match e {
                NextSolverError::TrueError(o) => ("E0277", o),
                NextSolverError::Overflow(o) => ("E0275", o),
                NextSolverError::Ambiguity(_) => continue,
            };
            let Some(msg) = self.message(code, &o) else { continue };
            if !seen.insert((o.cause.span, msg.clone())) { continue; }
            out.push(self.prog.record_error(file, o.cause.span, "typeck", msg));
        }
        out
    }

    fn message(&self, code: &str, o: &PredicateObligation) -> Option<String> {
        fulfillment_message(self.infcx, self.prog, code, &o.goal)
    }
}

/// The failing leaf of a well-formedness goal: `WellFormed(T)` stands for the obligations of
/// `T`'s components (wf.rs), and the first of them that cannot hold is what is reported.
pub(crate) fn leaf_goal(infcx: &crate::infer::InferCtxt<'_>, prog: &Program, goal: &Goal, depth: u32) -> Goal {
    if depth > 8 { return goal.clone(); }
    if let PredicateKind::Clause(ClauseKind::WellFormed(term)) = &goal.predicate.kind {
        if let Ok(Some(goals)) = crate::next_solver::wf::unnormalized_obligations(infcx, prog, &goal.param_env, term.clone()) {
            for g in goals {
                if g == *goal { continue; }
                if matches!(infcx.evaluate_obligation(prog, g.clone()), crate::next_solver::evaluate_obligation::EvaluationResult::EvaluatedToErr) {
                    return leaf_goal(infcx, prog, &g, depth + 1);
                }
            }
        }
    }
    goal.clone()
}

/// rustc's wording of an unmet obligation (report_selection_error); None: not one of ours to
/// report (regions, constants).
pub(crate) fn fulfillment_message(infcx: &crate::infer::InferCtxt<'_>, prog: &Program, code: &str, goal: &Goal) -> Option<String> {
    let tcx = infcx.tcx;
    let goal = leaf_goal(infcx, prog, goal, 0);
    let ty_str = |t: TyId| crate::typeck::ty_to_string(false, prog, tcx, infcx.deeply_resolve_ignoring_regions(t));
    match &goal.predicate.kind {
        PredicateKind::Clause(ClauseKind::Trait(p)) => Some(format!("{code}: {}", crate::typeck::trait_error_message(prog, tcx, code, p, &mut |t| ty_str(t)))),
        PredicateKind::Clause(ClauseKind::Projection(p)) => {
            let (AliasTerm::Ty(a), Term::Ty(t)) = (&p.projection_term, &p.term) else { return None };
            Some(format!("E0271: type mismatch resolving `{}` == `{}`", ty_str(*a), ty_str(*t)))
        }
        PredicateKind::DynCompatible(d) => Some(format!("E0038: the trait `{}` is not dyn compatible", prog.name(*d))),
        PredicateKind::Clause(ClauseKind::WellFormed(Term::Ty(t))) => Some(format!("E0277: the type `{}` is not well-formed", ty_str(*t))),
        // regions, constants and the rest belong to their own checks
        _ => None,
    }
}

fn with_wfcx(prog: &Program, tcx: &Tcx, def: DefId, f: impl FnOnce(&mut Wfcx<'_, '_>)) -> Vec<String> {
    let infcx = crate::infer::InferCtxt::for_item(tcx, prog, crate::tcx::TypingMode::non_body_analysis(), def);
    let env = tcx.param_env_id(prog, def);
    let mut w = Wfcx { prog, tcx, infcx: &infcx, ocx: ObligationCtxt::new(&infcx, prog), env, def };
    w.check_false_global_bounds();
    f(&mut w);
    w.finish(prog.def(def).file)
}

/// check_well_formed for one definition (a body-less, header-level check: bodies are the
/// type checker's).
pub fn check_def(prog: &Program, tcx: &Tcx, did: DefId) -> Vec<String> {
    let def = prog.def(did);
    if prog.item_defs.get(&(def.file, def.item.0)) != Some(&did) { return Vec::new(); }
    let ast = &prog.files[def.file as usize].ast;
    let item = ast.item(def.item);
    match def.kind {
        DefKind::Struct | DefKind::Enum | DefKind::Union => with_wfcx(prog, tcx, did, |w| check_type_defn(w, ast, item)),
        DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn => with_wfcx(prog, tcx, did, |w| check_fn(w, ast, item)),
        DefKind::Impl => {
            let mut errors = check_drop_impl(prog, tcx, did, ast, item);
            errors.extend(with_wfcx(prog, tcx, did, |w| check_impl(w, ast, item)));
            errors
        }
        // (a trait's own environment is not built here: `param_env_id` of `trait Qux: Foo + AsRef<Self::Bar>` never
        // returns -- solver, crash lane)
        DefKind::Trait => Vec::new(),
        DefKind::Static => with_wfcx(prog, tcx, did, |w| check_static(w, ast, item)),
        DefKind::AssocConst => with_wfcx(prog, tcx, did, |w| check_assoc_const(w, ast, item)),
        DefKind::AssocTy => with_wfcx(prog, tcx, did, |w| check_assoc_ty(w, ast, item)),
        _ => Vec::new(),
    }
}

fn check_type_defn(w: &mut Wfcx<'_, '_>, ast: &ast::Ast, item: &ast::Item) {
    let Some(adt) = w.tcx.adts.get(&w.def) else { return };
    let mut fields: Vec<Vec<ast::FieldDef>> = Vec::new();
    let data = |d: &ast::VariantData| match d { ast::VariantData::Unit => Vec::new(), ast::VariantData::Tuple(l) | ast::VariantData::Struct(l) => ast.list(*l).to_vec() };
    let all_sized = match &item.kind {
        ItemKind::Struct(_) => { fields.push(data(&ast.as_struct(&item.kind).unwrap().data)); false }
        ItemKind::Union(_) => { fields.push(ast.list(ast.as_union(&item.kind).unwrap().fields).to_vec()); true }
        ItemKind::Enum(_) => { for v in ast.list(ast.as_enum(&item.kind).unwrap().variants) { fields.push(data(&v.data)); } true }
        _ => return,
    };
    let packed = adt.repr_packed != 0;
    for (variant, written) in adt.variants.iter().zip(&fields) {
        let n = variant.fields.len();
        let tys: Vec<TyId> = variant.fields.iter().map(|f| f.ty).collect();
        let pos_of = |i: usize| written.get(i).map_or(item.lo, |f| f.ty_span.0);
        for (i, &ty) in tys.iter().enumerate() {
            let ty = w.normalize(ty);
            w.register_wf(ty, pos_of(i));
        }
        // All fields (except for possibly the last) should be sized.
        let _ = packed;
        let unsized_len = if all_sized || n == 0 { 0 } else { 1 };
        for (i, &ty) in tys[..n - unsized_len].iter().enumerate() {
            let ty = w.normalize(ty);
            w.sized(ty, pos_of(i));
        }
    }
    w.check_where_clauses(item.lo);
}

/// The fn's signature with its late-bound regions liberated, one component at a time.
fn check_fn(w: &mut Wfcx<'_, '_>, ast: &ast::Ast, item: &ast::Item) {
    let Some(sig) = w.tcx.fn_sig(w.prog, w.def).cloned() else { return };
    let ItemKind::Fn(s, body, _) = &item.kind else { return };
    let fsig = ast.fn_sig(*s);
    let has_body = body.is_some() || fsig.lazy_body.is_some();
    let liberate = |t: TyId| crate::next_solver::dyn_compatibility::liberate_late_bound_regions(w.tcx, w.def, t);
    let params: Vec<TyId> = sig.params.iter().map(|&t| liberate(t)).collect();
    let ret = liberate(sig.ret);
    let own = ast.list(fsig.params);
    let skip = params.len().saturating_sub(own.len());
    for (i, &ty) in params.iter().enumerate() {
        let pos = if i >= skip { ty_pos(ast, own[i - skip].ty).unwrap_or(item.name.lo) } else { item.name.lo };
        let ty = w.normalize(ty);
        w.register_wf(ty, pos);
    }
    let ret = w.normalize(ret);
    let ret_pos = fsig.ret.and_then(|t| ty_pos(ast, t)).unwrap_or(item.name.lo);
    w.register_wf(ret, ret_pos);
    w.check_where_clauses(item.lo);
    // If the function has a body, additionally require that the return type is sized.
    if has_body { w.sized(ret, ret_pos); }
}

fn check_impl(w: &mut Wfcx<'_, '_>, ast: &ast::Ast, item: &ast::Item) {
    let imp = ast.as_impl(&item.kind).unwrap();
    if imp.negative { return; }
    let indices = w.tcx.generic_indices_of(w.prog, w.def);
    let args = indices.identity_args(&w.tcx.tys);
    if w.tcx.impl_trait.contains_key(&w.def) {
        let trait_ref = w.tcx.impl_trait_ref(w.prog, w.def, &args);
        if trait_ref.args.iter().any(|a| matches!(*a, GenericArg::Type(t) if w.tcx.tys.has_error(t))) { return; }
        let self_pos = ty_pos(ast, imp.self_ty).unwrap_or(item.lo);
        // wf.rs trait_obligations: the trait's own predicates at the impl's arguments, and each
        // argument well formed
        let p = collect::trait_predicate(trait_ref.def_id, trait_ref.args.clone());
        let PredicateKind::Clause(ClauseKind::Trait(tc)) = &p.kind else { unreachable!() };
        let def = trait_ref.def_id;
        for q in w.tcx.clauses_of(w.prog, def) {
            if matches!(&q.kind, PredicateKind::Clause(ClauseKind::Trait(u)) if matches!(u.trait_ref.args.first(), Some(GenericArg::Type(t)) if matches!(w.tcx.tys.kind(*t), TyKind::Alias(..)))) { continue; }
            let q = w.tcx.instantiate_predicate(w.prog, def, &tc.trait_ref.args, &q);
            if crate::next_solver::wf::predicate_has_escaping_bound_vars(&w.tcx.tys, &q) { continue; }
            if matches!(&q.kind, PredicateKind::Clause(ClauseKind::Trait(u)) if u.trait_ref.def_id == def) { continue; }
            // Elaborate::All: what the trait's bounds imply holds too
            for e in w.tcx.supertraits(w.prog, q) {
                if matches!(&e.kind, PredicateKind::Clause(ClauseKind::Trait(u)) if u.trait_ref.def_id == def) { continue; }
                w.register(Goal { param_env: w.env.clone(), predicate: e }, self_pos);
            }
        }
        for a in &trait_ref.args {
            if let GenericArg::Type(t) = a { let t = w.normalize(*t); w.register_wf(t, self_pos); }
        }
    } else if let Some(&self_ty) = w.tcx.impl_self.get(&w.def) {
        let self_ty = w.normalize(self_ty);
        w.register_wf(self_ty, ty_pos(ast, imp.self_ty).unwrap_or(item.lo));
    }
    w.check_where_clauses(item.lo);
}

fn check_static(w: &mut Wfcx<'_, '_>, ast: &ast::Ast, item: &ast::Item) {
    let ItemKind::Static(mutable, _, _) = &item.kind else { return };
    let Some(ty) = w.tcx.const_ty(w.prog, w.def) else { return };
    let ty = w.normalize(ty);
    w.register_wf(ty, item.name.lo);
    w.sized(ty, item.name.lo);
    // Ensure that the end result is `Sync` in a non-thread local `static`.
    let attrs: Vec<ast::Attr> = ast.list(item.attrs).to_vec();
    let thread_local = relax_front::lang_items::has_attr(w.prog, w.prog.def(w.def).file, &attrs, "thread_local");
    if !*mutable && !thread_local {
        let sync = w.tcx.lang_items.get(crate::lang_items::LangItem::Sync);
        w.register_bound(ty, sync, item.name.lo);
    }
}

fn check_assoc_const(w: &mut Wfcx<'_, '_>, _ast: &ast::Ast, item: &ast::Item) {
    let Some(ty) = w.tcx.const_ty(w.prog, w.def) else { return };
    let ty = w.normalize(ty);
    w.register_wf(ty, item.name.lo);
    if let ItemKind::Const(_, init) = &item.kind { if init.is_some() { w.sized(ty, item.name.lo); } }
}

fn check_assoc_ty(w: &mut Wfcx<'_, '_>, ast: &ast::Ast, item: &ast::Item) {
    let Some(alias) = ast.as_alias(&item.kind) else { return };
    if alias.ty.is_none() { return; }
    let Ok(ty) = w.tcx.type_of(w.prog, w.def) else { return };
    let ty = w.normalize(ty);
    w.register_wf(ty, item.name.lo);
}

/// Where a written type starts: types carry no span of their own, a path its position.
fn ty_pos(ast: &ast::Ast, t: ast::TyId) -> Option<u32> {
    match ast.ty(t) {
        ast::Ty::Path(p) => Some(p.lo),
        ast::Ty::Ref(_, _, i) | ast::Ty::Ptr(_, i) | ast::Ty::Slice(i) | ast::Ty::Array(i, _) | ast::Ty::Paren(i) => ty_pos(ast, *i),
        ast::Ty::Tuple(l) => ast.list(*l).first().and_then(|&i| ty_pos(ast, i)),
        _ => None,
    }
}

/// A plain `fn main()` of the Rust ABI: `#[start]` / `#[no_mangle]` / `extern \"C\" fn main` are other entry points.
pub fn is_entry_main(prog: &Program, main: DefId) -> bool {
    let def = prog.def(main);
    let ast = &prog.files[def.file as usize].ast;
    let item = ast.item(def.item);
    let ItemKind::Fn(s, _, _) = &item.kind else { return false };
    let fsig = ast.fn_sig(*s);
    fsig.abi.is_none() && fsig.params.is_empty() && fsig.self_param.is_none() && item.attrs.is_empty()
}

/// rustc_hir_analysis/src/check/entry.rs check_main_fn_ty: the return type of the entry
/// function implements `Termination`.
pub fn check_main(prog: &Program, tcx: &Tcx, main: DefId) -> Vec<String> {
    let def = prog.def(main);
    let ast = &prog.files[def.file as usize].ast;
    let item = ast.item(def.item);
    let ItemKind::Fn(s, _, _) = &item.kind else { return Vec::new() };
    let Some(term) = tcx.lang_items.get(crate::lang_items::LangItem::Termination) else { return Vec::new() };
    let Some(sig) = tcx.fn_sig(prog, main) else { return Vec::new() };
    if sig.n_generics != 0 || tcx.tys.has_error(sig.ret) { return Vec::new(); }
    let infcx = crate::infer::InferCtxt::for_item(tcx, prog, crate::tcx::TypingMode::non_body_analysis(), main);
    let env = ParamEnvId::EMPTY;
    let mut ocx = ObligationCtxt::new(&infcx, prog);
    let ret = ocx.normalize_ty(&env, sig.ret);
    ocx.register_obligation(Goal { param_env: env.clone(), predicate: collect::trait_predicate(term, vec![GenericArg::Type(ret)]) });
    let bad = ocx.try_evaluate_obligations().into_iter().any(|e| matches!(e, NextSolverError::TrueError(_)));
    if !bad { return Vec::new(); }
    let pos = ast.fn_sig(*s).ret.and_then(|t| ty_pos(ast, t)).unwrap_or(item.name.lo);
    let shown = crate::typeck::ty_to_string(false, prog, tcx, infcx.deeply_resolve_ignoring_regions(ret));
    vec![prog.record_error(def.file, pos, "typeck", format!("E0277: `main` has invalid return type `{}`", shown))]
}

/// rustc_hir_analysis/src/coherence/builtin.rs visit_implementation_of_drop: `Drop` is implemented
/// for structs, enums and unions of the crate only (E0120).
fn check_drop_impl(prog: &Program, tcx: &Tcx, imp: DefId, ast: &ast::Ast, item: &ast::Item) -> Vec<String> {
    let Some(&td) = tcx.impl_trait.get(&imp) else { return Vec::new() };
    if tcx.lang_items.get(crate::lang_items::LangItem::Drop) != Some(td) { return Vec::new(); }
    let Some(&self_ty) = tcx.impl_self.get(&imp) else { return Vec::new() };
    let def = prog.def(imp);
    match tcx.tys.kind(self_ty) {
        TyKind::Error => Vec::new(),
        TyKind::Adt(d, _, _) if prog.def(*d).krate == def.krate => Vec::new(),
        _ => {
            let pos = ast.as_impl(&item.kind).and_then(|i| ty_pos(ast, i.self_ty)).unwrap_or(item.lo);
            vec![prog.record_error(def.file, pos, "typeck", "E0120: the `Drop` trait may only be implemented for local structs, enums, and unions".to_string())]
        }
    }
}

/// Whether every ADT / fn item / alias in `ty` carries as many arguments as its definition has
/// parameters; a path with the wrong count is reported (E0107) and has no well-formedness.
pub(crate) fn arity_ok(tcx: &Tcx, prog: &Program, ty: TyId) -> bool {
    use crate::types::fold::{TypeFolder, super_fold_ty};
    use crate::types::{Types, AliasTyKind};
    struct V<'a> { tcx: &'a Tcx, prog: &'a Program, ok: bool }
    impl TypeFolder for V<'_> {
        fn fold_ty(&mut self, tys: &Types, t: TyId, depth: u32) -> TyId {
            if !self.ok { return t; }
            let (def, n, r) = match tys.kind(t) {
                TyKind::Adt(d, a, r) | TyKind::FnDef(d, a, r) => (Some(*d), tys.list(*a).len(), tys.region_args(*r).len()),
                TyKind::Alias(_, a) if matches!(a.kind, AliasTyKind::Projection { .. }) => (Some(a.kind.def_id()), tys.list(a.args).len(), tys.region_args(a.regions).len()),
                _ => (None, 0, 0),
            };
            if let TyKind::Dyn(p, a, _, r, ..) = tys.kind(t) {
                let ix = self.tcx.generic_indices_of(self.prog, *p);
                if ix.types_consts.len() != tys.list(*a).len() + 1 || ix.lifetimes.len() != tys.region_args(*r).len() { self.ok = false; return t; }
            }
            if let Some(d) = def {
                let ix = self.tcx.generic_indices_of(self.prog, d);
                if ix.types_consts.len() != n || ix.lifetimes.len() != r { self.ok = false; return t; }
            }
            super_fold_ty(tys, t, self, depth)
        }
    }
    let mut v = V { tcx, prog, ok: true };
    v.fold_ty(&tcx.tys, ty, 0);
    v.ok
}
