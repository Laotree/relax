// ported from compiler/rustc_type_ir/src/search_graph/mod.rs @8d1a764
//! Candidate assembly, probing, winnowing and confirmation follow
//! rustc_trait_selection/src/traits/select/{mod.rs:1857,2527,confirmation.rs:430}.
use super::canonical::{InferDelegate, TyVariableKind};
use super::goal::*;
use super::search_graph::{PathKind, SearchGraph, SearchGraphConfig, SearchGraphDelegate};
use crate::ast::{Bound, GenericArgs, GenericArg, GenericParamKind, ItemKind, WherePred};
use crate::lang_items::LangItem;
use crate::program::{DefId, DefKind};
use crate::tcx::{ty_key, EvalCx, Tcx, TyKey};
use crate::types::{TyId, TyKind, RegionArgsId};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct Selected {
    pub source: CandidateSource,
    pub args: Vec<TyId>,
    pub nested: Vec<Goal>,
}

#[derive(Clone, Debug)]
pub enum SelectionResult {
    Ok(Selected),
    Ambiguous(MaybeCause),
    NoSolution,
}

pub fn trait_goal(cx: &EvalCx<'_>, def: DefId, self_ty: TyId, args: &[TyId]) -> Goal {
    let mut all = vec![self_ty];
    all.extend_from_slice(args);
    Goal { param_env: ParamEnvId(cx.typing_env.param_env.index()), predicate: Predicate::Clause(Clause::Trait(TraitPredicate {
        trait_ref: TraitRef { def, args: all }, polarity: PredicatePolarity::Positive,
    })) }
}

pub fn select(tcx: &Tcx, cx: &EvalCx<'_>, infcx: &mut dyn InferDelegate, predicate: TraitPredicate) -> SelectionResult {
    let mut graph = SearchGraph::new(SearchGraphConfig::default());
    let mut ecx = Evaluation::new(tcx, cx, infcx);
    ecx.select(&mut graph, &predicate)
}

pub fn evaluate(tcx: &Tcx, cx: &EvalCx<'_>, infcx: &mut dyn InferDelegate, goal: Goal) -> Result<Certainty, NoSolution> {
    let mut graph = SearchGraph::new(SearchGraphConfig::default());
    let mut ecx = Evaluation::new(tcx, cx, infcx);
    ecx.evaluate(&mut graph, goal)
}

#[derive(Clone)]
struct Candidate {
    source: CandidateSource,
    trait_ref: Option<TraitRef>,
    nested: Vec<Goal>,
    args: Vec<TyId>,
    global: bool,
    sized: bool,
}

struct Evaluation<'a, 'p> {
    tcx: &'a Tcx,
    cx: &'a EvalCx<'p>,
    infcx: &'a mut dyn InferDelegate,
    goals: Vec<Goal>,
    ids: HashMap<Goal, u32>,
}

impl<'a, 'p> Evaluation<'a, 'p> {
    fn new(tcx: &'a Tcx, cx: &'a EvalCx<'p>, infcx: &'a mut dyn InferDelegate) -> Self {
        Self { tcx, cx, infcx, goals: Vec::new(), ids: HashMap::new() }
    }

    fn goal(&self, def: DefId, ty: TyId, args: &[TyId]) -> Goal { trait_goal(self.cx, def, ty, args) }

    fn resolve_goal(&mut self, mut goal: Goal) -> Goal {
        match &mut goal.predicate {
            Predicate::Clause(Clause::Trait(t)) => for a in &mut t.trait_ref.args { *a = self.infcx.resolve_deep(*a); },
            Predicate::Clause(Clause::Projection(p)) => {
                for a in &mut p.alias.args { *a = self.infcx.resolve_deep(*a); }
                if let Term::Ty(t) = &mut p.term { *t = self.infcx.resolve_deep(*t); }
            }
            Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), _) => {
                *a = self.infcx.resolve_deep(*a); *b = self.infcx.resolve_deep(*b);
            }
            _ => {}
        }
        goal
    }

    fn has_infer(&self, goal: &Goal) -> bool {
        match &goal.predicate {
            Predicate::Clause(Clause::Trait(t)) => {
                for a in &t.trait_ref.args { if self.tcx.tys.has_infer(*a) { return true; } }
                false
            }
            Predicate::Clause(Clause::Projection(p)) => {
                for t in &p.alias.args { if self.tcx.tys.has_infer(*t) { return true; } }
                match p.term { Term::Ty(t) | Term::Const(t) => self.tcx.tys.has_infer(t) }
            }
            Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), _) => self.tcx.tys.has_infer(*a) || self.tcx.tys.has_infer(*b),
            _ => false,
        }
    }

    fn evaluate(&mut self, graph: &mut SearchGraph, goal: Goal) -> Result<Certainty, NoSolution> {
        crate::preempt::point();
        let Some(_depth) = crate::tcx::Depth::enter_solver(self.cx.state) else { return Ok(Certainty::overflow(true)); };
        let goal = self.resolve_goal(goal);
        assert_eq!(goal.param_env.0, self.cx.typing_env.param_env.index());
        // Inference responses cannot be replayed until T2b2 canonicalizes them.
        if self.has_infer(&goal) {
            return self.compute_goal(graph, goal);
        }
        let id = match self.ids.get(&goal) {
            Some(id) => *id,
            None => {
                let id = self.goals.len() as u32;
                self.ids.insert(goal.clone(), id);
                self.goals.push(goal);
                id
            }
        };
        decode(graph.evaluate(self, id))
    }

    fn compute_goal(&mut self, graph: &mut SearchGraph, goal: Goal) -> Result<Certainty, NoSolution> {
        match goal.predicate {
            Predicate::Clause(Clause::Trait(predicate)) => match self.select(graph, &predicate) {
                SelectionResult::Ok(selected) => self.evaluate_nested(graph, &selected.nested),
                SelectionResult::Ambiguous(cause) => Ok(Certainty::Maybe(cause)),
                SelectionResult::NoSolution => Err(NoSolution),
            },
            Predicate::Clause(Clause::Projection(p)) => {
                let Term::Ty(value) = p.term else { return Err(NoSolution); };
                let projection = self.tcx.tys.intern(TyKind::Assoc(p.alias.def, p.alias.args, RegionArgsId::EMPTY));
                self.equate_alias(graph, projection, value)
            }
            Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), AliasRelationDirection::Equate) => self.equate_alias(graph, a, b),
            Predicate::Ambiguous => Ok(Certainty::Maybe(MaybeCause::Ambiguity)),
            _ => Ok(Certainty::Maybe(MaybeCause::Ambiguity)),
        }
    }

    fn evaluate_nested(&mut self, graph: &mut SearchGraph, nested: &[Goal]) -> Result<Certainty, NoSolution> {
        let mut pending = nested.to_vec();
        for _ in 0..128 {
            let mut next = Vec::new();
            let mut certainty = Certainty::Yes;
            for goal in pending {
                let goal = self.resolve_goal(goal);
                let result = self.evaluate(graph, goal.clone())?;
                if result != Certainty::Yes { next.push(goal); }
                certainty = certainty.and(result);
            }
            let mut progress = false;
            for goal in &mut next {
                let resolved = self.resolve_goal(goal.clone());
                progress |= resolved != *goal;
                *goal = resolved;
            }
            if next.is_empty() || !progress { return Ok(certainty); }
            pending = next;
        }
        Ok(Certainty::overflow(false))
    }

    fn select(&mut self, graph: &mut SearchGraph, predicate: &TraitPredicate) -> SelectionResult {
        let mut predicate = predicate.clone();
        for a in &mut predicate.trait_ref.args { *a = self.infcx.resolve_deep(*a); }
        let mut unresolved_projection = None;
        let mut normalization_goals = Vec::new();
        for arg in &mut predicate.trait_ref.args {
            if matches!(self.tcx.tys.kind(*arg), TyKind::Assoc(..)) {
                match self.normalize_alias(graph, *arg) {
                    Ok((value, Certainty::Yes)) => *arg = value,
                    Ok((_, Certainty::Maybe(cause @ MaybeCause::Overflow { .. }))) => return SelectionResult::Ambiguous(cause),
                    Ok((value, Certainty::Maybe(cause))) => {
                        unresolved_projection = Some(cause);
                        if value != *arg {
                            // A known projected type guides impl indexing even if
                            // its nested obligations still await closure inference.
                            // Preserve that proof (traits/project.rs:377-406).
                            normalization_goals.push(Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::AliasRelate(Term::Ty(*arg), Term::Ty(value), AliasRelationDirection::Equate) });
                            *arg = value;
                        }
                    }
                    Err(_) => {}
                }
            }
        }
        let tr = &predicate.trait_ref;
        let Some(&self_ty) = tr.args.first() else { return SelectionResult::NoSolution; };
        // candidate_assembly.rs:43: unresolved Self cannot guide candidate assembly.
        if let TyKind::Infer(v) = self.tcx.tys.kind(self_ty) {
            if self.infcx.ty_variable(*v).kind == TyVariableKind::General || self.is_auto(tr.def) {
                // candidate_assembly.rs:807: numeric auto-trait goals also stall.
                return SelectionResult::Ambiguous(MaybeCause::Ambiguity);
            }
        }
        if self.tcx.callable_trait(tr.def) {
            if let TyKind::Closure(file, expr, _, _, owner) = self.tcx.tys.kind(self_ty) {
                let once = matches!(self.tcx.lang_items.by_def.get(&tr.def), Some(LangItem::FnOnce | LangItem::AsyncFnOnce));
                let epoch = self.tcx.collect_epoch.load(std::sync::atomic::Ordering::Relaxed);
                let _ = epoch;
                if !once && crate::upvar::ensure_closure_captures(self.cx, self.tcx, *file, *expr, *owner).is_none() {
                    return SelectionResult::Ambiguous(MaybeCause::Ambiguity);
                }
            }
        }
        if self.is_auto(tr.def) {
            if let TyKind::Closure(file, expr, _, _, owner) = self.tcx.tys.kind(self_ty) {
                // candidate_assembly.rs:825: retain the original goal for retry,
                // rather than confirming a candidate with a bare Ambiguous goal.
                if crate::upvar::ensure_closure_captures(self.cx, self.tcx, *file, *expr, *owner).is_none() {
                    return SelectionResult::Ambiguous(MaybeCause::Ambiguity);
                }
            }
        }
        let candidates = self.assemble(&predicate);
        let mut viable = Vec::new();
        for c in candidates {
            let mark = self.infcx.snapshot();
            let matched = self.confirm(&predicate, &c);
            self.infcx.rollback(mark);
            if matched.is_some() { viable.push(c); }
        }
        let mut unresolved = Certainty::Maybe(MaybeCause::Ambiguity);
        if viable.len() > 1 {
            let mut evaluated = Vec::new();
            for c in viable {
                let mark = self.infcx.snapshot();
                // a selection nested in a candidate's evaluation without a goal of its own (the
                // projection of an argument, normalize_alias -> select) runs on the same stack
                // entry: its head usages are the enclosing candidate's (rustc evaluates every
                // nested goal on a new entry, so its candidates never nest on one)
                let track = !graph.is_empty() && !graph.in_single_candidate();
                if track { graph.enter_single_candidate(); }
                let result = match self.confirm(&predicate, &c) {
                    Some(selected) => self.evaluate_nested(graph, &selected.nested),
                    None => Err(NoSolution),
                };
                if track {
                    let usages = graph.finish_single_candidate();
                    if result.is_err() { graph.ignore_candidate_head_usages(usages); }
                }
                self.infcx.rollback(mark);
                if let Ok(certainty) = result { unresolved = unresolved.and(certainty); evaluated.push((c, certainty)); }
            }
            viable = self.winnow(&predicate, evaluated);
        }
        match viable.len() {
            0 => match unresolved_projection { Some(cause) => SelectionResult::Ambiguous(cause), None => SelectionResult::NoSolution },
            1 => match self.confirm(&predicate, &viable[0]) {
                Some(mut selected) => {
                    selected.nested.extend(normalization_goals);
                    SelectionResult::Ok(selected)
                },
                None => SelectionResult::NoSolution,
            },
            _ => SelectionResult::Ambiguous(match unresolved { Certainty::Maybe(cause) => cause, Certainty::Yes => MaybeCause::Ambiguity }),
        }
    }

    fn confirm(&mut self, predicate: &TraitPredicate, candidate: &Candidate) -> Option<Selected> {
        let mark = self.infcx.snapshot();
        let mut nested = candidate.nested.clone();
        let mut args = candidate.args.clone();
        let tr = match candidate.source {
            CandidateSource::Impl(imp) => {
                let n = self.tcx.impl_generics.get(&imp).map_or(0, |e| e.names.len());
                args.clear();
                for _ in 0..n { args.push(self.infcx.fresh_ty(TyVariableKind::General)); }
                let pat = *self.tcx.impl_self.get(&imp)?;
                let mut all = vec![self.tcx.tys.subst(pat, &args)];
                if let Some(ta) = self.tcx.impl_trait_args.get(&imp) {
                    for t in ta { all.push(self.tcx.tys.subst(*t, &args)); }
                }
                Some(TraitRef { def: predicate.trait_ref.def, args: all })
            }
            _ => candidate.trait_ref.clone(),
        };
        if let Some(tr) = tr {
            if tr.def != predicate.trait_ref.def || tr.args.len() != predicate.trait_ref.args.len() { return None; }
            for i in 0..tr.args.len() {
                if !self.infcx.relate(tr.args[i], predicate.trait_ref.args[i]) { return None; }
            }
        }
        if let CandidateSource::Impl(imp) = candidate.source {
            nested.extend(self.impl_goals(imp, &args));
        }
        for (a, b) in self.infcx.take_relations_since(mark) {
            nested.push(Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), AliasRelationDirection::Equate) });
        }
        for a in &mut args { *a = self.infcx.resolve_deep(*a); }
        Some(Selected { source: candidate.source, args, nested })
    }

    fn candidate(&self, source: CandidateSource, tr: Option<TraitRef>) -> Candidate {
        Candidate { source, trait_ref: tr, nested: Vec::new(), args: Vec::new(), global: false, sized: false }
    }

    fn assemble(&mut self, predicate: &TraitPredicate) -> Vec<Candidate> {
        let tr = &predicate.trait_ref;
        let ty = tr.args[0];
        let mut candidates = Vec::new();
        let key = ty_key(&self.tcx.tys, ty);
        let mut keys = if key == TyKey::Other { vec![key] } else { vec![key, TyKey::Other] };
        // An integer/float variable may match any impl of its numeric kind.
        // rustc_middle/src/ty/trait_def.rs:for_each_relevant_impl.
        if let TyKind::Infer(v) = self.tcx.tys.kind(ty) {
            let kind = self.infcx.ty_variable(*v).kind;
            // the primitive keys of this trait's impls: a lookup per primitive, not a pass
            // over every trait impl key (a restored table decodes what it visits)
            for (_, prim) in crate::program::PRIMS {
                let candidate = TyKey::Prim(prim);
                if !self.tcx.trait_impls.contains_key(&(candidate, tr.def)) { continue; }
                let matches = match self.tcx.tys.kind(self.tcx.tys.prim(prim)) {
                    TyKind::Int(_) => kind == TyVariableKind::Int,
                    TyKind::Float(_) => kind == TyVariableKind::Float,
                    _ => false,
                };
                if matches && !keys.contains(&candidate) { keys.push(candidate); }
            }
        }
        for key in keys {
            if let Some(impls) = self.tcx.trait_impls.get(&(key, tr.def)) {
                for &imp in impls {
                    let d = self.cx.prog.def(imp);
                    let negative = matches!(self.cx.prog.files[d.file as usize].ast.item(d.item).kind, ItemKind::Impl { negative: true, .. });
                    if negative != (predicate.polarity == PredicatePolarity::Negative) { continue; }
                    candidates.push(self.candidate(CandidateSource::Impl(imp), None));
                }
            }
        }
        if predicate.polarity == PredicatePolarity::Negative { return candidates; }
        if let Some(env) = self.tcx.param_env(self.cx.typing_env.param_env) {
            let mut seen = Vec::new();
            for (index, (ty, def, args)) in env.preds.iter().enumerate() {
                if *def != tr.def { continue; }
                let mut all = vec![*ty]; all.extend_from_slice(args);
                let bound = TraitRef { def: *def, args: all };
                if seen.contains(&bound) { continue; }
                seen.push(bound.clone());
                let mut c = self.candidate(CandidateSource::ParamEnv(index as u32), Some(bound.clone()));
                c.global = true;
                for a in &bound.args { if self.tcx.has_param(*a) || self.tcx.tys.has_infer(*a) { c.global = false; } }
                candidates.push(c);
            }
        }
        let bounds = match self.tcx.tys.kind(ty).clone() {
            TyKind::Assoc(def, args, _) => self.tcx.assoc_decl_bounds(self.cx, self.cx.prog, def, &args),
            TyKind::Opaque(def, index, args, _) => {
                let mut bounds = Vec::new();
                if let Some(decl) = self.tcx.opaques.get(&(def, index)) {
                    for (d, a) in decl.bounds {
                        let mut b = Vec::new();
                        for t in a { b.push(self.tcx.tys.subst(t, &args)); }
                        bounds.push((d, b));
                    }
                }
                bounds
            }
            TyKind::Dyn(def, args, _, _, _, _, autos) => {
                let mut bounds = vec![(def, args.to_vec())];
                for ad in autos { if ad != def { bounds.push((ad, Vec::new())); } }
                bounds
            },
            _ => Vec::new(),
        };
        let object = matches!(self.tcx.tys.kind(ty), TyKind::Dyn(..));
        let mut todo = bounds;
        let mut seen = Vec::new();
        while let Some((def, args)) = todo.pop() {
            if seen.contains(&(def, args.clone())) { continue; }
            seen.push((def, args.clone()));
            if def == tr.def {
                let mut all = vec![ty]; all.extend_from_slice(&args);
                let source = if object { CandidateSource::BuiltinImpl(BuiltinImplKind::Object(seen.len() as u32 - 1)) } else { CandidateSource::AliasBound };
                candidates.push(self.candidate(source, Some(TraitRef { def, args: all })));
            }
            todo.extend(self.tcx.trait_super_refs_of(self.cx, self.cx.prog, def, ty, &args));
        }
        self.assemble_builtin(predicate, &mut candidates);
        // assembly/mod.rs:470-497: impls (and object bounds) are not assembled when a
        // non-global where-bound or an alias bound applies without constraining anything;
        // they would be shadowed by it in winnowing, and evaluating them can recurse back
        // into this goal (`U: IntoIterator` -> `impl<I: Iterator> IntoIterator for I` ->
        // `U: Iterator` -> `<U as IntoIterator>::IntoIter == U` -> `U: IntoIterator`).
        let shadowed = candidates.iter().any(|c| {
            let applies = match c.source {
                CandidateSource::ParamEnv(_) => !c.global,
                CandidateSource::AliasBound => true,
                _ => false,
            };
            applies && c.nested.is_empty() && c.trait_ref.as_ref().is_some_and(|b| {
                b.def == tr.def && b.args.len() == tr.args.len()
                    && b.args.iter().zip(&tr.args).all(|(a, b)| self.tcx.tys.eq_mod_regions(*a, *b))
            })
        });
        if shadowed {
            candidates.retain(|c| !matches!(c.source, CandidateSource::Impl(_) | CandidateSource::BuiltinImpl(BuiltinImplKind::Object(_))));
        }
        candidates
    }

    // Stable solver preference is deliberately narrower than unconditional
    // where-clause priority: select/mod.rs:1872-2022.
    fn winnow(&self, predicate: &TraitPredicate, candidates: Vec<(Candidate, Certainty)>) -> Vec<Candidate> {
        if candidates.len() <= 1 { return candidate_sources(candidates); }
        for (c, certainty) in &candidates {
            if c.sized {
                if *certainty == Certainty::Yes { return vec![c.clone()]; }
                return candidate_sources(candidates);
            }
        }
        let mut infer = false;
        for a in &predicate.trait_ref.args { infer |= self.tcx.tys.has_infer(*a); }
        if self.is_auto(predicate.trait_ref.def) || self.tcx.lang_items.get(LangItem::Sized) == Some(predicate.trait_ref.def) {
            let mut aliases = Vec::new();
            for (c, _) in &candidates { if c.source == CandidateSource::AliasBound { aliases.push(c.clone()); } }
            if !aliases.is_empty() { if !infer { aliases.truncate(1); } return aliases; }
        }
        let mut non_global = Vec::new();
        let mut global = false;
        for (c, _) in &candidates {
            if matches!(c.source, CandidateSource::ParamEnv(_)) {
                if c.global { global = true; } else { non_global.push(c.clone()); }
            }
        }
        if !non_global.is_empty() {
            if global { return candidate_sources(candidates); }
            return non_global;
        }
        let mut alias = Vec::new();
        let mut object = Vec::new();
        for (c, _) in &candidates {
            if c.source == CandidateSource::AliasBound { alias.push(c.clone()); }
            if matches!(c.source, CandidateSource::BuiltinImpl(BuiltinImplKind::Object(_))) { object.push(c.clone()); }
        }
        if !alias.is_empty() { if !infer { alias.truncate(1); } return alias; }
        if !object.is_empty() && !infer { object.truncate(1); return object; }
        let mut remaining = Vec::new();
        for (c, _) in &candidates {
            if !(matches!(c.source, CandidateSource::ParamEnv(_)) && c.global) { remaining.push(c.clone()); }
        }
        if remaining.len() == 1 { return remaining; }
        candidate_sources(candidates)
    }

    fn is_auto(&self, def: DefId) -> bool {
        let d = self.cx.prog.def(def);
        matches!(self.cx.prog.files[d.file as usize].ast.item(d.item).kind, ItemKind::Trait { auto: true, .. })
    }

    fn assemble_builtin(&self, predicate: &TraitPredicate, candidates: &mut Vec<Candidate>) {
        let tr = &predicate.trait_ref;
        let ty = tr.args[0];
        let kind = self.tcx.tys.kind(ty);
        let sized = self.tcx.lang_items.get(LangItem::Sized) == Some(tr.def);
        let copy_clone = Some(tr.def) == self.tcx.copy_trait || Some(tr.def) == self.tcx.clone_trait;
        let mut c = self.candidate(CandidateSource::BuiltinImpl(BuiltinImplKind::Misc), None);
        c.sized = sized;
        let mut parts = Vec::new();
        let mut applies = false;
        if self.tcx.callable_trait(tr.def) {
            let signature = match kind {
                TyKind::FnPtr(_, _, header, _) if header.is_fn_trait_compatible() => Some(ty),
                TyKind::FnDef(def, args, _) => self.tcx.fn_item_sig(self.cx.prog, *def).and_then(|sig| {
                    if !sig.header.is_fn_trait_compatible() { return None; }
                    let d = self.cx.prog.def(*def);
                    let attrs = self.cx.prog.files[d.file as usize].ast.item(d.item).attrs;
                    if crate::lang_items::has_attr(self.cx.prog, d.file, self.cx.prog.files[d.file as usize].ast.list(attrs), "target_feature") { return None; }
                    let mut ps = Vec::new();
                    for p in &sig.params { ps.push(self.tcx.tys.subst_for_inference(*p, args)); }
                    Some(self.tcx.tys.intern(TyKind::FnPtr(ps, self.tcx.tys.subst_for_inference(sig.ret, args), sig.header, 0)))
                }),
                TyKind::Closure(file, expr, signature, _, owner) if !self.tcx.is_coroutine(ty) => {
                    use crate::upvar::ClosureKind;
                    let required = match self.tcx.lang_items.by_def.get(&tr.def) {
                        Some(LangItem::Fn | LangItem::AsyncFn) => ClosureKind::Fn,
                        Some(LangItem::FnMut | LangItem::AsyncFnMut) => ClosureKind::FnMut,
                        _ => ClosureKind::FnOnce,
                    };
                    match crate::upvar::ensure_closure_captures(self.cx, self.tcx, *file, *expr, *owner) {
                        Some(captures) if captures.kind <= required => Some(*signature),
                        Some(_) => None,
                        None if required == ClosureKind::FnOnce => Some(*signature),
                        None => None
                    }
                }
                _ => None,
            };
            if let Some(sig) = signature {
                let sig = self.tcx.tys.erase_all_regions(sig);
                if let TyKind::FnPtr(ps, ret, _, _) = self.tcx.tys.kind(sig) {
                    c.trait_ref = Some(TraitRef { def: tr.def, args: vec![ty, self.tcx.tys.intern(TyKind::Tuple(ps.clone()))] });
                    if let Some(sized) = self.tcx.lang_items.get(LangItem::Sized) { c.nested.push(self.goal(sized, *ret, &[])); }
                    // confirmation.rs:833-889: AsyncFn additionally requires Future.
                    if self.tcx.async_callable_trait(tr.def) {
                        let Some(future) = self.tcx.lang_items.get(LangItem::Future) else { return; };
                        c.nested.push(self.goal(future, *ret, &[]));
                    }
                    candidates.push(c);
                }
            }
            return;
        }
        if self.tcx.lang_items.get(LangItem::Tuple) == Some(tr.def) {
            if matches!(kind, TyKind::Tuple(_)) { candidates.push(c); }
            return;
        }
        if sized {
            applies = true;
            match kind {
                TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..) | TyKind::Param(_) | TyKind::Assoc(..) | TyKind::Opaque(..) | TyKind::Bound(..) | TyKind::Placeholder(_) => applies = false,
                TyKind::Tuple(v) => parts.extend_from_slice(v),
                TyKind::Adt(d, args, _) => {
                    if let Some(adt) = self.tcx.adts.get(d) {
                        if !adt.is_enum && !adt.is_union {
                            if let Some(field) = adt.variants.first().and_then(|v| v.fields.last()) {
                                parts.push(self.tcx.tys.subst(field.ty, args));
                            }
                        }
                    }
                }
                TyKind::Infer(v) => {
                    if self.infcx.ty_variable(*v).kind == TyVariableKind::General {
                        c.nested.push(Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::Ambiguous });
                    }
                },
                _ => {}
            }
        } else if copy_clone {
            match kind {
                // Primitive, reference and array impls belong to core, as in
                // candidate_assembly.rs:1139. Fn and tuple impls are builtin.
                TyKind::FnPtr(..) | TyKind::FnDef(..) | TyKind::Error => applies = true,
                TyKind::Tuple(v) => { applies = true; parts.extend_from_slice(v); }
                TyKind::Closure(_, _, _, up, _) if !self.tcx.is_coroutine(ty) => {
                    applies = true;
                    parts.push(*up);
                }
                _ => {}
            }
        } else if self.tcx.is_coroutine(ty) && self.tcx.lang_items.get(LangItem::Future) == Some(tr.def) {
            applies = true;
        } else if self.is_auto(tr.def) {
            // Explicit impls suppress the structural auto candidate; negative
            // impls suppress it too (candidate_assembly.rs auto-candidate rule).
            let key = ty_key(&self.tcx.tys, ty);
            let explicit = self.tcx.trait_impls.get(&(key, tr.def)).map_or(false, |v| !v.is_empty())
                || self.tcx.trait_impls.get(&(TyKey::Other, tr.def)).map_or(false, |v| !v.is_empty());
            if !explicit {
                applies = true;
                match kind {
                    TyKind::Tuple(v) => parts.extend_from_slice(v),
                    TyKind::Array(t, _) | TyKind::Slice(t) | TyKind::Ref(_, t, _) | TyKind::Ptr(_, t) => parts.push(*t),
                    TyKind::Adt(d, args, _) => {
                        if let Some(adt) = self.tcx.adts.get(d) {
                            for v in &adt.variants { for f in &v.fields { parts.push(self.tcx.tys.subst(f.ty, args)); } }
                        }
                    }
                    TyKind::Closure(file, expr, _, _, owner) => {
                        // select/mod.rs:2383-2399: auto traits use minimum-capture
                        // types, not the enclosing roots retained by lowering.
                        // Plan M2b (arch-scope) supplies the coroutine interior
                        // witness. Until then, published upvars alone determine
                        // coroutine auto traits (round 8's known accept-more gap).
                        let epoch = self.tcx.collect_epoch.load(std::sync::atomic::Ordering::Relaxed);
                        let captures = self.tcx.closure_capture_types.get(&(*file, *expr, *owner, epoch))
                            .expect("closure captures checked before candidate assembly");
                        parts.push(captures.upvars);
                    }
                    TyKind::Opaque(..) => {
                        // candidate_assembly.rs:841-863; select/mod.rs:2427-2440:
                        // only auto traits leak to the hidden type. An explicit
                        // opaque bound needs no hidden-type query.
                        if candidates.iter().any(|c| c.source == CandidateSource::AliasBound) {
                            applies = false;
                        } else if let Some(hidden) = self.tcx.opaque_hidden.get(&ty) {
                            parts.push(hidden);
                        } else {
                            let mut requests = self.cx.state.opaque_requests.borrow_mut();
                            if !requests.contains(&ty) { requests.push(ty); }
                            c.nested.push(Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::Ambiguous });
                        }
                    }
                    TyKind::Param(_) | TyKind::Assoc(..) | TyKind::Dyn(..) | TyKind::Bound(..) | TyKind::Placeholder(_) => applies = false,
                    TyKind::Infer(_) => c.nested.push(Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::Ambiguous }),
                    _ => {}
                }
            }
        }
        if applies {
            for part in parts { c.nested.push(self.goal(tr.def, part, &[])); }
            candidates.push(c);
        }
        if let TyKind::Adt(d, args, _) = kind {
            if self.tcx.derived.contains_key(&(*d, tr.def)) {
                let mut header = vec![ty];
                header.extend(self.tcx.fill_trait_defaults(self.cx, self.cx.prog, tr.def, ty, Vec::new()));
                let mut derived = self.candidate(CandidateSource::BuiltinImpl(BuiltinImplKind::Derived), Some(TraitRef { def: tr.def, args: header }));
                derived.args = args.clone();
                for arg in args {
                    if matches!(self.tcx.tys.kind(*arg), TyKind::ConstVal(_)) { continue; }
                    let defaults = self.tcx.fill_trait_defaults(self.cx, self.cx.prog, tr.def, *arg, Vec::new());
                    derived.nested.push(self.goal(tr.def, *arg, &defaults));
                }
                candidates.push(derived);
            }
        }
    }

    /// Lower every written predicate, including composite where-clause Self
    /// types, callable Output equalities, and implicit Sized bounds.
    fn impl_goals(&self, imp: DefId, args: &[TyId]) -> Vec<Goal> {
        let prog = self.cx.prog;
        let def = prog.def(imp);
        let ast = &prog.files[def.file as usize].ast;
        let Some(env) = self.tcx.impl_generics.get(&imp) else { return Vec::new(); };
        let ItemKind::Impl { generics, .. } = ast.item(def.item).kind else { return Vec::new(); };
        let mut out = Vec::new();
        let mut index = 0;
        for p in ast.list(generics.params) {
            match p.kind {
                GenericParamKind::Lifetime(_) => continue,
                GenericParamKind::Type(bounds, _) => {
                    if let Some(&ty) = args.get(index) {
                        let mut maybe_sized = false;
                        for bound in ast.list(bounds) {
                            if matches!(bound, Bound::Trait { maybe: true, .. }) { maybe_sized = true; }
                            self.lower_bound(imp, env, args, ty, *bound, &mut out);
                        }
                        for w in ast.list(generics.where_) {
                            if let WherePred::Bound { ty: wt, bounds, .. } = *w {
                                let wty = self.tcx.lower_ty(self.cx, prog, def.file, def.scope, env, wt);
                                if wty == self.tcx.tys.intern(TyKind::Param(index as u32)) {
                                    for b in ast.list(bounds) { maybe_sized |= matches!(b, Bound::Trait { maybe: true, .. }); }
                                }
                            }
                        }
                        if !maybe_sized {
                            if let Some(sized) = self.tcx.lang_items.get(LangItem::Sized) { out.push(self.goal(sized, ty, &[])); }
                        }
                    }
                }
                GenericParamKind::Const(..) => {}
            }
            index += 1;
        }
        for w in ast.list(generics.where_) {
            if let WherePred::Bound { ty, bounds, .. } = *w {

                let ty = self.tcx.lower_ty(self.cx, prog, def.file, def.scope, env, ty);
                let ty = self.tcx.tys.subst(ty, args);
                for bound in ast.list(bounds) { self.lower_bound(imp, env, args, ty, *bound, &mut out); }
            }
        }
        out
    }

    fn lower_bound(&self, imp: DefId, env: &crate::tcx::GenEnv, args: &[TyId], ty: TyId, bound: Bound, out: &mut Vec<Goal>) {
        let Bound::Trait { maybe: false, path, .. } = bound else { return; };

        let prog = self.cx.prog;
        let def = prog.def(imp);
        let ast = &prog.files[def.file as usize].ast;
        let Some(td) = self.tcx.resolve_type_path_def(prog, def.file, def.scope, &path) else { return; };
        if prog.def(td).kind != DefKind::Trait { return; }
        let written = self.tcx.lower_generic_args(self.cx, prog, def.file, def.scope, env, &path);
        let mut ta = Vec::new();
        for t in written { ta.push(self.tcx.tys.subst(t, args)); }
        let ta = self.tcx.fill_trait_defaults(self.cx, prog, td, ty, ta);
        out.push(self.goal(td, ty, &ta));
        if let Some(GenericArgs::Paren(_, ret)) = ast.segs(path.segs).last().and_then(|s| ast.gargs(s.args)) {
            if let Some(output) = self.tcx.callable_output(td) {
                let value = match ret { Some(t) => self.tcx.lower_ty(self.cx, prog, def.file, def.scope, env, *t), None => self.tcx.tys.unit };
                let value = self.tcx.tys.subst_for_inference(value, args);
                let mut pa = vec![ty]; pa.extend_from_slice(&ta);
                let projection = self.tcx.tys.intern(TyKind::Assoc(output, pa, RegionArgsId::EMPTY));
                out.push(Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::AliasRelate(Term::Ty(projection), Term::Ty(value), AliasRelationDirection::Equate) });
            }
        }
        if let Some(GenericArgs::Angle(bindings)) = ast.segs(path.segs).last().and_then(|s| ast.gargs(s.args)) {
            for b in ast.list(*bindings) {
                if let GenericArg::Binding(name, _, value) = b {
                    let symbol = prog.syms.get(prog.files[def.file as usize].text(*name)).unwrap_or(u32::MAX);
                    if let Some(ad) = self.tcx.trait_assoc(prog, td, symbol) {
                        let mut pa = vec![ty]; pa.extend_from_slice(&ta);
                        let projection = self.tcx.tys.intern(TyKind::Assoc(ad, pa, RegionArgsId::EMPTY));
                        let value = self.tcx.lower_ty(self.cx, prog, def.file, def.scope, env, *value);
                        let value = self.tcx.tys.subst(value, args);
                        out.push(Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::AliasRelate(Term::Ty(projection), Term::Ty(value), AliasRelationDirection::Equate) });
                    }
                }
            }
        }
    }

    fn trace_overflow(&self, ty: TyId) {
        if std::env::var_os("RELAX_TRACE_OVERFLOW").is_some() && !self.cx.state.overflow_traced.replace(true) {
            let owner = self.cx.state.typeck_inprog.borrow().last().copied();
            if let TyKind::Assoc(ad, args, _) = self.tcx.tys.kind(ty) {
                eprintln!("RELAX_TRACE_OVERFLOW alias={} args={:?} env={:?}", self.cx.prog.def_path(*ad), args, self.tcx.param_env(self.cx.typing_env.param_env));
            }
            eprintln!("RELAX_TRACE_OVERFLOW body={:?} projection={}",
                owner.map(|d| self.cx.prog.def_path(d)),
                crate::typeck::ty_to_string(false, self.cx.prog, self.tcx, ty));
        }
    }

    fn normalize_alias(&mut self, graph: &mut SearchGraph, ty: TyId) -> Result<(TyId, Certainty), NoSolution> {
        let Some(_depth) = crate::tcx::Depth::enter_solver(self.cx.state) else {
            self.trace_overflow(ty);
            return Ok((ty, Certainty::overflow(true)));
        };
        self.normalize_alias_inner(graph, ty)
    }

    fn normalize_alias_inner(&mut self, graph: &mut SearchGraph, ty: TyId) -> Result<(TyId, Certainty), NoSolution> {
        let (value, nested, certainty) = self.project_alias(graph, ty)?;
        let certainty = certainty.and(self.evaluate_nested(graph, &nested)?);
        if matches!(certainty, Certainty::Maybe(MaybeCause::Overflow { .. })) { return Ok((ty, certainty)); }
        let value = self.infcx.resolve_deep(value);
        // The selected associated value can itself be a projection. Normalize
        // it under the same recursion budget (traits/project.rs:377-392).
        if value != ty && matches!(self.tcx.tys.kind(value), TyKind::Assoc(..)) {
            let (value, nested_certainty) = self.normalize_alias(graph, value)?;
            return Ok((value, certainty.and(nested_certainty)));
        }
        Ok((value, certainty))
    }

    fn project_alias(&mut self, graph: &mut SearchGraph, ty: TyId) -> Result<(TyId, Vec<Goal>, Certainty), NoSolution> {
        let Some(_depth) = crate::tcx::Depth::enter_solver(self.cx.state) else {
            self.trace_overflow(ty);
            return Ok((ty, Vec::new(), Certainty::overflow(true)));
        };
        let (value, nested, certainty) = self.project_alias_inner(graph, ty)?;
        // PostAnalysis (codegen) normalization reveals opaque types (rustc
        // traits/normalize.rs AssocTypeNormalizer::fold_ty: `ty::Opaque` under
        // TypingMode::PostAnalysis folds `type_of(def).instantiate(args)`): `<fn item as
        // FnOnce<A>>::Output` of a fn returning `impl Trait` is its hidden type there, as the
        // revealed closure signatures and field types it is related to are
        if matches!(self.cx.typing_env.mode, crate::tcx::TypingMode::PostAnalysis) && self.tcx.tys.has_opaque(value) {
            return Ok((crate::typeck::reveal(self.cx, self.cx.prog, self.tcx, value), nested, certainty));
        }
        Ok((value, nested, certainty))
    }

    fn project_alias_inner(&mut self, graph: &mut SearchGraph, ty: TyId) -> Result<(TyId, Vec<Goal>, Certainty), NoSolution> {
        if let Some(env) = self.tcx.param_env(self.cx.typing_env.param_env) {
            for (a, b) in &env.eqs { if self.tcx.tys.eq_mod_regions(*a, ty) { return Ok((*b, Vec::new(), Certainty::Yes)); } }
        }
        match self.tcx.tys.kind(ty).clone() {
            TyKind::Assoc(ad, args, _) if !args.is_empty() => {
                let self_ty = self.infcx.resolve_deep(args[0]);
                match self.tcx.tys.kind(self_ty).clone() {
                    TyKind::Dyn(_, _, bindings, ..) => {
                        for (def, value, _) in bindings { if def == ad { return Ok((value, Vec::new(), Certainty::Yes)); } }
                    }
                    TyKind::Opaque(def, i, oa, _) => {
                        if let Some(decl) = self.tcx.opaques.get(&(def, i)) {
                            for (def, bound_args, value) in decl.bindings {
                                if def != ad || bound_args.len() + 1 != args.len() { continue; }
                                let mark = self.infcx.snapshot();
                                let mut matched = true;
                                for (a, b) in bound_args.iter().zip(&args[1..]) {
                                    matched &= self.infcx.relate(self.tcx.tys.subst_for_inference(*a, &oa), *b);
                                }
                                if matched { return Ok((self.tcx.tys.subst_for_inference(value, &oa), Vec::new(), Certainty::Yes)); }
                                self.infcx.rollback(mark);
                            }
                        }
                    }
                    TyKind::Assoc(def, ref pa, _) => {
                        let (_, eqs) = self.tcx.assoc_decl_bounds_eqs(self.cx, self.cx.prog, def, pa);
                        for (a, b) in eqs { if self.tcx.tys.eq_mod_regions(a, ty) { return Ok((b, Vec::new(), Certainty::Yes)); } }
                    }
                    TyKind::Closure(_, _, sig, _, _) if self.tcx.is_coroutine(self_ty)
                        && self.tcx.lang_items.get(LangItem::FutureOutput) == Some(ad) => {
                        if let TyKind::FnPtr(_, ret, _, _) = self.tcx.tys.kind(sig) { return Ok((*ret, Vec::new(), Certainty::Yes)); }
                    }
                    _ => {}
                }
                let owner = self.cx.prog.def(ad).parent;
                let predicate = TraitPredicate { trait_ref: TraitRef { def: owner, args }, polarity: PredicatePolarity::Positive };
                match self.select(graph, &predicate) {
                    SelectionResult::NoSolution => Err(NoSolution),
                    SelectionResult::Ambiguous(cause) => Ok((ty, Vec::new(), Certainty::Maybe(cause))),
                    SelectionResult::Ok(selected) => {
                        let certainty = Certainty::Yes;
                        if let CandidateSource::Impl(imp) = selected.source {
                            let name = self.cx.prog.def(ad).name;
                            if let Some(value) = self.tcx.impl_assoc_ty(self.cx, self.cx.prog, imp, name) {
                                let mut args = Vec::new();
                                for t in selected.args { args.push(self.infcx.resolve_deep(t)); }
                                return Ok((self.tcx.tys.subst_for_inference(value, &args), selected.nested, certainty));
                            }
                        }
                        if matches!(self.tcx.lang_items.by_def.get(&ad), Some(LangItem::FnOnceOutput | LangItem::AsyncFnOnceOutput | LangItem::CallOnceFuture)) {
                            let self_ty = predicate.trait_ref.args[0];
                            let output = match self.tcx.tys.kind(self_ty) {
                                TyKind::FnPtr(_, ret, _, _) => Some(*ret),
                                TyKind::FnDef(def, args, _) => self.tcx.fn_item_sig(self.cx.prog, *def).map(|sig| self.tcx.tys.subst_for_inference(sig.ret, args)),
                                TyKind::Closure(_, _, sig, _, _) => match self.tcx.tys.kind(*sig) { TyKind::FnPtr(_, ret, _, _) => Some(*ret), _ => None },
                                TyKind::Dyn(_, _, bindings, ..) => bindings.iter().find(|b| b.0 == ad).map(|b| b.1),
                                TyKind::Opaque(def, i, args, _) => self.tcx.opaques.get(&(*def, *i)).and_then(|d| d.bindings.iter().find(|b| b.0 == ad).map(|b| self.tcx.tys.subst_for_inference(b.2, args))),
                                _ => None,
                            };
                            if let Some(output) = output {
                                if self.tcx.lang_items.get(LangItem::AsyncFnOnceOutput) == Some(ad) {
                                    let Some(future_output) = self.tcx.lang_items.get(LangItem::FutureOutput) else { return Err(NoSolution); };
                                    let projection = self.tcx.tys.intern(TyKind::Assoc(future_output, vec![output], RegionArgsId::EMPTY));
                                    let (value, mut nested, certainty) = self.project_alias(graph, projection)?;
                                    nested.extend(selected.nested);
                                    return Ok((value, nested, certainty));
                                }
                                return Ok((output, selected.nested, certainty));
                            }
                        }
                        // Proven via a where-bound and no projection bound in the environment
                        // (env.eqs above): the alias is rigid, as in normalizes_to
                        // (assembly/mod.rs:1236-1246, inject_normalize_to_rigid_candidate).
                        if matches!(selected.source, CandidateSource::ParamEnv(_)) && !predicate.trait_ref.args.iter().any(|a| self.tcx.tys.has_infer(*a)) {
                            return Ok((ty, selected.nested, certainty));
                        }
                        Ok((ty, selected.nested, certainty.and(Certainty::Maybe(MaybeCause::Ambiguity))))
                    }
                }
            }
            TyKind::Opaque(..) => match self.tcx.opaque_hidden.get(&ty) {
                Some(hidden) => Ok((hidden, Vec::new(), Certainty::Yes)),
                None => Ok((ty, Vec::new(), Certainty::Maybe(MaybeCause::Ambiguity))),
            },
            _ => Ok((ty, Vec::new(), Certainty::Yes)),
        }
    }

    fn equate_alias(&mut self, graph: &mut SearchGraph, a: TyId, b: TyId) -> Result<Certainty, NoSolution> {
        if self.tcx.tys.eq_mod_regions(a, b) { return Ok(Certainty::Yes); }
        // the projections first, an opaque type's hidden type only when the two sides still
        // differ: an opaque type equals itself in every typing mode, while its hidden type
        // is known only once its defining body was checked (opaque_hidden). Revealing one
        // side alone made `<fn item as FnOnce<A>>::Output == impl Iterator` (the fn returns
        // that opaque) fail exactly when the hidden type was already known: Stage's
        // `groups.iter().flat_map(TermGroup::all).enumerate()` E0599, depending on check order.
        // (each side is projected one step, as before: an opaque type a projection yields
        // stays opaque)
        let (oa, ob) = (matches!(self.tcx.tys.kind(a), TyKind::Opaque(..)), matches!(self.tcx.tys.kind(b), TyKind::Opaque(..)));
        let (a0, b0) = (a, b);
        let (mut a, mut nested, mut certainty) = if oa { (a, Vec::new(), Certainty::Yes) } else { self.project_alias(graph, a)? };
        let mut b = b;
        if !ob {
            let (pb, other, cb) = self.project_alias(graph, b)?;
            b = pb;
            nested.extend(other);
            certainty = certainty.and(cb);
        }
        if certainty == Certainty::Yes && !self.tcx.tys.eq_mod_regions(a, b) {
            for (t, was_opaque) in [(&mut a, oa), (&mut b, ob)] {
                if was_opaque {
                    let (pt, other, ct) = self.project_alias(graph, *t)?;
                    *t = pt;
                    nested.extend(other);
                    certainty = certainty.and(ct);
                }
            }
        }
        if certainty != Certainty::Yes { return Ok(certainty); }
        let mark = self.infcx.snapshot();
        // an alias its projection left unchanged is rigid
        let rigid = |t: TyId, t0: TyId| t == t0 && matches!(self.tcx.tys.kind(t), TyKind::Assoc(..));
        let related = if rigid(a, a0) || rigid(b, b0) { self.infcx.relate_rigid(a, b) } else { self.infcx.relate(a, b) };
        if !related { return Err(NoSolution); }
        let relations = self.infcx.take_relations_since(mark);
        // Relate the projected value before fulfilling its obligations: the
        // equality can determine the output variable required by Sized.
        // rustc_trait_selection/src/traits/project.rs:262-282.
        let mut certainty = self.evaluate_nested(graph, &nested)?;
        for (a, b) in relations {
            let goal = Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()), predicate: Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), AliasRelationDirection::Equate) };
            certainty = certainty.and(self.evaluate(graph, goal)?);
        }
        Ok(certainty)
    }
}

fn encode(result: Result<Certainty, NoSolution>) -> u32 {
    match result {
        Err(_) => 0,
        Ok(Certainty::Yes) => 1,
        Ok(Certainty::Maybe(MaybeCause::Ambiguity)) => 2,
        Ok(Certainty::Maybe(MaybeCause::Overflow { suggest_increasing_limit: true, .. })) => 3,
        Ok(Certainty::Maybe(MaybeCause::Overflow { .. })) => 4,
    }
}

fn decode(result: u32) -> Result<Certainty, NoSolution> {
    match result {
        0 => Err(NoSolution), 1 => Ok(Certainty::Yes),
        2 => Ok(Certainty::Maybe(MaybeCause::Ambiguity)),
        3 => Ok(Certainty::overflow(true)), 4 => Ok(Certainty::overflow(false)),
        _ => unreachable!(),
    }
}

impl SearchGraphDelegate for Evaluation<'_, '_> {
    fn can_cache_global(&self, _: u32, result: u32) -> bool { result <= 1 }
    fn is_coinductive(&self, input: u32) -> bool {
        match &self.goals[input as usize].predicate {
            Predicate::Clause(Clause::Trait(t)) => self.is_auto(t.trait_ref.def) || self.tcx.lang_items.get(LangItem::Sized) == Some(t.trait_ref.def),
            _ => false,
        }
    }
    fn initial_provisional_result(&mut self, kind: PathKind, _: u32) -> u32 {
        match kind { PathKind::Inductive => 0, PathKind::Coinductive => 1, _ => 2 }
    }
    fn is_initial_provisional_result(&self, result: u32) -> Option<PathKind> {
        match result { 0 => Some(PathKind::Inductive), 1 => Some(PathKind::Coinductive), 2 => Some(PathKind::Unknown), _ => None }
    }
    fn stack_overflow_result(&mut self, _: u32) -> u32 { 3 }
    fn fixpoint_overflow_result(&mut self, _: u32) -> u32 { 4 }
    fn is_ambiguous_result(&self, result: u32) -> Option<u32> { if result >= 2 { Some(result) } else { None } }
    fn propagate_ambiguity(&mut self, _: u32, ambiguity: u32) -> u32 { ambiguity }
    fn compute(&mut self, graph: &mut SearchGraph, input: u32) -> u32 {
        let goal = self.goals[input as usize].clone();
        encode(self.compute_goal(graph, goal))
    }
}

/// Fulfilled selection at a dispatch boundary. Property callers must retain
/// NoSolution as an ordinary negative answer; only the dispatch owner may ICE.
/// rustc_traits/src/codegen.rs:40-46.
pub fn select_fulfilled(tcx: &Tcx, cx: &EvalCx<'_>, infcx: &mut dyn InferDelegate, predicate: TraitPredicate) -> SelectionResult {
    let mut graph = SearchGraph::new(SearchGraphConfig::default());
    let mut ecx = Evaluation::new(tcx, cx, infcx);
    let mut selected = match ecx.select(&mut graph, &predicate) {
        SelectionResult::Ok(selected) => selected,
        other => return other,
    };
    match ecx.evaluate_nested(&mut graph, &selected.nested) {
        Err(_) => SelectionResult::NoSolution,
        Ok(Certainty::Maybe(cause)) => SelectionResult::Ambiguous(cause),
        Ok(Certainty::Yes) => {
            for arg in &mut selected.args {
                *arg = ecx.infcx.resolve_deep(*arg);
            }
            selected.nested = selected.nested.into_iter().map(|goal| ecx.resolve_goal(goal)).collect();
            SelectionResult::Ok(selected)
        }
    }
}

#[cfg(test)]
mod tests;

fn candidate_sources(candidates: Vec<(Candidate, Certainty)>) -> Vec<Candidate> {
    let mut out = Vec::new();
    for (candidate, _) in candidates { out.push(candidate); }
    out
}

pub fn impl_goals(tcx: &Tcx, cx: &EvalCx<'_>, infcx: &mut dyn InferDelegate, imp: DefId, args: &[TyId]) -> Vec<Goal> {
    Evaluation::new(tcx, cx, infcx).impl_goals(imp, args)
}

pub fn normalize_projection(tcx: &Tcx, cx: &EvalCx<'_>, infcx: &mut dyn InferDelegate, ty: TyId) -> Result<(TyId, Certainty), NoSolution> {
    let mut graph = SearchGraph::new(SearchGraphConfig::default());
    Evaluation::new(tcx, cx, infcx).normalize_alias(&mut graph, ty)
}

/// Projection result and obligations stay together until the caller can fulfill them.
pub fn project(tcx: &Tcx, cx: &EvalCx<'_>, infcx: &mut dyn InferDelegate, ty: TyId) -> Result<(TyId, Vec<Goal>, Certainty), NoSolution> {
    let mut graph = SearchGraph::new(SearchGraphConfig::default());
    Evaluation::new(tcx, cx, infcx).project_alias(&mut graph, ty)
}
