//! Written regions during type lowering. Bodies retain region payloads while
//! inference compares erased keys; borrowck is responsible for region constraints.
use super::*;
use crate::types::BoundVar;
use std::sync::{Arc, atomic::{AtomicU32, Ordering}};

#[derive(Clone, Default)]
pub struct RegionEnv {
    pub enabled: bool,
    /// Indices are in the complete generics list (including parent, type and const
    /// parameters), although RegionArgs stores only its lifetime entries.
    pub names: Vec<(String, RegionKind)>,
    pub next_param: u32,
    /// Full indices allocated for elided impl-header lifetimes. They have no
    /// source name but are inherited generic parameters of the impl's methods.
    pub(crate) anonymous_params: Vec<u32>,
    pub static_elision: bool,
    pub object_default: Option<RegionId>,
    fresh: Option<Arc<AtomicU32>>,
    early_fresh: bool,
    infer_fresh: bool,
    /// A trait binder binds its written parameters, but does not introduce
    /// anonymous lifetime parameters. Those resolve in the surrounding scope.
    elision_parent: Option<Box<RegionEnv>>,
    output: Option<RegionId>,
    uses: Option<Arc<std::sync::Mutex<Vec<RegionKind>>>>,
    refs: Option<Arc<std::sync::Mutex<Vec<(u32, ast::TyId, RegionId)>>>>,
}

crate::collected_fields!(RegionEnv, enabled, names, next_param, anonymous_params,
    static_elision, object_default, fresh, early_fresh, infer_fresh, elision_parent,
    output, uses, refs);

impl RegionEnv {
    /// Elision inside a body creates inference regions, not bound parameters.
    pub(crate) fn enter_body(&mut self, fresh: Arc<AtomicU32>) {
        self.enabled = true;
        self.static_elision = false;
        self.output = None;
        self.object_default = None;
        self.elision_parent = None;
        self.uses = None;
        self.refs = None;
        self.early_fresh = false;
        self.infer_fresh = true;
        self.fresh = Some(fresh);
    }

    pub fn identity_args(&self, tys: &Types) -> RegionArgsId {
        if !self.enabled { return RegionArgsId::EMPTY; }
        tys.intern_region_args(&self.names.iter().filter_map(|(_, r)| {
            matches!(r, RegionKind::ReEarlyParam(_)).then(|| tys.intern_region(*r))
        }).collect::<Vec<_>>())
    }

    pub fn impl_elision(&mut self) {
        self.fresh = Some(Arc::new(AtomicU32::new(self.next_param)));
        self.early_fresh = true;
    }

    pub fn finish_impl_elision(&mut self) {
        if let Some(n) = self.fresh.take() {
            let end = n.load(Ordering::Relaxed);
            self.anonymous_params.extend(self.next_param..end);
            self.next_param = end;
        }
        self.early_fresh = false;
    }

    pub fn resolve(&self, tys: &Types, prog: &Program, file: u32, name: Option<ast::Ident>) -> RegionId {
        let r = self.resolve_inner(tys, prog, file, name);
        self.record_use(tys.region_kind(r));
        r
    }

    fn record_use(&self, r: RegionKind) {
        if let Some(uses) = &self.uses {
            let mut uses = uses.lock().unwrap();
            if !uses.contains(&r) { uses.push(r); }
        }
        if let Some(parent) = &self.elision_parent {
            match r {
                RegionKind::ReBound(0, _) => {},
                RegionKind::ReBound(d, v) => parent.record_use(RegionKind::ReBound(d - 1, v)),
                _ => parent.record_use(r),
            }
        }
    }

    pub fn start_parameter(&mut self) {
        self.uses = Some(Arc::new(std::sync::Mutex::new(Vec::new())));
        if self.refs.is_none() { self.refs = Some(Arc::new(std::sync::Mutex::new(Vec::new()))); }
    }
    pub fn parameter_uses(&self) -> Vec<RegionKind> {
        self.uses.as_ref().map_or_else(Vec::new, |u| u.lock().unwrap().clone())
    }

    fn resolve_inner(&self, tys: &Types, prog: &Program, file: u32, name: Option<ast::Ident>) -> RegionId {
        if !self.enabled { return RegionId::ERASED; }
        if let Some(name) = name {
            let name = prog.files[file as usize].text(name);
            if name == "'static" { return tys.intern_region(RegionKind::ReStatic); }
            if name != "'_" {
                return tys.intern_region(self.names.iter().rev().find(|(n, _)| n == name).map_or(RegionKind::ReError, |(_, r)| *r));
            }
        }
        if let Some(parent) = &self.elision_parent {
            let r = parent.resolve_inner(tys, prog, file, name);
            return match tys.region_kind(r) {
                RegionKind::ReBound(d, v) => tys.intern_region(RegionKind::ReBound(d + 1, v)),
                _ => r,
            };
        }
        if let Some(r) = self.output { return r; }
        if let Some(fresh) = &self.fresh {
            let i = fresh.fetch_add(1, Ordering::Relaxed);
            return tys.intern_region(if self.infer_fresh { RegionKind::ReVar(i) } else if self.early_fresh { RegionKind::ReEarlyParam(i) } else { RegionKind::ReBound(0, BoundVar(i)) });
        }
        tys.intern_region(if self.static_elision { RegionKind::ReStatic } else { RegionKind::ReError })
    }
}

impl Tcx {
    /// rustc_hir_analysis/hir_ty_lowering/mod.rs:589: a resolved early parameter
    /// is instantiated by its declaration index, not its position in a type-only list.
    pub(crate) fn subst_decl_regions(&self, t: TyId, decl: &GenEnv, args: RegionArgsId) -> TyId {
        let args = self.tys.region_args(args);
        let bindings: Vec<_> = decl.regions.names.iter().filter_map(|(_, r)| match r {
            RegionKind::ReEarlyParam(i) => Some(*i), _ => None,
        }).zip(args.iter().copied()).collect();
        self.tys.map_regions(t, &|r, depth| match self.tys.region_kind(r) {
            RegionKind::ReEarlyParam(i) => bindings.iter().find(|(j, _)| *j == i).map_or(RegionId::ERASED, |(_, r)| {
                match self.tys.region_kind(*r) {
                    RegionKind::ReBound(d, v) => self.tys.intern_region(RegionKind::ReBound(d + depth, v)),
                    _ => *r,
                }
            }),
            _ => r,
        }, 0)
    }

    pub(crate) fn lower_region_args(&self, prog: &Program, file: u32, module: u32, env: &GenEnv, p: &ast::Path) -> RegionArgsId {
        if !env.regions.enabled { return RegionArgsId::EMPTY; }
        let ast = &prog.files[file as usize].ast;
        let mut out = Vec::new();
        if let Some(GenericArgs::Angle(v)) = ast.segs(p.segs).last().and_then(|s| ast.gargs(s.args)) {
            for a in ast.list(*v) {
                if let GenericArg::Lifetime(lt) = a { out.push(env.regions.resolve(&self.tys, prog, file, Some(*lt))); }
            }
        }
        if out.is_empty() {
            if let Some(d) = self.resolve_type_path_def(prog, file, module, p) {
                let df = prog.def(d);
                if !matches!(df.kind, DefKind::Struct | DefKind::Union | DefKind::Enum | DefKind::TypeAlias | DefKind::Trait | DefKind::AssocTy) { return RegionArgsId::EMPTY; }
                let a = &prog.files[df.file as usize].ast;
                let g = match &a.item(df.item).kind {
                    ItemKind::Struct(g, _) | ItemKind::Union(g, _) | ItemKind::Enum(g, _) |
                    ItemKind::TypeAlias { generics: g, .. } | ItemKind::Trait { generics: g, .. } => Some(g),
                    _ => None,
                };
                if let Some(g) = g {
                    for _ in a.list(g.params).iter().filter(|p| matches!(p.kind, GenericParamKind::Lifetime(_))) {
                        out.push(env.regions.resolve(&self.tys, prog, file, None));
                    }
                }
            }
        }
        self.tys.intern_region_args(&out)
    }
}

impl RegionEnv {
    pub(crate) fn binder(&self, tys: &Types, prog: &Program, file: u32, params: ast::List<ast::GenericParam>) -> Self {
        let mut env = self.clone();
        env.static_elision = false;
        env.output = None;
        env.elision_parent = None;
        env.early_fresh = false;
        env.infer_fresh = false;
        for (_, r) in &mut env.names {
            if let RegionKind::ReBound(d, _) = r { *d += 1; }
        }
        env.object_default = self.object_default.map(|r| match tys.region_kind(r) {
            RegionKind::ReBound(d, v) => tys.intern_region(RegionKind::ReBound(d + 1, v)), _ => r,
        });
        let f = &prog.files[file as usize];
        let mut n = 0;
        for p in f.ast.list(params) {
            if matches!(p.kind, GenericParamKind::Lifetime(_)) {
                env.names.push((f.text(p.name).to_owned(), RegionKind::ReBound(0, BoundVar(n))));
                n += 1;
            }
        }
        env.fresh = Some(Arc::new(AtomicU32::new(n)));
        env.uses = None;
        env.refs = None;
        env
    }

    pub(super) fn predicate_binder(&self, tys: &Types, prog: &Program, file: u32, params: ast::List<ast::GenericParam>) -> Self {
        let mut env = self.binder(tys, prog, file, params);
        // rustc_resolve/late.rs:1041 introduces only the named parameter rib.
        // Unlike a fn/parenthesized Fn signature, it does not push an
        // AnonymousCreateParameter rib for elided lifetimes.
        env.elision_parent = Some(Box::new(self.clone()));
        env
    }

    pub fn bound_count(&self) -> u32 {
        if !self.enabled || self.early_fresh { return 0; }
        self.fresh.as_ref().map_or(0, |n| n.load(Ordering::Relaxed))
    }
}

impl Tcx {
    /// Regions which constrain a type, mirroring ConstrainedCollectorPostHirTyLowering
    /// (resolve_bound_vars.rs:2424). Projections do not constrain their arguments.
    fn constrained_regions(&self, t: TyId, out: &mut Vec<RegionKind>, depth: u32) {
        let mut add = |r| {
            let r = self.tys.region_kind(r);
            let r = match r {
                RegionKind::ReBound(d, v) if d >= depth => RegionKind::ReBound(d - depth, v),
                RegionKind::ReBound(..) => return,
                _ => r,
            };
            if !out.contains(&r) { out.push(r); }
        };
        match self.tys.kind(t) {
            TyKind::Ref(_, x, r) => { add(*r); self.constrained_regions(*x, out, depth); }
            TyKind::Adt(_, v, rs) | TyKind::FnDef(_, v, rs) => {
                for r in self.tys.region_args(*rs).iter() { add(*r); }
                for t in v { self.constrained_regions(*t, out, depth); }
            }
            TyKind::Dyn(_, v, bs, rs, r, _, _) => {
                add(*r);
                for r in self.tys.region_args(*rs).iter() {
                    match self.tys.region_kind(*r) {
                        RegionKind::ReBound(0, _) => {},
                        RegionKind::ReBound(d, v) => add(self.tys.intern_region(RegionKind::ReBound(d - 1, v))),
                        _ => add(*r),
                    }
                }
                for t in v { self.constrained_regions(*t, out, depth + 1); }
                for (_, t, _) in bs { self.constrained_regions(*t, out, depth + 1); }
            }
            TyKind::Tuple(v) => for t in v { self.constrained_regions(*t, out, depth); },
            TyKind::Ptr(_, x) | TyKind::Slice(x) | TyKind::Array(x, _) => self.constrained_regions(*x, out, depth),
            TyKind::FnPtr(ps, r, _, _) => {
                for t in ps { self.constrained_regions(*t, out, depth + 1); }
                self.constrained_regions(*r, out, depth + 1);
            }
            _ => {}
        }
    }

    pub(crate) fn fn_region_env(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &mut GenEnv, sig: &ast::FnSig, owner: DefId) {
        env.regions.enabled = true;
        let f = &prog.files[file as usize];
        let mut constrained = Vec::new();
        // Resolve aliases before deciding which declared lifetimes inputs constrain.
        // The draft has early parameters, so their complete generic indices identify them.
        for p in f.ast.list(sig.params) {
            let t = self.lower_ty(cx, prog, file, module, env, p.ty);
            self.constrained_regions(t, &mut constrained, 0);
        }
        match sig.self_param {
            Some(ast::SelfParam::Ref(Some(lt), _)) => {
                constrained.push(self.tys.region_kind(env.regions.resolve(&self.tys, prog, file, Some(lt))));
            }
            Some(ast::SelfParam::Typed(_, t)) => self.constrained_regions(self.lower_ty(cx, prog, file, module, env, t), &mut constrained, 0),
            _ => {}
        }
        let mut wh = LifetimeUses::new(prog, file);
        wh.generics(&sig.generics);
        let mut ret = LifetimeUses::new(prog, file);
        if let Some(t) = sig.ret { ret.ty(t); }
        let parent = prog.def(prog.def(owner).parent).kind;
        let captures_all = sig.asyncness || (ret.opaque_without_use &&
            (prog.crates[prog.def(owner).krate as usize].edition >= 2024 ||
             parent == DefKind::Trait || (parent == DefKind::Impl && self.impl_trait.contains_key(&prog.def(owner).parent))));
        if captures_all { ret.names.extend(env.regions.names.iter().map(|(n, _)| n.clone())); }
        // rustc resolve_bound_vars::is_late_bound_map (2326): unused parameters can
        // be late; output-only and predicate-mentioned parameters are early.
        let own = f.ast.list(sig.generics.params);
        let mut next = env.regions.next_param - own.len() as u32;
        let mut bound = 0;
        for p in own {
            if matches!(p.kind, GenericParamKind::Lifetime(_)) {
                let name = f.text(p.name);
                let (_, r) = env.regions.names.iter_mut().rev().find(|(n, _)| n == name).unwrap();
                if !wh.names.iter().any(|n| n == name) && (constrained.contains(r) || !ret.names.iter().any(|n| n == name)) {
                    *r = RegionKind::ReBound(0, BoundVar(bound));
                    bound += 1;
                } else {
                    *r = RegionKind::ReEarlyParam(next);
                    next += 1;
                }
            } else { next += 1; }
        }
        env.regions.next_param = next;
        env.regions.fresh = Some(Arc::new(AtomicU32::new(bound)));
        env.regions.static_elision = false;
    }

    pub(super) fn lower_fn_pointer(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, fp: &ast::FnPtr) -> TyId {
        self.lower_fn_bound_pointer(cx, prog, file, module, env, fp, ast::List::new(0, 0))
    }

    pub(super) fn lower_fn_bound_pointer(&self, cx: &crate::tcx::EvalCx<'_>, prog: &Program, file: u32, module: u32, env: &GenEnv, fp: &ast::FnPtr, where_hrtb: ast::List<ast::GenericParam>) -> TyId {
        let outer_regions = env.regions.clone();
        let mut env = env.clone();
        env.regions = env.regions.binder(&self.tys, prog, file, where_hrtb);
        // The where predicate and parenthesized Fn sugar use the same bound
        // variable list (resolve_bound_vars::visit_where_predicate).
        for p in prog.files[file as usize].ast.list(fp.hrtb) {
            if matches!(p.kind, GenericParamKind::Lifetime(_)) {
                let i = env.regions.fresh.as_ref().unwrap().fetch_add(1, Ordering::Relaxed);
                env.regions.names.push((prog.files[file as usize].text(p.name).to_owned(), RegionKind::ReBound(0, BoundVar(i))));
            }
        }
        let f = &prog.files[file as usize];
        let mut ps = Vec::new();
        let mut uses = Vec::new();
        for t in f.ast.list(fp.params) {
            env.regions.start_parameter();
            ps.push(self.lower_ty(cx, prog, file, module, &env, *t));
            uses.push(env.regions.parameter_uses());
        }
        self.output_region_env(&mut env, &ps, None, &uses);
        env.regions.start_parameter();
        let ret = fp.ret.map_or(self.tys.unit, |t| self.lower_ty(cx, prog, file, module, &env, t));
        uses.push(env.regions.parameter_uses());
        for r in uses.into_iter().flatten() {
            let r = match r {
                RegionKind::ReBound(0, _) => continue,
                RegionKind::ReBound(d, v) => RegionKind::ReBound(d - 1, v),
                _ => r,
            };
            outer_regions.record_use(r);
        }
        let header = self.lower_fn_header(cx, prog, file, fp.unsafe_, fp.abi, fp.variadic);
        self.tys.intern(TyKind::FnPtr(ps, ret, header, env.regions.bound_count()))
    }

    pub(super) fn output_region_env(&self, env: &mut GenEnv, _params: &[TyId], self_regions: Option<Vec<RegionKind>>, uses: &[Vec<RegionKind>]) {
        let has_self = self_regions.is_some();
        let mut candidates = self_regions.unwrap_or_default();
        if candidates.is_empty() {
            for rs in uses.iter().skip(usize::from(has_self)) {
                candidates.extend(rs.iter().copied());
            }
        }
        env.regions.uses = None;
        env.regions.output = Some(self.tys.intern_region(if candidates.len() == 1 { candidates[0] } else { RegionKind::ReError }));
    }
}

/// The all-regions visitor from resolve_bound_vars.rs. Unlike constrained_regions,
/// this visits projection arguments and bounds too.
struct LifetimeUses<'a> {
    prog: &'a Program,
    file: u32,
    names: Vec<String>,
    opaque_without_use: bool,
}
impl<'a> LifetimeUses<'a> {
    fn new(prog: &'a Program, file: u32) -> Self { Self { prog, file, names: Vec::new(), opaque_without_use: false } }
    fn name(&mut self, n: ast::Ident) {
        let n = self.prog.files[self.file as usize].text(n).to_owned();
        if !self.names.contains(&n) { self.names.push(n); }
    }
    fn generics(&mut self, g: &ast::Generics) {
        let ast = &self.prog.files[self.file as usize].ast;
        for p in ast.list(g.params) {
            match p.kind {
                GenericParamKind::Lifetime(bs) => if !bs.is_empty() { self.name(p.name); for n in ast.list(bs) { self.name(*n); } },
                GenericParamKind::Type(bs, _) => self.bounds(bs),
                GenericParamKind::Const(..) => {}
            }
        }
        for w in ast.list(g.where_) {
            match w {
                ast::WherePred::Lifetime(n, bs) => { self.name(*n); for n in ast.list(*bs) { self.name(*n); } }
                ast::WherePred::Bound { ty, bounds, .. } => { self.ty(*ty); self.bounds(*bounds); }
            }
        }
    }
    fn bounds(&mut self, bs: ast::List<ast::Bound>) {
        let ast = &self.prog.files[self.file as usize].ast;
        for b in ast.list(bs) {
            match b {
                ast::Bound::Lifetime(n) => self.name(*n),
                ast::Bound::Trait { path, .. } => self.path(path),
                ast::Bound::Use(args) => {
                    if let Some(GenericArgs::Angle(v)) = ast.gargs(*args) {
                        for a in ast.list(*v) { if let GenericArg::Lifetime(n) = a { self.name(*n); } }
                    }
                }
            }
        }
    }
    fn path(&mut self, p: &ast::Path) {
        let ast = &self.prog.files[self.file as usize].ast;
        if let Some(q) = ast.qself(p) { self.ty(q.ty); if let Some(p) = q.trait_path { self.path(&p); } }
        for s in ast.segs(p.segs) {
            match ast.gargs(s.args) {
                Some(GenericArgs::Angle(v)) => for a in ast.list(*v) {
                    match a {
                        GenericArg::Lifetime(n) => self.name(*n),
                        GenericArg::Type(t) | GenericArg::Binding(_, _, t) => self.ty(*t),
                        GenericArg::Constraint(_, bs) => self.bounds(*bs),
                        _ => {}
                    }
                },
                Some(GenericArgs::Paren(ps, r)) => { for t in ast.list(*ps) { self.ty(*t); } if let Some(t) = r { self.ty(*t); } }
                _ => {}
            }
        }
    }
    fn ty(&mut self, t: ast::TyId) {
        let ast = &self.prog.files[self.file as usize].ast;
        match ast.ty(t) {
            ast::Ty::Ref(n, _, t) => { if let Some(n) = n { self.name(*n); } self.ty(*t); }
            ast::Ty::Path(p) => self.path(p),
            ast::Ty::Ptr(_, t) | ast::Ty::Slice(t) | ast::Ty::Array(t, _) | ast::Ty::Paren(t) => self.ty(*t),
            ast::Ty::Tuple(v) => for t in ast.list(*v) { self.ty(*t); },
            ast::Ty::Fn(f) => { let f = ast.fn_ptr(*f); for t in ast.list(f.params) { self.ty(*t); } if let Some(t) = f.ret { self.ty(t); } }
            ast::Ty::DynTrait(bs, _) => self.bounds(*bs),
            ast::Ty::ImplTrait(bs) => {
                if !ast.list(*bs).iter().any(|b| matches!(b, ast::Bound::Use(_))) { self.opaque_without_use = true; }
                self.bounds(*bs);
            }
            _ => {}
        }
    }
}

impl Tcx {
    /// Object defaults for a type parameter (resolve_bound_vars.rs:1052,1728).
    /// The enclosing reference's default stops at a generic argument boundary.
    pub(super) fn generic_object_defaults(&self, prog: &Program, d: DefId, args: RegionArgsId) -> Vec<RegionId> {
        let df = prog.def(d);
        if !matches!(df.kind, DefKind::Struct | DefKind::Union | DefKind::Enum | DefKind::TypeAlias | DefKind::Trait | DefKind::AssocTy) { return Vec::new(); }
        let f = &prog.files[df.file as usize];
        let g = match &f.ast.item(df.item).kind {
            ItemKind::Struct(g, _) | ItemKind::Union(g, _) | ItemKind::Enum(g, _) |
            ItemKind::TypeAlias { generics: g, .. } | ItemKind::Trait { generics: g, .. } => g,
            _ => return Vec::new(),
        };
        let rs = self.tys.region_args(args);
        let mut lts = f.ast.list(g.params).iter().filter(|p| matches!(p.kind, GenericParamKind::Lifetime(_)));
        let lts: Vec<_> = lts.by_ref().zip(rs.iter()).map(|(p, r)| (f.text(p.name), *r)).collect();
        let lookup = |n: ast::Ident| {
            let n = f.text(n);
            if n == "'static" { self.tys.intern_region(RegionKind::ReStatic) }
            else { lts.iter().find(|(name, _)| *name == n).map_or(self.tys.intern_region(RegionKind::ReError), |(_, r)| *r) }
        };
        let mut out = Vec::new();
        for p in f.ast.list(g.params) {
            let GenericParamKind::Type(bs, _) = p.kind else {
                if matches!(p.kind, GenericParamKind::Const(..)) { out.push(self.tys.intern_region(RegionKind::ReStatic)); }
                continue;
            };
            let mut bounds = Vec::new();
            let mut add_bounds = |bs| {
                for b in f.ast.list(bs) {
                    if let ast::Bound::Lifetime(n) = b {
                        if !bounds.iter().any(|old| f.text(*old) == f.text(*n)) { bounds.push(*n); }
                    }
                }
            };
            add_bounds(bs);
            for w in f.ast.list(g.where_) {
                if let ast::WherePred::Bound { hrtb, ty, bounds } = w {
                    if !hrtb.is_empty() { continue; }
                    if let ast::Ty::Path(path) = f.ast.ty(*ty) {
                        if path.qself.is_none() && path.segs.len() == 1 && f.text(f.ast.segs(path.segs)[0].name) == f.text(p.name) { add_bounds(*bounds); }
                    }
                }
            }
            out.push(match bounds.as_slice() {
                [] => self.tys.intern_region(RegionKind::ReStatic),
                [n] => lookup(*n),
                _ => self.tys.intern_region(RegionKind::ReError),
            });
        }
        out
    }

    pub(super) fn object_region(&self, prog: &Program, file: u32, env: &GenEnv, bs: &[ast::Bound]) -> RegionId {
        if !env.regions.enabled { return RegionId::ERASED; }
        for b in bs {
            if let ast::Bound::Lifetime(n) = b {
                return env.regions.resolve(&self.tys, prog, file, Some(*n));
            }
        }
        env.regions.object_default.unwrap_or_else(|| {
            if env.regions.infer_fresh {
                env.regions.resolve(&self.tys, prog, file, None)
            } else {
                self.tys.intern_region(RegionKind::ReStatic)
            }
        })
    }
}

impl Tcx {
    // rustc_hir_analysis::compute_object_lifetime_bound (hir_ty_lowering/mod.rs:3749)
    // elaborates Self: 'r predicates, including supertraits, before using a default.
    pub(super) fn derived_object_regions(&self, prog: &Program, td: DefId, args: RegionArgsId, seen: &mut Vec<DefId>, out: &mut Vec<RegionId>) {
        if seen.contains(&td) { return; }
        seen.push(td);
        let d = prog.def(td);
        let f = &prog.files[d.file as usize];
        if let ItemKind::Trait { generics, supers, .. } = &f.ast.item(d.item).kind {
            let mut env = GenEnv::default();
            env.regions.enabled = true;
            let rs = self.tys.region_args(args);
            for (p, r) in f.ast.list(generics.params).iter().filter(|p| matches!(p.kind, GenericParamKind::Lifetime(_))).zip(rs.iter()) {
                env.regions.names.push((f.text(p.name).to_owned(), self.tys.region_kind(*r)));
            }
            let mut all = f.ast.list(*supers).to_vec();
            for w in f.ast.list(generics.where_) {
                if let ast::WherePred::Bound { hrtb, ty, bounds } = w {
                    if hrtb.is_empty() && matches!(f.ast.ty(*ty), ast::Ty::Path(p) if p.qself.is_none() && p.segs.len() == 1 && f.ast.segs(p.segs)[0].kind == SegKind::SelfType) {
                        all.extend_from_slice(f.ast.list(*bounds));
                    }
                }
            }
            for b in all {
                match b {
                    ast::Bound::Lifetime(n) => {
                        let r = env.regions.resolve(&self.tys, prog, d.file, Some(n));
                        if !out.contains(&r) { out.push(r); }
                    }
                    ast::Bound::Trait { hrtb, path, .. } if hrtb.is_empty() => {
                        if let Some(td) = self.resolve_type_path_def(prog, d.file, d.scope, &path) {
                            let rs = self.lower_region_args(prog, d.file, d.scope, &env, &path);
                            self.derived_object_regions(prog, td, rs, seen, out);
                        }
                    }
                    _ => {}
                }
            }
        }
        seen.pop();
    }

    pub(super) fn object_region_with_bounds(&self, prog: &Program, file: u32, env: &GenEnv, bounds: &[ast::Bound], td: DefId, rs: RegionArgsId) -> RegionId {
        if !env.regions.enabled { return RegionId::ERASED; }
        let explicit = bounds.iter().find_map(|b| match b { ast::Bound::Lifetime(n) => Some(*n), _ => None });
        if let Some(n) = explicit {
            if prog.files[file as usize].text(n) != "'_" { return env.regions.resolve(&self.tys, prog, file, Some(n)); }
        }
        let mut derived = Vec::new();
        self.derived_object_regions(prog, td, rs, &mut Vec::new(), &mut derived);
        // rustc_trait_selection::traits::wf::object_region_bounds: a region
        // escaping the existential predicate binder is not an object bound.
        derived.retain(|r| !matches!(self.tys.region_kind(*r), RegionKind::ReBound(..)));
        if let Some(r) = derived.iter().find(|r| self.tys.region_kind(**r) == RegionKind::ReStatic) { return *r; }
        if let Some(r) = derived.first() { return *r; }
        self.object_region(prog, file, env, bounds)
    }
}

fn child_types(ast: &ast::Ast, t: ast::TyId) -> Vec<ast::TyId> {
    let mut out = Vec::new();
    let mut path = |p: &ast::Path| {
        if let Some(q) = ast.qself(p) { out.push(q.ty); }
        for s in ast.segs(p.segs) {
            match ast.gargs(s.args) {
                Some(GenericArgs::Angle(v)) => for a in ast.list(*v) {
                    if let GenericArg::Type(t) | GenericArg::Binding(_, _, t) = a { out.push(*t); }
                },
                Some(GenericArgs::Paren(ps, r)) => { out.extend_from_slice(ast.list(*ps)); out.extend(*r); }
                _ => {}
            }
        }
    };
    match ast.ty(t) {
        ast::Ty::Path(p) => path(p),
        ast::Ty::DynTrait(bs, _) | ast::Ty::ImplTrait(bs) => for b in ast.list(*bs) { if let ast::Bound::Trait { path: p, .. } = b { path(p); } },
        ast::Ty::Ref(_, _, t) | ast::Ty::Ptr(_, t) | ast::Ty::Array(t, _) | ast::Ty::Slice(t) | ast::Ty::Paren(t) => out.push(*t),
        ast::Ty::Tuple(v) => out.extend_from_slice(ast.list(*v)),
        ast::Ty::Fn(f) => { let f = ast.fn_ptr(*f); out.extend_from_slice(ast.list(f.params)); out.extend(f.ret); }
        _ => {}
    }
    out
}

impl RegionEnv {
    pub fn record_reference(&self, file: u32, t: ast::TyId, r: RegionId) {
        if let Some(refs) = &self.refs { refs.lock().unwrap().push((file, t, r)); }
    }
}

impl Tcx {
    /// rustc_resolve::late::find_lifetime_for_self (2614): every reference whose
    /// syntactic referent contains Self, not just the outer reference to Self.
    pub(super) fn self_elision_regions(&self, prog: &Program, file: u32, module: u32, env: &GenEnv, receiver: Option<&ast::SelfParam>, params: &[TyId]) -> Option<Vec<RegionKind>> {
        let receiver = receiver?;
        let mut out = Vec::new();
        if let ast::SelfParam::Ref(..) = receiver {
            if let Some(t) = params.first() {
                if let TyKind::Ref(_, _, r) = self.tys.kind(*t) { out.push(self.tys.region_kind(*r)); }
            }
        } else if let ast::SelfParam::Typed(_, root) = receiver {
            let ast = &prog.files[file as usize].ast;
            let self_def = env.self_ty.and_then(|t| match self.tys.kind(t) { TyKind::Adt(d, ..) => Some(*d), _ => None });
            let is_self = |t| match ast.ty(t) {
                ast::Ty::ImplicitSelf => true,
                ast::Ty::Path(p) if p.qself.is_none() => {
                    (p.segs.len() == 1 && ast.segs(p.segs)[0].kind == SegKind::SelfType) ||
                    self_def.is_some_and(|d| self.resolve_type_path_def(prog, file, module, p) == Some(d))
                }
                _ => false,
            };
            fn contains(ast: &ast::Ast, t: ast::TyId, pred: &impl Fn(ast::TyId) -> bool) -> bool {
                pred(t) || child_types(ast, t).iter().any(|t| contains(ast, *t, pred))
            }
            let refs = env.regions.refs.as_ref().map(|v| v.lock().unwrap().clone()).unwrap_or_default();
            let mut todo = vec![*root];
            while let Some(t) = todo.pop() {
                if let ast::Ty::Ref(_, _, inner) = ast.ty(t) {
                    if contains(ast, *inner, &is_self) {
                        if let Some((_, _, r)) = refs.iter().find(|(f, ty, _)| *f == file && *ty == t) {
                            let r = self.tys.region_kind(*r);
                            if !out.contains(&r) { out.push(r); }
                        }
                    }
                }
                todo.extend(child_types(ast, t));
            }
        }
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The UI suite still consumes AST-reconstructed regions in A2, so it cannot
    // observe incorrect region metadata. Check the actual collected item types.
    #[test]
    fn written_regions_and_inference_keys() {
        let source = br#"
            #![no_std]
            struct S<'a, T>(&'a T);
            type A<'a> = &'a u32;
            type F<T> = fn(T);
            trait Tr<'a> { fn inherited(&'a self); }
            trait Hr<'a, T> { type Item; }
            #[lang = "fn_once"] trait FnOnce<T> { #[lang = "fn_once_output"] type Output; }
            #[lang = "fn"] trait Fn<T>: FnOnce<T> {}
            type Obj<T> = dyn for<'a> Hr<'a, T, Item = &'a T>;
            fn substituted<'a>(x: &'a u32, p: &Obj<&'a u32>) {}
            fn higher<'a>(x: &'a u32, p: &dyn for<'b> Hr<'b, &'a u32, Item = &'b u32>) {}
            fn elided_object(p: *const dyn Hr<'_, u32, Item = u32>) -> &u32 { loop {} }
            fn callable(p: &dyn for<'a> Fn(&'a u32) -> &'a u32) {}
            fn takes<F: for<'a> Fn(&'a u32) -> &'a u32>(f: F) {}
            struct O<'a, T: 'a + ?Sized>(&'a T);
            fn closure_annotations<'a>(z: &'a u32) {
                let a = |x: &u32, y: &u32| {};
                let b = |f: for<'b> fn(&'b u32), x: &'a u32| {};
                let c = |x: &u32| -> &u32 { x };
                let n = const { 1u32 };
            }
            fn takes_ref<F: for<'a> Fn(&'a u32) -> &'a u32>(f: &F) {}
            fn takes_mut<F: for<'a> Fn(&'a u32) -> &'a u32>(f: &mut F) {}
            fn takes_where<F>(f: F) where for<'a> F: Fn(&'a u32) -> &'a u32 {}
            fn takes_pointer(f: for<'a> fn(&'a u32) -> &'a u32) {}
            fn closure_expected() {
                let f: for<'unused, 'a> fn(&'a u32) -> &'a u32 = |x: &_| x;
                takes(|x: &_| x);
                takes_pointer(|x: &_| x);
                takes_where(|x: &_| x);
                takes_ref(&|x| x);
                takes_mut(&mut |x| x);
                takes_mut(&mut { (|x| x) });
                let g;
                takes(g);
                g = |x| x;
                let object: &dyn for<'a> Fn(&'a u32) -> &'a u32 = &|x: &_| x;
            }
            type Callback = for<'a> fn(&'a u32) -> &'a u32;
            struct Factory { make: fn(Callback) }
            impl Factory { fn get(&self) -> fn(Callback) { takes_pointer } }
            fn make_pointer() -> fn(Callback) { takes_pointer }
            fn closure_routes(factory: Factory) {
                (factory.make)(|x: &_| x);
                make_pointer()(|x: &_| x);
                (factory.get())(|x: &_| x);
                let ptr: fn(Callback) = takes_pointer;
                let r = &ptr;
                r(|x: &_| x);
                let tuple: (Callback,) = (|x| x,);
                let array: [Callback; 1] = [|x| x];
            }
            fn named<'a>(x: &'a u32) -> &'a u32 { x }
            fn early<'a>(x: &'a u32) -> &'a u32 where 'a: 'static { x }
            fn output<'a>() -> &'a u32 { loop {} }
            fn elided(x: &u32) -> &u32 { x }
            fn alias<'a>(x: A<'a>) -> A<'a> { x }
            fn nested<'a>(x: &'a u32, f: F<&'a u32>) {}
            fn objects<'a>(x: &'a dyn Tr<'a>, y: O<'a, dyn Tr<'a>>) {}
            impl<'a, T> S<'a, T> {
                fn get(&self) -> &T { self.0 }
                fn parent<'b>(&'b self) -> &'b T where 'b: 'a { self.0 }
            }
        "#;
        let dir = std::env::temp_dir().join(format!("relax-written-regions-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("lib.rs");
        std::fs::write(&path, source).unwrap();
        let sess = &std::sync::Arc::new(crate::Session::default());
        let mut prog = Program::new(sess);
        prog.load_crate("regions", path.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(sess, &[]), Vec::new()).unwrap();
        // This self-contained fixture supplies its own Fn trait.
        prog.prelude_crate = Some(0);
        let mut tcx = Tcx::new();
        tcx.collect(&prog);
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_dir(&dir).unwrap();
        assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
        let named = |name: &str| (0..prog.defs.len() as u32).rev().map(DefId).find(|&d| prog.name(d) == name).unwrap();
        // Select the last declaration: both Factory and S have a `get` method.
        let sig = |name: &str| tcx.fn_sig(&prog, named(name)).unwrap();
        let region = |t| match tcx.tys.kind(t) {
            TyKind::Ref(_, _, r) => tcx.tys.region_kind(*r), _ => panic!("expected reference"),
        };
        for name in ["named", "elided", "alias", "get"] {
            let s = sig(name);
            assert_eq!(s.bound_regions, 1, "{name}");
            assert_eq!(region(s.params[0]), RegionKind::ReBound(0, BoundVar(0)), "{name}");
            assert_eq!(region(s.ret), RegionKind::ReBound(0, BoundVar(0)), "{name}");
            assert!(tcx.tys.eq_mod_regions(s.ret, tcx.tys.erase_all_regions(s.ret)));
        }
        assert_eq!(region(sig("early").ret), RegionKind::ReEarlyParam(0));
        assert_eq!(region(sig("output").ret), RegionKind::ReEarlyParam(0));
        assert_eq!(region(sig("parent").ret), RegionKind::ReEarlyParam(2));
        assert_eq!(region(sig("inherited").params[0]), RegionKind::ReEarlyParam(1));
        let nested = sig("nested");
        let TyKind::FnPtr(ps, _, _, n) = tcx.tys.kind(nested.params[1]) else { panic!("expected fn pointer") };
        assert_eq!(*n, 0);
        assert_eq!(region(ps[0]), RegionKind::ReBound(1, BoundVar(0)));
        let objects = sig("objects");
        let TyKind::Adt(_, args, rs) = tcx.tys.kind(objects.params[1]) else { panic!("expected ADT") };
        let r = tcx.tys.region_args(*rs)[0];
        let TyKind::Dyn(_, _, _, _, object_r, _, _) = tcx.tys.kind(args[0]) else { panic!("expected dyn") };
        assert_eq!(r, *object_r);
        let elided = sig("elided_object");
        assert_eq!(elided.bound_regions, 1);
        assert_eq!(region(elided.ret), RegionKind::ReBound(0, BoundVar(0)));
        let TyKind::Ptr(_, object) = tcx.tys.kind(elided.params[0]) else { panic!("ptr") };
        let TyKind::Dyn(_, _, _, rs, _, n, _) = tcx.tys.kind(*object) else { panic!("dyn") };
        assert_eq!(*n, 0);
        assert_eq!(tcx.tys.region_kind(tcx.tys.region_args(*rs)[0]), RegionKind::ReBound(1, BoundVar(0)));
        let higher = sig("higher");
        assert_eq!(higher.bound_regions, 2);
        let TyKind::Ref(_, object, _) = tcx.tys.kind(higher.params[1]) else { panic!("ref") };
        let TyKind::Dyn(_, args, bindings, regions, _, n, _) = tcx.tys.kind(*object) else { panic!("dyn") };
        assert_eq!(*n, 1);
        assert_eq!(tcx.tys.region_kind(tcx.tys.region_args(*regions)[0]), RegionKind::ReBound(0, BoundVar(0)));
        assert_eq!(region(args[0]), RegionKind::ReBound(1, BoundVar(0)));
        assert_eq!(bindings[0].2, 1);
        assert_eq!(region(bindings[0].1), RegionKind::ReBound(0, BoundVar(0)));
        let TyKind::Dyn(_, _, erased_bindings, _, _, erased_n, _) = tcx.tys.kind(tcx.tys.erase_all_regions(*object)) else { panic!("dyn") };
        assert_eq!(*erased_n, 0);
        assert_eq!(erased_bindings[0].2, 0);
        let TyKind::Ref(_, object, _) = tcx.tys.kind(sig("callable").params[0]) else { panic!("ref") };
        let TyKind::Dyn(_, args, bindings, _, _, n, _) = tcx.tys.kind(*object) else { panic!("dyn") };
        assert_eq!(*n, 0);
        let TyKind::Tuple(ps) = tcx.tys.kind(args[0]) else { panic!("Args tuple") };
        assert_eq!(region(ps[0]), RegionKind::ReErased);
        assert_eq!(region(bindings[0].1), RegionKind::ReErased);
        let TyKind::Ref(_, object, _) = tcx.tys.kind(sig("substituted").params[1]) else { panic!("ref") };
        let TyKind::Dyn(_, args, bindings, _, _, n, _) = tcx.tys.kind(*object) else { panic!("dyn") };
        assert_eq!(*n, 1);
        assert_eq!(region(args[0]), RegionKind::ReBound(1, BoundVar(0)));
        assert_eq!(region(bindings[0].1), RegionKind::ReBound(0, BoundVar(0)));
        let TyKind::Ref(_, inner, _) = tcx.tys.kind(bindings[0].1) else { panic!("ref") };
        assert_eq!(region(*inner), RegionKind::ReBound(1, BoundVar(0)));
        let def = named("takes");
        let TyKind::FnPtr(ps, r, _, n) = tcx.tys.kind(tcx.callable_signatures(&prog, def)[0].signature) else { panic!("fn") };
        assert_eq!(*n, 1);
        assert_eq!(region(ps[0]), RegionKind::ReBound(0, BoundVar(0)));
        assert_eq!(region(*r), RegionKind::ReBound(0, BoundVar(0)));
        // Selection still uses its ordinary region-erased trait clauses.
        for clause in tcx.item_clauses(&prog, def).unwrap() {
            if let crate::solve::goal::Clause::Trait(p) = clause {
                assert!(p.trait_ref.args.iter().all(|t| tcx.tys.erase_all_regions(*t) == *t));
            }
        }

        // Borrowck still reconstructs closure regions in A3. Assert the typeck
        // results themselves: the UI suite cannot observe binder corruption.
        let state = crate::tcx::EvalState::new();
        let cx = crate::tcx::EvalCx::new(&prog, crate::tcx::TypingEnv::fully_monomorphized(), &state);
        let check = |name| {
            let d = named(name);
            crate::typeck::check_fn_uncached(&cx, &prog, &tcx, d, &[])
        };
        let body = check("closure_annotations");
        assert!(body.errors.is_empty(), "{:?}", body.errors);
        assert_eq!(body.closure_sigs.len(), 3);
        assert_eq!(body.inline_const_types.len(), 1);
        let first = body.closure_sigs[&body.closures[0]];
        let TyKind::FnPtr(ps, _, _, n) = tcx.tys.kind(first.bound) else { panic!("fn") };
        assert_eq!(*n, 2);
        assert_eq!(region(ps[0]), RegionKind::ReBound(0, BoundVar(0)));
        assert_eq!(region(ps[1]), RegionKind::ReBound(0, BoundVar(1)));
        let TyKind::FnPtr(ps, _, _, n) = tcx.tys.kind(first.liberated) else { panic!("fn") };
        assert_eq!(*n, 0);
        assert_eq!(region(ps[0]), RegionKind::ReLateParam(
            crate::types::RegionScope::Closure { owner: body.def, expr: body.closures[0] },
            crate::types::LateParamKind::Anon(0)));
        let second = body.closure_sigs[&body.closures[1]];
        let TyKind::FnPtr(ps, _, _, n) = tcx.tys.kind(second.bound) else { panic!("fn") };
        assert_eq!(*n, 0);
        assert!(matches!(region(ps[1]), RegionKind::ReLateParam(crate::types::RegionScope::Item(_), _)));
        let TyKind::FnPtr(inner, _, _, n) = tcx.tys.kind(ps[0]) else { panic!("fn") };
        assert_eq!(*n, 1);
        assert_eq!(region(inner[0]), RegionKind::ReBound(0, BoundVar(0)));
        let explicit_output = body.closure_sigs[&body.closures[2]];
        let TyKind::FnPtr(ps, r, _, n) = tcx.tys.kind(explicit_output.bound) else { panic!("fn") };
        assert_eq!(*n, 1);
        assert_eq!(region(ps[0]), RegionKind::ReBound(0, BoundVar(0)));
        assert!(matches!(region(*r), RegionKind::ReVar(_)));
        for (name, count) in [("closure_expected", 9), ("closure_routes", 6)] {
            let body = check(name);
            assert!(body.errors.is_empty(), "{name}: {:?}", body.errors);
            assert_eq!(body.closure_sigs.len(), count);
            let mut erased = 0;
            for sig in body.closure_sigs.values() {
                let TyKind::FnPtr(ps, r, _, n) = tcx.tys.kind(sig.bound) else { panic!("fn") };
                // Direct callable bounds and function pointers retain their binder.
                // The callable-object producer still supplies erased regions.
                let expected_region = if *n == 0 { erased += 1; RegionKind::ReErased } else {
                    assert_eq!(*n, 1);
                    RegionKind::ReBound(0, BoundVar(0))
                };
                assert_eq!(region(ps[0]), expected_region);
                assert_eq!(region(*r), expected_region);
                assert!(!tcx.tys.has_infer(sig.bound));
                let (supplied, expected) = sig.annotation_eq.unwrap();
                let TyKind::FnPtr(ps, _, _, _) = tcx.tys.kind(supplied) else { panic!("fn") };
                if *n == 0 { assert!(matches!(region(ps[0]), RegionKind::ReErased | RegionKind::ReVar(_) | RegionKind::ReLateParam(..))); }
                else { assert!(matches!(region(ps[0]), RegionKind::ReVar(_) | RegionKind::ReLateParam(..))); }
                assert!(tcx.tys.eq_mod_regions(supplied, expected));
            }
            assert_eq!(erased, if name == "closure_expected" { 1 } else { 0 });
        }
    }
}
