// ported from compiler/rustc_trait_selection/src/traits/project.rs @8d1a764
//! Type checking of one function instance. Generic functions are checked per
//! instance with concrete type arguments (rustc already proved the bounds; the
//! dialect is valid Rust), so every body Relax lowers is fully monomorphic.
//! Inference is forward with local unification variables (dialect rule R4).

use crate::solve::SelectionResult;
use crate::ast::*;
use crate::program::{DefId, DefKind, Prim, Program, Sym, NO_DEF};
use crate::tcx::{ty_key, FnSigT, GenEnv, Tcx, TyKey};
use crate::types::{Abi, FnHeader, Safety, TyId, TyKind, UniverseIndex};
use crate::fxhash::HashMap;

mod closure;
mod call;
pub use call::CallTrait;
pub use closure::ClosureSignatures;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Res {
    Local(u32),
    Def(DefId),
    /// a const generic param used as a value (`N`): index into the instance args
    ConstParam(u32),
    Err,
}

#[derive(Clone)]
pub struct MethodRes {
    pub def: DefId,
    /// number of derefs applied to the receiver before the call
    pub derefs: u8,
    /// 0 none, 1 `&`, 2 `&mut`
    pub autoref: u8,
    /// full generic args (impl params then method params)
    pub args: Vec<TyId>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Coerce {
    /// fn item -> fn pointer
    ReifyFn,
    /// non-capturing closure -> fn pointer
    ClosureFn,
    /// safe fn pointer -> unsafe fn pointer (rustc coercion.rs:1034).
    UnsafeFn,
    /// &[T; N] -> &[T]
    Unsize,
    /// &mut T -> &T, *mut T -> *const T
    MutToConst,
    /// Deref followed by Borrow(RawPtr): the reference itself is not consumed.
    RefToRaw(bool),
    /// `!` -> any
    Never,
    /// pointer to a sized type -> pointer to `dyn Trait` (&T, *T, Box<T>, Rc<T>, ..):
    /// (source pointee, dyn type)
    ToDyn(TyId, TyId),
    /// `&A -> &B` through n autoderef steps (`&String -> &str`, `&Vec<T> -> &[T]`); overloaded
    /// steps are recorded in ov_derefs under (expr | DEREF_COERCE_KEY, step)
    DerefRef(u8),
    /// trait object upcasting `&dyn Sub -> &dyn Super` (also Box/Rc/raw pointers): the vtable
    /// pointer becomes Sub's stored vtable for Super (rustc vtable_trait_upcasting_coercion_new_vptr_slot):
    /// (source dyn type, target dyn type)
    Upcast(TyId, TyId),
}

pub const DEREF_COERCE_KEY: u32 = 0x8000_0000;
/// res_args of a path pattern are recorded under (pat id | PAT_KEY): pattern and expression
/// ids are separate arenas (`<i32 as Foo>::NUM =>` needs Self = i32 to pick the impl's const)
pub const PAT_KEY: u32 = 0x4000_0000;

pub struct Local {
    pub name: Sym,
    pub ty: TyId,
    pub mutable: bool,
    pub pat: u32,
}

#[derive(Clone, Copy)]
pub enum ExpectedClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

/// Results of type checking one function instance.
pub struct Body {
    pub def: DefId,
    pub args: Vec<TyId>,
    pub file: u32,
    pub expr_lo: u32,
    pub expr_ty: Vec<TyId>,
    pub pat_lo: u32,
    pub pat_ty: Vec<TyId>,
    /// a lazily parsed body's nodes (ParsedFile::part) follow the item's own range in
    /// expr_ty / pat_ty: their first ids (u32::MAX: none) and the item range's lengths
    pub expr_lo2: u32,
    pub expr_n1: u32,
    pub pat_lo2: u32,
    pub pat_n1: u32,
    pub res: HashMap<u32, Res>,
    pub res_args: HashMap<u32, Vec<TyId>>,
    pub pat_res: HashMap<u32, Res>,
    pub pat_local: HashMap<u32, u32>,
    pub methods: HashMap<u32, MethodRes>,
    /// binary operators on non-primitive types: expr -> operator trait method call
    pub binops: HashMap<u32, MethodRes>,
    pub coerce: HashMap<u32, Coerce>,
    /// Reference coercions, including equal-type reborrows (rustc coerce_to_ref).
    pub reborrows: HashMap<u32, bool>,
    pub min_captures: HashMap<u32, crate::upvar::ClosureCaptures>,
    pub field_idx: HashMap<u32, (u8, u32)>,
    /// every struct field the body names, resolved: (ADT, field index) -- a live layout edit's
    /// dependents (reload.rs: the fns using a removed or renamed field, not its name)
    pub field_uses: Vec<(DefId, u32)>,
    /// Resolved definitions read while checking; deduplicated by the warm session.
    pub dependencies: Vec<DefId>,
    /// overloaded deref steps: (expr, step index) -> `Deref::deref` with [Self]
    pub ov_derefs: HashMap<(u32, u8), (DefId, Vec<TyId>)>,
    /// overloaded indexing: expr -> `Index::index` with [Self, Idx]
    pub ov_index: HashMap<u32, (DefId, Vec<TyId>)>,
    /// Every checked `for` head -> `Iterator::next` with [Iter].
    pub for_next: HashMap<u32, (DefId, Vec<TyId>)>,
    /// Every checked `for` head -> (`IntoIterator::into_iter`, [Self], iterator type).
    /// The head is passed by value with identity adjustment (no method receiver coercion).
    pub for_into: HashMap<u32, (DefId, Vec<TyId>, TyId)>,
    pub index_derefs: HashMap<u32, u8>,
    /// call expr -> deref steps from the callee expression to the callable
    pub call_derefs: HashMap<u32, u8>,
    /// Fn-family selection in the generic body, before instance substitution.
    pub call_traits: HashMap<u32, CallTrait>,
    /// calls of `#[rustc_legacy_const_generics]` fns: the argument positions that are const
    /// generic args (not passed as values)
    pub legacy_args: HashMap<u32, Vec<u32>>,
    /// match ergonomics: pattern -> references peeled before matching it
    pub pat_derefs: HashMap<u32, u8>,
    /// identifier patterns bound by reference through the default binding mode (1 ref, 2 ref mut)
    pub pat_bind_ref: HashMap<u32, u8>,
    /// Semantic discriminant reads of constructor patterns, including irrefutable
    /// patterns of enums with uninhabited variants (ExprUseVisitor::walk_pat).
    /// These are capture uses even when runtime lowering needs no discriminant test.
    pub pat_discriminant_reads: HashMap<u32, ()>,
    /// `x?` expr -> the error conversion (`From::from` def, [target, source]) when needed
    pub try_conv: HashMap<u32, Option<(DefId, Vec<TyId>)>>,
    pub locals: Vec<Local>,
    pub param_pats: Vec<PatId>,
    pub ret: TyId,
    pub body: Option<BlockId>,
    /// (macro expr, named arg) -> resolution of `{name}` in a format string
    pub fmt_named: HashMap<(u32, Sym), Res>,
    /// closures that capture nothing (can become plain functions)
    pub closures: Vec<u32>,
    pub closure_locals: HashMap<u32, Vec<u32>>,
    /// Kind deduced from the closure's expected type, before capture inference.
    pub closure_expected_kinds: HashMap<u32, ExpectedClosureKind>,
    /// PolyFnSig and the signature used inside each closure body.
    pub closure_sigs: HashMap<u32, ClosureSignatures>,
    pub inline_const_types: HashMap<u32, TyId>,
    /// Derived root-slot lowering view of `min_captures`: ownership per `closure_locals`.
    pub capture_by_value: HashMap<u32, Vec<bool>>,
    /// Derived root-slot lowering view: top-level fields owned by each root slot.
    /// None means the whole root; precise places remain in `min_captures`.
    pub capture_fields: HashMap<u32, Vec<Option<Vec<u32>>>>,
    /// `S { a: 1, .. }` (bare `..`): struct literal expr -> (field index, the const holding the
    /// field's declared default) for every omitted field (rustc default_field_values)
    pub struct_defaults: HashMap<u32, Vec<(u32, DefId)>>,
    pub errors: Vec<String>,
    /// the where-clauses of a body checked polymorphically (its ParamEnv): the borrow checker
    /// answers impl queries on its params with it too (`DerefMut` of `D: DerefMut<Target = X>`)
    pub param_env: Option<crate::tcx::ParamEnvId>,
}

impl Body {
    /// A body with nothing in it (compiler-generated functions lowered without source).
    pub fn empty(def: DefId, args: Vec<TyId>, file: u32, unit: TyId) -> Body {
        Body {
            def,
            args,
            file,
            expr_lo: 0,
            expr_ty: Vec::new(),
            pat_lo: 0,
            pat_ty: Vec::new(),
            expr_lo2: u32::MAX,
            expr_n1: 0,
            pat_lo2: u32::MAX,
            pat_n1: 0,
            res: HashMap::default(),
            res_args: HashMap::default(),
            pat_res: HashMap::default(),
            pat_local: HashMap::default(),
            methods: HashMap::default(),
            binops: HashMap::default(),
            coerce: HashMap::default(),
            reborrows: HashMap::default(),
            min_captures: HashMap::default(),
            field_idx: HashMap::default(),
            field_uses: Vec::new(),
            dependencies: Vec::new(),
            ov_derefs: HashMap::default(),
            ov_index: HashMap::default(),
            for_next: HashMap::default(),
            for_into: HashMap::default(),
            index_derefs: HashMap::default(),
            call_derefs: HashMap::default(),
            call_traits: HashMap::default(),
            legacy_args: HashMap::default(),
            pat_derefs: HashMap::default(),
            pat_bind_ref: HashMap::default(),
            pat_discriminant_reads: HashMap::default(),
            try_conv: HashMap::default(),
            locals: Vec::new(),
            param_pats: Vec::new(),
            ret: unit,
            body: None,
            fmt_named: HashMap::default(),
            closures: Vec::new(),
            closure_locals: HashMap::default(),
            closure_expected_kinds: HashMap::default(),
            closure_sigs: HashMap::default(),
            inline_const_types: HashMap::default(),
            capture_by_value: HashMap::default(),
            capture_fields: HashMap::default(),
            struct_defaults: HashMap::default(),
            errors: Vec::new(),
            param_env: None,
        }
    }

    #[inline]
    pub fn ty(&self, e: ExprId) -> TyId {
        self.expr_ty[self.expr_ix(e)]
    }
    #[inline]
    pub fn pty(&self, p: PatId) -> TyId {
        self.pat_ty[self.pat_ix(p)]
    }
    /// Index of expression `e` in expr_ty (not checked against its length).
    #[inline]
    pub fn expr_ix(&self, e: ExprId) -> usize {
        if e.0 >= self.expr_lo2 {
            (e.0 - self.expr_lo2 + self.expr_n1) as usize
        } else {
            e.0.wrapping_sub(self.expr_lo) as usize
        }
    }
    #[inline]
    pub fn pat_ix(&self, p: PatId) -> usize {
        if p.0 >= self.pat_lo2 {
            (p.0 - self.pat_lo2 + self.pat_n1) as usize
        } else {
            p.0.wrapping_sub(self.pat_lo) as usize
        }
    }
    /// The expression at expr_ty index `i`.
    #[inline]
    pub fn expr_at(&self, i: usize) -> ExprId {
        if (i as u32) < self.expr_n1 || self.expr_lo2 == u32::MAX {
            ExprId(self.expr_lo + i as u32)
        } else {
            ExprId(self.expr_lo2 + i as u32 - self.expr_n1)
        }
    }
    /// Expression `e` is one this body typed.
    #[inline]
    pub fn has_expr(&self, e: ExprId) -> bool {
        self.expr_ix(e) < self.expr_ty.len()
    }

    /// Heap bytes this body owns (memory report: tables at their capacity, nested vectors
    /// followed one level), without the struct itself.
    pub fn heap_bytes(&self) -> usize {
        fn v<T>(x: &Vec<T>) -> usize {
            x.capacity() * std::mem::size_of::<T>()
        }
        fn m<K, V>(x: &HashMap<K, V>) -> usize {
            let c = x.capacity();
            if c == 0 {
                return 0;
            }
            let buckets = if c < 4 { 4 } else if c < 8 { 8 } else { (c * 8 / 7).next_power_of_two() };
            buckets * (std::mem::size_of::<(K, V)>() + 1) + 16
        }
        let mut n = v(&self.args) + v(&self.expr_ty) + v(&self.pat_ty) + m(&self.res) + m(&self.res_args) + m(&self.pat_res) + m(&self.pat_local) + m(&self.methods) + m(&self.binops) + m(&self.coerce) + m(&self.reborrows) + m(&self.min_captures) + m(&self.field_idx) + v(&self.field_uses) + v(&self.dependencies) + m(&self.ov_derefs) + m(&self.ov_index) + m(&self.for_next) + m(&self.for_into) + m(&self.index_derefs) + m(&self.call_derefs) + m(&self.call_traits) + m(&self.legacy_args) + m(&self.pat_derefs) + m(&self.pat_bind_ref) + m(&self.pat_discriminant_reads) + m(&self.try_conv) + v(&self.locals) + v(&self.param_pats) + m(&self.fmt_named) + v(&self.closures) + m(&self.closure_locals) + m(&self.closure_expected_kinds) + m(&self.closure_sigs) + m(&self.inline_const_types) + m(&self.capture_by_value) + m(&self.capture_fields) + m(&self.struct_defaults) + v(&self.errors);
        n += self.res_args.values().map(v).sum::<usize>() + self.methods.values().chain(self.binops.values()).map(|x| v(&x.args)).sum::<usize>();
        n += self.ov_derefs.values().chain(self.ov_index.values()).chain(self.for_next.values()).map(|x| v(&x.1)).sum::<usize>() + self.for_into.values().map(|x| v(&x.1)).sum::<usize>();
        n += self.legacy_args.values().map(v).sum::<usize>() + self.try_conv.values().map(|x| x.as_ref().map_or(0, |x| v(&x.1))).sum::<usize>();
        n += self.closure_locals.values().map(v).sum::<usize>() + self.capture_by_value.values().map(v).sum::<usize>() + self.struct_defaults.values().map(v).sum::<usize>();
        n += self.capture_fields.values().map(|x| v(x) + x.iter().map(|y| y.as_ref().map_or(0, v)).sum::<usize>()).sum::<usize>();
        n += self.min_captures.values().map(|c| v(&c.captures) + v(&c.fake_reads) + v(&c.errors)).sum::<usize>();
        n += self.errors.iter().map(|e| e.capacity()).sum::<usize>();
        n
    }
}

#[derive(Clone, Copy)]
enum VarSt {
    Free(u8), // 0 general, 1 int, 2 float
    Bound(TyId),
}

struct Loop {
    /// (name, position of the label: hygiene)
    label: Option<(Sym, u32)>,
    break_ty: Option<TyId>,
    is_loop: bool,
}

#[derive(Clone)]
struct PendingGoal {
    goal: crate::solve::goal::Goal,
    lo: u32,
    certainty: crate::solve::goal::Certainty,
    // rustc_trait_selection/src/traits/fulfill.rs:327-365 retries stalled goals
    // only when their inputs change. Captures and hidden types are published separately
    // from inference variables here, so publication must also wake these goals.
    stalled: Option<(crate::solve::goal::Goal, u64)>,
}

impl PendingGoal {
    fn is_stalled(&self, goal: &crate::solve::goal::Goal, revision: u64) -> bool {
        matches!(&self.stalled, Some((previous, seen)) if previous == goal && *seen == revision)
    }
}

pub struct Fcx<'a> {
    cx: crate::tcx::EvalCx<'a>,
    prog: &'a Program,
    tcx: &'a Tcx,
    file: u32,
    module: u32,
    env: GenEnv,
    inst_args: Vec<TyId>,
    b: Body,
    scopes: Vec<(Sym, u32)>,
    /// per local (by index): its hygiene context and the source position of its binding
    /// (u32::MAX context: `self`, matched by any use)
    local_hyg: Vec<(Option<crate::parser::HygCtxt>, u32)>,
    vars: Vec<VarSt>,
    /// Root metadata, restored with bindings; rustc_infer/src/infer/type_variable.rs:389.
    var_universes: Vec<UniverseIndex>,
    /// Monotonic while allocations survive rollback, like this context's vars.
    /// T-infer owns full snapshot rollback of allocations and universes together.
    universe: UniverseIndex,
    /// Existing shared-allocator region variables are ROOT; only explicit
    /// canonical allocations need an entry. Resolution/constraints belong to T-infer.
    region_universes: HashMap<u32, UniverseIndex>,
    region_vars: std::sync::Arc<std::sync::atomic::AtomicU32>,
    loops: Vec<Loop>,
    in_loop_condition: bool,
    diverges: bool,
    ret_stack: Vec<TyId>,
    closure_depth: Vec<(u32, usize)>, // (closure expr, scope depth at entry)
    /// > 0 inside an async block or async fn body (where `.await` is allowed); a closure
    /// inside resets it
    async_depth: u32,
    /// `.await`s of the coroutine body being checked (its suspension points)
    await_count: u32,
    cur_binop: u32,
    /// resolve without defaulting `{integer}`/`{float}` (mid-check normalisation)
    keep_literal_vars: bool,
    /// default binding mode while checking a pattern: 0 move, 1 ref, 2 ref mut
    bind_mode: u8,
    /// a path pattern's resolution, made before its adjust mode is chosen (rustc pat.rs
    /// resolve_pat_path / calc_adjust_mode): (the resolution, its type)
    pat_path_pre: Option<(Res, TyId)>,
    /// calls whose bound-driven inference is retried after each statement
    /// calls whose Fn-bounded argument's type was still open when the call was checked
    /// (`parallel_for(tasks)` with `tasks` collected later): their Fn bounds are applied again
    /// at the end (rustc keeps the `F: FnOnce() -> R` obligation pending)
    pending_goals: Vec<PendingGoal>,
    /// Registered direct Fn-family projections, in obligation order: (Self, PolyFnSig).
    fn_expectations: Vec<(TyId, TyId, crate::upvar::ClosureKind)>,
    /// `?` in a closure / async block whose return type was open: (the `?` expr, its error type,
    /// the return type's error type) -- converted through From once the body fixed the latter
    pending_tries: Vec<(u32, TyId, TyId, TyId)>,
    /// type of a synthesized trailing method argument (consumed by the next method check)
    extra_arg: Option<TyId>,
    /// Postorder closure analysis, after body inference and before upvar tuples are fixed.
    pending_captures: Vec<crate::upvar::PendingCapture>,
    expected_closure_kinds: HashMap<u32, crate::upvar::ClosureKind>,
    /// position of the expression checked last (patterns have no spans of their own)
    last_lo: u32,
    /// traits of the body's generic bounds (and its trait), with supertraits: in scope for
    /// method calls (computed on first use)
    bound_traits: Option<crate::fxhash::HashSet<DefId>>,
    /// trait args of the next trait method call, fixed by a generic bound
    known_targs: Option<Vec<TyId>>,
    /// this body's own return-position `impl Trait` types and the inference variables standing
    /// for their hidden types while it is checked (rustc replace_opaque_types_with_inference_vars)
    opaque_vars: Vec<(TyId, TyId)>,
    /// `[x; N]` expressions whose `Copy` check waits for the end of the body (rustc
    /// deferred_repeat_expr_checks): (element, element type, the array type)
    deferred_repeats: Vec<(ExprId, TyId, TyId)>,
    /// the probe picked a by-value method of `&U` for receiver U: autoref it
    forced_autoref: Option<u8>,
    /// every variable binding with the previous state (snapshots roll back through it)
    undo: Vec<(u32, VarSt, UniverseIndex)>,
    /// Alias equations emitted by the shared relation, with their source offset.
    /// Candidate confirmation reads equations since its snapshot as nested goals;
    /// body checking transfers them to pending_goals. MAX undo entries pop them.
    projection_relations: Vec<(TyId, TyId, u32)>,
    /// the expected type of the method call being checked (check_method's expectation)
    method_expected: Option<TyId>,
    /// finishing: opaque types are revealed to their hidden types (codegen's view)
    revealing: bool,
    /// coercions to a `dyn` pointer whose source pointee was still open: (expr, actual,
    /// expected, pos), decided in `finish`
    deferred_dyn: Vec<(ExprId, TyId, TyId, u32)>,
    /// pointer casts whose target pointee was open: (operand, its type, target type)
    deferred_casts: Vec<(ExprId, TyId, TyId)>,
    /// inference variables a `!` value was coerced to (rustc diverging type variables): left
    /// unconstrained, they fall back to `()` (`!` from edition 2024) at the end
    diverging: Vec<TyId>,
}

pub fn check_fn(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, def: DefId, args: &[TyId]) -> Body {
    // Diagnostic only: sample one in N calls, including queries outside JIT scopes.
    // Keep this off for timing runs; symbolizing a backtrace is deliberately expensive.
    static SAMPLE: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    static CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let sample = *SAMPLE.get_or_init(|| std::env::var("RELAX_TYPECK_BACKTRACE").ok().and_then(|s| s.parse().ok()).unwrap_or(0));
    if sample != 0 && CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed) % sample == 0 {
        let trace = format!("relax-typeck-backtrace: {} def={} args={:?} origin={} time={}\n{}\nrelax-typeck-backtrace-end\n",
            prog.def_path(def), def.0, args, crate::clock::TYS_ORIGIN.with(|o| o.get()),
            crate::fncost::mono(), std::backtrace::Backtrace::force_capture());
        // The app may write directly to fd 2 without Rust's stderr lock. Format
        // first, so its startup messages cannot split the diagnostic header.
        use std::io::Write;
        let _ = std::io::stderr().lock().write_all(trace.as_bytes());
    }
    let _census = crate::exec_census::Record::body(crate::exec_census::instance(def.0,
        || args.iter().map(|t| t.0).collect(), || {
            let d = prog.def(def);
            crate::exec_census::Metadata {
                name: format!("{}<{args:?}>", prog.def_path(def)),
                krate: prog.syms.str(prog.crates[d.krate as usize].name).to_owned(),
                module: prog.def_path(prog.mods[prog.mods[d.scope as usize].normal as usize].def),
                initializer: match d.kind { DefKind::Static => "static-initializer", DefKind::Const | DefKind::AssocConst => "const-initializer", _ => "" },
            }
        }));
    let _cost_typeck = crate::fncost::phase(1);
    let cost_start = if crate::fncost::enabled() { (crate::fncost::mono(), crate::clock::cpu_ns()) } else { (0, 0) };
    let _mem = crate::memstat::tag(crate::memstat::Tag::Typeck);
    let b = match crate::tytemplate::instance(cx, prog, tcx, def, args) {
        Some(b) => b,
        None => check_fn_uncached(cx, prog, tcx, def, args),
    };
    if crate::fncost::enabled() {
        crate::fncost::type_detail(def.0, &args.iter().map(|a| a.0).collect::<Vec<_>>(), b.expr_ty.len(), &prog.def_path(def), cost_start.0, cost_start.1);
    }
    b
}

/// check_fn without templates (the template itself is checked this way).
pub fn check_fn_uncached(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, def: DefId, args: &[TyId]) -> Body {
    static ST: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let st = *ST.get_or_init(|| std::env::var("RELAX_TYSTATS").is_ok());
    let t0 = if st { crate::clock::cpu_ns() } else { 0 };
    let _warm = crate::warm::enabled().then(|| crate::warm::Scope::body(def.0, &args.iter().map(|t| t.0).collect::<Vec<_>>(), crate::clock::TYS_ORIGIN.with(|o| o.get()) == "gandalf", || {
        let args: Vec<_> = args.iter().map(|t| ty_to_string(false, prog, tcx, *t)).collect();
        if args.is_empty() { prog.def_path(def) } else { format!("{}<{}>", prog.def_path(def), args.join(", ")) }
    }));
    cx.state.typeck_inprog.borrow_mut().push(def);
    let b = check_fn_body(cx, prog, tcx, def, args);
    cx.state.typeck_inprog.borrow_mut().pop();
    if st {
        eprintln!("TYS\t{}\t{}\t{}\t{}\t{}\t{:?}\t{}", def.0, args.len(), crate::clock::cpu_ns() - t0, b.expr_ty.len(), prog.def_path(def), args.iter().map(|a| a.0).collect::<Vec<u32>>(), crate::clock::TYS_ORIGIN.with(|o| o.get()));
    }
    b
}

/// RELAX_LAZY_STATS: the fn defs whose bodies were type-checked (what a lazy parse would parse)
pub static CHECKED_DEFS: std::sync::Mutex<Option<std::collections::HashSet<u32>>> = std::sync::Mutex::new(None);

fn check_fn_body(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, def: DefId, args: &[TyId]) -> Body {
    let _why = crate::why::enabled().then(|| {
        let cause = prog.why_def(def, "typeck-caller");
        crate::why::event("typeck", &cause.file, cause.line, &cause.symbol, None);
        crate::why::enter(cause)
    });
    static LAZY_STATS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *LAZY_STATS.get_or_init(|| std::env::var_os("RELAX_LAZY_STATS").is_some()) {
        CHECKED_DEFS.lock().unwrap().get_or_insert_with(Default::default).insert(def.0);
    }
    let d = prog.def(def);
    let file = d.file;
    let (ranges, ranges2) = match prog.body_ranges(file, d.item) {
        Ok(r) => r,
        Err(e) => {
            let mut b = Body::empty(def, args.to_vec(), file, tcx.tys.unit);
            b.errors.push(e);
            return b;
        }
    };
    let env = tcx.item_env(prog, def);
    let sig = match tcx.fn_sig(prog, def) {
        Some(s) => s.clone(),
        None => FnSigT { region_contract: Default::default(), generic_indices: Default::default(), bound_regions: 0,
            params: Vec::new(),
            ret: tcx.tys.unit,
            self_kind: 0,
            n_generics: 0,
            n_parent_generics: 0,
            is_const: false,
            rustc_promotable: false,
            header: FnHeader::RUST,
            track_caller: false,
            legacy_const: Vec::new(),
        },
    };
    let n_expr1 = ranges[1] - ranges[0];
    let n_pat1 = ranges[3] - ranges[2];
    let n_expr = (n_expr1 + ranges2.map_or(0, |r| r[1] - r[0])) as usize;
    let n_pat = (n_pat1 + ranges2.map_or(0, |r| r[3] - r[2])) as usize;
    let error = tcx.tys.error;
    let mut fcx = Fcx {
        cx: cx.body(),
        prog,
        tcx,
        file,
        module: d.scope,
        env,
        inst_args: args.to_vec(),
        b: Body {
            def,
            args: args.to_vec(),
            file,
            expr_lo: ranges[0],
            expr_ty: vec![error; n_expr],
            pat_lo: ranges[2],
            pat_ty: vec![error; n_pat],
            expr_lo2: ranges2.map_or(u32::MAX, |r| r[0]),
            expr_n1: n_expr1,
            pat_lo2: ranges2.map_or(u32::MAX, |r| r[2]),
            pat_n1: n_pat1,
            res: HashMap::default(),
            res_args: HashMap::default(),
            pat_res: HashMap::default(),
            pat_local: HashMap::default(),
            methods: HashMap::default(),
            binops: HashMap::default(),
            coerce: HashMap::default(),
            reborrows: HashMap::default(),
            min_captures: HashMap::default(),
            field_idx: HashMap::default(),
            field_uses: Vec::new(),
            dependencies: Vec::new(),
            ov_derefs: HashMap::default(),
            ov_index: HashMap::default(),
            for_next: HashMap::default(),
            for_into: HashMap::default(),
            index_derefs: HashMap::default(),
            call_derefs: HashMap::default(),
            call_traits: HashMap::default(),
            legacy_args: HashMap::default(),
            try_conv: HashMap::default(),
            pat_derefs: HashMap::default(),
            pat_bind_ref: HashMap::default(),
            pat_discriminant_reads: HashMap::default(),
            locals: Vec::new(),
            param_pats: Vec::new(),
            ret: error,
            body: None,
            fmt_named: HashMap::default(),
            closures: Vec::new(),
            closure_locals: HashMap::default(),
            closure_expected_kinds: HashMap::default(),
            closure_sigs: HashMap::default(),
            inline_const_types: HashMap::default(),
            capture_by_value: HashMap::default(),
            capture_fields: HashMap::default(),
            struct_defaults: HashMap::default(),
            errors: tcx.signature_errors(prog, def).to_vec(),
            param_env: None,
        },
        scopes: Vec::new(),
        local_hyg: Vec::new(),
        vars: Vec::new(),
        var_universes: Vec::new(),
        universe: UniverseIndex::ROOT,
        region_universes: HashMap::default(),
        region_vars: Default::default(),
        loops: Vec::new(),
        in_loop_condition: false,
        diverges: false,
        ret_stack: Vec::new(),
        closure_depth: Vec::new(),
        async_depth: 0,
        await_count: 0,
        cur_binop: 0,
        keep_literal_vars: true,
        diverging: Vec::new(),
        deferred_dyn: Vec::new(),
        deferred_casts: Vec::new(),
        bind_mode: 0,
        pat_path_pre: None,
        pending_goals: Vec::new(),
        fn_expectations: Vec::new(),
        pending_tries: Vec::new(),
        extra_arg: None,
        pending_captures: Vec::new(),
        expected_closure_kinds: HashMap::default(),
        last_lo: 0,
        bound_traits: None,
        known_targs: None,
        opaque_vars: Vec::new(),
        deferred_repeats: Vec::new(),
        forced_autoref: None,
        undo: Vec::new(),
        projection_relations: Vec::new(),
        method_expected: None,
        revealing: false,
    };
    fcx.init_body_regions();
    // a body checked polymorphically (its own params as args): its where-clauses answer impl
    // queries on params and projections (trait selection), for the body's duration
    let penv = tcx.intern_param_env(if args.iter().any(|a| matches!(tcx.tys.kind(*a), TyKind::Param(_))) || (args.is_empty() && tcx.fn_ty_bounds(prog, def).is_some()) { fcx.param_env_entries() } else { Default::default() });
    // (also an empty one: a body checked inside another's check never sees the outer's env)
    fcx.cx.typing_env = crate::tcx::TypingEnv { param_env: penv, mode: crate::tcx::TypingMode::Analysis { defining_opaques: tcx.intern_defining_opaques(vec![def]) } };
    if penv != crate::tcx::ParamEnvId::EMPTY {
        fcx.b.param_env = Some(penv);
    }
    let (params, ret) = fcx.body_signature(&sig, args);
    if params.iter().any(|p| fcx.tcx.tys.has_error(*p)) || fcx.tcx.tys.has_error(ret) {
        // the signature's own error is the root cause; checking the body would only cascade
        let lo = prog.files[file as usize].ast.item(d.item).lo;
        fcx.err(lo, "signature has unresolved types -- fix the signature errors first".to_string());
        return fcx.b;
    }
    // the body defines its own opaque return types: checked against inference variables
    // whose values become the hidden types (rustc check_fn / replace_opaque_types_with_inference_vars)
    let ret = fcx.define_opaques(def, ret);
    fcx.b.ret = ret;
    fcx.ret_stack.push(ret);
    let ast = &prog.files[file as usize].ast;
    let (fsig, body) = match &ast.item(d.item).kind {
        ItemKind::Fn(s, b, _) => (ast.fn_sig(*s), b.or_else(|| prog.fn_body(file, d.item).ok().flatten())),
        ItemKind::Const(_, Some(init)) | ItemKind::Static(_, _, Some(init)) => {
            let init = &prog.const_body(file, d.item).expect("body_ranges validated initializer").unwrap_or(*init);
            // const/static initializer: checked against the declared type
            let ct = fcx.tcx.const_tys.get(&def).copied().unwrap_or(error);
            let ct = fcx.tcx.tys.subst_for_inference(ct, args);
            fcx.b.ret = ct;
            fcx.ret_stack.push(ct);
            let t = fcx.check_expr(*init, Some(ct));
            fcx.coerce_or_unify(t, ct, Some(*init), ast.expr(*init).lo);
            fcx.finish();
            return fcx.b;
        }
        _ => return fcx.b,
    };
    let mut pi = 0;
    if fsig.self_param.is_some() {
        let mutable = matches!(fsig.self_param, Some(SelfParam::Value(true)) | Some(SelfParam::Typed(true, _)));
        let s = prog.syms.get("self").unwrap_or(0);
        let li = fcx.b.locals.len() as u32;
        fcx.b.locals.push(Local { name: s, ty: params[0], mutable, pat: u32::MAX });
        fcx.local_hyg.resize(li as usize + 1, (Some(Vec::new()), 0));
        fcx.local_hyg[li as usize] = (None, 0);
        fcx.scopes.push((s, li));
        pi = 1;
    }
    for p in ast.list(fsig.params) {
        let t = if pi < params.len() { params[pi] } else { fcx.tcx.tys.error };
        fcx.check_pat(p.pat, t);
        fcx.b.param_pats.push(p.pat);
        pi += 1;
    }
    if let (Some(bid), true) = (body, fsig.asyncness) {
        // `async fn`: the body is a coroutine owning every parameter (rustc moves them all into
        // the future); the declared return type is its output, the opaque's hidden type the
        // coroutine
        fcx.b.body = Some(bid);
        let out = match fcx.tcx.async_fns.get(&def) {
            Some(o) => {
                let o = fcx.tcx.tys.subst_for_inference(o, args);
                fcx.tcx.normalize_for_inference(&fcx.cx, prog, o)
            }
            None => error,
        };
        // `async fn f() -> impl Tr`: the output's own opaque types are defined by this body too
        let out = fcx.define_opaques(def, out);
        let ce = crate::tcx::ASYNC_FN_BODY | bid.0;
        let caps: Vec<u32> = (0..fcx.b.locals.len() as u32).collect();
        let saved = fcx.scopes.len();
        fcx.closure_depth.push((ce, saved));
        fcx.ret_stack.push(out);
        fcx.async_depth += 1;
        let t = fcx.check_block(bid, Some(out));
        if !fcx.diverges {
            fcx.coerce_or_unify(t, out, None, ast.block(bid).hi);
        }
        fcx.async_depth -= 1;
        fcx.ret_stack.pop();
        fcx.closure_depth.pop();
        fcx.diverges = false;
        let points = fcx.await_count;
        fcx.b.closure_locals.insert(ce, caps.clone());
        let ct = fcx.coroutine_type(ce, bid, caps, false, false, out, points);
        fcx.unify(ret, ct);
    } else if let Some(bid) = body {
        fcx.b.body = Some(bid);
        let t = fcx.check_block(bid, Some(ret));
        if !fcx.diverges {
            fcx.coerce_or_unify(t, ret, None, ast.block(bid).hi);
        } else {
            // a tail after a diverging statement still types the return (rustc coerces the
            // tail; `panic!(); MyStruct` defines `impl MyTrait` as MyStruct)
            let st = fcx.shallow(t);
            if !matches!(fcx.tcx.tys.kind(st), TyKind::Never) {
                let save = fcx.snapshot();
                if !fcx.try_coerce(t, ret, None) {
                    fcx.rollback(save);
                }
            }
            // a body that only diverges (`fn f() -> impl Sized { todo!() }`): the return type's
            // still-open variable falls back like any variable a `!` flowed into
            let sr = fcx.shallow(ret);
            if matches!(fcx.tcx.tys.kind(sr), TyKind::Infer(_)) {
                fcx.diverging.push(sr);
            }
        }
    }
    fcx.opaque_item_bounds();
    fcx.finish();
    fcx.b
}

/// `t` with every opaque type replaced by its hidden type (rustc Reveal::All, used by codegen):
/// the hidden type of an instance comes from type checking the defining fn with its args, an
/// RPITIT's from the impl method the call resolves to.
pub fn reveal(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, t: TyId) -> TyId {
    let mut t = t;
    for _ in 0..8 {
        if !tcx.tys.has_opaque(t) {
            break;
        }
        let mut os = Vec::new();
        tcx.tys.opaques_in(t, &mut os);
        let mut pairs = Vec::new();
        for o in os {
            let h = hidden_of(cx, prog, tcx, o);
            pairs.push((o, h));
        }
        let r = tcx.tys.replace(t, &pairs);
        t = tcx.normalize_for_inference(cx, prog, r);
    }
    tcx.tys.erase_regions(t)
}

fn hidden_of(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, o: TyId) -> TyId {
    if let Some(h) = tcx.opaque_hidden.get(&o) {
        return h;
    }
    let ik = o;
    let (d, args) = match tcx.tys.kind(o).clone() {
        TyKind::Opaque(d, _, args, _) => (d, args),
        _ => return o,
    };
    // rustc_trait_selection/select/mod.rs:2432-2437 queries type_of_opaque.
    // An active defining body must publish its own hidden type; re-entering it
    // here would turn an ordinary stalled auto-trait goal into a query cycle.
    if cx.state.opaque_inprog.borrow().contains(&ik) || cx.state.typeck_inprog.borrow().contains(&d) {
        return o;
    }
    let error = tcx.tys.error;
    // an instance whose args are still being inferred (a caller's variables) or generic
    // cannot be revealed; it stays opaque (the caller reports what it cannot infer)
    if args.iter().any(|a| tcx.tys.has_infer(*a) || tcx.tys.has_error(*a)) {
        return o;
    }
    cx.state.opaque_inprog.borrow_mut().insert(ik);
    if prog.def(prog.def(d).parent).kind == DefKind::Trait {
        // RPITIT: the impl's method returns the type at the same place of its signature
        let (m, margs) = match tcx.resolve_trait_method(cx, prog, d, &args) {
            crate::tcx::MethodResolution::Resolved(def, args) => (def, args),
            crate::tcx::MethodResolution::Ambiguous(..) | crate::tcx::MethodResolution::NoSolution(_) => {
                cx.state.opaque_inprog.borrow_mut().remove(&ik);
                return o;
            }
        };
        if m != d {
            let (tr, ir) = match (tcx.fn_sig(prog, d), tcx.fn_sig(prog, m)) {
                (Some(a), Some(b)) => (a.ret, b.ret),
                _ => {
                    cx.state.opaque_inprog.borrow_mut().remove(&ik);
                    tcx.opaque_hidden.insert(o, error);
                    return error;
                }
            };
            let tr = tcx.tys.subst_for_inference(tr, &args);
            let ir = tcx.tys.subst_for_inference(ir, &margs);
            let ir = tcx.normalize_for_inference(cx, prog, ir);
            let h = match type_at(tcx, tr, ir, o) {
                Some(x) => reveal(cx, prog, tcx, x),
                None => error,
            };
            cx.state.opaque_inprog.borrow_mut().remove(&ik);
            tcx.opaque_hidden.insert(o, h);
            tcx.trait_input_revision.fetch_add(1, std::sync::atomic::Ordering::Release);
            return h;
        }
    }
    // the defining body records the hidden type when it finishes
    let _ = { let _o = crate::clock::origin("opaque"); check_fn(cx, prog, tcx, d, &args) };
    cx.state.opaque_inprog.borrow_mut().remove(&ik);
    match tcx.opaque_hidden.get(&o) {
        Some(h) => h,
        None => {
            tcx.opaque_hidden.insert(o, error);
            error
        }
    }
}

/// The part of `b` at the place where `a` (same shape) has `target`.
fn type_at(tcx: &Tcx, a: TyId, b: TyId, target: TyId) -> Option<TyId> {
    if a == target {
        return Some(b);
    }
    let (ka, kb) = (tcx.tys.kind(a), tcx.tys.kind(b));
    let pairs: Vec<(TyId, TyId)> = match (ka, kb) {
        (TyKind::Tuple(x), TyKind::Tuple(y)) | (TyKind::Adt(_, x, _), TyKind::Adt(_, y, _)) if x.len() == y.len() => x.iter().copied().zip(y.iter().copied()).collect(),
        (TyKind::Ref(_, x, _), TyKind::Ref(_, y, _)) | (TyKind::Ptr(_, x), TyKind::Ptr(_, y)) | (TyKind::Slice(x), TyKind::Slice(y)) | (TyKind::Array(x, _), TyKind::Array(y, _)) => vec![(*x, *y)],
        _ => return None,
    };
    pairs.into_iter().find_map(|(x, y)| type_at(tcx, x, y, target))
}

impl<'a> Fcx<'a> {
    fn ast(&self) -> &'a Ast {
        &self.prog.files[self.file as usize].ast
    }

    fn err(&mut self, pos: u32, msg: String) {
        self.b.errors.push(self.prog.record_error(self.file, pos, "typeck", msg));
    }

    fn text(&self, id: Ident) -> &'a str {
        let f = &self.prog.files[self.file as usize];
        let s = std::str::from_utf8(f.bytes(id.lo, id.hi)).unwrap_or("?");
        match s.strip_prefix("r#") {
            Some(x) => x,
            None => s,
        }
    }

    fn sym(&self, id: Ident) -> Sym {
        self.prog.syms.get(self.text(id)).unwrap_or(u32::MAX)
    }

    // ------------------------------------------------------------ inference variables

    fn fresh(&mut self, kind: u8) -> TyId {
        self.fresh_in_universe(kind, UniverseIndex::ROOT)
    }

    fn fresh_in_universe(&mut self, kind: u8, universe: UniverseIndex) -> TyId {
        assert!(kind == 0 || universe == UniverseIndex::ROOT);
        let n = self.vars.len() as u32;
        self.vars.push(VarSt::Free(kind));
        self.var_universes.push(universe);
        self.cx.lit_vars.borrow_mut().push(kind);
        self.tcx.tys.intern(TyKind::Infer(n))
    }

    /// Undoes the bindings made since snapshot `save` (a speculative unification). Variables
    /// created since stay allocated: types mentioning them may already be interned.
    fn rollback(&mut self, mark: usize) {
        while self.undo.len() > mark {
            let (i, old, universe) = self.undo.pop().unwrap();
            if i == u32::MAX {
                self.projection_relations.pop();
                continue;
            }
            if i == u32::MAX - 1 { self.pending_goals.pop(); continue; }
            self.vars[i as usize] = old;
            self.var_universes[i as usize] = universe;
        }
    }

    /// A mark to roll speculative bindings back to (rustc's snapshot of the unification table's
    /// undo log: O(bindings made since), not O(variables)).
    fn snapshot(&self) -> usize {
        self.undo.len()
    }

    fn set_var(&mut self, i: u32, st: VarSt) {
        let old = self.vars[i as usize];
        self.undo.push((i, old, self.var_universes[i as usize]));
        self.vars[i as usize] = st;
    }

    fn merge_var_universes(&mut self, root: u32, other: u32) {
        let universe = self.var_universes[root as usize].min(self.var_universes[other as usize]);
        if universe != self.var_universes[root as usize] {
            self.set_var(root, self.vars[root as usize]);
            self.var_universes[root as usize] = universe;
        }
    }

    fn shallow(&mut self, t: TyId) -> TyId {
        let t = self.shallow_vars(t);
        // a projection whose Self became known normalizes to the impl's type
        if let TyKind::Assoc(..) = self.tcx.tys.kind(t) {
            let save = self.keep_literal_vars;
            self.keep_literal_vars = true;
            let d = self.deep(t);
            self.keep_literal_vars = save;
            let outer_overflow = self.cx.state.norm_overflow.replace(false);
            let n = self.tcx.normalize_for_inference(&self.cx, self.prog, d);
            self.record_normalization_overflow(d, outer_overflow);
            if !matches!(self.tcx.tys.kind(n), TyKind::Assoc(..)) {
                return self.shallow_vars(n);
            }
        }
        t
    }

    /// Preserve normalization overflow as a use-site obligation until final
    /// fulfillment (rustc_trait_selection/src/traits/project.rs:419-439).
    fn record_normalization_overflow(&mut self, projection: TyId, outer: bool) {
        use crate::solve::goal::*;
        let overflow = self.cx.state.norm_overflow.replace(outer);
        if !overflow { return; }
        for pending in &self.pending_goals {
            if matches!(pending.goal.predicate, Predicate::AliasRelate(Term::Ty(a), _, _) if a == projection) { return; }
        }
        let value = self.fresh(0);
        let goal = Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()),
            predicate: Predicate::AliasRelate(Term::Ty(projection), Term::Ty(value), AliasRelationDirection::Equate) };
        let revision = self.tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire);
        self.push_pending(PendingGoal { goal: goal.clone(), lo: self.last_lo,
            certainty: Certainty::overflow(true), stalled: Some((goal, revision)) });
    }

    fn shallow_vars(&self, t: TyId) -> TyId {
        self.tcx.tys.erase_all_regions(self.shallow_region_vars(t))
    }

    fn shallow_region_vars(&self, mut t: TyId) -> TyId {
        loop {
            match self.tcx.tys.kind(t) {
                TyKind::Infer(v) => match self.vars[*v as usize] {
                    VarSt::Bound(b) => t = b,
                    VarSt::Free(_) => return t,
                },
                _ => return t,
            }
        }
    }

    fn deep(&mut self, t: TyId) -> TyId {
        let t = self.tcx.tys.erase_all_regions(t);
        let t = self.resolve_region_vars(t);
        self.tcx.tys.erase_all_regions(t)
    }

    fn resolve_region_vars(&mut self, t: TyId) -> TyId {
        // nothing to resolve: the type is already itself (interning would find it again)
        if !self.tcx.tys.has_infer(t) {
            return t;
        }
        let t = self.shallow_region_vars(t);
        let k = self.tcx.tys.kind(t).clone();
        match k {
            TyKind::Infer(v) => match self.vars[v as usize] {
                VarSt::Free(1) if !self.keep_literal_vars => self.tcx.tys.i32_,
                VarSt::Free(2) if !self.keep_literal_vars => self.tcx.tys.f64_,
                _ => t,
            },
            TyKind::Tuple(v) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.resolve_region_vars(x));
                }
                self.tcx.tys.intern(TyKind::Tuple(n))
            }
            TyKind::Array(e, l) => {
                let e = self.resolve_region_vars(e);
                match crate::types::len_ty(l) {
                    // a const length variable / param: its value once known
                    Some(lt) => {
                        let lt = self.resolve_region_vars(lt);
                        self.tcx.tys.mk_array(e, lt)
                    }
                    None => self.tcx.tys.intern(TyKind::Array(e, l)),
                }
            }
            TyKind::Slice(e) => {
                let e = self.resolve_region_vars(e);
                self.tcx.tys.intern(TyKind::Slice(e))
            }
            TyKind::Ref(m, e, region) => {
                let e = self.resolve_region_vars(e);
                self.tcx.tys.intern(TyKind::Ref(m, e, region))
            }
            TyKind::Ptr(m, e) => {
                let e = self.resolve_region_vars(e);
                self.tcx.tys.intern(TyKind::Ptr(m, e))
            }
            TyKind::Adt(d, v, regions) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.resolve_region_vars(x));
                }
                self.tcx.tys.intern(TyKind::Adt(d, n, regions))
            }
            TyKind::FnPtr(ps, r, c, bound) => {
                let mut n = Vec::new();
                for x in ps {
                    n.push(self.resolve_region_vars(x));
                }
                let r = self.resolve_region_vars(r);
                self.tcx.tys.intern(TyKind::FnPtr(n, r, c, bound))
            }
            TyKind::FnDef(d, v, regions) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.resolve_region_vars(x));
                }
                self.tcx.tys.intern(TyKind::FnDef(d, n, regions))
            }
            TyKind::Dyn(d, v, bs, regions, region, bound, autos) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.resolve_region_vars(x));
                }
                let mut nb = Vec::new();
                for (a, x, n) in bs {
                    nb.push((a, self.resolve_region_vars(x), n));
                }
                self.tcx.tys.intern(TyKind::Dyn(d, n.into(), nb.into(), regions, region, bound, autos.clone()))
            }
            TyKind::Assoc(d, v, regions) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.resolve_region_vars(x));
                }
                self.tcx.tys.intern(TyKind::Assoc(d, n, regions))
            }
            TyKind::Opaque(d, i, v, regions) => {
                let n: Vec<TyId> = v.iter().map(|x| self.resolve_region_vars(*x)).collect();
                self.tcx.tys.intern(TyKind::Opaque(d, i, n, regions))
            }
            TyKind::Closure(f, e, sig, up, owner) => {
                let sig = self.resolve_region_vars(sig);
                let up = self.resolve_region_vars(up);
                self.tcx.tys.intern(TyKind::Closure(f, e, sig, up, owner))
            }
            _ => t,
        }
    }

    /// The same projection normalization as shallow(), retaining the payload
    /// while the unifier's equality/selection keys remain region-insensitive.
    fn shallow_with_regions(&mut self, t: TyId) -> TyId {
        let t = self.shallow_region_vars(t);
        if let TyKind::Assoc(..) = self.tcx.tys.kind(t) {
            let save = self.keep_literal_vars;
            self.keep_literal_vars = true;
            let d = self.resolve_region_vars(t);
            self.keep_literal_vars = save;
            let outer_overflow = self.cx.state.norm_overflow.replace(false);
            let n = self.tcx.normalize(&self.cx, self.prog, d);
            self.record_normalization_overflow(d, outer_overflow);
            if !matches!(self.tcx.tys.kind(n), TyKind::Assoc(..)) {
                return self.shallow_region_vars(n);
            }
        }
        t
    }

    fn unify(&mut self, a: TyId, b: TyId) -> bool {
        let a = self.shallow_with_regions(a);
        let b = self.shallow_with_regions(b);
        if self.tcx.tys.eq_mod_regions(a, b) {
            return true;
        }
        if !matches!(self.tcx.tys.kind(a), TyKind::Infer(_) | TyKind::Error)
            && !matches!(self.tcx.tys.kind(b), TyKind::Infer(_) | TyKind::Error)
            && (self.defined_opaque_var(a).is_some() || self.defined_opaque_var(b).is_some()) {
            let (opaque, other) = if self.defined_opaque_var(a).is_some() { (a, b) } else { (b, a) };
            let variable = self.defined_opaque_var(opaque).unwrap();
            return self.define_opaque_as(opaque, variable, other);
        }
        if let Some(result) = crate::solve::relate::relate_structural(&self.tcx.tys, self, a, b) {
            return result;
        }
        let ka = self.tcx.tys.kind(a).clone();
        let kb = self.tcx.tys.kind(b).clone();
        match (&ka, &kb) {
            (TyKind::Error, _) | (_, TyKind::Error) => true,
            (TyKind::Infer(va), _) => self.bind(*va, b),
            (_, TyKind::Infer(vb)) => self.bind(*vb, a),
            // a projection whose Self is still open (`Cow::Owned(s)`: `<?B as ToOwned>::Owned`
            // against String): rustc normalizes it to a fresh variable under a projection
            // obligation; the equation is checked once the projection normalizes
            // an opaque type and its hidden type (an instance whose args were revealed --
            // `then::<closure, fn printer>` -- checks `f()` returning `impl FnMut`): the same
            // type once revealed (rustc reveals opaques in monomorphic code)
            (TyKind::Opaque(..), _) if self.tcx.opaque_hidden.get(&a) == Some(b) => true,
            (_, TyKind::Opaque(..)) if self.tcx.opaque_hidden.get(&b) == Some(a) => true,
            // a projection whose args are bound variables (`<?A as Arr>::Item` with ?A = A) is
            // the same type as the one spelled with the args (one interned TyId once resolved)
            (TyKind::Assoc(..), _) | (_, TyKind::Assoc(..)) if {
                let (da, db) = (self.deep(a), self.deep(b));
                da == db
            } => true,
            // a projection without inference variables that normalizes (`Self::Output` of the
            // signature, lowered before the body's param env existed): its normal form
            (TyKind::Assoc(..), _) if !self.has_open_infer(a) && self.tcx.normalize_for_inference(&self.cx, self.prog, a) != a => {
                let n = self.tcx.normalize_for_inference(&self.cx, self.prog, a);
                self.unify(n, b)
            }
            (_, TyKind::Assoc(..)) if !self.has_open_infer(b) && self.tcx.normalize_for_inference(&self.cx, self.prog, b) != b => {
                let n = self.tcx.normalize_for_inference(&self.cx, self.prog, b);
                self.unify(a, n)
            }
            (TyKind::Assoc(..), _) => self.defer_proj_eq(b, a),
            (_, TyKind::Assoc(..)) => self.defer_proj_eq(a, b),
            _ => false,
        }
    }

    /// The hidden type variable of the opaque type `o` when this body defines it.
    fn defined_opaque_var(&self, o: TyId) -> Option<TyId> {
        self.opaque_vars.iter().find(|x| x.0 == o).map(|x| x.1)
    }

    /// `o` (defined by this body, hidden type variable `v`) related to `other`: `v = other`.
    /// A `v` that an earlier use bound to `o` itself (a recursive call's result met the
    /// declared return type) holds no information yet: it is replaced.
    fn define_opaque_as(&mut self, o: TyId, v: TyId, other: TyId) -> bool {
        let cur = self.shallow(v);
        if cur == o {
            if let TyKind::Infer(id) = self.tcx.tys.kind(v).clone() {
                if let VarSt::Bound(_) = self.vars[id as usize] {
                    self.set_var(id, VarSt::Bound(other));
                    return true;
                }
            }
        }
        self.unify(v, other)
    }

    fn has_open_infer(&mut self, t: TyId) -> bool {
        let d = self.deep(t);
        self.tcx.tys.has_infer(d)
    }

    fn defer_proj_eq(&mut self, other: TyId, proj: TyId) -> bool {
        self.projection_relations.push((other, proj, self.last_lo));
        self.undo.push((u32::MAX, VarSt::Free(0), UniverseIndex::ROOT));
        true
    }

    /// `&T -> &dyn Tr`, `*T -> *dyn Tr`, `P<T> -> P<dyn Tr>` when T implements Tr.
    /// Array-to-slice unsizing (rustc coerce_unsized with `[T; N]: Unsize<[T]>`): `&[T; N]` ->
    /// `&[T]` / `*const [T]`, `*mut [T; N]` -> `*mut [T]`, and smart pointers (`Box<[T; N]>` ->
    /// `Box<[T]>`, Rc, Arc, ..; same shape as `dyn_coercion`). Inference variables are only bound
    /// when the coercion applies.
    /// ADT coercions and unsized tails require structs (rustc_hir_analysis/src/coherence/
    /// builtin.rs:870-871); enums/unions must relate their generic arguments normally.
    fn unsize_coercion(&mut self, ka: &TyKind, kx: &TyKind) -> bool {
        let save = self.snapshot();
        let ok = match (ka, kx) {
            (TyKind::Ref(m1, a, _), TyKind::Ref(m2, d, _)) | (TyKind::Ref(m1, a, _), TyKind::Ptr(m2, d)) | (TyKind::Ptr(m1, a), TyKind::Ptr(m2, d)) if *m1 || !*m2 => self.array_to_slice(*a, *d),
            (TyKind::Adt(d1, xs, _), TyKind::Adt(d2, ys, _)) if d1 == d2 && self.prog.def(*d1).kind == DefKind::Struct && xs.len() == ys.len() => {
                let mut found = None;
                for i in 0..xs.len() {
                    let (x, y) = (self.shallow(xs[i]), self.shallow(ys[i]));
                    // `Box<[T; N]>` -> `Box<[T]>`, also through a struct tail (`Box<S<[T; N]>>`
                    // -> `Box<S<[T]>>`)
                    if matches!(self.tcx.tys.kind(x), TyKind::Array(..)) && matches!(self.tcx.tys.kind(y), TyKind::Slice(..))
                        || x != y && matches!((self.tcx.tys.kind(x), self.tcx.tys.kind(y)), (TyKind::Adt(a1, _, _), TyKind::Adt(a2, _, _)) if a1 == a2) && self.has_slice(y)
                    {
                        found = Some(i);
                    }
                }
                match found {
                    Some(i) => (0..xs.len()).all(|j| j == i || self.unify(xs[j], ys[j])) && self.array_to_slice(xs[i], ys[i]),
                    None => false,
                }
            }
            _ => false,
        };
        if !ok {
            self.rollback(save);
        }
        ok
    }

    /// `[T; N]` -> `[T]`, also as the tail of a struct (`Holder<[T; N]>` -> `Holder<[T]>`, rustc
    /// Unsize for structs whose last field's type is the only one mentioning the parameter).
    fn array_to_slice(&mut self, a: TyId, d: TyId) -> bool {
        let (a, d) = (self.shallow(a), self.shallow(d));
        match (self.tcx.tys.kind(a).clone(), self.tcx.tys.kind(d).clone()) {
            (TyKind::Array(ea, _), TyKind::Slice(es)) => self.unify(ea, es),
            (TyKind::Adt(d1, xs, _), TyKind::Adt(d2, ys, _)) if d1 == d2 && self.prog.def(d1).kind == DefKind::Struct && xs.len() == ys.len() && !xs.is_empty() => {
                let i = match (0..xs.len()).find(|&i| {
                    let (x, y) = (self.shallow(xs[i]), self.shallow(ys[i]));
                    x != y && !matches!(self.tcx.tys.kind(y), TyKind::Infer(_))
                }) {
                    Some(i) => i,
                    None => return false,
                };
                (0..xs.len()).all(|j| j == i || self.unify(xs[j], ys[j])) && self.array_to_slice(xs[i], ys[i])
            }
            _ => false,
        }
    }

    /// `P<?T>` against `P<dyn Tr>` (same pointer shape, the pointee still open).
    fn pointee_pair_open_to_dyn(&mut self, ka: &TyKind, kx: &TyKind) -> bool {
        let (a, d) = match (ka, kx) {
            (TyKind::Ref(_, a, _), TyKind::Ref(_, d, _)) | (TyKind::Ptr(_, a), TyKind::Ptr(_, d)) => (*a, *d),
            (TyKind::Adt(d1, xs, _), TyKind::Adt(d2, ys, _)) if d1 == d2 && self.prog.def(*d1).kind == DefKind::Struct && xs.len() == ys.len() && !xs.is_empty() => {
                match (0..xs.len()).find(|&i| {
                    let y = self.shallow(ys[i]);
                    matches!(self.tcx.tys.kind(y), TyKind::Dyn(..))
                }) {
                    Some(i) => (xs[i], ys[i]),
                    None => return false,
                }
            }
            _ => return false,
        };
        let (a, d) = (self.shallow(a), self.shallow(d));
        matches!(self.tcx.tys.kind(a), TyKind::Infer(_)) && matches!(self.tcx.tys.kind(d), TyKind::Dyn(..))
    }

    /// Is item `d` visible from this body's module (`pub`, or private and defined in this module
    /// or one of its ancestors)?
    fn item_visible(&self, d: DefId) -> bool {
        let def = self.prog.def(d);
        if def.krate != self.prog.def(self.b.def).krate {
            return true;
        }
        if def.is_pub {
            // `pub`, `pub(super)`, `pub(in path)`: inside that module only
            let vis = &self.prog.files[def.file as usize].ast.item(def.item).vis;
            // (no written visibility on a pub def: inherited -- a trait's items, a variant)
            return match vis {
                crate::ast::Vis::Pub | crate::ast::Vis::Private => true,
                _ => match self.prog.vis_module(def.file, def.scope, vis) {
                    Some(m) => self.prog.mod_within(self.module, m),
                    None => true,
                },
            };
        }
        let home = self.prog.mods[def.scope as usize].normal;
        let mut m = Some(self.prog.mods[self.module as usize].normal);
        let mut guard = 0;
        while let Some(x) = m {
            if x == home {
                return true;
            }
            guard += 1;
            if guard > 64 {
                break;
            }
            m = self.prog.mods[x as usize].parent_mod.map(|p| self.prog.mods[p as usize].normal);
        }
        false
    }

    /// Coerces `a` to `x` if a coercion (or unification) applies; otherwise leaves no trace
    /// (bindings, errors and the recorded coercion are rolled back).
    fn try_coerce(&mut self, a: TyId, x: TyId, e: Option<ExprId>) -> bool {
        let snap = self.snapshot();
        let n_err = self.b.errors.len();
        let n_dd = self.deferred_dyn.len();
        let old = e.and_then(|e| self.b.coerce.get(&e.0).copied());
        if self.coerce_or_unify(a, x, e, 0) {
            return true;
        }
        self.rollback(snap);
        self.b.errors.truncate(n_err);
        self.deferred_dyn.truncate(n_dd);
        if let Some(e) = e {
            match old {
                Some(c) => {
                    self.b.coerce.insert(e.0, c);
                }
                None => {
                    self.b.coerce.remove(&e.0);
                }
            }
        }
        false
    }

    fn is_literal_var(&self, t: TyId) -> bool {
        match self.tcx.tys.kind(t) {
            TyKind::Infer(v) => matches!(self.vars[*v as usize], VarSt::Free(1) | VarSt::Free(2)),
            _ => false,
        }
    }

    /// The fn pointer type a fn item / capture-free closure / fn pointer coerces to.
    fn fn_ptr_of(&mut self, t: TyId) -> Option<TyId> {
        let t = self.shallow_with_regions(t);
        match self.tcx.tys.kind(t).clone() {
            TyKind::FnPtr(..) => Some(t),
            TyKind::FnDef(d, args, _) => {
                let sig = self.tcx.fn_item_sig(self.prog, d).cloned()?;
                let poly = self.tcx.tys.intern(TyKind::FnPtr(sig.params, sig.ret, sig.header, sig.bound_regions));
                Some(self.tcx.tys.subst(poly, &args))
            }
            TyKind::Closure(_, _, sig, up, _) => {
                let captures = match self.tcx.tys.kind(up) {
                    TyKind::Tuple(v) => !v.is_empty(),
                    _ => true,
                };
                if captures {
                    None
                } else {
                    Some(sig)
                }
            }
            _ => None,
        }
    }

    /// rustc CoerceMany: a new branch value joins the branches seen so far -- the new value
    /// coerces to their type, else (two different fn items / closures) all meet at a fn
    /// pointer, else the earlier ones coerce to the new type (`&String` then `&str`).
    fn coerce_many(&mut self, prev: &[ExprId], prev_ty: TyId, new_e: ExprId, new_ty: TyId, lo: u32) -> TyId {
        if self.try_coerce(new_ty, prev_ty, Some(new_e)) {
            return prev_ty;
        }
        if let (Some(mut fp), Some(other)) = (self.fn_ptr_of(prev_ty), self.fn_ptr_of(new_ty)) {
            // rustc_hir_typeck/src/coercion.rs:1404: the common signature can be unsafe.
            if let (TyKind::FnPtr(ps, r, header, bound), TyKind::FnPtr(_, _, other, _)) =
                (self.tcx.tys.kind(fp).clone(), self.tcx.tys.kind(other).clone()) {
                if other.safety == Safety::Unsafe {
                    fp = self.tcx.tys.intern(TyKind::FnPtr(ps, r,
                        FnHeader { safety: Safety::Unsafe, ..header }, bound));
                }
            }
            let snap = self.snapshot();
            let mut ok = true;
            for &p in prev {
                let pt = self.b.ty(p);
                ok = ok && self.try_coerce(pt, fp, Some(p));
            }
            ok = ok && self.try_coerce(new_ty, fp, Some(new_e));
            if ok {
                return fp;
            }
            self.rollback(snap);
        }
        if !prev.is_empty() {
            let snap = self.snapshot();
            let mut ok = true;
            for &p in prev {
                let pt = self.b.ty(p);
                ok = ok && self.try_coerce(pt, new_ty, Some(p));
            }
            if ok {
                return new_ty;
            }
            self.rollback(snap);
        }
        self.coerce_or_unify(new_ty, prev_ty, Some(new_e), lo);
        prev_ty
    }

    /// Trait object upcasting (stable since 1.86): a pointer to `dyn Sub` as a pointer to
    /// `dyn Super` where Super is a supertrait of Sub (transitively); pointer shapes as for
    /// `dyn_coercion`. Generic supertraits other than the Fn family are not upcast here.
    fn dyn_upcast(&mut self, ka: &TyKind, kx: &TyKind) -> Option<(TyId, TyId)> {
        let (a, d) = match (ka, kx) {
            (TyKind::Ref(m1, a, _), TyKind::Ref(m2, d, _)) | (TyKind::Ptr(m1, a), TyKind::Ptr(m2, d)) | (TyKind::Ref(m1, a, _), TyKind::Ptr(m2, d)) if *m1 || !*m2 => (*a, *d),
            (TyKind::Adt(d1, xs, _), TyKind::Adt(d2, ys, _)) if d1 == d2 && self.prog.def(*d1).kind == DefKind::Struct && xs.len() == ys.len() => {
                let i = (0..xs.len()).find(|&i| {
                    let (x, y) = (self.shallow(xs[i]), self.shallow(ys[i]));
                    matches!(self.tcx.tys.kind(x), TyKind::Dyn(..)) && matches!(self.tcx.tys.kind(y), TyKind::Dyn(..)) && x != y
                })?;
                for j in 0..xs.len() {
                    if j != i && !self.unify(xs[j], ys[j]) {
                        return None;
                    }
                }
                (xs[i], ys[i])
            }
            _ => return None,
        };
        let (a, d) = (self.shallow(a), self.shallow(d));
        let (sd, sargs, sautos) = match self.tcx.tys.kind(a).clone() {
            TyKind::Dyn(t, v, _, _, _, _, autos) => (t, v, autos),
            _ => return None,
        };
        let (td, targs, tautos) = match self.tcx.tys.kind(d).clone() {
            TyKind::Dyn(t, v, _, _, _, _, autos) => (t, v, autos),
            _ => return None,
        };
        if !tautos.iter().all(|t| sautos.contains(t)) { return None; }
        if sd == td {
            let TyKind::Dyn(td, args, bindings, rs, region, bound, _) = self.tcx.tys.kind(a).clone() else { unreachable!() };
            let erased = self.tcx.tys.intern(TyKind::Dyn(td, args, bindings, rs, region, bound, tautos));
            return if self.unify(erased, d) { Some((a, d)) } else { None };
        }
        // Fn -> FnMut -> FnOnce: the same call entry
        if self.is_fn_trait(sd) && self.is_fn_trait(td) {
            if let (Some(x), Some(y)) = (sargs.first(), targs.first()) {
                if self.unify(*x, *y) {
                    return Some((a, d));
                }
            }
            return None;
        }
        // the supertrait instantiations of `sd<sargs>` (rustc: upcasting to a supertrait trait
        // ref; `dyn Foo<bool>` -> `dyn Bar<bool>` where `Foo<T>: Bar<i32> + Bar<T>`)
        let sargs: Vec<TyId> = sargs.iter().map(|x| self.deep(*x)).collect();
        let mut todo = vec![(sd, sargs)];
        let mut seen: Vec<(DefId, Vec<TyId>)> = Vec::new();
        let mut hits: Vec<Vec<TyId>> = Vec::new();
        while let Some(t) = todo.pop() {
            if seen.contains(&t) {
                continue;
            }
            seen.push(t.clone());
            for (sup, supargs) in self.tcx.trait_super_refs(&self.cx, self.prog, t.0, &t.1) {
                if sup == td && !hits.contains(&supargs) {
                    hits.push(supargs.clone());
                }
                todo.push((sup, supargs));
            }
        }
        // the one instantiation the target's args can be
        let mut fit = Vec::new();
        for h in hits {
            let snap = self.snapshot();
            let ok = h.len() == targs.len() && (0..h.len()).all(|i| self.unify(h[i], targs[i]));
            self.rollback(snap);
            if ok {
                fit.push(h);
            }
        }
        if fit.len() == 1 {
            let h = fit.pop().unwrap();
            for i in 0..h.len() {
                self.unify(h[i], targs[i]);
            }
            return Some((a, d));
        }
        None
    }

    fn dyn_coercion(&mut self, ka: &TyKind, kx: &TyKind) -> Option<(TyId, TyId)> {
        let (src, dy) = match (ka, kx) {
            (TyKind::Ref(m1, a, _), TyKind::Ref(m2, d, _)) | (TyKind::Ref(m1, a, _), TyKind::Ptr(m2, d)) | (TyKind::Ptr(m1, a), TyKind::Ptr(m2, d)) if *m1 || !*m2 => (*a, *d),
            (TyKind::Adt(d1, xs, _), TyKind::Adt(d2, ys, _)) if d1 == d2 && self.prog.def(*d1).kind == DefKind::Struct && xs.len() == ys.len() => {
                let mut found = None;
                for i in 0..xs.len() {
                    let y = self.shallow(ys[i]);
                    let x = self.shallow(xs[i]);
                    // a literal pointee (`Box::new(1)` as `Box<dyn Any>`) is decided below: the one
                    // numeric impl, or the literal fallback's
                    let open = match self.tcx.tys.kind(x) {
                        TyKind::Infer(v) => !matches!(self.vars[*v as usize], VarSt::Free(1) | VarSt::Free(2)),
                        TyKind::Dyn(..) => true,
                        _ => false,
                    };
                    if x != y && self.has_dyn(y) && !open {
                        found = Some(i);
                    }
                }
                let i = found?;
                for j in 0..xs.len() {
                    if j != i && !self.unify(xs[j], ys[j]) {
                        return None;
                    }
                }
                (xs[i], ys[i])
            }
            _ => return None,
        };
        // `P<S<..T..>>` -> `P<S<..dyn Tr..>>` (also `&S<T>` -> `&S<dyn Tr>`): struct tail
        // unsizing (rustc coerce_unsized: `S<T>: Unsize<S<U>>` when the last field's type does),
        // down to the type that becomes the trait object
        let (src, dy) = {
                let (mut x, mut y) = (self.shallow(src), self.shallow(dy));
                loop {
                    if matches!(self.tcx.tys.kind(y), TyKind::Dyn(..)) {
                        break (x, y);
                    }
                    match (self.tcx.tys.kind(x).clone(), self.tcx.tys.kind(y).clone()) {
                        (TyKind::Adt(a1, xa, _), TyKind::Adt(a2, ya, _)) if a1 == a2 && xa.len() == ya.len() && self.tcx.adts.get(&a1).map_or(false, |ad| !ad.is_enum && !ad.is_union) => {
                            let mut k = None;
                            for j in 0..xa.len() {
                                let yj = self.shallow(ya[j]);
                                if self.has_dyn(yj) && self.shallow(xa[j]) != yj {
                                    k = Some(j);
                                } else if !self.unify(xa[j], ya[j]) {
                                    return None;
                                }
                            }
                            let k = k?;
                            x = self.shallow(xa[k]);
                            y = self.shallow(ya[k]);
                        }
                        _ => return None,
                    }
                }
        };
        let src = self.shallow(src);
        let dy = self.shallow(dy);
        let (td, targs, autos) = match self.tcx.tys.kind(dy).clone() {
            TyKind::Dyn(td, targs, _, _, _, _, autos) => (td, targs, autos),
            _ => return None,
        };
        if matches!(self.tcx.tys.kind(src), TyKind::Dyn(..)) { return None; }
        for auto in autos {
            if matches!(self.select_trait(auto, src, &[]), SelectionResult::NoSolution) { return None; }
        }
        // Selection relates the trait arguments and retains every unresolved goal.
        // Object bindings are obligations even when the principal trait is ambiguous.
        if matches!(self.select_trait(td, src, &targs), SelectionResult::NoSolution) { return None; }
        let mut refs = vec![(td, targs.to_vec())];
        let mut i = 0;
        while i < refs.len() {
            let (def, args) = refs[i].clone();
            for bound in self.tcx.trait_super_refs_of(&self.cx, self.prog, def, src, &args) {
                if !refs.contains(&bound) { refs.push(bound); }
            }
            i += 1;
        }
        let bindings = match self.tcx.tys.kind(dy).clone() {
            TyKind::Dyn(_, _, bindings, ..) => bindings,
            _ => unreachable!(),
        };
        for (ad, value, _) in bindings {
            use crate::solve::goal::{AliasKind, AliasTerm, Clause, Goal, ParamEnvId, Predicate, ProjectionPredicate, Term};
            let owner = self.prog.def(ad).parent;
            let mut args = vec![src];
            if let Some((_, trait_args)) = refs.iter().find(|(def, _)| *def == owner) { args.extend_from_slice(trait_args); }
            let goal = Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()),
                predicate: Predicate::Clause(Clause::Projection(ProjectionPredicate {
                    alias: AliasTerm { kind: AliasKind::Projection, def: ad, args }, term: Term::Ty(value),
                })) };
            self.register_goal(goal, self.last_lo);
        }
        Some((src, dy))
    }

    /// The where-clauses of this body on `t` (and the trait's implicit `Self: Trait<..>` in
    /// its own bodies), elaborated through supertraits: rustc's param-env candidates, as
    /// (trait, trait args) with the body's args substituted.
    fn param_bounds(&mut self, t: TyId) -> Vec<(DefId, Vec<TyId>)> {
        let mut todo: Vec<(DefId, Vec<TyId>)> = Vec::new();
        for (pi, bd, bargs) in self.tcx.fn_trait_bounds(self.prog, self.b.def).cloned().unwrap_or_default() {
            if let Some(a) = self.b.args.get(pi as usize).copied() {
                if self.shallow(a) != t {
                    continue;
                }
                let ba: Vec<TyId> = bargs.iter().map(|x| self.tcx.tys.subst_for_inference(*x, &self.b.args)).collect();
                todo.push((bd, ba));
            }
        }
        // the enclosing impl's bounds on its params (`impl<R: BufRead> D<R>`: the fn's own bound
        // tables hold only its own generics); Fn-family sugar is param_fn_sig's
        if let TyKind::Param(pi) = self.tcx.tys.kind(t).clone() {
            let parent = self.prog.def(self.b.def).parent;
            if self.prog.def(parent).kind == DefKind::Impl {
                let env = self.env.clone();
                for (bi, bfile, path) in env.bounds.iter() {
                    if *bi != pi || matches!(self.prog.files[*bfile as usize].ast.segs(path.segs).last().and_then(|l| self.prog.files[*bfile as usize].ast.gargs(l.args)), Some(GenericArgs::Paren(..))) {
                        continue;
                    }
                    if let Some(td) = self.tcx.resolve_type_path_def(self.prog, *bfile, self.module, path) {
                        if self.prog.def(td).kind != DefKind::Trait {
                            continue;
                        }
                        let inst = self.inst_args.clone();
                        let ta: Vec<TyId> = self.tcx.lower_generic_args(&self.cx, self.prog, *bfile, self.module, &env, path).into_iter().map(|x| self.tcx.tys.subst_for_inference(x, &inst)).collect();
                        let ta = self.tcx.fill_trait_defaults(&self.cx, self.prog, td, t, ta);
                        todo.push((td, ta));
                    }
                }
            }
        }
        // where-clauses naming this type itself (`where A::Item: Clone`, the fn's or its impl's)
        if matches!(self.tcx.tys.kind(t), TyKind::Assoc(..) | TyKind::Param(_)) {
            for (st, d, a) in self.tcx.fn_ty_bounds(self.prog, self.b.def).cloned().unwrap_or_default() {
                let st = self.tcx.tys.subst_for_inference(st, &self.b.args);
                let st = self.tcx.normalize_for_inference(&self.cx, self.prog, st);
                if st == t {
                    let a: Vec<TyId> = a.iter().map(|x| self.tcx.tys.subst_for_inference(*x, &self.b.args)).collect();
                    todo.push((d, a));
                }
            }
        }
        // a projection (`A::Mem` with `type Mem: Default`): its declared bounds (rustc
        // item_bounds, part of the param env of a generic body)
        if let TyKind::Assoc(ad, pa, _) = self.tcx.tys.kind(t).clone() {
            todo.extend(self.tcx.assoc_decl_bounds(&self.cx, self.prog, ad, &pa));
        }
        if let Some(trd) = self.env.trait_def {
            let a0 = self.b.args.first().copied();
            if self.prog.def(self.b.def).parent == trd && a0.map(|a| self.shallow(a)) == Some(t) {
                let nt = self.tcx.trait_generic_count(self.prog, trd);
                todo.push((trd, self.b.args.get(1..=nt).map_or(Vec::new(), |a| a.to_vec())));
            }
        }
        let mut out: Vec<(DefId, Vec<TyId>)> = Vec::new();
        while let Some((d, a)) = todo.pop() {
            if out.iter().any(|(x, xa)| *x == d && *xa == a) {
                continue;
            }
            todo.extend(self.tcx.trait_super_refs_of(&self.cx, self.prog, d, t, &a));
            out.push((d, a));
        }
        out
    }

    /// The param env of a polymorphic body (TypingEnv::param_env): every param's bounds
    /// (param_bounds, plus `Copy`, which the bound tables leave out), and the declared bounds of
    /// the associated types of those traits on the param (`<I as IntoIterator>::IntoIter:
    /// Iterator`), elaborated through supertraits.
    fn param_env_entries(&mut self) -> crate::tcx::ParamEnv {
        let mut params: Vec<TyId> = Vec::new();
        for a in self.b.args.clone() {
            if matches!(self.tcx.tys.kind(a), TyKind::Param(_)) && !params.contains(&a) {
                params.push(a);
            }
        }
        let mut out: Vec<(TyId, DefId, Vec<TyId>)> = Vec::new();
        if let Some(sized) = self.tcx.lang_items.get(crate::lang_items::LangItem::Sized) {
            for &pi in &self.env.sized_params {
                if let Some(&ty) = self.b.args.get(pi as usize) { out.push((ty, sized, Vec::new())); }
            }
        }
        let mut eqs: Vec<(TyId, TyId)> = Vec::new();
        // the where-clauses' bindings (`I: IntoIterator<Item = u32>`)
        for (pi, ad, targs, v) in self.tcx.fn_bound_bindings(self.prog, self.b.def).cloned().unwrap_or_default() {
            if let Some(&p) = self.b.args.get(pi as usize) {
                let mut pa = vec![p];
                pa.extend(targs.iter().map(|t| self.tcx.tys.subst_for_inference(*t, &self.b.args)));
                let proj = self.tcx.tys.intern(TyKind::Assoc(ad, pa, crate::types::RegionArgsId::EMPTY));
                eqs.push((proj, self.tcx.tys.subst_for_inference(v, &self.b.args)));
            }
        }
        // where-clauses on other types than a param (`for<'x> &'x V: IntoIterator`,
        // `Vec<T>: Debug`): the env proves them as written
        for (st, d, a) in self.tcx.fn_ty_bounds(self.prog, self.b.def).cloned().unwrap_or_default() {
            let st = self.tcx.tys.subst_for_inference(st, &self.b.args);
            let a: Vec<TyId> = a.iter().map(|x| self.tcx.tys.subst_for_inference(*x, &self.b.args)).collect();
            if !out.iter().any(|(t, x, xa)| *t == st && *x == d && *xa == a) {
                out.push((st, d, a));
            }
        }
        let copy = self.tcx.copy_trait;
        let raw = self.tcx.item_env(self.prog, self.b.def).bounds;
        for p in params {
            let bs = self.param_bounds(p);
            for (d, a) in &bs {
                out.push((p, *d, a.clone()));
                // the trait's associated types on this param, by their declared bounds
                for it in self.prog.traits[self.prog.def(*d).sub as usize].clone() {
                    if self.prog.def(it).kind != DefKind::AssocTy {
                        continue;
                    }
                    let mut pa = vec![p];
                    pa.extend(a.iter().copied());
                    let proj = self.tcx.tys.intern(TyKind::Assoc(it, pa.clone(), crate::types::RegionArgsId::EMPTY));
                    let (mut todo, peqs) = self.tcx.assoc_decl_bounds_eqs(&self.cx, self.prog, it, &pa);
                    eqs.extend(peqs);
                    let mut seen: Vec<(DefId, Vec<TyId>)> = Vec::new();
                    while let Some((bd, ba)) = todo.pop() {
                        if seen.contains(&(bd, ba.clone())) {
                            continue;
                        }
                        todo.extend(self.tcx.trait_super_refs_of(&self.cx, self.prog, bd, proj, &ba));
                        out.push((proj, bd, ba.clone()));
                        seen.push((bd, ba));
                    }
                }
            }
            if let (Some(ct), TyKind::Param(k)) = (copy, self.tcx.tys.kind(p).clone()) {
                let module = self.module;
                let has_copy = bs.iter().any(|(d, _)| *d == ct)
                    || raw.iter().any(|(pi, f, path)| *pi == k && self.tcx.resolve_type_path_def(self.prog, *f, module, path) == Some(ct))
                    || bs.iter().any(|(d, _)| self.tcx.trait_closure.get(d).map_or(false, |c| c.contains(&ct)));
                if has_copy {
                    out.push((p, ct, Vec::new()));
                }
            }
        }
        use crate::solve::goal::{Clause, Term};
        if let Some(clauses) = self.tcx.item_clauses(self.prog, self.b.def) {
            for clause in clauses {
                match clause {
                    Clause::Trait(p) => {
                        let mut args = Vec::new();
                        for t in &p.trait_ref.args { args.push(self.tcx.tys.subst_for_inference(*t, &self.b.args)); }
                        out.push((args[0], p.trait_ref.def, args[1..].to_vec()));
                    }
                    Clause::Projection(p) => {
                        let mut args = Vec::new();
                        for t in &p.alias.args { args.push(self.tcx.tys.subst_for_inference(*t, &self.b.args)); }
                        let lhs = self.tcx.tys.intern(TyKind::Assoc(p.alias.def, args, crate::types::RegionArgsId::EMPTY));
                        if let Term::Ty(t) = p.term { eqs.push((lhs, self.tcx.tys.subst_for_inference(t, &self.b.args))); }
                    }
                    _ => {}
                }
            }
        }
        // the bound traits' supertrait bindings (`trait FloatNumber: Neg<Output = Self>` gives
        // `<T as Neg>::Output == T` for T: FloatNumber, and so for a bounded projection)
        for (st, d, a) in out.clone() {
            for e in self.tcx.trait_super_bindings(&self.cx, self.prog, d, st, &a) {
                if !eqs.contains(&e) {
                    eqs.push(e);
                }
            }
        }
        crate::tcx::ParamEnv { preds: out, eqs }
    }

    /// A call of a value whose type is a generic param with an `Fn*` bound (`f(1)` with
    /// `F: FnMut(u32) -> u32`): the bound's signature.
    /// The Fn-family supertrait signature of a trait object's principal (transitively).
    fn dyn_super_fn_sig(&mut self, td: DefId, t: TyId, targs: &[TyId]) -> Option<(Vec<TyId>, TyId)> {
        let mut todo = self.tcx.trait_super_refs_of(&self.cx, self.prog, td, t, targs);
        let mut seen = Vec::new();
        while let Some((d, a)) = todo.pop() {
            if self.is_fn_trait(d) {
                if let Some(sig) = self.tcx.callable_sig(&self.cx, t, d, &a) { return Some(sig); }
            }
            if seen.contains(&d) {
                continue;
            }
            seen.push(d);
            todo.extend(self.tcx.trait_super_refs_of(&self.cx, self.prog, d, t, &a));
        }
        None
    }

    fn param_fn_sig(&mut self, t: TyId) -> Option<(Vec<TyId>, TyId)> {
        for bound in self.tcx.callable_signatures(self.prog, self.b.def) {
            let (pi, sig) = (bound.param, bound.signature);
            if self.b.args.get(pi as usize).map_or(false, |a| *a == t) {
                let sig = self.tcx.tys.subst_for_inference(sig, &self.b.args);
                if let TyKind::FnPtr(ps, r, _, _) = self.tcx.tys.kind(sig).clone() {
                    return Some((ps, r));
                }
            }
        }
        for (d, a) in self.param_bounds(t) {
            if self.is_fn_trait(d) {
                if let Some(sig) = self.tcx.callable_sig(&self.cx, t, d, &a) { return Some(sig); }
            }
        }

        None
    }

    /// Is `t` dynamically sized (str, slice, dyn, or a struct whose last field is)?
    fn is_unsized_ty(&mut self, t: TyId) -> bool {
        let t = self.shallow(t);
        match self.tcx.tys.kind(t).clone() {
            TyKind::Dyn(..) | TyKind::Str | TyKind::Slice(_) => true,
            TyKind::Adt(d, args, _) => {
                let last = match self.tcx.adts.get(&d) {
                    Some(a) if !a.is_enum && !a.is_union => a.variants.first().and_then(|v| v.fields.last()).map(|f| f.ty),
                    _ => None,
                };
                match last {
                    Some(ft) => {
                        let ft = self.tcx.tys.subst_for_inference(ft, &args);
                        self.is_unsized_ty(ft)
                    }
                    None => false,
                }
            }
            _ => false,
        }
    }

    /// Does `t` contain a trait object type (as a generic argument, transitively)?
    fn has_dyn(&mut self, t: TyId) -> bool {
        let t = self.shallow(t);
        match self.tcx.tys.kind(t).clone() {
            TyKind::Dyn(..) => true,
            TyKind::Adt(_, v, _) => v.iter().any(|x| self.has_dyn(*x)),
            _ => false,
        }
    }

    fn has_slice(&mut self, t: TyId) -> bool {
        let t = self.shallow(t);
        match self.tcx.tys.kind(t).clone() {
            TyKind::Slice(..) => true,
            TyKind::Adt(_, v, _) => v.iter().any(|x| self.has_slice(*x)),
            _ => false,
        }
    }

    fn occurs(&mut self, v: u32, t: TyId, depth: u32) -> bool {
        if depth > 64 {
            return true;
        }
        let t = self.shallow_vars(t);
        match self.tcx.tys.kind(t).clone() {
            TyKind::Infer(w) => w == v,
            TyKind::Tuple(xs) | TyKind::Adt(_, xs, _) | TyKind::FnDef(_, xs, _) | TyKind::Assoc(_, xs, _) => xs.iter().any(|x| self.occurs(v, *x, depth + 1)),
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::Ref(_, e, _) | TyKind::Ptr(_, e) => self.occurs(v, e, depth + 1),
            TyKind::FnPtr(ps, r, _, _) => ps.iter().any(|x| self.occurs(v, *x, depth + 1)) || self.occurs(v, r, depth + 1),
            TyKind::Dyn(_, xs, bs, _, _, _, _) => xs.iter().any(|x| self.occurs(v, *x, depth + 1)) || bs.iter().any(|x| self.occurs(v, x.1, depth + 1)),
            TyKind::Closure(_, _, s, u, _) => self.occurs(v, s, depth + 1) || self.occurs(v, u, depth + 1),
            _ => false,
        }
    }

    /// `&&u8` -> `u8` when the referent is a primitive number/bool/char; other types unchanged.
    fn peel_prim_refs(&mut self, t: TyId) -> TyId {
        let mut cur = self.shallow(t);
        let mut n = 0;
        while let TyKind::Ref(_, inner, _) = self.tcx.tys.kind(cur).clone() {
            cur = self.shallow(inner);
            n += 1;
        }
        if n > 0 && (self.is_numeric(cur) || matches!(self.tcx.tys.kind(cur), TyKind::Bool | TyKind::Char)) {
            cur
        } else {
            t
        }
    }


    /// Autoderef steps from `a` to `x` (both pointees of references), if any.
    fn deref_coercion(&mut self, e: ExprId, a: TyId, x: TyId) -> Option<u8> {
        let xs = self.shallow(x);
        // an open target takes the source as is; an integer / float variable is no reference,
        // so `&&{integer}` to `&{integer}` derefs (rustc coerce_borrowed_pointer autoderefs
        // until the pointees unify)
        if matches!(self.tcx.tys.kind(xs), TyKind::Infer(_)) && !self.is_literal_var(xs) {
            return None;
        }
        let mut cur = self.shallow(a);
        let key = e.0 | DEREF_COERCE_KEY;
        for step in 0..8u8 {
            cur = self.deref_step(key, step, cur)?;
            let save = self.snapshot();
            if self.unify(cur, xs) {
                return Some(step + 1);
            }
            self.rollback(save);
        }
        None
    }

    pub fn is_fn_trait(&self, td: DefId) -> bool {
        let d = self.prog.def(td);
        Some(d.krate) == self.prog.prelude_crate && matches!(self.prog.name(td), "Fn" | "FnMut" | "FnOnce")
    }

    fn bind(&mut self, v: u32, t: TyId) -> bool {
        let kind = match self.vars[v as usize] {
            VarSt::Free(k) => k,
            VarSt::Bound(b) => return self.unify(b, t),
        };
        let tk = self.tcx.tys.kind(t).clone();
        // A projection mentioning this variable can normalize to the variable itself
        // (`?I = <Range<?I> as Iterator>::Item`). Relate its normalized value before
        // the occurs check (rustc_trait_selection/src/traits/project.rs:211-246;
        // ambiguous projections remain obligations at 256-282).
        if matches!(tk, TyKind::Assoc(..)) && self.occurs(v, t, 0) {
            let tv = self.tcx.tys.intern(TyKind::Infer(v));
            return self.defer_proj_eq(tv, t);
        }
        // occurs check: `?v = Option<?v>` would be an infinite type
        if !matches!(tk, TyKind::Infer(_)) && self.occurs(v, t, 0) {
            return false;
        }
        match tk {
            TyKind::Infer(w) => {
                let k2 = match self.vars[w as usize] {
                    VarSt::Free(k) => k,
                    _ => 0,
                };
                if kind != 0 && k2 != 0 && kind != k2 {
                    return false;
                }
                if kind != 0 && k2 == 0 {
                    // keep the more specific variable free
                    let tv = self.tcx.tys.intern(TyKind::Infer(v));
                    self.merge_var_universes(v, w);
                    self.set_var(w, VarSt::Bound(tv));
                    return true;
                }
                self.merge_var_universes(w, v);
                self.set_var(v, VarSt::Bound(t));
                true
            }
            TyKind::Int(_) if kind == 1 || kind == 0 => {
                self.set_var(v, VarSt::Bound(t));
                true
            }
            TyKind::Float(_) if kind == 2 || kind == 0 => {
                self.set_var(v, VarSt::Bound(t));
                true
            }
            _ if kind == 0 => {
                self.set_var(v, VarSt::Bound(t));
                true
            }
            TyKind::Error => true,
            TyKind::Assoc(..) => {
                let tv = self.tcx.tys.intern(TyKind::Infer(v));
                self.projection_relations.push((tv, t, self.last_lo));
                self.undo.push((u32::MAX, VarSt::Free(0), UniverseIndex::ROOT));
                true
            }
            _ => false,
        }
    }

    /// Transfer relation-produced projection equations to ordinary fulfillment.
    /// A concrete alias may still depend on a closure kind; lack of free type
    /// variables does not make a stuck projection a mismatch (project.rs:262).
    fn flush_projection_relations(&mut self) {
        use crate::solve::goal::*;
        let relations = std::mem::take(&mut self.projection_relations);
        self.undo.retain(|u| u.0 != u32::MAX);
        for (a, b, lo) in relations {
            let goal = Goal { param_env: ParamEnvId(self.cx.typing_env.param_env.index()),
                predicate: Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), AliasRelationDirection::Equate) };
            self.register_goal(goal, lo);
        }
    }

    fn ty_str(&mut self, t: TyId) -> String {
        let t = self.deep(t);
        ty_to_string(false, self.prog, self.tcx, t)
    }

    /// Coercion site: `actual` flows into a place of type `expected`.
    fn coerce_or_unify(&mut self, actual: TyId, expected: TyId, e: Option<ExprId>, pos: u32) -> bool {
        let a = self.shallow(actual);
        let x = self.shallow(expected);
        if a == x {
            if let (Some(e), TyKind::Ref(true, _, _)) = (e, self.tcx.tys.kind(x)) {
                self.b.reborrows.insert(e.0, true);
            }
            return true;
        }
        let ka = self.tcx.tys.kind(a).clone();
        let kx = self.tcx.tys.kind(x).clone();
        if let TyKind::Never = ka {
            if let Some(e) = e {
                self.b.coerce.insert(e.0, Coerce::Never);
            }
            if matches!(kx, TyKind::Infer(_)) {
                self.diverging.push(x);
            }
            return true;
        }
        if let Some((src, dy)) = self.dyn_coercion(&ka, &kx) {
            if let Some(e) = e {
                self.b.coerce.insert(e.0, Coerce::ToDyn(src, dy));
                if let (TyKind::Ref(..), TyKind::Ref(m, _, _) | TyKind::Ptr(m, _)) = (&ka, &kx) { self.b.reborrows.insert(e.0, *m); }
            }
            return true;
        }
        if let Some((sd, dd)) = self.dyn_upcast(&ka, &kx) {
            if let Some(e) = e {
                self.b.coerce.insert(e.0, Coerce::Upcast(sd, dd));
                if let (TyKind::Ref(..), TyKind::Ref(m, _, _) | TyKind::Ptr(m, _)) = (&ka, &kx) { self.b.reborrows.insert(e.0, *m); }
            }
            return true;
        }
        // a pointer to a not yet known type as a pointer to `dyn Tr` (`let b: Box<dyn Tr> =
        // v.clone();`): decided at the end, once the pointee is known (rustc keeps the
        // CoerceUnsized obligation pending)
        if let Some(ex) = e {
            if self.pointee_pair_open_to_dyn(&ka, &kx) {
                self.deferred_dyn.push((ex, a, x, pos));
                return true;
            }
        }
        if let (TyKind::Ref(m1, ia, _), TyKind::Ref(m2, ix, _), Some(ex)) = (&ka, &kx, e) {
            if *m1 || !*m2 {
                let save = self.snapshot();
                if self.unify(*ia, *ix) {
                    if *m1 { self.b.reborrows.insert(ex.0, *m2); }
                    return true;
                }
                self.rollback(save);
                if let Some(n) = self.deref_coercion(ex, *ia, *ix) {
                    self.b.coerce.insert(ex.0, Coerce::DerefRef(n));
                    self.b.reborrows.insert(ex.0, *m2);
                    return true;
                }
            }
        }
        if self.unsize_coercion(&ka, &kx) {
            if let Some(e) = e {
                self.b.coerce.insert(e.0, Coerce::Unsize);
                if let (TyKind::Ref(..), TyKind::Ref(m, _, _) | TyKind::Ptr(m, _)) = (&ka, &kx) { self.b.reborrows.insert(e.0, *m); }
            }
            return true;
        }
        match (&ka, &kx) {
            (TyKind::FnDef(d, args, _), TyKind::FnPtr(ps, r, c, _)) => {
                if let Some(sig) = self.tcx.fn_item_sig(self.prog, *d).cloned() {
                    let args = args.clone();
                    // a fn item reifies to a pointer of its own ABI (`extern "C" fn` items to
                    // `extern "C" fn(..)`)
                    let mut ok = sig.params.len() == ps.len() && sig.header.can_coerce_to(*c);
                    if ok {
                        for i in 0..ps.len() {
                            let p = self.tcx.tys.subst_for_inference(sig.params[i], &args);
                            ok = ok && self.unify(p, ps[i]);
                        }
                        let rr = self.tcx.tys.subst_for_inference(sig.ret, &args);
                        ok = ok && self.unify(rr, *r);
                    }
                    if ok {
                        if let Some(e) = e {
                            self.b.coerce.insert(e.0, Coerce::ReifyFn);
                        }
                        return true;
                    }
                }
            }
            (TyKind::FnPtr(ps, r, header, bound), TyKind::FnPtr(_, _, target, _))
                if header.safety == Safety::Safe && target.safety == Safety::Unsafe => {
                let unsafe_ty = self.tcx.tys.intern(TyKind::FnPtr(ps.clone(), *r,
                    FnHeader { safety: Safety::Unsafe, ..*header }, *bound));
                if self.unify(unsafe_ty, x) {
                    if let Some(e) = e { self.b.coerce.insert(e.0, Coerce::UnsafeFn); }
                    return true;
                }
            }
            (TyKind::Closure(file, ce, sig, _, _), TyKind::FnPtr(_, _, target, _)) => {
                // coercion.rs:1309: before capture inference, use mentioned
                // roots to decide whether function-pointer coercion is possible.
                let captures = *file != self.file || self.b.closure_locals.get(ce).is_some_and(|v| !v.is_empty());
                let pointer = match self.tcx.tys.kind(*sig).clone() {
                    TyKind::FnPtr(ps, r, header, bound) if header.can_coerce_to(*target) =>
                        self.tcx.tys.intern(TyKind::FnPtr(ps, r, *target, bound)),
                    _ => *sig,
                };
                if !captures && self.unify(pointer, x) {
                    if let Some(e) = e {
                        self.b.coerce.insert(e.0, Coerce::ClosureFn);
                    }
                    return true;
                }
            }
            (TyKind::Ref(m1, ia, _), TyKind::Ref(m2, ix, _)) => {
                let ia = self.shallow(*ia);
                let ix = self.shallow(*ix);
                if *m1 && !*m2 && self.unify(ia, ix) {
                    if let Some(e) = e {
                        self.b.coerce.insert(e.0, Coerce::MutToConst);
                    }
                    return true;
                }
            }
            // `&mut T -> *mut T`, `&T -> *const T`, `&mut T -> *const T` (same bits)
            (TyKind::Ref(m1, ia, _), TyKind::Ptr(m2, ix)) if *m1 || !*m2 => {
                let (ia, ix) = (*ia, *ix);
                if self.unify(ia, ix) {
                    if let Some(e) = e { self.b.coerce.insert(e.0, Coerce::RefToRaw(*m2)); }
                    return true;
                }
            }
            (TyKind::Ptr(true, ia), TyKind::Ptr(false, ix)) => {
                let (ia, ix) = (*ia, *ix);
                if self.unify(ia, ix) {
                    if let Some(e) = e {
                        self.b.coerce.insert(e.0, Coerce::MutToConst);
                    }
                    return true;
                }
            }
            _ => {}
        }
        if self.unify(actual, expected) {
            return true;
        }
        let sa = self.ty_str(a);
        let sx = self.ty_str(x);
        // same printed name for different types: show where each is defined
        let (sx, sa) = if sx == sa {
            let (x, a2) = (self.deep(expected), self.deep(actual));
            (ty_to_string_paths(self.prog, self.tcx, x), ty_to_string_paths(self.prog, self.tcx, a2))
        } else {
            (sx, sa)
        };
        self.err(pos, format!("mismatched types: expected `{}`, found `{}`", sx, sa));
        false
    }

    /// Casts use coercion adjustments too (rustc cast.rs: try_coercion_cast).
    /// Record their borrow before capture analysis; MIR lowering reads this same
    /// adjustment instead of independently deciding whether a cast moves a reference.
    fn record_cast_borrow(&mut self, e: ExprId, source: TyId, target: TyId) {
        let (source, target) = (self.shallow(source), self.shallow(target));
        let TyKind::Ref(sm, inner, _) = self.tcx.tys.kind(source).clone() else { return };
        match self.tcx.tys.kind(target).clone() {
            TyKind::Ptr(tm, pointee) if sm || !tm => {
                if self.b.coerce.contains_key(&e.0) {
                    // Unsizing / trait-object coercions borrow before the pointer conversion.
                    self.b.reborrows.insert(e.0, tm);
                } else {
                    let pointee = self.shallow(pointee);
                    if matches!(self.tcx.tys.kind(pointee), TyKind::Infer(_)) { return; }
                    let snap = self.snapshot();
                    if self.unify(inner, pointee) {
                        self.b.coerce.insert(e.0, Coerce::RefToRaw(tm));
                    } else {
                        self.rollback(snap);
                        // rustc check_ref_cast: &[T; N] -> *const T first coerces
                        // to a pointer to the array, using the source mutability.
                        let inner = self.shallow(inner);
                        if let TyKind::Array(element, _) = self.tcx.tys.kind(inner).clone() {
                            let snap = self.snapshot();
                            if self.unify(element, pointee) {
                                self.b.coerce.insert(e.0, Coerce::RefToRaw(sm));
                            } else { self.rollback(snap); }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // ------------------------------------------------------------ writeback

    /// Replaces this body's own opaque types in its return type `ret` (and those nested in their
    /// bounds' bindings) by fresh inference variables.
    fn define_opaques(&mut self, def: DefId, ret: TyId) -> TyId {
        if !self.tcx.tys.has_opaque(ret) {
            return ret;
        }
        let mut todo = Vec::new();
        self.tcx.tys.opaques_in(ret, &mut todo);
        let mut own: Vec<TyId> = Vec::new();
        while let Some(o) = todo.pop() {
            let (d, i, args) = match self.tcx.tys.kind(o).clone() {
                TyKind::Opaque(d, i, a, _) => (d, i, a),
                _ => continue,
            };
            if d != def || own.contains(&o) {
                continue;
            }
            own.push(o);
            let decl = self.tcx.opaques.get(&(d, i)).unwrap_or_default();
            for (_, _, bt) in decl.bindings {
                let x = self.tcx.tys.subst_for_inference(bt, &args);
                self.tcx.tys.opaques_in(x, &mut todo);
            }
        }
        for o in own {
            // an opaque already defined here (an async fn's output opaque, reached again through
            // its `impl Future<Output = ..>`) keeps its variable
            if self.opaque_vars.iter().any(|x| x.0 == o) {
                continue;
            }
            let v = self.fresh(0);
            self.opaque_vars.push((o, v));
        }
        let pairs = self.opaque_vars.clone();
        self.tcx.tys.replace(ret, &pairs)
    }

    /// The hidden types meet their opaque type's bounds: `Assoc = T` bindings constrain them
    /// (`-> impl Iterator<Item = u64>` types the body's literals as u64; rustc registers the
    /// opaque's item bounds as obligations on the hidden type).
    fn opaque_item_bounds(&mut self) {
        let pairs = self.opaque_vars.clone();
        for &(o, v) in &pairs {
            let (d, i, args) = match self.tcx.tys.kind(o).clone() {
                TyKind::Opaque(d, i, a, _) => (d, i, a),
                _ => continue,
            };
            let decl = self.tcx.opaques.get(&(d, i)).unwrap_or_default();
            for (ad, ta, bt) in decl.bindings {
                let mut pa = vec![v];
                for x in ta {
                    let x = self.tcx.tys.subst_for_inference(x, &args);
                    pa.push(self.tcx.tys.replace(x, &pairs));
                }
                let proj = self.tcx.tys.intern(TyKind::Assoc(ad, pa, crate::types::RegionArgsId::EMPTY));
                let saved = self.keep_literal_vars;
                self.keep_literal_vars = true;
                let n = self.norm(proj);
                self.keep_literal_vars = saved;
                if matches!(self.tcx.tys.kind(n), TyKind::Assoc(..)) {
                    continue;
                }
                let want = self.tcx.tys.subst_for_inference(bt, &args);
                let want = self.tcx.tys.replace(want, &pairs);
                self.unify(n, want);
            }
        }
        self.retry_goals(false);
    }

    /// A method of an opaque type's bounds: (method, its trait's args when the method is the
    /// bound trait's own).
    fn opaque_method(&mut self, t: TyId, s: Sym) -> Option<(DefId, Vec<TyId>)> {
        let (d, i, args) = match self.tcx.tys.kind(t).clone() {
            TyKind::Opaque(d, i, a, _) => (d, i, a),
            _ => return None,
        };
        let decl = self.tcx.opaques.get(&(d, i))?;
        for (td, targs) in &decl.bounds {
            if let Some(m) = self.dyn_method(*td, s) {
                let ta = if self.prog.def(m).parent == *td { targs.iter().map(|x| self.tcx.tys.subst_for_inference(*x, &args)).collect() } else { Vec::new() };
                return Some((m, ta));
            }
        }
        None
    }

    /// `impl Fn(A) -> R`'s signature.
    fn opaque_fn_sig(&mut self, t: TyId) -> Option<(Vec<TyId>, TyId)> {
        let (d, i, owner_args) = match self.tcx.tys.kind(t).clone() {
            TyKind::Opaque(d, i, a, _) => (d, i, a),
            _ => return None,
        };
        let decl = self.tcx.opaques.get(&(d, i))?;
        for (td, args) in decl.bounds {
            if let Some(output) = self.tcx.callable_output(td) {
                if let Some(TyKind::Tuple(ps)) = args.first().map(|t| self.tcx.tys.kind(*t)) {
                    for (ad, _, ret) in &decl.bindings {
                        if *ad == output {
                            let mut params = Vec::new();
                            for t in ps { params.push(self.tcx.tys.subst_for_inference(*t, &owner_args)); }
                            return Some((params, self.tcx.tys.subst_for_inference(*ret, &owner_args)));
                        }
                    }
                }
            }
        }
        None
    }


    /// The unbound variables in `t` (already resolved by `deep`).
    fn free_vars(&self, t: TyId, out: &mut Vec<u32>) {
        match self.tcx.tys.kind(t) {
            TyKind::Infer(v) => {
                if !out.contains(v) {
                    out.push(*v);
                }
            }
            TyKind::Tuple(v) | TyKind::Adt(_, v, _) | TyKind::FnDef(_, v, _) | TyKind::Assoc(_, v, _) | TyKind::Opaque(_, _, v, _) => v.iter().for_each(|x| self.free_vars(*x, out)),
            TyKind::Array(e, l) => {
                self.free_vars(*e, out);
                if let Some(x) = crate::types::len_ty(*l) {
                    self.free_vars(x, out);
                }
            }
            TyKind::Slice(e) | TyKind::Ref(_, e, _) | TyKind::Ptr(_, e) => self.free_vars(*e, out),
            TyKind::FnPtr(ps, r, _, _) => {
                ps.iter().for_each(|x| self.free_vars(*x, out));
                self.free_vars(*r, out)
            }
            TyKind::Dyn(_, v, bs, _, _, _, _) => {
                v.iter().for_each(|x| self.free_vars(*x, out));
                bs.iter().for_each(|x| self.free_vars(x.1, out))
            }
            TyKind::Closure(_, _, sg, u, _) => {
                self.free_vars(*sg, out);
                self.free_vars(*u, out)
            }
            _ => {}
        }
    }

    /// Retry trait predicates through selection before and after numeric fallback.
    /// rustc_hir_typeck/src/fallback.rs:select_obligations_where_possible.
    fn select_literal_obligations(&mut self, _after_fallback: bool) {
        let mut uses = Vec::new();
        for (key, args) in &self.b.res_args {
            if let Some(Res::Def(def)) = self.b.res.get(key) { uses.push((*def, args.clone())); }
        }
        for method in self.b.methods.values().chain(self.b.binops.values()) { uses.push((method.def, method.args.clone())); }
        for (def, args) in uses {
            if let Some(bounds) = self.tcx.fn_trait_bounds(self.prog, def).cloned() { self.infer_from_bounds_inner(&args, bounds); }
            let td = self.prog.def(def).parent;
            if td == NO_DEF || self.prog.def(td).kind != DefKind::Trait || args.is_empty() { continue; }
            let n = self.tcx.trait_generic_count(self.prog, td);
            if args.len() > n {
                let goal = crate::solve::select::trait_goal(&self.cx, td, args[0], &args[1..=n]);
                self.register_goal(goal, self.last_lo);
            }
        }
        self.retry_goals(false);
    }

    /// A diverging scrutinee (`match return 1 { 2 => .. }`): rustc types it against a fresh
    /// variable (demand_scrutinee_type), so `!` reaches the patterns as NeverToAny to that
    /// variable, which falls back like any diverging one.
    fn never_scrutinee(&mut self, x: ExprId, t: TyId) -> TyId {
        let s = self.shallow(t);
        if !matches!(self.tcx.tys.kind(s), TyKind::Never) {
            return t;
        }
        let v = self.fresh(0);
        self.b.coerce.insert(x.0, Coerce::Never);
        self.diverging.push(v);
        v
    }

    /// A pending pointer-to-dyn coercion (`deferred_dyn`), once its pointee is known.
    fn finish_dyn_coercion(&mut self, ex: ExprId, a: TyId, x: TyId, pos: u32) {
        let (sa, sx) = (self.shallow(a), self.shallow(x));
        let (ka, kx) = (self.tcx.tys.kind(sa).clone(), self.tcx.tys.kind(sx).clone());
        if let Some((src, dy)) = self.dyn_coercion(&ka, &kx) {
            self.b.coerce.insert(ex.0, Coerce::ToDyn(src, dy));
        } else if let Some((sd, dd)) = self.dyn_upcast(&ka, &kx) {
            self.b.coerce.insert(ex.0, Coerce::Upcast(sd, dd));
        } else if !self.unify(sa, sx) {
            let (p, q) = (self.ty_str(sx), self.ty_str(sa));
            self.err(pos, format!("mismatched types: expected `{}`, found `{}`", p, q));
        }
    }

    /// rustc upvar.rs:76, 157, 540: analyze nested bodies before their parents,
    /// infer kind, equate upvars, then let deferred obligations see the result.
    fn analyze_closures(&mut self) {
        if self.pending_captures.is_empty() || !self.b.errors.is_empty() { return; }
        // The visitor's type queries must see this inference context's assignments.
        for i in 0..self.b.locals.len() { self.b.locals[i].ty = self.norm(self.b.locals[i].ty); }
        for i in 0..self.b.expr_ty.len() { self.b.expr_ty[i] = self.norm(self.b.expr_ty[i]); }
        for i in 0..self.b.pat_ty.len() { self.b.pat_ty[i] = self.norm(self.b.pat_ty[i]); }
        for k in self.b.methods.keys().copied().collect::<Vec<_>>() {
            let args = self.b.methods[&k].args.clone();
            self.b.methods.get_mut(&k).unwrap().args = args.into_iter().map(|t| self.norm(t)).collect();
        }
        for k in self.b.ov_derefs.keys().copied().collect::<Vec<_>>() {
            let (method, args) = self.b.ov_derefs[&k].clone();
            let args = args.into_iter().map(|t| self.norm(t)).collect();
            self.b.ov_derefs.insert(k, (method, args));
        }
        for pending in std::mem::take(&mut self.pending_captures) {
            crate::upvar::analyze(&self.cx, self.prog, self.tcx, &mut self.b, &pending);
            let ce = pending.closure;
            let result = &self.b.min_captures[&ce];
            if !result.errors.is_empty() {
                let errors = result.errors.clone();
                for (expr, reason) in errors {
                    let lo = if expr & crate::tcx::ASYNC_FN_BODY == 0 { self.ast().expr(ExprId(expr)).lo } else { self.last_lo };
                    self.err(lo, format!("capture analysis incomplete: {}", reason));
                }
                continue;
            }
            let once = result.kind == crate::upvar::ClosureKind::FnOnce;
            let up = crate::upvar::derive_root_view(self.tcx, &mut self.b, ce);
            let caps = &self.b.closure_locals[&ce];
            let mut fields = up;
            // Existing lowering ABI: coroutines need drop flags for owned state;
            // ordinary closures need them only for the consuming call body.
            let flags = if pending.points.is_some() { self.b.capture_by_value[&ce].iter().any(|v| *v) } else { once };
            if flags {
                fields.extend(std::iter::repeat(self.tcx.tys.prim(Prim::U8)).take(caps.len()));
                let owner = self.tcx.tys.intern(TyKind::FnDef(self.b.def, self.b.args.clone(), crate::types::RegionArgsId::EMPTY));
                self.tcx.closure_once.insert((self.file, ce, owner), ());
            }
            if let Some(points) = pending.points {
                let states = points as u64 + 3;
                fields.push(self.tcx.tys.prim(if states <= 1 << 8 { Prim::U8 } else if states <= 1 << 16 { Prim::U16 } else { Prim::U32 }));
            }
            let up = self.tcx.tys.intern(TyKind::Tuple(fields));
            self.unify(pending.upvars, up);
        }
    }

    fn resolve_capture_place(&mut self, place: &mut crate::expr_use::Place) {
        place.root_ty = self.norm(place.root_ty);
        for (_, ty) in &mut place.projections { *ty = self.norm(*ty); }
    }

    fn finish(&mut self) {
        // Used foreign declarations have no body of their own to report signature
        // diagnostics. Keep those errors with each body that depends on them.
        for &d in &self.b.dependencies {
            for error in self.tcx.signature_errors(self.prog, d) {
                if !self.b.errors.contains(error) { self.b.errors.push(error.clone()); }
            }
        }
        self.retry_goals(false);
        // closures' `?`s whose error type the whole body left open: Relax's fallback (the first
        // `?`'s error; rustc asks for an annotation), the others through From
        if !self.pending_tries.is_empty() {
            self.finish_tries_at(None, true);
        }
        self.flush_projection_relations();
        self.check_repeat_exprs();
        self.select_literal_obligations(false);
        self.flush_projection_relations();
        self.retry_goals(false);
        for (x, xt, target) in std::mem::take(&mut self.deferred_casts) {
            let (sx, st) = (self.shallow(xt), self.shallow(target));
            let (kx, kt) = (self.tcx.tys.kind(sx).clone(), self.tcx.tys.kind(st).clone());
            // rustc cast.rs try_coercion_cast: a cast that is a coercion is one (`Arc::new(v) as _`
            // whose `_` became `Arc<dyn Send + Sync>`, `&s as _` as `&dyn Tr`)
            if let Some((src, dy)) = self.dyn_coercion(&kx, &kt) {
                self.b.coerce.insert(x.0, Coerce::ToDyn(src, dy));
            } else if let Some((sd, dd)) = self.dyn_upcast(&kx, &kt) {
                self.b.coerce.insert(x.0, Coerce::Upcast(sd, dd));
            } else if self.unsize_coercion(&kx, &kt) {
                self.b.coerce.insert(x.0, Coerce::Unsize);
            } else if let (TyKind::Ref(_, a, _) | TyKind::Ptr(_, a), TyKind::Ptr(_, p)) = (&kx, &kt) {
                // rustc cast.rs try_coercion_cast (casts are checked after inference): a cast
                // that is a coercion is one, so `&() as *const _` has pointee `()`; a pointee
                // already known to differ makes it a plain pointer cast
                let sp = self.shallow(*p);
                // (also an open source pointee against a known target: `&data as *const *const ()`
                // with data: *const ?T is the coercion &*const ?T -> *const *const (), T = ())
                if matches!(self.tcx.tys.kind(sp), TyKind::Infer(_)) || self.has_open_infer(*a) {
                    let snap = self.snapshot();
                    if !self.unify(*a, sp) {
                        self.rollback(snap);
                    }
                }
            }
            self.record_cast_borrow(x, xt, target);
        }
        // pending pointer-to-dyn coercions, now that their pointees are known
        for (ex, a, x, pos) in std::mem::take(&mut self.deferred_dyn) {
            self.finish_dyn_coercion(ex, a, x, pos);
        }
        // diverging fallback (rustc fallback.rs): a variable only a `!` value flowed into is `()`
        // before edition 2024 and `!` from 2024 (`f(|_| panic!())` instantiates R = ())
        if !self.diverging.is_empty() {
            let ed = self.prog.crates[self.prog.def(self.b.def).krate as usize].edition;
            let fb = if ed >= 2024 { self.tcx.tys.never } else { self.tcx.tys.unit };
            for v in std::mem::take(&mut self.diverging) {
                let s = self.shallow(v);
                if matches!(self.tcx.tys.kind(s), TyKind::Infer(_)) {
                    self.unify(s, fb);
                }
            }
            self.retry_goals(false);
        }
        // integer/float literal fallback happens once, at the end (rustc fallback.rs)
        self.keep_literal_vars = false;
        self.select_literal_obligations(true);
        self.retry_goals(false);
        self.analyze_closures();
        crate::upvar::publish(self.prog, self.tcx, &self.b);
        self.retry_goals(false);
        // codegen sees through opaque types: the hidden types are recorded first (this body
        // defines its own), then every type is revealed
        self.revealing = true;
        // the bounds' bindings constrain the hidden types first (rustc: the opaque's item bounds
        // are obligations on the hidden type): `impl Iterator<Item = u8>` returning `Empty<?T>`
        // makes T = u8, `impl Trait<Assoc = impl Send>` returning 42 makes the nested opaque's
        // hidden type `<i32 as Trait>::Assoc`
        for _ in 0..2 {
            for (o, v) in self.opaque_vars.clone() {
                let (d, i, args) = match self.tcx.tys.kind(o).clone() {
                    TyKind::Opaque(d, i, a, _) => (d, i, a),
                    _ => continue,
                };
                let hv = self.deep(v);
                if matches!(self.tcx.tys.kind(hv), TyKind::Infer(_)) {
                    continue;
                }
                let decl = self.tcx.opaques.get(&(d, i)).unwrap_or_default();
                for (ad, ta, bt) in decl.bindings {
                    let mut pa = vec![hv];
                    for x in ta {
                        let x = self.tcx.tys.subst_for_inference(x, &args);
                        pa.push(self.deep(x));
                    }
                    let proj = self.tcx.tys.intern(TyKind::Assoc(ad, pa, crate::types::RegionArgsId::EMPTY));
                    let have = self.norm_keep(proj);
                    if matches!(self.tcx.tys.kind(have), TyKind::Assoc(..)) {
                        continue;
                    }
                    let want = self.tcx.tys.subst_for_inference(bt, &args);
                    // nested opaques in the binding: their hidden types' variables
                    let pairs: Vec<(TyId, TyId)> = self.opaque_vars.clone();
                    let want = if self.tcx.tys.has_opaque(want) { self.tcx.tys.replace(want, &pairs) } else { want };
                    let save = self.snapshot();
                    if !self.unify(have, want) {
                        self.rollback(save);
                    }
                }
            }
        }
        for (o, v) in self.opaque_vars.clone() {
            let h = self.norm(v);
            // inference variables are this body's: a hidden type left open cannot leave it
            let h = if self.tcx.tys.has_infer(h) {
                if self.b.errors.is_empty() {
                    let lo = self.ast().item(self.prog.def(self.b.def).item).lo;
                    let ts = self.ty_str(h);
                    self.err(lo, format!("the returned `impl Trait`'s type is not fully known (`{}`)", ts));
                }
                self.tcx.tys.error
            } else {
                h
            };
            self.tcx.opaque_hidden.insert(o, h);
        }
        if !self.opaque_vars.is_empty() {
            self.tcx.trait_input_revision.fetch_add(1, std::sync::atomic::Ordering::Release);
        }
        self.retry_goals(false);
        // the hidden types must meet their bounds' bindings: callers were typed by them
        for (o, _) in self.opaque_vars.clone() {
            let (d, i, args) = match self.tcx.tys.kind(o).clone() {
                TyKind::Opaque(d, i, a, _) => (d, i, a),
                _ => continue,
            };
            let h = self.tcx.opaque_hidden.get(&o).unwrap_or(self.tcx.tys.error);
            let decl = self.tcx.opaques.get(&(d, i)).unwrap_or_default();
            for (ad, ta, bt) in decl.bindings {
                let mut pa = vec![h];
                for x in ta {
                    let x = self.tcx.tys.subst_for_inference(x, &args);
                    pa.push(self.norm(x));
                }
                let proj = self.tcx.tys.intern(TyKind::Assoc(ad, pa, crate::types::RegionArgsId::EMPTY));
                let have = self.norm(proj);
                let want = self.tcx.tys.subst_for_inference(bt, &args);
                let want = self.norm(want);
                if have != want && self.b.errors.is_empty() && !self.tcx.tys.has_error(have) && !self.tcx.tys.has_error(want) {
                    let lo = self.ast().item(self.prog.def(self.b.def).item).lo;
                    let (x, y, z) = (self.ty_str(h), self.ty_str(have), self.ty_str(want));
                    let n = self.prog.syms.str(self.prog.def(ad).name).to_string();
                    self.err(lo, format!("the returned `{}` has `{} = {}`, but the signature promises `{} = {}`", x, n, y, n, z));
                }
            }
        }
        self.finish_closure_signatures();
        let mut err_at = None;
        for i in 0..self.b.expr_ty.len() {
            let t = self.b.expr_ty[i];
            let n = self.norm(t);
            self.b.expr_ty[i] = n;
            if err_at.is_none() && n != self.tcx.tys.error && (self.tcx.tys.has_error(n) || self.tcx.tys.has_stuck_assoc(n) || self.tcx.tys.has_opaque(n)) {
                err_at = Some(i);
            }
        }
        // an expression whose type contains an unresolved type (e.g. a field of an unresolved
        // type) cannot be lowered: report it unless an error already explains the function
        if let (Some(i), true) = (err_at, self.b.errors.is_empty()) {
            let e = self.b.expr_at(i);
            let lo = self.ast().expr(e).lo;
            let ts = self.ty_str(self.b.expr_ty[i]);
            if self.tcx.tys.has_opaque(self.b.expr_ty[i]) {
                self.err(lo, format!("cannot infer the `impl Trait` type `{}` -- annotate the generic arguments", ts));
            } else if self.tcx.tys.has_stuck_assoc(self.b.expr_ty[i]) {
                self.err(lo, format!("no impl resolves `{}` -- the trait is not implemented for these types", ts));
            } else {
                self.err(lo, format!("type `{}` contains an unresolved type -- fix that type's error first", ts));
            }
        }
        for i in 0..self.b.pat_ty.len() {
            let t = self.b.pat_ty[i];
            self.b.pat_ty[i] = self.norm(t);
        }
        for i in 0..self.b.locals.len() {
            let t = self.b.locals[i].ty;
            let n = self.norm(t);
            self.b.locals[i].ty = n;
            // a local whose type inference left open cannot be laid out
            if self.b.errors.is_empty() && self.tcx.tys.has_infer(n) {
                let p = self.b.locals[i].pat;
                let _ = p;
                let lo = self.ast().item(self.prog.def(self.b.def).item).lo;
                let name = self.prog.syms.str(self.b.locals[i].name).to_string();
                let ts = self.ty_str(n);
                self.err(lo, format!("type of `{}` is not fully known (`{}`) -- annotate: let {}: T", name, ts, name));
            }
        }
        let r = self.b.ret;
        self.b.ret = self.norm(r);
        let keys: Vec<u32> = self.b.res_args.keys().copied().collect();
        for k in keys {
            let v = self.b.res_args[&k].clone();
            let mut n = Vec::new();
            for t in v {
                n.push(self.norm(t));
            }
            self.b.res_args.insert(k, n);
        }
        let keys: Vec<u32> = self.b.methods.keys().copied().collect();
        for k in keys {
            let v = self.b.methods[&k].args.clone();
            let mut n = Vec::new();
            for t in v {
                n.push(self.norm(t));
            }
            self.b.methods.get_mut(&k).unwrap().args = n;
        }
        // every recorded instantiation gets its projections resolved (layout and intrinsics
        // of `A::Item` inside generic code, F-STD14)
        let keys: Vec<(u32, u8)> = self.b.ov_derefs.keys().copied().collect();
        for k in keys {
            let (d, v) = self.b.ov_derefs[&k].clone();
            let n: Vec<TyId> = v.iter().map(|t| self.norm(*t)).collect();
            self.b.ov_derefs.insert(k, (d, n));
        }
        let keys: Vec<u32> = self.b.ov_index.keys().copied().collect();
        for k in keys {
            let (d, v) = self.b.ov_index[&k].clone();
            let n: Vec<TyId> = v.iter().map(|t| self.norm(*t)).collect();
            self.b.ov_index.insert(k, (d, n));
        }
        let keys: Vec<u32> = self.b.for_next.keys().copied().collect();
        for k in keys {
            let (d, v) = self.b.for_next[&k].clone();
            let n: Vec<TyId> = v.iter().map(|t| self.norm(*t)).collect();
            self.b.for_next.insert(k, (d, n));
        }
        let keys: Vec<u32> = self.b.for_into.keys().copied().collect();
        for k in keys {
            let (d, v, it) = self.b.for_into[&k].clone();
            let n: Vec<TyId> = v.iter().map(|t| self.norm(*t)).collect();
            let it = self.norm(it);
            self.b.for_into.insert(k, (d, n, it));
        }
        let keys: Vec<u32> = self.b.try_conv.keys().copied().collect();
        for k in keys {
            if let Some((d, v)) = self.b.try_conv[&k].clone() {
                let n: Vec<TyId> = v.iter().map(|t| self.norm(*t)).collect();
                self.b.try_conv.insert(k, Some((d, n)));
            }
        }
        // a call whose generic args are still unknown cannot be instantiated: diagnose it here
        // (instead of an internal error when the instance is compiled)
        // rustc_hir_typeck/src/writeback.rs:916: a body already tainted by errors does
        // not emit another inference failure (its closure captures may be unresolved).
        if self.b.errors.is_empty() {
            let mut stuck: Vec<(u32, DefId)> = Vec::new();
            let ast = self.ast();
            for (k, v) in &self.b.res_args {
                // res_args keys are expr or pat ids (shared number space): only path
                // expressions of this body are calls' callees
                let in_body = self.b.has_expr(ExprId(*k));
                if !in_body || self.b.pat_res.contains_key(k) || !matches!(ast.expr(ExprId(*k)).kind, ExprKind::Path(_)) {
                    continue;
                }
                if v.iter().any(|t| self.tcx.tys.has_infer(*t)) {
                    if let Some(Res::Def(d)) = self.b.res.get(k) {
                        if matches!(self.prog.def(*d).kind, DefKind::Fn | DefKind::AssocFn) {
                            stuck.push((*k, *d));
                        }
                    }
                }
            }
            for (k, m) in &self.b.methods {
                if m.args.iter().any(|t| self.tcx.tys.has_infer(*t)) {
                    stuck.push((*k, m.def));
                }
            }
            stuck.sort_by_key(|x| x.0);
            if let Some(&(k, d)) = stuck.first() {
                let lo = if self.b.has_expr(ExprId(k)) { ast.expr(ExprId(k)).lo } else { self.last_lo };
                let n = self.prog.def_path(d);
                self.err(lo, format!("cannot infer the generic arguments of `{}` -- annotate the types (e.g. `let x: T = ..` or `::<T>`)", n));
            }
        }
        // unsize-to-dyn coercions recorded before inference finished (`&mut FmtAdapter<?W>`
        // as `&mut dyn Write`): their vtable is built from these types
        let keys: Vec<u32> = self.b.coerce.keys().copied().collect();
        for k in keys {
            if let Some(Coerce::ToDyn(src, dy)) = self.b.coerce.get(&k).copied() {
                let (s2, d2) = (self.norm(src), self.norm(dy));
                self.b.coerce.insert(k, Coerce::ToDyn(s2, d2));
            }
            if let Some(Coerce::Upcast(src, dy)) = self.b.coerce.get(&k).copied() {
                let (s2, d2) = (self.norm(src), self.norm(dy));
                self.b.coerce.insert(k, Coerce::Upcast(s2, d2));
            }
        }
        let keys: Vec<u32> = self.b.binops.keys().copied().collect();
        for k in keys {
            let v = self.b.binops[&k].args.clone();
            let mut n = Vec::new();
            for t in v {
                n.push(self.norm(t));
            }
            self.b.binops.get_mut(&k).unwrap().args = n;
        }
        // Capture types may contain an inner closure's formerly open upvar
        // tuple. Resolve these through the same context as expression/local types.
        let mut captures = std::mem::take(&mut self.b.min_captures);
        for c in captures.values_mut() {
            for capture in &mut c.captures { self.resolve_capture_place(&mut capture.place); }
            for (place, _) in &mut c.fake_reads { self.resolve_capture_place(place); }
        }
        self.b.min_captures = captures;
        crate::upvar::coroutine_closure_views(self.prog, self.tcx, &mut self.b);
        crate::upvar::publish(self.prog, self.tcx, &self.b);
        self.retry_goals(true);
    }

    // ------------------------------------------------------------ scopes

    /// The local named `s` that an identifier at `pos` refers to, with macro_rules hygiene
    /// (rustc: locals and labels resolve by name and SyntaxContext; walking out of the scopes
    /// a macro body sees, past the macro's definition, drops the expansion's mark): a binding
    /// of the same context, or -- for an identifier of a macro body -- a binding of the root
    /// context made before the macro's definition (in this file).
    fn lookup_local(&self, s: Sym, pos: u32) -> Option<u32> {
        let pf = &self.prog.files[self.file as usize];
        let c = pf.hyg_ctxt(pos);
        let mut i = self.scopes.len();
        while i > 0 {
            i -= 1;
            if self.scopes[i].0 == s {
                let li = self.scopes[i].1;
                let (bc, bpos) = match self.local_hyg.get(li as usize) {
                    Some(x) => x,
                    None => return Some(li),
                };
                let bc = match bc {
                    Some(b) => b,
                    None => return Some(li),
                };
                // the binding's context is the use's minus marks whose macros were defined
                // after the binding (in this file)
                if c.len() >= bc.len() && c[..bc.len()] == bc[..] && c[bc.len()..].iter().all(|m| {
                    let d = pf.hyg_def_pos(*m);
                    d != u32::MAX && pf.pos_before(*bpos, d)
                }) {
                    return Some(li);
                }
            }
        }
        None
    }

    fn set_ty(&mut self, e: ExprId, t: TyId) {
        let i = self.b.expr_ix(e);
        if i < self.b.expr_ty.len() {
            self.b.expr_ty[i] = t;
        }
    }

    // ------------------------------------------------------------ patterns

    pub fn check_pat(&mut self, p: PatId, expected: TyId) {
        let ast = self.ast();
        // the pattern's type is the matched value's (lowering peels pat_derefs itself)
        let pi = self.b.pat_ix(p);
        if pi < self.b.pat_ty.len() {
            self.b.pat_ty[pi] = expected;
        }
        // match ergonomics: a structural pattern against references matches through them and
        // switches the default binding mode to `ref` / `ref mut`
        // literal and range patterns peel references too, except string / byte-string
        // literals, which match `&str` / `&[u8]` themselves (rustc pat.rs calc_adjust_mode:
        // AdjustMode::Peel for PatKind::Expr unless the literal's type is a reference)
        let peel_lit = match ast.pat(p) {
            Pat::Lit(e) => !matches!(ast.expr(*e).kind, ExprKind::Lit(LitKind::Str) | ExprKind::Lit(LitKind::RawStr) | ExprKind::Lit(LitKind::ByteStr) | ExprKind::Lit(LitKind::CStr)),
            Pat::Range(..) => true,
            _ => false,
        };
        // (a constant pattern passes the expected type unpeeled: its own type may be a
        // reference, `const Z: &() = ..; match &() { Z => .. }`; rustc pat.rs AdjustMode::Pass)
        // a path pattern resolves first: a const (or assoc const, `i32::C`, `Self::C`) keeps the
        // expected type as it is, an ADT constructor peels references
        let mut pre_const = false;
        if let Pat::Path(path) = ast.pat(p) {
            let (r, t) = self.resolve_value_path(path, p.0 | PAT_KEY, true);
            pre_const = matches!(r, Res::Def(d) if matches!(self.prog.def(d).kind, DefKind::Const | DefKind::AssocConst));
            self.pat_path_pre = Some((r, t));
        }
        let structural = peel_lit
            || matches!(ast.pat(p), Pat::Tuple(_) | Pat::TupleStruct(..) | Pat::Struct(..) | Pat::Slice(_))
            || matches!(ast.pat(p), Pat::Path(_) if !pre_const)
            || matches!(ast.pat(p), Pat::Ident { sub: None, by_ref: false, mutbl: false, .. } if self.ident_pat_is_path(p) && !self.ident_pat_is_const(p));
        let mut expected = expected;
        let saved_mode = self.bind_mode;
        if structural {
            let mut n = 0u8;
            loop {
                let s = self.shallow_with_regions(expected);
                match self.tcx.tys.kind(s).clone() {
                    TyKind::Ref(m, inner, _) => {
                        n += 1;
                        self.bind_mode = if !m || self.bind_mode == 1 { 1 } else { 2 };
                        expected = inner;
                    }
                    _ => break,
                }
            }
            if n > 0 {
                self.b.pat_derefs.insert(p.0, n);
            }
        }
        if let Pat::Ref(..) = ast.pat(p) {
            self.bind_mode = 0;
        }
        self.check_pat_inner(p, expected);
        // rustc_hir_typeck/expr_use_visitor.rs:943-947, 1858: capture semantics
        // depend on the variant list, never on which variants are inhabited.
        // Non-exhaustiveness counts in the defining crate as well as other crates.
        let constructor = matches!(ast.pat(p), Pat::TupleStruct(..) | Pat::Struct(..))
            || matches!(self.b.pat_res.get(&p.0), Some(Res::Def(d))
                if matches!(self.prog.def(*d).kind, DefKind::Variant | DefKind::Struct));
        if constructor {
            let t = self.shallow(expected);
            if let TyKind::Adt(d, _, _) = self.tcx.tys.kind(t) {
                let multiple = self.tcx.adts.get(d).map_or(false, |a| a.variants.len() > 1);
                let def = self.prog.def(*d);
                let pf = &self.prog.files[def.file as usize];
                let non_exhaustive = def.kind == DefKind::Enum
                    && pf.ast.list(pf.ast.item(def.item).attrs).iter().any(|a| {
                        a.toks.lo < a.toks.hi && pf.tok_text(a.toks.lo) == "non_exhaustive"
                    });
                if multiple || non_exhaustive {
                    self.b.pat_discriminant_reads.insert(p.0, ());
                }
            }
        }
        self.bind_mode = saved_mode;
    }

    fn ident_pat_is_const(&self, p: PatId) -> bool {
        if let Pat::Ident { name, .. } = self.ast().pat(p) {
            let s = self.sym(*name);
            if let Some(d) = self.prog.lookup_in_scope(self.module, s, false) {
                return matches!(self.prog.def(d).kind, DefKind::Const | DefKind::AssocConst);
            }
        }
        false
    }

    /// An identifier pattern naming a unit struct / unit variant / const (not a binding).
    fn ident_pat_is_path(&self, p: PatId) -> bool {
        if let Pat::Ident { name, .. } = self.ast().pat(p) {
            let s = self.sym(*name);
            if let Some(d) = self.prog.lookup_in_scope(self.module, s, false) {
                return matches!(self.prog.def(d).kind, DefKind::Const | DefKind::Variant | DefKind::Struct | DefKind::AssocConst);
            }
        }
        false
    }

    fn check_pat_inner(&mut self, p: PatId, expected: TyId) {
        let ast = self.ast();
        match ast.pat(p) {
            Pat::Wild | Pat::Rest => {}
            Pat::Ident { by_ref, mutbl, name, sub } => {
                let s = self.sym(*name);
                // a unit struct / unit variant / const in scope is a path pattern, not a binding
                if sub.is_none() && !*by_ref && !*mutbl {
                    if let Some(d) = self.prog.lookup_in_scope(self.module, s, false) {
                        let k = self.prog.def(d).kind;
                        if matches!(k, DefKind::Const | DefKind::Variant | DefKind::Struct | DefKind::AssocConst) {
                            self.b.pat_res.insert(p.0, Res::Def(d));
                            let t = self.value_def_ty(d, None, p.0 | PAT_KEY, 0);
                            self.coerce_or_unify(t, expected, None, name.lo);
                            return;
                        }
                    }
                }
                let ty = if *by_ref {
                    self.tcx.tys.intern(TyKind::Ref(*mutbl, expected, crate::types::RegionId::ERASED))
                } else if self.bind_mode != 0 && !*mutbl {
                    // bound by reference through the default binding mode (a `mut x` binding
                    // resets it to move, rustc pat.rs check_pat_ident, editions <= 2021)
                    self.b.pat_bind_ref.insert(p.0, self.bind_mode);
                    self.tcx.tys.intern(TyKind::Ref(self.bind_mode == 2, expected, crate::types::RegionId::ERASED))
                } else {
                    expected
                };
                let li = self.b.locals.len() as u32;
                self.b.locals.push(Local { name: s, ty, mutable: *mutbl && !*by_ref, pat: p.0 });
                self.b.pat_local.insert(p.0, li);
                let pf = &self.prog.files[self.file as usize];
                let h = (Some(pf.hyg_ctxt(name.lo)), name.lo);
                self.local_hyg.resize(li as usize + 1, (Some(Vec::new()), 0));
                self.local_hyg[li as usize] = h;
                self.scopes.push((s, li));
                if let Some(sp) = sub {
                    self.check_pat(*sp, expected);
                }
            }
            Pat::Lit(e) => {
                let t = self.check_expr(*e, Some(expected));
                // string literal patterns against &str, byte strings against &[u8]
                self.coerce_or_unify(t, expected, Some(*e), ast.expr(*e).lo);
            }
            Pat::Range(a, b, _) => {
                if let Some(a) = a {
                    let t = self.check_expr(*a, Some(expected));
                    self.unify(t, expected);
                }
                if let Some(b) = b {
                    let t = self.check_expr(*b, Some(expected));
                    self.unify(t, expected);
                }
            }
            Pat::Tuple(v) => {
                let et = self.shallow_with_regions(expected);
                let elems = match self.tcx.tys.kind(et).clone() {
                    TyKind::Tuple(x) => x,
                    _ => {
                        let mut x = Vec::new();
                        for _ in 0..v.len() {
                            x.push(self.fresh(0));
                        }
                        let tt = self.tcx.tys.intern(TyKind::Tuple(x.clone()));
                        self.unify(tt, et);
                        x
                    }
                };
                self.check_seq_pats(self.ast().list(*v), &elems);
            }
            Pat::Paren(x) => self.check_pat(*x, expected),
            Pat::Ref(_, x) => {
                let et = self.shallow_with_regions(expected);
                let inner = match self.tcx.tys.kind(et).clone() {
                    TyKind::Ref(_, i, _) => i,
                    _ => self.tcx.tys.error,
                };
                self.check_pat(*x, inner);
            }
            Pat::Or(v) => {
                // every alternative binds the same names to the same variables (rustc: one
                // binding per name, the alternatives' types must agree)
                let mark = self.scopes.len();
                let mut first: Vec<(Sym, u32)> = Vec::new();
                for (i, x) in self.ast().list(*v).iter().enumerate() {
                    let m = self.scopes.len();
                    self.check_pat(*x, expected);
                    if i == 0 {
                        first = self.scopes[mark..].to_vec();
                        continue;
                    }
                    let added: Vec<(Sym, u32)> = self.scopes[m..].to_vec();
                    self.scopes.truncate(m);
                    for (s, li) in added {
                        if let Some(&(_, l0)) = first.iter().find(|b| b.0 == s) {
                            let (t0, t1) = (self.b.locals[l0 as usize].ty, self.b.locals[li as usize].ty);
                            self.unify(t1, t0);
                            let pp = self.b.locals[li as usize].pat;
                            self.b.pat_local.insert(pp, l0);
                        }
                    }
                }
            }
            Pat::Slice(v) => {
                let et = self.shallow_with_regions(expected);
                let (elem, n) = match self.tcx.tys.kind(et).clone() {
                    TyKind::Array(e, n) => (e, Some(n)),
                    TyKind::Slice(e) => (e, None),
                    _ => {
                        if !matches!(self.tcx.tys.kind(et), TyKind::Error | TyKind::Infer(_)) {
                            let ts = self.ty_str(et);
                            self.err(self.last_lo, format!("slice pattern on `{}` -- match an array or a slice", ts));
                        }
                        (self.tcx.tys.error, None)
                    }
                };
                let fixed = self.ast().list(*v).iter().filter(|x| !is_rest_pat(ast, **x)).count() as u64;
                // an array whose length is still open (`let [a, b] = array::from_fn(..)`): a
                // pattern without `..` gives it (rustc pat.rs check_array_pat_len)
                let mut n = n;
                if let Some(len) = n {
                    let open = crate::types::len_ty(len).is_some_and(|lt| matches!(self.tcx.tys.kind(self.shallow(lt)), TyKind::Infer(_)));
                    if open && fixed as usize == v.len() {
                        let want = self.tcx.tys.intern(TyKind::Array(elem, fixed));
                        self.unify(et, want);
                        n = Some(fixed);
                    }
                }
                for x in self.ast().list(*v) {
                    if let Pat::Rest = ast.pat(*x) {
                        continue;
                    }
                    if let Pat::Ident { sub: Some(s), .. } = ast.pat(*x) {
                        if let Pat::Rest = ast.pat(*s) {
                            // `name @ ..`: the subslice / subarray
                            let st = match n {
                                Some(n) => self.tcx.tys.intern(TyKind::Array(elem, n.saturating_sub(fixed))),
                                None => self.tcx.tys.intern(TyKind::Slice(elem)),
                            };
                            self.check_pat(*x, st);
                            continue;
                        }
                    }
                    self.check_pat(*x, elem);
                }
            }
            Pat::Path(path) => {
                let (r, t) = match self.pat_path_pre.take() {
                    Some(x) => x,
                    None => self.resolve_value_path(path, p.0 | PAT_KEY, true),
                };
                self.b.pat_res.insert(p.0, r);
                self.coerce_or_unify(t, expected, None, path.lo);
            }
            Pat::TupleStruct(path, v) => {
                let (r, _) = self.resolve_value_path(path, p.0 | PAT_KEY, true);
                self.b.pat_res.insert(p.0, r);
                let fields = self.ctor_fields_with(r, expected, path.lo, Some(p.0 | PAT_KEY));
                self.check_seq_pats(self.ast().list(*v), &fields);
            }
            Pat::Struct(path, fields, rest) => {
                let d = self.resolve_struct_path(path);
                self.b.pat_res.insert(p.0, d);
                if let Res::Def(dd) = d {
                    let (adt_ty, vi) = self.adt_of_ctor(dd);
                    let adt_ty = self.instantiate_adt(adt_ty);
                    let adt_ty = if self.prog.def(dd).kind == DefKind::Variant { adt_ty } else { self.struct_path_ty(path, adt_ty) };
                    self.coerce_or_unify(adt_ty, expected, None, path.lo);
                    let et = self.shallow_with_regions(expected);
                    let mut mentioned: Vec<u32> = Vec::new();
                    let mut bad = false;
                    for fp in self.ast().list(*fields) {
                        let fname = self.sym(fp.name);
                        // `S { 0: a, 1: b }` (a tuple struct's fields by index)
                        let fname = if fp.name.hi > fp.name.lo && self.text(fp.name).as_bytes()[0].is_ascii_digit() {
                            crate::ast::tuple_index(self.text(fp.name)).map_or(u32::MAX - 1, |n| n | 0x8000_0000)
                        } else {
                            fname
                        };
                        let ft = self.field_ty(et, vi, fname);
                        match ft {
                            Some((fi, t)) => {
                                mentioned.push(fi);
                                self.check_pat(fp.pat, t)
                            }
                            None => {
                                bad = true;
                                self.err(fp.name.lo, format!("no field `{}`", self.text(fp.name)))
                            }
                        }
                    }
                    // without `..` every field is named (rustc E0027; a union names one)
                    if !*rest && !bad && self.prog.def(dd).kind != DefKind::Union {
                        if let TyKind::Adt(ad, _, _) = self.tcx.tys.kind(self.shallow(et)).clone() {
                            if let Some(v) = self.tcx.adts.get(&ad).and_then(|a| a.variants.get(vi as usize).cloned()) {
                                // (a field a live edit removed is a dead slot no code names, M10)
                                let missing: Vec<String> = v.fields.iter().enumerate().filter(|(i, f)| !mentioned.contains(&(*i as u32)) && !(f.name & 0x8000_0000 == 0 && self.prog.syms.str(f.name).starts_with("__relax_dead_"))).map(|(_, f)| {
                                    if f.name & 0x8000_0000 != 0 { (f.name & 0x7fff_ffff).to_string() } else { self.prog.syms.str(f.name).to_string() }
                                }).collect();
                                if !missing.is_empty() {
                                    self.err(path.lo, format!("E0027: pattern does not mention field{} `{}` -- name {} or add `..`", if missing.len() > 1 { "s" } else { "" }, missing.join("`, `"), if missing.len() > 1 { "them" } else { "it" }));
                                }
                            }
                        }
                    }
                }
            }
            Pat::Box(x) => self.check_pat(*x, expected),
            Pat::Mac(m) => self.err(m.path.lo, "macro in pattern position".to_string()),
        }
    }

    /// The assignee of a destructuring assignment against the assigned type `t`.
    fn check_assignee(&mut self, a: ExprId, t: TyId, lo: u32) {
        let ast = self.ast();
        let is_rest = |x: ExprId| matches!(ast.expr(x).kind, ExprKind::Range(None, None, false));
        let pi = self.b.expr_ix(a);
        match ast.expr(a).kind.clone() {
            ExprKind::Paren(x) if is_rest(x) => {}
            ExprKind::Paren(x) => {
                self.check_assignee(x, t, lo);
            }
            ExprKind::Underscore => {}
            ExprKind::Tuple(elems) => {
                let st = self.shallow(t);
                let tys = match self.tcx.tys.kind(st).clone() {
                    TyKind::Tuple(v) => v,
                    _ => {
                        if self.ast().list(elems).iter().any(|x| is_rest(*x)) {
                            self.err(lo, "destructuring assignment with `..` needs a tuple of known length".to_string());
                            return;
                        }
                        let v: Vec<TyId> = self.ast().list(elems).iter().map(|_| self.fresh(0)).collect();
                        let tt = self.tcx.tys.intern(TyKind::Tuple(v.clone()));
                        self.unify(st, tt);
                        v
                    }
                };
                let r = self.ast().list(elems).iter().position(|x| is_rest(*x));
                let (n, m) = (elems.len(), tys.len());
                for (i, x) in self.ast().list(elems).iter().enumerate() {
                    if Some(i) == r {
                        continue;
                    }
                    let fi = match r {
                        Some(r) if i > r => m.wrapping_sub(n - i),
                        _ => i,
                    };
                    match tys.get(fi) {
                        Some(ft) => self.check_assignee(*x, *ft, lo),
                        None => self.err(lo, format!("mismatched types: the tuple has {} elements", m)),
                    }
                }
            }
            ExprKind::Array(elems) => {
                let st = self.shallow(t);
                let et = match self.tcx.tys.kind(st).clone() {
                    TyKind::Array(e, _) | TyKind::Slice(e) => e,
                    _ => {
                        let e = self.fresh(0);
                        let at = self.tcx.tys.intern(TyKind::Array(e, elems.len() as u64));
                        self.unify(st, at);
                        e
                    }
                };
                for x in self.ast().list(elems).iter().copied() {
                    if !is_rest(x) {
                        self.check_assignee(x, et, lo);
                    }
                }
            }
            ExprKind::Call(f, args) if matches!(ast.expr(f).kind, ExprKind::Path(_)) => {
                // `TupleStruct(x, y) = v` / `Variant(x, ..) = v`: fields by position
                let path = match &ast.expr(f).kind {
                    ExprKind::Path(p) => p.clone(),
                    _ => return,
                };
                let r = self.resolve_struct_path(&path);
                self.b.res.insert(a.0, r);
                if let Res::Def(d) = r {
                    let (adt_ty, vi) = self.adt_of_ctor(d);
                    let adt_ty = self.instantiate_adt(adt_ty);
                    self.unify(adt_ty, t);
                    let n = args.len();
                    let r = self.ast().list(args).iter().position(|x| is_rest(*x));
                    let sat = self.shallow(adt_ty);
                    let nf = match self.tcx.tys.kind(sat).clone() {
                        TyKind::Adt(ad, _, _) => self.tcx.adts.get(&ad).map_or(0, |x| x.variants.get(vi as usize).map_or(0, |v| v.fields.len())),
                        _ => 0,
                    };
                    for (i, x) in self.ast().list(args).iter().enumerate() {
                        if Some(i) == r {
                            continue;
                        }
                        let fi = match r {
                            Some(r) if i > r => nf.wrapping_sub(n - i),
                            _ => i,
                        };
                        if let Some((_, ft)) = self.field_ty(adt_ty, vi, (fi as u32) | 0x8000_0000) {
                            self.check_assignee(*x, ft, lo);
                        }
                    }
                }
            }
            ExprKind::Struct(path, fields, _, _) => {
                let r = self.resolve_struct_path(&path);
                self.b.res.insert(a.0, r);
                if let Res::Def(d) = r {
                    let (adt_ty, vi) = self.adt_of_ctor(d);
                    let adt_ty = self.instantiate_adt(adt_ty);
                    self.unify(adt_ty, t);
                    for fe in self.ast().list(fields) {
                        let fname = self.sym(fe.name);
                        let fname = if fe.name.hi > fe.name.lo && self.text(fe.name).as_bytes()[0].is_ascii_digit() {
                            crate::ast::tuple_index(self.text(fe.name)).map_or(u32::MAX - 1, |n| n | 0x8000_0000)
                        } else {
                            fname
                        };
                        match self.field_ty(adt_ty, vi, fname) {
                            Some((_, ft)) => self.check_assignee(fe.expr, ft, lo),
                            None => self.err(fe.name.lo, format!("no field `{}`", self.text(fe.name))),
                        }
                    }
                }
            }
            _ => {
                let ta = self.check_expr(a, None);
                self.coerce_or_unify(t, ta, None, lo);
                return;
            }
        }
        if pi < self.b.expr_ty.len() {
            self.b.expr_ty[pi] = t;
        }
    }

    fn check_seq_pats(&mut self, v: &[PatId], elems: &[TyId]) {
        let ast = self.ast();
        let mut rest_at = None;
        for (i, x) in v.iter().enumerate() {
            if let Pat::Rest = ast.pat(*x) {
                rest_at = Some(i);
            }
        }
        match rest_at {
            None => {
                for i in 0..v.len() {
                    let t = if i < elems.len() { elems[i] } else { self.tcx.tys.error };
                    self.check_pat(v[i], t);
                }
            }
            Some(r) => {
                for i in 0..r {
                    let t = if i < elems.len() { elems[i] } else { self.tcx.tys.error };
                    self.check_pat(v[i], t);
                }
                let after = v.len() - r - 1;
                for j in 0..after {
                    let ei = elems.len() as isize - after as isize + j as isize;
                    let t = if ei >= 0 { elems[ei as usize] } else { self.tcx.tys.error };
                    self.check_pat(v[r + 1 + j], t);
                }
            }
        }
    }

    // ------------------------------------------------------------ ADT helpers

    /// For a struct/variant def: (adt type with Param args, variant index).
    fn adt_of_ctor(&mut self, d: DefId) -> (TyId, u32) {
        let def = self.prog.def(d);
        let (adt_def, vi) = match def.kind {
            DefKind::Variant => (def.parent, def.sub),
            _ => (d, 0),
        };
        let n = match self.tcx.adts.get(&adt_def) {
            Some(a) => a.n_generics,
            None => 0,
        };
        let mut args = Vec::new();
        for i in 0..n {
            args.push(self.tcx.tys.intern(TyKind::Param(i)));
        }
        (self.tcx.tys.intern(TyKind::Adt(adt_def, args, crate::types::RegionArgsId::EMPTY)), vi)
    }

    /// Replace Param args of an ADT type by fresh variables.
    /// The type a struct literal / struct pattern path names: explicit generic args
    /// (`S::<u16> { .. }`) and type aliases (`type S4<U> = S3<U, char>; S4::<u8> { .. }`) fix
    /// args; the rest are fresh (rustc instantiates the path's type, alias substituted).
    /// `T::A { a, b }` / `Self::Out { .. }`: a struct named through an associated type of a
    /// param (rustc resolves the path as a type, then takes its ADT and args).
    fn assoc_struct_path(&mut self, path: &Path) -> Option<TyId> {
        let n = path.segs.len();
        if n < 2 || path.qself != QSelfId::NONE {
            return None;
        }
        let s0 = self.ast().segs(path.segs)[0].clone();
        if s0.kind != SegKind::SelfType && !self.env.names.contains(&self.sym(s0.name)) {
            return None;
        }
        if let Some(d) = self.tcx.resolve_type_path_def(self.prog, self.file, self.module, path) {
            if matches!(self.prog.def(d).kind, DefKind::Struct | DefKind::Union | DefKind::Variant | DefKind::TypeAlias) {
                return None;
            }
        }
        // a probe: `Self::Variant { .. }` is not a type (resolve_struct_path then finds the
        // variant), so its lowering errors are kept only when the path is a struct here. They
        // used to reach the shared error sink, where the next collection (a live edit adding
        // items) returned them as that edit's errors: E0412 `cannot find type Self::ExpDecay`.
        let outer = self.tcx.begin_errors(&self.cx);
        let t = self.type_of_prefix(path, n);
        let errs = self.tcx.end_errors(&self.cx, outer);
        let t = self.shallow(t?);
        match self.tcx.tys.kind(t) {
            TyKind::Adt(d, _, _) if matches!(self.prog.def(*d).kind, DefKind::Struct | DefKind::Union) => {
                for e in errs {
                    self.tcx.reraise_error(&self.cx, e);
                }
                Some(t)
            }
            _ => None,
        }
    }

    fn struct_path_ty(&mut self, path: &Path, fresh_adt: TyId) -> TyId {
        let prog = self.prog;
        if let Some(t) = self.assoc_struct_path(path) {
            return t;
        }
        let segs = crate::program::path_segs(prog, self.file, path);
        let explicit = self.explicit_args(path);
        if segs.len() == 1 {
            if let Some(d) = prog.lookup_in_scope(self.module, segs[0].1, true) {
                if prog.def(d).kind == DefKind::TypeAlias {
                    let at = self.tcx.alias_ty(&self.cx, prog, d);
                    let n = self.tcx.item_env(prog, d).names.len();
                    let mut args: Vec<TyId> = explicit.clone().unwrap_or_default();
                    while args.len() < n {
                        args.push(self.fresh(0));
                    }
                    args.truncate(n);
                    let t = self.tcx.tys.subst_for_inference(at, &args);
                    if matches!(self.tcx.tys.kind(t), TyKind::Adt(..)) {
                        return t;
                    }
                    return fresh_adt;
                }
            }
        }
        if let (Some(a), TyKind::Adt(d, fa, _)) = (explicit, self.tcx.tys.kind(fresh_adt).clone()) {
            if !a.is_empty() && a.len() <= fa.len() {
                let mut args = a;
                args.extend_from_slice(&fa[args.len()..]);
                return self.tcx.tys.intern(TyKind::Adt(d, args, crate::types::RegionArgsId::EMPTY));
            }
        }
        fresh_adt
    }

    fn instantiate_adt(&mut self, t: TyId) -> TyId {
        if let TyKind::Adt(d, args, _) = self.tcx.tys.kind(t).clone() {
            if args.is_empty() {
                return t;
            }
            let mut fresh = Vec::new();
            for _ in 0..args.len() {
                fresh.push(self.fresh(0));
            }
            return self.tcx.tys.intern(TyKind::Adt(d, fresh, crate::types::RegionArgsId::EMPTY));
        }
        t
    }

    /// `S { a: 1, .. }`: the omitted fields of `adt_ty`'s variant `vi` take their declared
    /// defaults, the anonymous consts the parser made (derive.rs default_consts).
    fn struct_defaults(&mut self, e: ExprId, ctor: DefId, adt_ty: TyId, vi: u32, given: &[u32], lo: u32) {
        let t = self.shallow(adt_ty);
        let TyKind::Adt(ad, _, _) = self.tcx.tys.kind(t).clone() else { return };
        let Some(adt) = self.tcx.adts.get(&ad).cloned() else { return };
        let Some(v) = adt.variants.get(vi as usize) else { return };
        let ty_name = self.prog.syms.str(self.prog.def(ad).name).to_string();
        let variant = if self.prog.def(ctor).kind == DefKind::Variant { Some(self.prog.syms.str(self.prog.def(ctor).name).to_string()) } else { None };
        let scope = self.prog.def(ad).scope;
        let mut out = Vec::new();
        for (i, f) in v.fields.iter().enumerate() {
            if given.contains(&(i as u32)) {
                continue;
            }
            let fname = self.prog.syms.str(f.name).to_string();
            // a dead slot of a live layout edit (M10) and the fields an edit added (the extension
            // block gives them their Default) need no value
            if fname.starts_with("__relax_dead_") || adt.ext_from != u32::MAX && i as u32 >= adt.ext_from {
                continue;
            }
            let cname = crate::parser::derive::default_const_name(&ty_name, variant.as_deref(), &fname);
            match self.prog.syms.get(&cname).and_then(|s| self.prog.lookup_in_scope(scope, s, false)) {
                Some(cd) => out.push((i as u32, cd)),
                // rustc: E0063 missing field (a bare `..` fills only fields with a default value)
                None => self.err(lo, format!("E0063: missing field `{}` in initializer of `{}`; `..` fills only fields declared with a default value (`{}: T = value`){}", fname, ty_name, fname, if adt.n_generics > 0 { "; default values of generic types are not supported yet" } else { "" })),
            }
        }
        self.b.struct_defaults.insert(e.0, out);
    }

    fn field_ty(&mut self, adt_ty: TyId, vi: u32, name: Sym) -> Option<(u32, TyId)> {
        let t = self.shallow_with_regions(adt_ty);
        if let TyKind::Adt(d, args, regions) = self.tcx.tys.kind(t).clone() {
            let adt = self.tcx.adts.get(&d)?.clone();
            let v = adt.variants.get(vi as usize)?;
            for (i, f) in v.fields.iter().enumerate() {
                if f.name == name {
                    let ft = self.instantiate_field_type(f.ty, adt.region_params, regions, &args);
                    if !adt.is_enum && !self.b.field_uses.contains(&(d, i as u32)) {
                        self.b.field_uses.push((d, i as u32));
                        self.b.dependencies.push(d);
                    }
                    return Some((i as u32, ft));
                }
            }
        }
        None
    }

    /// Field types of a tuple-struct / tuple-variant pattern or constructor, with the path's generic args (`let Foo::<i32>(a, b) = ..`: the
    /// resolution recorded them under `key`).
    fn ctor_fields_with(&mut self, r: Res, expected: TyId, pos: u32, key: Option<u32>) -> Vec<TyId> {
        if let Res::Def(d) = r {
            let (adt_ty, vi) = self.adt_of_ctor(d);
            let given = key.and_then(|k| self.b.res_args.get(&k).cloned());
            let adt_ty = match (self.tcx.tys.kind(adt_ty).clone(), given) {
                (TyKind::Adt(ad, gen, _), Some(a)) if a.len() == gen.len() && !a.is_empty() => self.tcx.tys.intern(TyKind::Adt(ad, a, crate::types::RegionArgsId::EMPTY)),
                _ => self.instantiate_adt(adt_ty),
            };
            self.coerce_or_unify(adt_ty, expected, None, pos);
            let t = self.shallow_with_regions(adt_ty);
            if let TyKind::Adt(ad, args, regions) = self.tcx.tys.kind(t).clone() {
                if let Some(adt) = self.tcx.adts.get(&ad).cloned() {
                    if let Some(v) = adt.variants.get(vi as usize) {
                        let mut out = Vec::new();
                        for f in &v.fields {
                            out.push(self.instantiate_field_type(f.ty, adt.region_params, regions, &args));
                        }
                        return out;
                    }
                }
            }
        }
        Vec::new()
    }

    // ------------------------------------------------------------ paths

    fn resolve_struct_path(&mut self, path: &Path) -> Res {
        let prog = self.prog;
        let segs = crate::program::path_segs(prog, self.file, path);
        if segs.len() == 1 && segs[0].0 == SegKind::SelfType {
            if let Some(st) = self.env.self_ty {
                let st = self.tcx.tys.subst_for_inference(st, &self.inst_args.clone());
                if let TyKind::Adt(d, _, _) = self.tcx.tys.kind(st) {
                    return Res::Def(*d);
                }
            }
            return Res::Err;
        }
        if segs.len() == 1 {
            if let Some(d) = prog.lookup_in_scope(self.module, segs[0].1, true) {
                if matches!(prog.def(d).kind, DefKind::Struct | DefKind::Union) {
                    return Res::Def(d);
                }
                if prog.def(d).kind == DefKind::TypeAlias {
                    let t = self.tcx.alias_ty(&self.cx, prog, d);
                    if let TyKind::Adt(ad, _, _) = self.tcx.tys.kind(t) {
                        return Res::Def(*ad);
                    }
                }
            }
            if let Some(d) = prog.lookup_in_scope(self.module, segs[0].1, false) {
                if prog.def(d).kind == DefKind::Variant {
                    return Res::Def(d);
                }
            }
            self.err(path.lo, format!("unresolved struct `{}`", crate::tcx::path_str(prog, self.file, path)));
            return Res::Err;
        }
        // module::Struct, then Enum::Variant / Self::Variant
        if let Some(d) = self.tcx.resolve_type_path_def(prog, self.file, self.module, path) {
            if matches!(prog.def(d).kind, DefKind::Struct | DefKind::Union | DefKind::Variant) {
                return Res::Def(d);
            }
            // `module::Alias { .. }` (a type alias to a struct, as for a one-segment path)
            if prog.def(d).kind == DefKind::TypeAlias {
                let t = self.tcx.alias_ty(&self.cx, prog, d);
                if let TyKind::Adt(ad, _, _) = self.tcx.tys.kind(t) {
                    return Res::Def(*ad);
                }
            }
        }
        if let Some(t) = self.assoc_struct_path(path) {
            if let TyKind::Adt(ad, _, _) = self.tcx.tys.kind(t) {
                return Res::Def(*ad);
            }
        }
        let (r, _) = self.resolve_value_path(path, u32::MAX, false);
        r
    }

    /// Type of a value def used as an expression (fn items get fresh generic args).
    fn value_def_ty(&mut self, d: DefId, explicit: Option<Vec<TyId>>, key: u32, impl_args_from: u8) -> TyId {
        self.b.dependencies.push(d);
        let _ = impl_args_from;
        let def = self.prog.def(d);
        match def.kind {
            DefKind::Fn | DefKind::AssocFn | DefKind::ForeignFn => {
                let n = self.tcx.fn_sig(self.prog, d).map_or(0, |s| s.n_generics);
                let mut args = Vec::new();
                match explicit {
                    Some(v) => {
                        for i in 0..n as usize {
                            if i < v.len() {
                                args.push(v[i]);
                            } else {
                                args.push(self.fresh(0));
                            }
                        }
                    }
                    None => {
                        for _ in 0..n {
                            args.push(self.fresh(0));
                        }
                    }
                }
                self.b.res_args.insert(key, args.clone());
                self.tcx.tys.intern(TyKind::FnDef(d, args, crate::types::RegionArgsId::EMPTY))
            }
            DefKind::Const | DefKind::Static | DefKind::AssocConst | DefKind::ForeignStatic => {
                let t = self.tcx.const_tys.get(&d).copied().unwrap_or(self.tcx.tys.error);
                match explicit {
                    Some(v) => {
                        // the args pick the impl of a trait's const at evaluation (`T::ZERO`)
                        self.b.res_args.insert(key, v.clone());
                        self.tcx.tys.subst_for_inference(t, &v)
                    }
                    None => t,
                }
            }
            DefKind::Variant | DefKind::Struct => {
                let (adt_ty, vi) = self.adt_of_ctor(d);
                let adt_def = match self.tcx.tys.kind(adt_ty) {
                    TyKind::Adt(a, _, _) => *a,
                    _ => NO_DEF,
                };
                let adt = match self.tcx.adts.get(&adt_def) {
                    Some(a) => a.clone(),
                    None => return self.tcx.tys.error,
                };
                let mut args = Vec::new();
                match explicit {
                    Some(v) => args = v,
                    None => {
                        for _ in 0..adt.n_generics {
                            args.push(self.fresh(0));
                        }
                    }
                }
                self.b.res_args.insert(key, args.clone());
                let inst = self.tcx.tys.intern(TyKind::Adt(adt_def, args.clone(), crate::types::RegionArgsId::EMPTY));
                let v = &adt.variants[vi as usize];
                if v.shape == 1 && !adt.is_union {
                    // tuple ctor: a fn item of its own (rustc: FnDef with the ADT's args, which
                    // keeps the written lifetimes; it reifies to `fn(fields..) -> Adt` on demand)
                    self.tcx.tys.intern(TyKind::FnDef(d, args, crate::types::RegionArgsId::EMPTY))
                } else {
                    inst
                }
            }
            _ => self.tcx.tys.error,
        }
    }

    /// `<T>::item` (no trait): on `dyn Trait`, the trait's (or a supertrait's) item with
    /// Self = the trait object (a virtual call); otherwise T's inherent item.
    fn resolve_qself_no_trait(&mut self, self_t: TyId, name: Sym, key: u32, lo: u32, given: &[TyId]) -> (Res, TyId) {
        let error = self.tcx.tys.error;
        let st = self.shallow(self_t);
        if let TyKind::Dyn(td, targs, _, _, _, _, _) = self.tcx.tys.kind(st).clone() {
            if let Some(item) = self.dyn_method(td, name) {
                let mut args = vec![st];
                let parent = self.prog.def(item).parent;
                if parent == td {
                    args.extend(targs);
                } else if let Some(sa) = self.dyn_super_args(td, &targs, st, parent) {
                    args.extend(sa);
                }
                let sig = self.tcx.fn_sig(self.prog, item).cloned();
                let np = sig.as_ref().map_or(1, |s| s.n_parent_generics) as usize;
                while args.len() < np {
                    args.push(self.fresh(0));
                }
                let own = sig.map_or(0, |s| s.n_generics - s.n_parent_generics);
                for i in 0..own as usize {
                    args.push(given.get(i).copied().unwrap_or_else(|| self.fresh(0)));
                }
                let t = self.value_def_ty(item, Some(args), key, 1);
                return (Res::Def(item), t);
            }
        }
        if let Some((item, imp)) = self.tcx.inherent_item(&self.cx, self.prog, st, name) {
            let mut args = self.match_impl_args(imp, st);
            let own = self.tcx.fn_sig(self.prog, item).map_or(0, |s| s.n_generics - s.n_parent_generics);
            for i in 0..own as usize {
                args.push(given.get(i).copied().unwrap_or_else(|| self.fresh(0)));
            }
            let t = self.value_def_ty(item, Some(args), key, 1);
            return (Res::Def(item), t);
        }
        // `<*mut Object>::encode()`: like `T::item`, items of traits in scope count too
        // (rustc_hir_typeck method/mod.rs resolve_fully_qualified_call probes the traits in scope)
        let cands = self.scoped_trait_methods(st, name);
        if let Some(&(item, imp)) = cands.first() {
            let ambiguous = cands.iter().filter(|c| c.0 == item).count() > 1;
            let imp = if ambiguous { crate::program::NO_DEF } else { imp };
            let args = self.trait_call_args(item, imp, st, given);
            let t = self.value_def_ty(item, Some(args), key, 1);
            return (Res::Def(item), t);
        }
        // `<Self>::Variant(..)`, `Alias::Variant`: an enum's variant (rustc
        // resolve_fully_qualified_call looks up enum variants before probing)
        if let TyKind::Adt(ad, aargs, _) = self.tcx.tys.kind(st).clone() {
            if self.prog.def(ad).kind == DefKind::Enum {
                if let Some(v) = self.prog.lookup_in_container(ad, name, false) {
                    if self.prog.def(v).kind == DefKind::Variant {
                        let t = self.value_def_ty(v, Some(aargs), key, 0);
                        return (Res::Def(v), t);
                    }
                }
            }
        }
        // a rigid projection or param of a generic body (`<A as Alloc<T>>::Mem::default()`):
        // through its bounds
        if matches!(self.tcx.tys.kind(st), TyKind::Assoc(..) | TyKind::Param(_)) {
            if let Some((item, td_args)) = self.trait_item_for(st, name) {
                let mut args = vec![st];
                args.extend(td_args);
                let own = self.tcx.fn_sig(self.prog, item).map_or(0, |s| s.n_generics - s.n_parent_generics);
                for i in 0..own as usize {
                    args.push(given.get(i).copied().unwrap_or_else(|| self.fresh(0)));
                }
                let t = self.value_def_ty(item, Some(args), key, 1);
                return (Res::Def(item), t);
            }
        }
        // `<i32>::ONE`, `MyType::CONST`: an associated const of a trait in scope that the type
        // implements (the probe covers all associated items, not only methods)
        if let Some(r) = self.scoped_assoc_const(st, name, key) {
            return r;
        }
        let ts = self.ty_str(st);
        self.err(lo, format!("no item `{}` on `{}` -- name the trait: `<{} as Trait>::{}`", self.prog.syms.str(name), ts, ts, self.prog.syms.str(name)));
        (Res::Err, error)
    }

    /// `<i32>::ONE`, `Option::DEFAULT`: an associated const of a trait in scope with exactly
    /// one impl that can apply to `st`.
    fn scoped_assoc_const(&mut self, st: TyId, name: Sym, key: u32) -> Option<(Res, TyId)> {
        if !matches!(self.tcx.tys.kind(st), TyKind::Infer(_) | TyKind::Error) {
            let _ = self.scoped_trait_methods(st, name); // fills bound_traits
            let mut traits: Vec<DefId> = self.prog.traits_in_scope(self.module).iter().copied().collect();
            if let Some(b) = &self.bound_traits {
                traits.extend(b.iter().copied());
            }
            let mut seen = crate::fxhash::HashSet::default();
            traits.retain(|t| seen.insert(*t));
            let mut hits: Vec<(DefId, DefId)> = Vec::new();
            for td in traits {
                let it = self.prog.traits[self.prog.def(td).sub as usize].iter().copied().find(|&it| self.prog.def(it).name == name && self.prog.def(it).kind == DefKind::AssocConst);
                if let Some(it) = it {
                    let mark = self.snapshot();
                    let selected = self.select_unspecified_trait(td, st);
                    self.rollback(mark);
                    let imp = match selected {
                        SelectionResult::Ok(selected) => selected.method_owner(),
                        SelectionResult::Ambiguous(_) => crate::program::NO_DEF,
                        SelectionResult::NoSolution => continue,
                    };
                    hits.push((it, imp));
                }
            }
            if hits.len() == 1 {
                let (item, imp) = hits[0];
                let args = self.trait_call_args(item, imp, st, &[]);
                self.register_method_obligation(item, &args);
                let t = self.value_def_ty(item, Some(args), key, 1);
                return Some((Res::Def(item), t));
            }
        }
        None
    }

    /// Resolves a value path. `key`: expr or pat id for recording generic args.
    fn resolve_value_path(&mut self, path: &Path, key: u32, is_pat: bool) -> (Res, TyId) {
        let prog = self.prog;
        let segs = crate::program::path_segs(prog, self.file, path);
        let error = self.tcx.tys.error;
        if let Some(q) = self.ast().qself(path) {
            // `<T as Trait>::item`
            let self_t = self.lower_ty(q.ty);
            let tp = match &q.trait_path {
                Some(tp) => tp,
                None => return { let given = self.explicit_args(path).unwrap_or_default(); self.resolve_qself_no_trait(self_t, segs[segs.len() - 1].1, key, path.lo, &given) },
            };
            // `<T as Trait>::Assoc::item`: the qualified part names a type (a projection),
            // the last segment an item on it, resolved type-relatively as `<Ty>::item` (rustc
            // resolve_qpath with a partial resolution: the unresolved segments go to
            // hir_ty_lowering's associated-path lowering)
            if segs.len() >= 2 {
                let sub = Path { qself: path.qself, segs: path.segs.prefix(path.segs.len() - 1), lo: path.lo };
                let env = self.env.clone();
                let t = self.tcx.lower_path_ty(&self.cx, prog, self.file, self.module, &env, &sub);
                let inst = self.inst_args.clone();
                let t = self.tcx.tys.subst_for_inference(t, &inst);
                let t = self.norm(t);
                if matches!(self.tcx.tys.kind(t), TyKind::Error) {
                    return (Res::Err, error);
                }
                let given = self.explicit_args(path).unwrap_or_default();
                return self.resolve_qself_no_trait(t, segs[segs.len() - 1].1, key, path.lo, &given);
            }
            let td = match self.tcx.resolve_type_path_def(prog, self.file, self.module, tp) {
                Some(d) => d,
                None => return (Res::Err, error),
            };
            let name = segs[segs.len() - 1].1;
            let mut item = None;
            for &it in &prog.traits[prog.def(td).sub as usize] {
                if prog.def(it).name == name {
                    item = Some(it);
                }
            }
            let item = match item {
                Some(i) => i,
                None => {
                    self.err(path.lo, "no such trait item".to_string());
                    return (Res::Err, error);
                }
            };
            let env = self.env.clone();
            let explicit = self.tcx.lower_generic_args(&self.cx, prog, self.file, self.module, &env, tp);
            let inst = self.inst_args.clone();
            // `<T as Trait<_>>`: an inferred trait argument is an inference variable
            let written: Vec<crate::ast::TyId> = match self.ast().segs(tp.segs).last().and_then(|s| self.ast().gargs(s.args)) {
                Some(GenericArgs::Angle(v)) => self.ast().list(*v).iter().filter_map(|g| match g {
                    GenericArg::Type(t) => Some(*t),
                    _ => None,
                }).collect(),
                _ => Vec::new(),
            };
            let mut explicit2 = Vec::new();
            for (i, e) in explicit.into_iter().enumerate() {
                let infer = written.get(i).map_or(false, |w| matches!(self.ast().ty(*w), crate::ast::Ty::Infer));
                if infer {
                    let v = self.fresh(0);
                    explicit2.push(v);
                } else {
                    explicit2.push(self.tcx.tys.subst_for_inference(e, &inst));
                }
            }
            let targs = self.tcx.fill_trait_defaults(&self.cx, prog, td, self_t, explicit2);
            let mut args = vec![self_t];
            args.extend(targs);
            // the item's own args from the path (`<S as T<123>>::l::<true>()`)
            let given = self.explicit_args(path).unwrap_or_default();
            let own = self.tcx.fn_sig(self.prog, item).map_or(0, |s| s.n_generics - s.n_parent_generics);
            for i in 0..own as usize {
                args.push(if i < given.len() { given[i] } else { self.fresh(0) });
            }
            let t = self.value_def_ty(item, Some(args), key, 1);
            return (Res::Def(item), t);
        }
        let last_args = self.explicit_args(path);
        if segs.len() == 1 && !path.global() {
            let (k, s) = segs[0];
            if k == SegKind::SelfValue || k == SegKind::Ident {
                if !is_pat {
                    if let Some(li) = self.lookup_local(s, self.ast().segs(path.segs)[0].name.lo) {
                        self.note_capture(li, key);
                        let t = self.b.locals[li as usize].ty;
                        return (Res::Local(li), t);
                    }
                }
                // a const generic param as a value: the instance's const arg, its declared type
                if let Some(&(i, cfile, cty)) = self.env.consts.iter().find(|c| self.env.names.get(c.0 as usize) == Some(&s)) {
                    let env = self.env.clone();
                    let t = self.tcx.lower_ty(&self.cx, prog, cfile, self.module, &env, cty);
                    let t = self.tcx.tys.subst_for_inference(t, &self.inst_args.clone());
                    return (Res::ConstParam(i), t);
                }
            }
            if k == SegKind::SelfType {
                // `Self` as a unit/tuple struct ctor
                if let Some(st) = self.env.self_ty {
                    let st = self.tcx.tys.subst_for_inference(st, &self.inst_args.clone());
                    if let TyKind::Adt(d, args, _) = self.tcx.tys.kind(st).clone() {
                        let t = self.value_def_ty(d, Some(args), key, 0);
                        return (Res::Def(d), t);
                    }
                }
            }
            if let Some(d) = prog.lookup_in_scope(self.module, s, false) {
                let t = self.value_def_ty(d, last_args, key, 0);
                return (Res::Def(d), t);
            }
            if path.segs.len() == 1 && !path.global() {
                if let Some(d) = prog.relaxed_import(self.module, s, false, self.file, path.lo) {
                    let t = self.value_def_ty(d, last_args, key, 0);
                    return (Res::Def(d), t);
                }
            }
            let help = import_help(prog, self.module, s, false);
            self.err(path.lo, format!("E0425: cannot find value `{}` in this scope{}", crate::tcx::path_str(prog, self.file, path), help));
            return (Res::Err, error);
        }
        let n = segs.len();
        // `::f` (2015: a path from the crate root)
        if n == 1 && path.global() && prog.crates[prog.mods[self.module as usize].krate as usize].edition < 2018 {
            let krate = prog.mods[self.module as usize].krate;
            let root = prog.mods[prog.crates[krate as usize].root_mod as usize].def;
            if let Some(d) = prog.lookup_in_container(root, segs[0].1, false) {
                let t = self.value_def_ty(d, last_args, key, 0);
                return (Res::Def(d), t);
            }
        }
        // container path (module / enum / trait)
        let parent = if segs[0].0 == SegKind::SelfType && n == 2 {
            None
        } else {
            prog.resolve_mod_path(self.module, path.global(), &segs[..n - 1], false, false)
        };
        if let Some(pd) = parent {
            let pk = prog.def(pd).kind;
            if matches!(pk, DefKind::Mod | DefKind::Enum | DefKind::Trait) {
                if let Some(d) = prog.lookup_in_container(pd, segs[n - 1].1, false) {
                    // enum variant: generic args may sit on the enum segment
                    let explicit = if pk == DefKind::Enum {
                        self.seg_args(path, n - 2).or(last_args)
                    } else if pk == DefKind::Trait && matches!(prog.def(d).kind, DefKind::AssocFn) && (last_args.is_some() || self.seg_args(path, n - 2).is_some()) {
                        // `Trait::<A>::m::<B>`: [Self (open), the trait's args, the fn's own]
                        let nt = self.tcx.trait_generic_count(prog, pd);
                        let ta = self.seg_args(path, n - 2).unwrap_or_default();
                        let mut v = vec![self.fresh(0)];
                        for i in 0..nt {
                            v.push(if i < ta.len() { ta[i] } else { self.fresh(0) });
                        }
                        v.extend(last_args.unwrap_or_default());
                        Some(v)
                    } else if pk == DefKind::Trait && matches!(prog.def(d).kind, DefKind::AssocConst) {
                        // `Trait::CONST`: [Self (open, inferred from the use), the trait's args];
                        // the impl's const is picked once Self is known (rustc: a projection)
                        let nt = self.tcx.trait_generic_count(prog, pd);
                        let ta = self.seg_args(path, n - 2).unwrap_or_default();
                        let mut v = vec![self.fresh(0)];
                        for i in 0..nt {
                            v.push(if i < ta.len() { ta[i] } else { self.fresh(0) });
                        }
                        Some(v)
                    } else {
                        last_args
                    };
                    let t = self.value_def_ty(d, explicit, key, 0);
                    return (Res::Def(d), t);
                }
                // `str::to_owned` with a module `str` in scope (a glob of std): a first segment
                // naming a primitive type falls back to the type when the module lacks the item
                // (rustc_resolve late.rs resolve_qpath, "required for backward compatibility")
                let prim_first = n == 2 && !path.global() && crate::program::PRIMS.iter().any(|(nm, _)| prog.syms.get(nm) == Some(segs[0].1));
                if pk != DefKind::Enum && pk != DefKind::Trait && !prim_first {
                    self.err(path.lo, format!("cannot find value `{}`", crate::tcx::path_str(prog, self.file, path)));
                    return (Res::Err, error);
                }
            }
        }
        // type-relative: <Type>::item
        let self_ty = match self.type_of_prefix(path, n - 1) {
            Some(t) => t,
            None => {
                // a missing first segment: where it exists (E0433, rustc's "failed to resolve")
                let help = if n == 2 && !path.global() { import_help(prog, self.module, self.sym(self.ast().segs(path.segs)[0].name), true) } else { String::new() };
                let code = if help.is_empty() { "" } else { "E0433: " };
                self.err(path.lo, format!("{}cannot resolve `{}`{}", code, crate::tcx::path_str(prog, self.file, path), help));
                return (Res::Err, error);
            }
        };
        let name = segs[n - 1].1;
        // enum variant through a type alias / Self
        if let TyKind::Adt(ad, aargs, _) = self.tcx.tys.kind(self_ty).clone() {
            if prog.def(ad).kind == DefKind::Enum {
                if let Some(v) = prog.lookup_in_container(ad, name, false) {
                    let t = self.value_def_ty(v, Some(aargs), key, 0);
                    return (Res::Def(v), t);
                }
            }
        }
        // `T::item` with T a generic param (or `Self` in a trait body): resolved through the
        // param's bounds only, as rustc does on the generic body; an inherent item of the type
        // a given instance substitutes is never seen (`U::from(x)` with U: From<T> calls
        // From::from even when the instance's U has an inherent `from`).
        // rustc_hir_analysis hir_ty_lowering lower_assoc_path / probe_single_bound_for_assoc_item
        let prefix_is_param = n == 2
            && path.qself.is_none()
            && match self.ast().segs(path.segs)[0].kind {
                SegKind::SelfType => self.env.trait_def.is_some(),
                _ => {
                    let s0 = self.sym(self.ast().segs(path.segs)[0].name);
                    self.env.names.iter().take(self.inst_args.len()).any(|nm| *nm == s0)
                }
            };
        if prefix_is_param {
            if let Some((item, td_args)) = self.trait_item_for(self_ty, name) {
                let mut args = vec![self_ty];
                args.extend(td_args);
                let la = last_args.clone().unwrap_or_default();
                let sig = self.tcx.fn_sig(self.prog, item).cloned();
                let own = sig.map_or(0, |s| s.n_generics - s.n_parent_generics);
                for i in 0..own as usize {
                    args.push(if i < la.len() { la[i] } else { self.fresh(0) });
                }
                let t = self.value_def_ty(item, Some(args), key, 1);
                return (Res::Def(item), t);
            }
        }
        match self.tcx.inherent_item(&self.cx, prog, self_ty, name) {
            Some((item, imp)) => {
                // impl generic args from matching the impl self type against self_ty
                let impl_args = self.match_impl_args(imp, self_ty);
                let own = self.tcx.fn_sig(self.prog, item).map_or(0, |s| s.n_generics - s.n_parent_generics);
                let mut args = impl_args;
                let la = last_args.unwrap_or_default();
                for i in 0..own as usize {
                    if i < la.len() {
                        args.push(la[i]);
                    } else {
                        args.push(self.fresh(0));
                    }
                }
                let t = self.value_def_ty(item, Some(args), key, 1);
                (Res::Def(item), t)
            }
            None => {
                // a trait method implemented for this type
                let cands = self.tcx.trait_methods_for(&self.cx, prog, self_ty, name);
                if let Some(&(item, imp)) = cands.first() {
                    let la = last_args.unwrap_or_default();
                    // several impls of the trait for this type (`Rc::from` from &str, String,
                    // Box..): leave the trait args open; the impl is chosen once they are known
                    let ambiguous = cands.iter().filter(|c| c.0 == item).count() > 1;
                    let imp = if ambiguous { crate::program::NO_DEF } else { imp };
                    let args = self.trait_call_args(item, imp, self_ty, &la);
                    let t = self.value_def_ty(item, Some(args), key, 1);
                    return (Res::Def(item), t);
                }
                // an associated const / fn of a trait: through the body's bounds (`T::ZERO` with
                // T: Zeroable, checked as the instance type), else a trait in scope implemented
                // for the type
                if let Some((item, td_args)) = self.trait_item_for(self_ty, name) {
                    let mut args = vec![self_ty];
                    args.extend(td_args);
                    let la = last_args.unwrap_or_default();
                    let sig = self.tcx.fn_sig(self.prog, item).cloned();
                    let own = sig.map_or(0, |s| s.n_generics - s.n_parent_generics);
                    for i in 0..own as usize {
                        args.push(if i < la.len() { la[i] } else { self.fresh(0) });
                    }
                    let t = self.value_def_ty(item, Some(args), key, 1);
                    return (Res::Def(item), t);
                }
                if let Some(r) = self.scoped_assoc_const(self_ty, name, key) {
                    return r;
                }
                let ts = self.ty_str(self_ty);
                self.err(path.lo, format!("no associated item `{}` on `{}`", prog.syms.str(name), ts));
                (Res::Err, error)
            }
        }
    }

    /// A trait item named `name` for type `t` and the trait's args: from a bound of this
    /// body whose param is instantiated to `t` (with the bound's args), else from a trait in
    /// scope with an impl for `t`.
    fn trait_item_for(&mut self, t: TyId, name: Sym) -> Option<(DefId, Vec<TyId>)> {
        let item_of = |prog: &Program, td: DefId| prog.traits[prog.def(td).sub as usize].iter().copied().find(|it| prog.def(*it).name == name);
        // the bounds on `t` (with supertraits, and `Self: Trait` in the trait's own bodies)
        for (d, ta) in self.param_bounds(t) {
            if let Some(it) = item_of(self.prog, d) {
                let ta = ta.into_iter().map(|x| self.norm(x)).collect();
                return Some((it, ta));
            }
        }
        let scope = self.prog.traits_in_scope(self.module);
        let mut tds: Vec<DefId> = scope.iter().copied().collect();
        tds.sort_by_key(|d| d.0);
        for td in tds {
            if let Some(it) = item_of(self.prog, td) {
                if self.tcx.trait_generic_count(self.prog, td) == 0 && !matches!(self.select_trait(td, t, &[]), SelectionResult::NoSolution) {
                    return Some((it, Vec::new()));
                }
            }
        }
        None
    }

    /// Generic args [Self, trait args.., own..] to call trait method `item` (found through
    /// impl `imp`) on receiver type `t`.
    /// Does `t` have a method named `s` taking `&self` / `&mut self` (inherent, trait object or
    /// trait impl)?
    /// A method call on a value whose type is a generic param of this body (checked per
    /// instance, so it arrives here as the param's instance type): rustc resolves it from the
    /// param's bounds alone, with the bound's trait args (`key.as_ref()` with
    /// `K: AsRef<OsStr>`, K = &str, is `AsRef<OsStr>`, not the first `AsRef` impl of str).
    fn bound_method(&mut self, e: ExprId, rt: TyId, s: Sym, turbofish: GenericArgsId, args: &[ExprId], lo: u32) -> Option<TyId> {
        let mut bounds = self.tcx.fn_trait_bounds(self.prog, self.b.def).cloned().unwrap_or_default();
        // a trait's own body has `Self: Trait<P..>` (rustc: the trait's implicit predicate,
        // predicates_of); Self is param 0, the trait's params follow. `self.draw(..)` in a
        // default method is the trait's `draw`, even when the instance's Self type has an
        // inherent `draw` of its own
        if let Some(td) = self.env.trait_def {
            if self.prog.def(self.b.def).parent == td {
                let nt = self.tcx.trait_generic_count(self.prog, td);
                let targs: Vec<TyId> = (1..=nt as u32).map(|i| self.tcx.tys.intern(TyKind::Param(i))).collect();
                // and its supertraits' (`Self: Widget` implies `Self: WidgetNode`: `self.visible()`
                // in Widget's default body is WidgetNode's method even when the instance's Self type
                // has an inherent `visible` of its own)
                let mut todo = self.tcx.trait_super_refs(&self.cx, self.prog, td, &targs);
                bounds.push((0, td, targs));
                let mut seen = vec![td];
                while let Some((sd, sargs)) = todo.pop() {
                    if seen.contains(&sd) {
                        continue;
                    }
                    seen.push(sd);
                    todo.extend(self.tcx.trait_super_refs(&self.cx, self.prog, sd, &sargs));
                    bounds.push((0, sd, sargs));
                }
            }
        }
        if bounds.is_empty() {
            return None;
        }
        // a bound's supertraits are bounds of its param too (rustc elaborates the param env:
        // `W: StyleWidget` with `StyleWidget: Styled` makes `value.apply(..)` Styled's method,
        // even when the instance's W has an inherent `apply` of its own)
        let mut i = 0;
        while i < bounds.len() {
            let (pi, td, targs) = bounds[i].clone();
            let self_t = self.tcx.tys.intern(TyKind::Param(pi));
            for (sd, sargs) in self.tcx.trait_super_refs_of(&self.cx, self.prog, td, self_t, &targs) {
                if !bounds.iter().any(|b| b.0 == pi && b.1 == sd && b.2 == sargs) {
                    bounds.push((pi, sd, sargs));
                }
            }
            i += 1;
        }
        let rts = self.shallow(rt);
        if matches!(self.tcx.tys.kind(rts), TyKind::Infer(_) | TyKind::Error) {
            return None;
        }
        // rustc's probe takes a by-value match first: with `key: &Q` and bounds `Q: Ord` and
        // `K: Ord` where K = &Q in this instance (BTreeMap<&[String], _>::search_key),
        // `key.cmp(..)` is Q's `&self` method on `key` itself, not K's through an autoref; a
        // bound reached through one dereference for a `&self` / `&mut self` method is taken
        // before one that needs an autoref
        let by_ref_self = |this: &Self, td: DefId| -> bool {
            this.prog.traits[this.prog.def(td).sub as usize].iter().any(|it| this.prog.def(*it).name == s && this.tcx.fn_sig(this.prog, *it).map_or(false, |sg| sg.self_kind >= 2))
        };
        let mut ordered: Vec<(u32, DefId, Vec<TyId>)> = Vec::new();
        let mut later: Vec<(u32, DefId, Vec<TyId>)> = Vec::new();
        for b in bounds {
            let pa = self.b.args.get(b.0 as usize).copied();
            let deref_hit = matches!(self.tcx.tys.kind(rts).clone(), TyKind::Ref(_, inner, _) if pa == Some(self.shallow(inner)));
            if deref_hit && pa != Some(rts) && by_ref_self(self, b.1) {
                ordered.push(b);
            } else {
                later.push(b);
            }
        }
        ordered.extend(later);
        // several bounds whose params this instance makes the same type, through different
        // trait args (`AllocU8: Allocator<u8>` and `AllocHC: Allocator<HuffmanCode>`, both
        // StandardAlloc): rustc resolves the call once, on the generic body, through the bound
        // of the receiver's declared param -- take the trait args the polymorphic body chose
        let poly = if self.b.args.iter().all(|a| self.tcx.tys.is_concrete(*a)) && self.ambiguous_bounds(&ordered, rts, s) { self.poly_method_targs(e) } else { None };
        if let Some((ptd, pta)) = poly {
            ordered.retain(|(_, td, targs)| {
                *td == ptd && targs.len() == pta.len() && targs.iter().zip(&pta).all(|(x, y)| self.tcx.tys.subst_for_inference(*x, &self.b.args) == *y)
            });
        }
        for (pi, td, targs) in ordered {
            // the receiver is the param's instance type, or a reference to it (`r.start_bound()` with
            // r: &R): probing autoderefs `&R` to `R` (method/probe.rs), then autorefs for `&self`
            let pa = self.b.args.get(pi as usize).copied();
            let recv = rts;
            let (rts, derefs) = if pa == Some(rts) {
                (rts, 0u8)
            } else {
                match self.tcx.tys.kind(rts).clone() {
                    TyKind::Ref(_, inner, _) if pa == Some(self.shallow(inner)) => (self.shallow(inner), 1u8),
                    _ => continue,
                }
            };
            // the trait's own method (a supertrait's has the supertrait's args)
            let item = match self.prog.traits[self.prog.def(td).sub as usize]
                .iter()
                .copied()
                .find(|it| self.prog.def(*it).name == s && self.prog.def(*it).kind == DefKind::AssocFn)
            {
                Some(i) => i,
                None => continue,
            };
            let ta: Vec<TyId> = targs.iter().map(|t| self.tcx.tys.subst_for_inference(*t, &self.b.args)).collect();
            let ta: Vec<TyId> = ta.into_iter().map(|t| self.norm(t)).collect();
            // a by-value `self` method on a reference to the param: the where-clause candidate's
            // xform self type is the param itself, which does not match step 0 (the reference) by
            // value; the trait's candidate on the reference does when the reference implements
            // the trait (rustc method/probe.rs pick_core l.1305 pick_by_value_method at the first
            // step, before the autoderef step). `reader.take(n)` with `reader: &mut R`, `R: Read`
            // is `<&mut R as Read>::take(reader)` -- never a bitwise move of `*reader`
            if derefs == 1 && self.tcx.fn_sig(self.prog, item).map_or(false, |sg| sg.self_kind == 1) {
                let imp = match self.select_trait(td, recv, &ta) {
                    SelectionResult::Ok(selected) => Some(selected.method_owner()),
                    SelectionResult::Ambiguous(_) => Some(crate::program::NO_DEF),
                    SelectionResult::NoSolution => None,
                };
                if let Some(imp) = imp {
                    self.known_targs = Some(ta);
                    return Some(self.check_trait_method_call(e, item, imp, recv, 0, turbofish, args, lo, None));
                }
            }
            // a param of a body checked polymorphically has no impl, only the bound (rustc's
            // where-clause candidate): the trait's method, its impl left open
            let imp = match self.select_trait(td, rts, &ta) {
                SelectionResult::Ok(selected) => selected.method_owner(),
                SelectionResult::Ambiguous(_) => crate::program::NO_DEF,
                SelectionResult::NoSolution => return None,
            };
            self.known_targs = Some(ta);
            return Some(self.check_trait_method_call(e, item, imp, rts, derefs, turbofish, args, lo, None));
        }
        None
    }

    /// A method call on a projection of a polymorphic body (`T::encs().as_ref()` with
    /// `type Encs: AsRef<[u8]>`), or a reference to one: through the projection's declared
    /// bounds in the param env (rustc: the projection's item bounds are its candidates).
    fn projection_method(&mut self, e: ExprId, rt: TyId, s: Sym, turbofish: GenericArgsId, args: &[ExprId], lo: u32) -> Option<TyId> {
        let r0 = self.shallow(rt);
        let r0 = self.norm(r0);
        let (rts, derefs) = match self.tcx.tys.kind(r0).clone() {
            TyKind::Assoc(..) => (r0, 0u8),
            TyKind::Ref(_, x, _) if matches!(self.tcx.tys.kind(self.shallow(x)), TyKind::Assoc(..)) => (self.shallow(x), 1u8),
            _ => return None,
        };
        // the param env's predicates on it, else the associated type's item bounds with
        // their supertraits (`<impl IntoIterator as IntoIterator>::IntoIter: Iterator`)
        let mut cands = self.tcx.param_env_of(&self.cx, rts);
        if let TyKind::Assoc(ad, pa, _) = self.tcx.tys.kind(rts).clone() {
            let mut todo = self.tcx.assoc_decl_bounds(&self.cx, self.prog, ad, &pa);
            while let Some((d, a)) = todo.pop() {
                if cands.iter().any(|c| c.0 == d && c.1 == a) {
                    continue;
                }
                todo.extend(self.tcx.trait_super_refs_of(&self.cx, self.prog, d, rts, &a));
                cands.push((d, a));
            }
        }
        for (td, ta) in cands {
            let item = match self.prog.traits[self.prog.def(td).sub as usize].iter().copied().find(|it| self.prog.def(*it).name == s && self.prog.def(*it).kind == DefKind::AssocFn) {
                Some(i) => i,
                None => continue,
            };
            self.known_targs = Some(ta);
            return Some(self.check_trait_method_call(e, item, crate::program::NO_DEF, rts, derefs, turbofish, args, lo, None));
        }
        None
    }

    /// Do two bounds of this body with a method named `s` apply to receiver `rts` (its param's
    /// instance type, or a reference to it) through different trait args?
    fn ambiguous_bounds(&mut self, bounds: &[(u32, DefId, Vec<TyId>)], rts: TyId, s: Sym) -> bool {
        let inner = match self.tcx.tys.kind(rts).clone() {
            TyKind::Ref(_, x, _) => Some(self.shallow(x)),
            _ => None,
        };
        let mut seen: Vec<(DefId, Vec<TyId>)> = Vec::new();
        for (pi, td, targs) in bounds {
            let pa = self.b.args.get(*pi as usize).copied();
            if pa != Some(rts) && pa != inner {
                continue;
            }
            if !self.prog.traits[self.prog.def(*td).sub as usize].iter().any(|it| self.prog.def(*it).name == s) {
                continue;
            }
            let ta: Vec<TyId> = targs.iter().map(|t| self.tcx.tys.subst_for_inference(*t, &self.b.args)).collect();
            if !seen.iter().any(|(d, a)| d == td && *a == ta) {
                seen.push((*td, ta));
            }
        }
        seen.len() > 1
    }

    /// Definition-time typeck facts, shared by method and call-trait resolution.
    fn polymorphic_body(&mut self) -> Option<std::sync::Arc<Body>> {
        let def = self.b.def;
        let epoch = self.tcx.collect_epoch.load(std::sync::atomic::Ordering::SeqCst);
        let body = match self.tcx.poly_bodies.get(&(def, epoch)) {
            Some(b) => b,
            None => {
                let n = self.tcx.fn_sig(self.prog, def)?.n_generics;
                let ids: Vec<TyId> = (0..n).map(|i| self.tcx.tys.intern(TyKind::Param(i))).collect();
                let b = std::sync::Arc::new(check_fn_uncached(&self.cx, self.prog, self.tcx, def, &ids));
                self.tcx.poly_bodies.insert((def, epoch), b.clone());
                b
            }
        };
        Some(body)
    }

    /// The trait arguments the generic body selected for method call `e`.
    fn poly_method_targs(&mut self, e: ExprId) -> Option<(DefId, Vec<TyId>)> {
        let body = self.polymorphic_body()?;
        let m = body.methods.get(&e.0)?;
        let td = self.prog.def(m.def).parent;
        if self.prog.def(td).kind != DefKind::Trait {
            return None;
        }
        let nt = self.tcx.trait_generic_count(self.prog, td);
        let ta: Vec<TyId> = m.args.get(1..1 + nt)?.iter().map(|t| self.tcx.tys.subst_for_inference(*t, &self.b.args)).collect();
        Some((td, ta))
    }

    /// rustc_ast_lowering/src/expr.rs:1774-1784,1826-1838: every head is the
    /// by-value argument of IntoIterator::into_iter, followed by next(&mut iter).
    /// UFCS does not autoderef or autoref the head; its adjustment is identity.
    fn for_into_iter_item(&mut self, it: u32, s: TyId) -> Option<TyId> {
        let into = self.tcx.lang_items.get(crate::lang_items::LangItem::IntoIterIntoIter)?;
        let td = self.prog.def(into).parent;
        let dt = self.deep(s);
        match self.select_trait(td, dt, &[]) { SelectionResult::Ok(_) | SelectionResult::Ambiguous(_) => {}, SelectionResult::NoSolution => return None };
        let ad = self.tcx.trait_assoc(self.prog, td, self.prog.syms.get("IntoIter")?)?;
        let proj = self.tcx.tys.intern(TyKind::Assoc(ad, vec![dt], crate::types::RegionArgsId::EMPTY));
        let iter_t = self.norm(proj);
        let item = self.iterator_item(it, iter_t)?;
        self.b.for_into.insert(it, (into, vec![dt], iter_t));
        Some(item)
    }

    /// The pointee of a smart-pointer receiver type (`Box<X>`, `Rc<X>`, `Arc<X>`, `Pin<&mut X>`,
    /// `Pin<&X>`, `Pin<Box<X>>`): where `self: Box<Self>`-style methods are declared.
    fn receiver_pointee(&mut self, t: TyId) -> Option<TyId> {
        let t = self.shallow(t);
        let (d, args) = match self.tcx.tys.kind(t).clone() {
            TyKind::Adt(d, a, _) => (d, a),
            _ => return None,
        };
        let name = self.prog.name(d);
        let a0 = self.shallow(*args.first()?);
        match name {
            "Box" | "Rc" | "Arc" => Some(a0),
            "Pin" => match self.tcx.tys.kind(a0).clone() {
                TyKind::Ref(_, x, _) => Some(self.shallow(x)),
                TyKind::Adt(..) => self.receiver_pointee(a0),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether method `item` (of impl `imp`, Self = `x`) takes exactly the adjusted
    /// receiver `u` (rustc probe.rs: xform_self_ty, checked speculatively).
    fn method_receiver_matches(&mut self, item: DefId, imp: DefId, x: TyId, u: TyId, is_trait: bool) -> bool {
        let sig = match self.tcx.fn_sig(self.prog, item).cloned() {
            Some(s) => s,
            None => return false,
        };
        if !(1..=3).contains(&sig.self_kind) || sig.params.is_empty() {
            return false;
        }
        let save = self.snapshot();
        let errors = self.b.errors.len();
        let args = if is_trait { self.trait_call_args(item, imp, x, &[]) } else { self.match_impl_args(imp, x) };
        let p0 = self.tcx.tys.subst_for_inference(sig.params[0], &args);
        let ok = self.unify(p0, u);
        self.rollback(save);
        self.b.errors.truncate(errors);
        ok
    }

    /// Trait methods `s` callable on `t` here: only traits in scope at the call (rustc's rule;
    /// `rc.borrow_mut()` is RefCell's through Deref unless BorrowMut is imported). Generic
    /// parameters and inference variables keep every candidate (bounds decide).
    fn scoped_trait_methods(&mut self, t: TyId, s: Sym) -> Vec<(DefId, DefId)> {
        let mut tm = self.tcx.trait_methods_for(&self.cx, self.prog, t, s);
        // a param / rigid projection of a generic body: its bounds' methods, supertraits
        // included (rustc assemble_inherent_candidates_from_param: where-clause candidates)
        if matches!(self.tcx.tys.kind(t), TyKind::Param(_) | TyKind::Assoc(..)) {
            for (td, _) in self.param_bounds(t) {
                for &it in &self.prog.traits[self.prog.def(td).sub as usize] {
                    if self.prog.def(it).name == s && self.prog.def(it).kind == DefKind::AssocFn && !tm.iter().any(|x| x.0 == it) {
                        tm.push((it, crate::program::NO_DEF));
                    }
                }
            }
        }
        // a generic param of a polymorphic body has the methods of its bounds / env and of
        // blanket impls only (`v.clone()` on `&T` without `T: Clone` is `<&T as Clone>`'s, not
        // T's through a deref)
        if let (false, TyKind::Param(_)) = (tm.is_empty(), self.tcx.tys.kind(t).clone()) {
            if self.b.args.iter().any(|a| matches!(self.tcx.tys.kind(*a), TyKind::Param(_))) {
                let mut env: Vec<DefId> = self.tcx.param_env_of(&self.cx, t).into_iter().map(|x| x.0).collect();
                env.extend(self.param_bounds(t).into_iter().map(|x| x.0));
                let keep: Vec<(DefId, DefId)> = tm
                    .iter()
                    .copied()
                    .filter(|(item, imp)| {
                        let td = self.prog.def(*item).parent;
                        *imp == crate::program::NO_DEF || env.contains(&td) || self.tcx.impl_self.get(imp).map_or(false, |p| matches!(self.tcx.tys.kind(*p), TyKind::Param(_)))
                    })
                    .collect();
                tm = keep;
            }
        }
        if tm.is_empty() || matches!(self.tcx.tys.kind(t), TyKind::Param(_) | TyKind::Infer(_) | TyKind::Error | TyKind::Assoc(..)) {
            return tm;
        }
        let scope = self.prog.traits_in_scope(self.module);
        if self.bound_traits.is_none() {
            // bodies are checked per instance: a receiver that was a generic param in the
            // source gets its bound's methods (`range.start_bound()` with R: RangeBounds),
            // and a trait's own default methods see the trait
            let mut set = crate::fxhash::HashSet::default();
            let mut todo: Vec<DefId> = Vec::new();
            if let Some(v) = self.tcx.fn_trait_bounds(self.prog, self.b.def) {
                todo.extend(v.iter().map(|x| x.1));
            }
            if let Some(td) = self.env.trait_def {
                todo.push(td);
            }
            while let Some(td) = todo.pop() {
                if set.insert(td) {
                    todo.extend(self.tcx.trait_supers(self.prog, td));
                }
            }
            // inside `impl Tr for X` the trait Tr itself is in scope (rustc resolve
            // traits_in_scope: current_trait_ref), e.g. `self.0.fmt(f)` in `impl fmt::Debug`
            let parent = self.prog.def(self.b.def).parent;
            if self.prog.def(parent).kind == DefKind::Impl {
                if let Some(&td) = self.tcx.impl_trait.get(&parent) {
                    set.insert(td);
                }
            }
            self.bound_traits = Some(set);
        }
        let bt = self.bound_traits.as_ref();
        tm.into_iter()
            .filter(|(item, _)| {
                let td = self.prog.def(*item).parent;
                scope.contains(&td) || bt.map_or(false, |b| b.contains(&td))
            })
            .collect()
    }

    /// For an integer / float inference variable `t`: per numeric type, the first trait
    /// method `s` its impls in scope provide (type, method, impl). None for other types.
    fn numeric_var_methods(&mut self, t: TyId, s: Sym) -> Option<Vec<(TyId, DefId, DefId)>> {
        let TyKind::Infer(v) = self.tcx.tys.kind(t).clone() else { return None };
        let kind = match self.vars[v as usize] {
            VarSt::Free(k) => k,
            _ => 0,
        };
        let prims: &[Prim] = match kind {
            1 => &[Prim::I8, Prim::I16, Prim::I32, Prim::I64, Prim::I128, Prim::Isize, Prim::U8, Prim::U16, Prim::U32, Prim::U64, Prim::U128, Prim::Usize],
            2 => &[Prim::F32, Prim::F64],
            _ => return None,
        };
        let mut hits = Vec::new();
        for &pr in prims {
            let pt = self.tcx.tys.prim(pr);
            let tm = self.scoped_trait_methods(pt, s);
            if let Some(&(item, imp)) = tm.first() {
                hits.push((pt, item, imp));
            }
        }
        Some(hits)
    }

    /// The by-value probe on a reference: only methods taking exactly `&t` / `&mut t`.
    fn has_ref_self_method(&mut self, t: TyId, s: Sym, mutbl: bool) -> bool {
        let receiver = self.tcx.tys.intern(TyKind::Ref(mutbl, t, crate::types::RegionId::ERASED));
        // `r.cmp(..)` with r: &{integer}: the integer types' Ord::cmp takes `&self` (rustc's
        // by-value step on `&{integer}` matches it with Self = {integer}, before the autoref'd
        // `impl Ord for &A`)
        if let Some(hits) = self.numeric_var_methods(t, s) {
            return !hits.is_empty() && hits.iter().all(|h| h.1 == hits[0].1)
                && self.tcx.fn_sig(self.prog, hits[0].1).map_or(false, |sg| sg.self_kind == if mutbl { 3 } else { 2 });
        }
        if let Some((item, imp)) = self.tcx.inherent_item(&self.cx, self.prog, t, s) {
            if self.item_visible(item) && self.method_receiver_matches(item, imp, t, receiver, false) {
                return true;
            }
        }
        if let TyKind::Dyn(td, ..) = self.tcx.tys.kind(t).clone() {
            if let Some(item) = self.dyn_method(td, s) {
                if self.method_receiver_matches(item, crate::program::NO_DEF, t, receiver, true) {
                    return true;
                }
            }
        }
        if let Some((item, _)) = self.opaque_method(t, s) {
            if self.method_receiver_matches(item, crate::program::NO_DEF, t, receiver, true) {
                return true;
            }
        }
        if matches!(self.tcx.tys.kind(t), TyKind::Infer(_) | TyKind::Error) {
            return false;
        }
        // any trait's `&self` method (`self.cmp(o)` with self: &Components, Components both
        // Iterator and Ord: Ord::cmp's receiver is `&Components`, matched by value at that step;
        // Iterator::cmp takes self and would need `&Components: Iterator`)
        let tm = self.scoped_trait_methods(t, s);
        tm.iter().any(|&(item, imp)| self.method_receiver_matches(item, imp, t, receiver, true))
    }

    /// A method named `s` of trait `td` or its supertraits (methods of a trait object).
    fn dyn_method(&self, td: DefId, s: Sym) -> Option<DefId> {
        for &it in &self.prog.traits[self.prog.def(td).sub as usize] {
            if self.prog.def(it).name == s && self.prog.def(it).kind == DefKind::AssocFn {
                return Some(it);
            }
        }
        for sup in self.tcx.trait_supers(self.prog, td) {
            if let Some(m) = self.dyn_method(sup, s) {
                return Some(m);
            }
        }
        None
    }

    /// The args of supertrait `target` reached from trait object principal `td<targs>` (Self =
    /// `dyn_t`): `dyn Bar` with `trait Bar: for<'a> Foo<&'a ()>` gives Foo's `[&()]`. None when no
    /// or several references reach it (rustc: the object's elaborated supertrait predicates).
    fn dyn_super_args(&self, td: DefId, targs: &[TyId], dyn_t: TyId, target: DefId) -> Option<Vec<TyId>> {
        let mut found: Vec<Vec<TyId>> = Vec::new();
        let mut queue: Vec<(DefId, Vec<TyId>, u32)> = vec![(td, targs.to_vec(), 0)];
        let mut seen = 0;
        while let Some((d, a, depth)) = queue.pop() {
            seen += 1;
            if seen > 64 || depth > 8 {
                return None;
            }
            for (sd, sa) in self.tcx.trait_super_refs_of(&self.cx, self.prog, d, dyn_t, &a) {
                if sd == target {
                    if !found.contains(&sa) {
                        found.push(sa.clone());
                    }
                } else {
                    queue.push((sd, sa, depth + 1));
                }
            }
        }
        if found.len() == 1 {
            found.pop()
        } else {
            None
        }
    }

    fn trait_call_args(&mut self, item: DefId, imp: DefId, t: TyId, explicit_own: &[TyId]) -> Vec<TyId> {
        // trait objects (NO_DEF) and #[derive]d impls have no impl item: trait args stay open
        if imp == crate::program::NO_DEF || imp == crate::tcx::DERIVED_IMPL {
            // trait object receiver: [dyn, the principal's args when the method is its own, own..]
            let mut args = vec![t];
            if let TyKind::Dyn(td, targs, _, _, _, _, _) = self.tcx.tys.kind(t).clone() {
                let parent = self.prog.def(item).parent;
                if parent == td {
                    args.extend(targs);
                } else if let Some(sa) = self.dyn_super_args(td, &targs, t, parent) {
                    args.extend(sa);
                }
            }
            let sig = self.tcx.fn_sig(self.prog, item).cloned();
            let np = sig.as_ref().map_or(1, |s| s.n_parent_generics) as usize;
            while args.len() < np {
                args.push(self.fresh(0));
            }
            let own = sig.map_or(0, |s| s.n_generics - s.n_parent_generics);
            for i in 0..own as usize {
                if i < explicit_own.len() {
                    args.push(explicit_own[i]);
                } else {
                    args.push(self.fresh(0));
                }
            }
            return args;
        }
        let impl_args = self.match_impl_args(imp, t);
        let targs = self.tcx.impl_trait_args.get(&imp).cloned().unwrap_or_default();
        let mut args = vec![t];
        for ta in targs {
            let x = self.tcx.tys.subst_for_inference(ta, &impl_args);
            args.push(x);
        }
        let own = self.tcx.fn_sig(self.prog, item).map_or(0, |s| s.n_generics - s.n_parent_generics);
        for i in 0..own as usize {
            if i < explicit_own.len() {
                args.push(explicit_own[i]);
            } else {
                args.push(self.fresh(0));
            }
        }
        args
    }

    /// One autoderef step from `t`: built-in for references and raw pointers, through
    /// `Deref` for other types. Records overloaded steps under (expr, step).
    fn deref_step(&mut self, e: u32, step: u8, t: TyId) -> Option<TyId> {
        let t = self.shallow_with_regions(t);
        match self.tcx.tys.kind(t).clone() {
            TyKind::Ref(_, i, _) | TyKind::Ptr(_, i) => Some(self.shallow_with_regions(i)),
            // (a param / rigid projection with a Deref bound derefs to its `Target` binding,
            // `D: DerefMut<Target = DrawVars>`)
            // (an opaque type derefs through its item bounds: `impl Deref<Target = Path>`,
            // rustc autoderef.rs overloaded_deref_ty selects the bound's candidate)
            TyKind::Adt(..) | TyKind::Param(_) | TyKind::Assoc(..) | TyKind::Opaque(..) => {
                let td = self.lang_item(&["ops", "Deref"])?;
                let dt = self.deep(t);
                if !self.tcx.opaque_implements(td, dt) {
                    match self.select_trait(td, dt, &[]) {
                        SelectionResult::Ambiguous(crate::solve::goal::MaybeCause::Overflow { .. }) | SelectionResult::NoSolution => return None,
                        SelectionResult::Ok(_) | SelectionResult::Ambiguous(_) => {},
                    };
                }
                let target = self.tcx.trait_assoc(self.prog, td, self.prog.syms.get("Target")?)?;
                let proj = self.tcx.tys.intern(TyKind::Assoc(target, vec![dt], crate::types::RegionArgsId::EMPTY));
                let r = self.norm(proj);
                let m = self.trait_fn(td, "deref")?;
                self.b.ov_derefs.insert((e, step), (m, vec![dt]));
                Some(r)
            }
            _ => None,
        }
    }

    /// The parameter names of fn `d` (its declaration's patterns, `_` for others), without self.
    fn param_names(&self, d: DefId) -> Vec<String> {
        let def = self.prog.def(d);
        let f = &self.prog.files[def.file as usize];
        match &f.ast.item(def.item).kind {
            crate::ast::ItemKind::Fn(sig, _, _) => f.ast.list(f.ast.fn_sig(*sig).params)
                .iter()
                .map(|p| match f.ast.pat(p.pat) {
                    Pat::Ident { name, .. } => f.text(*name).to_string(),
                    _ => "_".to_string(),
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    /// Help for E0061 (too few / too many arguments): which parameters are missing, by name and
    /// type (matched against the given arguments' types in order: the first parameter each
    /// argument fits), or which arguments are extra.
    fn arg_count_help(&mut self, callee: Option<DefId>, params: &[TyId], args: &[ExprId], skip: usize) -> String {
        let names = callee.map(|d| self.param_names(d)).unwrap_or_default();
        let name_of = |i: usize| names.get(i + skip).cloned().unwrap_or_else(|| format!("#{}", i + 1));
        if args.len() > params.len() {
            return format!(" -- remove the extra argument{}", if args.len() - params.len() == 1 { "" } else { "s" });
        }
        // the given arguments' types (no expectation: they are checked again by the caller)
        let mut arg_tys = Vec::new();
        for a in args {
            let save = self.snapshot();
            let nerr = self.b.errors.len();
            let t = self.check_expr(*a, None);
            let t = self.deep(t);
            self.b.errors.truncate(nerr);
            self.rollback(save);
            arg_tys.push(t);
        }
        let mut used = vec![false; params.len()];
        let mut pi = 0;
        for at in &arg_tys {
            while pi < params.len() {
                let save = self.snapshot();
                let ok = self.unify(params[pi], *at);
                self.rollback(save);
                pi += 1;
                if ok {
                    used[pi - 1] = true;
                    break;
                }
            }
        }
        // a parameter list that the arguments do not follow in order: name them all
        let matched = used.iter().filter(|u| **u).count();
        let missing: Vec<usize> = if matched == args.len() { (0..params.len()).filter(|i| !used[*i]).collect() } else { (args.len()..params.len()).collect() };
        let list: Vec<String> = missing.iter().map(|&i| format!("`{}: {}`", name_of(i), self.ty_str(params[i]))).collect();
        match list.len() {
            0 => String::new(),
            1 => format!(" -- missing argument {}", list[0]),
            _ => format!(" -- missing arguments {}", list.join(", ")),
        }
    }

    /// The methods that exist on `t` and its autoderef targets (inherent ones, and those of
    /// every trait implemented for the type anywhere in the program): (name, the trait when it
    /// comes from one).
    fn methods_of(&mut self, t: TyId) -> Vec<(Sym, Option<DefId>)> {
        let mut out: Vec<(Sym, Option<DefId>)> = Vec::new();
        let mut cur = self.shallow(t);
        for step in 0..6u8 {
            let key = crate::tcx::ty_key(&self.tcx.tys, cur);
            if let Some(list) = self.tcx.inherent.get(&key) {
                for &imp in list {
                    for &it in &self.prog.impls[self.prog.def(imp).sub as usize].items {
                        let d = self.prog.def(it);
                        if d.kind == DefKind::AssocFn && self.tcx.fn_sig(self.prog, it).map_or(false, |sg| sg.self_kind != 0) && !out.iter().any(|x| x.0 == d.name) {
                            out.push((d.name, None));
                        }
                    }
                }
            }
            if let Some(list) = self.tcx.impls_by_key.get(&key) {
                for &imp in list {
                    let Some(&td) = self.tcx.impl_trait.get(&imp) else { continue };
                    for &it in &self.prog.traits[self.prog.def(td).sub as usize] {
                        let d = self.prog.def(it);
                        if d.kind == DefKind::AssocFn && self.tcx.fn_sig(self.prog, it).map_or(false, |sg| sg.self_kind != 0) && !out.iter().any(|x| x.0 == d.name) {
                            out.push((d.name, Some(td)));
                        }
                    }
                }
            }
            match self.deref_step(u32::MAX - 1, step, cur) {
                Some(n) => cur = self.shallow(n),
                None => break,
            }
        }
        // (deref_step records the deref calls it found: none are part of this body)
        self.b.ov_derefs.retain(|k, _| k.0 != u32::MAX - 1);
        out
    }

    /// Help for E0599: the trait to import when the method exists in a trait implemented for the
    /// type but not in scope; else the type's methods closest to the name (real names, not
    /// guesses from other types).
    fn method_help(&mut self, t: TyId, name: Sym) -> String {
        let ms = self.methods_of(t);
        let scope = self.prog.traits_in_scope(self.module);
        if let Some((_, Some(td))) = ms.iter().find(|m| m.0 == name) {
            if !scope.contains(td) {
                let tn = self.prog.syms.str(self.prog.def(*td).name);
                let paths = self.prog.import_suggestions(self.module, self.prog.def(*td).name, true);
                return match paths.first() {
                    Some(p) => format!(" -- the method is in trait `{}`, which is not in scope: `use {};`", tn, p),
                    None => format!(" -- the method is in trait `{}`, which is not in scope", tn),
                };
            }
        }
        let want = self.prog.syms.str(name).to_string();
        let mut close: Vec<(usize, String)> = ms
            .iter()
            .map(|m| self.prog.syms.str(m.0).to_string())
            .filter_map(|n| {
                let d = edit_distance(&want, &n);
                let lim = (want.len().max(n.len()) / 3).max(1);
                let sub = n.contains(want.as_str()) || want.contains(n.as_str());
                if d <= lim || (sub && n.len() > 2) {
                    Some((d, n))
                } else {
                    None
                }
            })
            .collect();
        close.sort();
        close.dedup();
        match close.len() {
            0 => String::new(),
            _ => format!(" -- methods with a similar name on this type: {}", close.iter().take(4).map(|x| format!("`{}`", x.1)).collect::<Vec<_>>().join(", ")),
        }
    }

    fn trait_fn(&self, td: DefId, name: &str) -> Option<DefId> {
        let s = self.prog.syms.get(name)?;
        for &it in &self.prog.traits[self.prog.def(td).sub as usize] {
            if self.prog.def(it).name == s {
                return Some(it);
            }
        }
        None
    }

    /// Normalizes associated-type projections whose Self is known.
    fn norm(&mut self, t: TyId) -> TyId {
        let d = self.deep(t);
        let n = self.normalize_body_type(d);
        if self.revealing && self.tcx.tys.has_opaque(n) {
            return reveal(&self.cx, self.prog, self.tcx, n);
        }
        n
    }

    /// rustc traits/project.rs:262-282: ambiguity creates a fresh type and an
    /// obligation in the same inference owner, including concrete ambiguity.
    fn normalize_body_type(&mut self, ty: TyId) -> TyId {
        use crate::types::fold::{TypeFolder, super_fold_ty};
        use crate::solve::goal::*;
        struct Normalizer<'a, 'p> { fcx: &'a mut Fcx<'p>, active: Vec<TyId> }
        impl TypeFolder for Normalizer<'_, '_> {
            fn fold_ty(&mut self, tys: &crate::types::Types, ty: TyId, depth: u32) -> TyId {
                if !tys.has_assoc(ty) { return ty; }
                if self.active.contains(&ty) || self.active.len() >= 128 { return ty; }
                self.active.push(ty);
                let ty = super_fold_ty(tys, ty, self, depth);
                let value = if let TyKind::Assoc(ad, args, _) = tys.kind(ty).clone() {
                    let cx = self.fcx.cx.body();
                    let mark = self.fcx.snapshot();
                    match crate::solve::select::project(self.fcx.tcx, &cx, self.fcx, ty) {
                        Ok((value, nested, Certainty::Yes)) if value != ty => {
                            for goal in nested { self.fcx.register_goal(goal, self.fcx.last_lo); }
                            let value = self.fcx.deep(value);
                            self.fold_ty(tys, value, depth)
                        }
                        Ok((_, _, certainty)) if tys.has_infer(ty) || !self.fcx.tcx.has_param(ty) => {
                            self.fcx.rollback(mark);
                            let mut existing = None;
                            for pending in &self.fcx.pending_goals {
                                if let Predicate::Clause(Clause::Projection(p)) = &pending.goal.predicate {
                                    if p.alias.def == ad && p.alias.args == args { if let Term::Ty(t) = p.term { existing = Some(t); break; } }
                                }
                            }
                            match existing {
                                Some(t) => self.fcx.shallow_vars(t),
                                None => {
                                    let value = self.fcx.fresh(0);
                                    let goal = Goal { param_env: crate::solve::goal::ParamEnvId(cx.typing_env.param_env.index()), predicate: Predicate::Clause(Clause::Projection(ProjectionPredicate {
                                        alias: AliasTerm { kind: AliasKind::Projection, def: ad, args }, term: Term::Ty(value),
                                    })) };
                                    self.fcx.push_pending_goal(goal, self.fcx.last_lo, certainty);
                                    value
                                }
                            }
                        }
                        _ => { self.fcx.rollback(mark); ty }
                    }
                } else { ty };
                self.active.pop();
                value
            }
        }
        let tcx = self.tcx;
        tcx.tys.fold_with(ty, &mut Normalizer { fcx: self, active: Vec::new() })
    }

    /// Generic args of impl `imp` such that its self type equals `t`.
    fn match_impl_args(&mut self, imp: DefId, t: TyId) -> Vec<TyId> {
        let n = self.tcx.impl_generics.get(&imp).map_or(0, |e| e.names.len());
        let mut args = Vec::new();
        for _ in 0..n {
            args.push(self.fresh(0));
        }
        if let Some(&st) = self.tcx.impl_self.get(&imp) {
            let inst = self.tcx.tys.subst_for_inference(st, &args);
            self.unify(inst, t);
        }
        // the impl's where-clauses may fix args the caller only partly knows (an integer
        // literal B in `Vec<u32> == vec![1, 2]` through `A: PartialEq<B>`): retried with the
        // pending bounds once the trait args are unified
        if self.tcx.impl_trait_bounds.contains_key(&imp) {
            self.apply_impl_predicates(imp, &args);
        }
        args
    }

    fn explicit_args(&mut self, path: &Path) -> Option<Vec<TyId>> {
        let n = path.segs.len();
        self.seg_args(path, n - 1)
    }

    fn seg_args(&mut self, path: &Path, i: usize) -> Option<Vec<TyId>> {
        let seg = self.ast().segs(path.segs).get(i)?;
        let a = self.ast().gargs(seg.args)?;
        let mut out = Vec::new();
        if let GenericArgs::Angle(v) = a {
            for g in self.ast().list(*v) {
                if let Some(lt) = self.generic_arg(g) {
                    out.push(lt);
                }
            }
        }
        Some(out)
    }

    /// A type or const generic argument inside the body (instance args substituted).
    fn generic_arg(&mut self, g: &GenericArg) -> Option<TyId> {
        let prog = self.prog;
        let env = self.env.clone();
        let args = self.inst_args.clone();
        match g {
            GenericArg::Type(t) => {
                if let Ty::Infer = prog.files[self.file as usize].ast.ty(*t) {
                    return Some(self.fresh(0));
                }
                let lt = self.tcx.type_or_const_arg(&self.cx, prog, self.file, self.module, &env, *t);
                let lt = self.tcx.tys.subst(lt, &args);
                Some(self.replace_errors_with_vars(lt, *t))
            }
            GenericArg::Const(e) => {
                let lt = self.tcx.const_arg(&self.cx, prog, self.file, self.module, &env, *e);
                Some(self.tcx.tys.subst(lt, &args))
            }
            _ => None,
        }
    }

    /// Lowers a syntactic type inside the body (generic params map to the instance args).
    pub fn lower_ty(&mut self, t: crate::ast::TyId) -> TyId {
        let prog = self.prog;
        let env = self.env.clone();
        if let Ty::Infer = prog.files[self.file as usize].ast.ty(t) {
            return self.fresh(0);
        }
        if let Some(x) = self.lower_alias_with_infer(t, 0) {
            return x;
        }
        // (errors of the annotation itself belong to this body: `let m: HashMap<..>` without the
        // import is E0412 here, not a later "type not fully known")
        let (lt, errs) = self.tcx.with_errors(&self.cx, || self.tcx.lower_ty(&self.cx, prog, self.file, self.module, &env, t));
        // (only a missing name: other lowering errors -- an array length the lowering cannot
        // evaluate yet -- are recovered from the initializer, as before)
        for e in errs {
            if e.contains(": E0412: ") && !self.b.errors.contains(&e) {
                self.b.errors.push(e);
            }
        }
        let args = self.inst_args.clone();
        let lt = self.tcx.tys.subst(lt, &args);
        type_dependencies(self.tcx, lt, &mut self.b.dependencies);
        self.replace_errors_with_vars(lt, t)
    }

    /// A type alias applied to `_` (`P<_>` with `type P<T> = (T, T)`): one variable for the
    /// argument, used wherever the alias uses the param (lowering `_` to Error and replacing
    /// each Error by its own variable would split it). Also inside tuples / references.
    fn lower_alias_with_infer(&mut self, t: crate::ast::TyId, depth: u32) -> Option<TyId> {
        if depth > 8 {
            return None;
        }
        let prog = self.prog;
        let f = &prog.files[self.file as usize];
        fn has_infer_arg(ast: &crate::ast::Ast, t: crate::ast::TyId, depth: u32) -> bool {
            if depth > 8 {
                return false;
            }
            match ast.ty(t) {
                Ty::Path(p) => p.qself.is_none() && p.segs.len() == 1 && matches!(ast.gargs(ast.segs(p.segs)[0].args), Some(GenericArgs::Angle(v)) if ast.list(*v).iter().any(|g| matches!(g, GenericArg::Type(x) if matches!(ast.ty(*x), Ty::Infer)))),
                Ty::Tuple(v) => ast.list(*v).iter().any(|x| has_infer_arg(ast, *x, depth + 1)),
                Ty::Ref(_, _, x) | Ty::Paren(x) => has_infer_arg(ast, *x, depth + 1),
                _ => false,
            }
        }
        if !has_infer_arg(&f.ast, t, depth) {
            return None;
        }
        match f.ast.ty(t).clone() {
            Ty::Tuple(v) => {
                let mut out = Vec::new();
                for x in f.ast.list(v).iter().copied() {
                    let y = match self.lower_alias_with_infer(x, depth + 1) {
                        Some(y) => y,
                        None => self.lower_ty(x),
                    };
                    out.push(y);
                }
                Some(self.tcx.tys.intern(TyKind::Tuple(out)))
            }
            Ty::Ref(lt, m, x) => {
                let region = self.env.regions.resolve(&self.tcx.tys, prog, self.file, lt);
                let y = match self.lower_alias_with_infer(x, depth + 1) {
                    Some(y) => y,
                    None => self.lower_ty(x),
                };
                Some(self.tcx.tys.intern(TyKind::Ref(m, y, region)))
            }
            Ty::Paren(x) => self.lower_alias_with_infer(x, depth + 1),
            Ty::Path(p) => {
                let d = self.tcx.resolve_type_path_def(prog, self.file, self.module, &p)?;
                if prog.def(d).kind != DefKind::TypeAlias {
                    return None;
                }
                let pd = prog.def(d);
                let pf = &prog.files[pd.file as usize];
                let (generics, body) = match &pf.ast.item(pd.item).kind {
                    ItemKind::TypeAlias { generics, ty: Some(b), .. } => (generics.clone(), *b),
                    _ => return None,
                };
                let ntp = pf.ast.list(generics.params).iter().filter(|g| matches!(g.kind, GenericParamKind::Type(..))).count();
                if pf.ast.list(generics.params).iter().any(|g| matches!(g.kind, GenericParamKind::Const(..))) {
                    return None;
                }
                let written: Vec<crate::ast::TyId> = match f.ast.gargs(f.ast.segs(p.segs)[0].args) {
                    Some(GenericArgs::Angle(v)) => f.ast.list(*v).iter().filter_map(|g| match g {
                        GenericArg::Type(x) => Some(*x),
                        _ => None,
                    }).collect(),
                    _ => Vec::new(),
                };
                if written.len() != ntp {
                    return None;
                }
                let args: Vec<TyId> = written.iter().map(|x| self.lower_ty(*x)).collect();
                let mut aenv = self.tcx.item_env(prog, d);
                aenv.regions.enabled = self.env.regions.enabled;
                let bt = self.tcx.lower_ty(&self.cx, prog, pd.file, pd.scope, &aenv, body);
                if self.tcx.tys.has_error(bt) {
                    return None;
                }
                let rs = self.tcx.lower_region_args(prog, self.file, self.module, &self.env, &p);
                let bt = self.tcx.subst_decl_regions(bt, &aenv, rs);
                Some(self.tcx.tys.subst(bt, &args))
            }
            _ => None,
        }
    }

    /// `Vec<_>`: the `_` lowered to Error becomes a fresh variable.
    fn replace_errors_with_vars(&mut self, t: TyId, _ast: crate::ast::TyId) -> TyId {
        let k = self.tcx.tys.kind(t).clone();
        match k {
            TyKind::Error => self.fresh(0),
            TyKind::Adt(d, v, regions) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.replace_errors_with_vars(x, _ast));
                }
                self.tcx.tys.intern(TyKind::Adt(d, n, regions))
            }
            TyKind::Ref(m, x, region) => {
                let x = self.replace_errors_with_vars(x, _ast);
                self.tcx.tys.intern(TyKind::Ref(m, x, region))
            }
            TyKind::Tuple(v) => {
                let mut n = Vec::new();
                for x in v {
                    n.push(self.replace_errors_with_vars(x, _ast));
                }
                self.tcx.tys.intern(TyKind::Tuple(n))
            }
            TyKind::Array(x, l) => {
                let x = self.replace_errors_with_vars(x, _ast);
                // `[T; _]`: a length variable
                if crate::types::len_ty(l) == Some(self.tcx.tys.error) {
                    let v = self.fresh(0);
                    return self.tcx.tys.mk_array(x, v);
                }
                self.tcx.tys.intern(TyKind::Array(x, l))
            }
            TyKind::Slice(x) => {
                let x = self.replace_errors_with_vars(x, _ast);
                self.tcx.tys.intern(TyKind::Slice(x))
            }
            // `*const _` (`0 as *const _`)
            TyKind::Ptr(m, x) => {
                let x = self.replace_errors_with_vars(x, _ast);
                self.tcx.tys.intern(TyKind::Ptr(m, x))
            }
            // `fn(_) -> _`, `dyn Fn(isize) -> _`, `dyn Iterator<Item = _>`
            TyKind::FnPtr(ps, r, c, bound) => {
                let ps: Vec<TyId> = ps.into_iter().map(|x| self.replace_errors_with_vars(x, _ast)).collect();
                let r = self.replace_errors_with_vars(r, _ast);
                self.tcx.tys.intern(TyKind::FnPtr(ps, r, c, bound))
            }
            TyKind::Dyn(d, v, bs, regions, region, bound, autos) => {
                let v: Vec<TyId> = v.into_iter().map(|x| self.replace_errors_with_vars(x, _ast)).collect();
                let bs = bs.into_iter().map(|(a, x, n)| (a, self.replace_errors_with_vars(x, _ast), n)).collect();
                self.tcx.tys.intern(TyKind::Dyn(d, v.into(), bs, regions, region, bound, autos.clone()))
            }
            _ => t,
        }
    }

    /// Type named by the first `n` segments of a path (for `Type::item`).
    fn type_of_prefix(&mut self, path: &Path, n: usize) -> Option<TyId> {
        let prog = self.prog;
        if n == 1 && self.ast().segs(path.segs)[0].kind == SegKind::SelfType {
            let st = self.env.self_ty?;
            let args = self.inst_args.clone();
            return Some(self.tcx.tys.subst_for_inference(st, &args));
        }
        // generic param `T::item`
        if n == 1 {
            let s = self.sym(self.ast().segs(path.segs)[0].name);
            for (i, nm) in self.env.names.iter().enumerate() {
                if *nm == s && i < self.inst_args.len() {
                    return Some(self.inst_args[i]);
                }
            }
        }
        let sub = Path { qself: QSelfId::NONE, segs: path.segs.prefix(n), lo: path.lo };
        // `Self::Bits::EMPTY` / `T::Assoc::f`: the prefix is an associated-type projection,
        // lowered as a type path and normalized for this instance
        if n >= 2 && (self.ast().segs(path.segs)[0].kind == SegKind::SelfType || self.env.names.contains(&self.sym(self.ast().segs(path.segs)[0].name))) {
            let env = self.env.clone();
            // (an expression path may elide a generic associated type's lifetimes: rustc
            // reports E0107 only in types)
            let (t, errs) = self.tcx.with_errors(&self.cx, || self.tcx.lower_path_ty(&self.cx, prog, self.file, self.module, &env, &sub));
            for e in errs {
                if !e.contains("E0107: missing generics for associated type") {
                    self.tcx.reraise_error(&self.cx, e);
                }
            }
            let args = self.inst_args.clone();
            let t = self.tcx.tys.subst_for_inference(t, &args);
            let t = self.tcx.normalize_for_inference(&self.cx, prog, t);
            // (a projection that stays one is rigid in a generic body: `A::Mem::default()`
            // resolves through the associated type's bounds)
            if !matches!(self.tcx.tys.kind(t), TyKind::Error) && (!matches!(self.tcx.tys.kind(t), TyKind::Assoc(..)) || !self.tcx.tys.has_infer(t)) {
                return Some(t);
            }
        }
        let d = self.tcx.resolve_type_path_def(prog, self.file, self.module, &sub);
        // a primitive type's name that resolves to a module (or nothing): the primitive type
        // (rustc_resolve late.rs resolve_qpath fallback)
        if n == 1 && !path.global() && d.map_or(true, |d| prog.def(d).kind == DefKind::Mod) {
            let s = self.sym(self.ast().segs(path.segs)[0].name);
            if let Some((_, p)) = crate::program::PRIMS.iter().find(|(nm, _)| prog.syms.get(nm) == Some(s)) {
                return Some(self.tcx.tys.prim(*p));
            }
        }
        // relaxed imports: `HashMap::new()` with `HashMap` unique in the program
        let d = match d {
            Some(d) => d,
            None if n == 1 && !path.global() => prog.relaxed_import(self.module, self.sym(self.ast().segs(path.segs)[0].name), true, self.file, path.lo)?,
            None => return None,
        };
        let args = self.seg_args(path, n - 1);
        match prog.def(d).kind {
            DefKind::Prim(p) => Some(self.tcx.tys.prim(p)),
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                let ng = self.tcx.adts.get(&d).map_or(0, |a| a.n_generics);
                let mut a = args.unwrap_or_default();
                while a.len() < ng as usize {
                    a.push(self.fresh(0));
                }
                Some(self.tcx.tys.intern(TyKind::Adt(d, a, crate::types::RegionArgsId::EMPTY)))
            }
            DefKind::TypeAlias => {
                let t = self.tcx.alias_ty(&self.cx, prog, d);
                let mut a = args.unwrap_or_default();
                // `Alias::f` without generic args: the alias's parameters are inferred like a
                // struct's (`FxHashSet::default()`)
                let need = self.tcx.item_env(prog, d).names.len();
                while a.len() < need {
                    a.push(self.fresh(0));
                }
                Some(self.tcx.tys.subst_for_inference(t, &a))
            }
            _ => None,
        }
    }

    fn note_capture(&mut self, li: u32, _key: u32) {
        // a local declared outside a closure is captured by it (and by every closure between
        // it and the local's scope, so nested closures can reach it)
        for k in (0..self.closure_depth.len()).rev() {
            let (ce, depth) = self.closure_depth[k];
            let mut declared_inside = false;
            for i in depth..self.scopes.len() {
                if self.scopes[i].1 == li {
                    declared_inside = true;
                }
            }
            if declared_inside {
                break;
            }
            let caps = self.b.closure_locals.entry(ce).or_default();
            if !caps.contains(&li) {
                caps.push(li);
            }
        }
    }

    // ------------------------------------------------------------ blocks

    fn check_block(&mut self, b: BlockId, expected: Option<TyId>) -> TyId {
        let ast = self.ast();
        let blk = ast.block(b);
        let saved_scope = self.scopes.len();
        let saved_module = self.module;
        if let Some(&m) = self.prog.block_mods.get(&(self.file, b.0)) {
            self.module = m;
        }
        let mut result = self.tcx.tys.unit;
        let n = blk.stmts.len();
        let mut diverged = false;
        for (i, s) in self.ast().list(blk.stmts).iter().enumerate() {
            if i > 0 {
                self.retry_goals(false);
            }
            match s {
                Stmt::Let { attrs, pat, ty, init, else_ } => {
                    if !self.active(*attrs) {
                        continue;
                    }
                    // the annotation normalized in this body's inference context (rustc
                    // gather_locals: FnCtxt::lower_ty -> LoweredTy::from_raw normalizes):
                    // `&<(Wrap<?0>,) as Indirect>::Out` is `&?1` with that projection pending
                    let decl = match ty {
                        Some(t) => {
                            let d = self.lower_ty(*t);
                            Some(if self.tcx.tys.has_assoc(d) { self.norm(d) } else { d })
                        }
                        None => None,
                    };
                    let t = match init {
                        Some(e) => {
                            let it = self.check_expr(*e, decl);
                            match decl {
                                Some(d) => {
                                    self.coerce_or_unify(it, d, Some(*e), ast.expr(*e).lo);
                                    d
                                }
                                None => it,
                            }
                        }
                        None => match decl {
                            Some(d) => d,
                            None => self.fresh(0),
                        },
                    };
                    if self.diverges {
                        diverged = true;
                    }
                    if let Some(eb) = else_ {
                        let save = self.diverges;
                        self.check_block(*eb, None);
                        self.diverges = save;
                    }
                    self.check_pat(*pat, t);
                }
                // stripped at load (program::strip_cfg_stmts)
                Stmt::Item(_) | Stmt::Attrs(..) => {}
                Stmt::Expr(e, semi) => {
                    let is_tail = i == n - 1 && !*semi;
                    let t = self.check_expr(*e, if is_tail { expected } else { None });
                    if self.diverges {
                        diverged = true;
                    }
                    if is_tail {
                        result = t;
                        // the tail is a coercion site for the block's expected type
                        if let Some(x) = expected {
                            let (st, sx) = (self.shallow(t), self.shallow(x));
                            // an unsized expectation is only a hint (rustc Expectation::rvalue_hint,
                            // ExpectRvalueLikeUnsized): `RefCell::new({ .. closure })` for a
                            // `RefCell<dyn FnMut()>` keeps the closure type
                            let unsized_x = self.is_unsized_ty(sx);
                            if st == sx && matches!(self.tcx.tys.kind(st), TyKind::Ref(true, _, _)) {
                                self.b.reborrows.insert(e.0, true);
                            }
                            if !unsized_x && st != sx && !matches!(self.tcx.tys.kind(st), TyKind::Never | TyKind::Infer(_)) && !matches!(self.tcx.tys.kind(sx), TyKind::Infer(_)) {
                                // the expectation may be a mere hint (an if's other branch):
                                // when no coercion applies the block keeps its own type and the
                                // consumer (let, return, CoerceMany) decides
                                if self.try_coerce(t, x, Some(*e)) {
                                    result = x;
                                }
                            }
                        }
                    } else if !*semi {
                        // block-like statement without `;` must be unit (or diverge)
                        let st = self.shallow(t);
                        if st != self.tcx.tys.unit && st != self.tcx.tys.never {
                            let unit = self.tcx.tys.unit;
                            self.unify(st, unit);
                        }
                    }
                }
                Stmt::Empty => {}
            }
        }
        self.scopes.truncate(saved_scope);
        self.module = saved_module;
        if diverged {
            self.diverges = true;
            let tail_is_expr = n > 0 && matches!(self.ast().list(blk.stmts)[n - 1], Stmt::Expr(_, false));
            if !tail_is_expr {
                return self.tcx.tys.never;
            }
        }
        result
    }

    fn active(&self, attrs: List<Attr>) -> bool {
        if attrs.is_empty() {
            return true;
        }
        let krate = self.prog.file_crate[self.file as usize];
        crate::cfg::active(self.prog.src(self.file), self.prog.files[self.file as usize].ast.list(attrs), &self.prog.crates[krate as usize].cfg)
    }

    // ------------------------------------------------------------ expressions

    pub fn check_expr(&mut self, e: ExprId, expected: Option<TyId>) -> TyId {
        crate::preempt::point();
        let _why = crate::why::enabled().then(|| crate::why::enter(self.prog.why_expr(
            self.file, self.prog.files[self.file as usize].ast.expr(e).lo, self.b.def, "typeck-expression")));
        let save_div = self.diverges;
        self.diverges = false;
        let t = self.check_expr_inner(e, expected);
        let ts = self.shallow(t);
        if ts == self.tcx.tys.never {
            self.diverges = true;
        }
        self.diverges = self.diverges || save_div;
        self.set_ty(e, t);
        t
    }

    fn check_expr_inner(&mut self, e: ExprId, expected: Option<TyId>) -> TyId {
        let ast = self.ast();
        let ex = ast.expr(e);
        let lo = ex.lo;
        self.last_lo = lo;
        let unit = self.tcx.tys.unit;
        let error = self.tcx.tys.error;
        match &ex.kind {
            ExprKind::Lit(k) => self.check_lit(e, *k, expected),
            ExprKind::Path(path) => {
                let (r, t) = self.resolve_value_path(path, e.0, false);
                self.b.res.insert(e.0, r);
                t
            }
            ExprKind::Paren(x) => self.check_expr(*x, expected),
            ExprKind::Unary(op, x) => match op {
                // `-&x` / `!&b`: std's `impl Neg for &i64`, `impl Not for &bool` (operand derefs)
                UnOp::Neg => {
                    let t = self.check_expr(*x, expected);
                    let t = self.peel_prim_refs(t);
                    let st = self.shallow(t);
                    if let Some(r) = self.check_unop_trait(e, st, "Neg", "neg") {
                        return r;
                    }
                    if !self.is_numeric(st) {
                        let s = self.ty_str(st);
                        self.err(lo, format!("cannot negate `{}`", s));
                    }
                    t
                }
                UnOp::Not => {
                    let t = self.check_expr(*x, expected);
                    let t = self.peel_prim_refs(t);
                    let st = self.shallow(t);
                    if let Some(r) = self.check_unop_trait(e, st, "Not", "not") {
                        return r;
                    }
                    t
                }
                UnOp::Deref => {
                    let t = self.check_expr(*x, None);
                    match self.deref_step(e.0, 0, t) {
                        Some(i) => i,
                        None => {
                            let s = self.ty_str(t);
                            self.err(lo, format!("cannot deref `{}`", s));
                            error
                        }
                    }
                }
            },
            ExprKind::Binary(op, a, b) => self.check_binary(e, *op, *a, *b, expected, lo),
            ExprKind::Assign(a, b) => {
                if crate::lit::is_assignee_pattern(self.ast(), *a) {
                    // destructuring assignment: the right side's type is matched by the
                    // assignee like a pattern (rustc lowers it to `let` + assignments)
                    let tb = self.check_expr(*b, None);
                    self.check_assignee(*a, tb, lo);
                    return unit;
                }
                let ta = self.check_expr(*a, None);
                let tb = self.check_expr(*b, Some(ta));
                self.coerce_or_unify(tb, ta, Some(*b), lo);
                unit
            }
            ExprKind::AssignOp(op, a, b) => {
                let ta = self.check_expr(*a, None);
                let sa = self.shallow(ta);
                if matches!(self.tcx.tys.kind(sa), TyKind::Adt(..) | TyKind::Ref(..) | TyKind::Tuple(..) | TyKind::Array(..)) {
                    // `a op= b` on a non-primitive: core::ops::<Op>Assign
                    self.cur_binop = e.0;
                    self.check_op_trait(*op, sa, *b, lo, true);
                    return unit;
                }
                let is_shift = matches!(op, BinOp::Shl | BinOp::Shr);
                let tb = self.check_expr(*b, if is_shift { None } else { Some(ta) });
                // `sum += &i` with i still open and sum a literal: only core's primitive
                // `OpAssign<&T> for T` impls take a reference here, so the referent is sum's type
                let tb = match self.tcx.tys.kind(self.shallow(tb)).clone() {
                    TyKind::Ref(false, inner, _) if !is_shift && self.is_literal_var(sa) && matches!(self.tcx.tys.kind(self.shallow(inner)), TyKind::Infer(_)) => inner,
                    _ => tb,
                };
                let tb = self.peel_prim_refs(tb);
                if !is_shift {
                    self.coerce_or_unify(tb, ta, Some(*b), lo);
                }
                unit
            }
            ExprKind::Cast(x, t) => {
                let target = self.lower_ty(*t);
                let st = self.shallow(target);
                let xt = self.check_expr(*x, None);
                // `b as Box<dyn Tr>` / `&x as &dyn Tr`: an unsizing coercion
                let sx = self.shallow(xt);
                let (kx, kt) = (self.tcx.tys.kind(sx).clone(), self.tcx.tys.kind(st).clone());
                if let Some((src, dy)) = self.dyn_coercion(&kx, &kt) {
                    self.b.coerce.insert(x.0, Coerce::ToDyn(src, dy));
                } else if let Some((sd, dd)) = self.dyn_upcast(&kx, &kt) {
                    self.b.coerce.insert(x.0, Coerce::Upcast(sd, dd));
                } else if self.unsize_coercion(&kx, &kt) {
                    // rustc check_cast: a cast that is a coercion is one (`&mut [1] as *mut [i32]`)
                    self.b.coerce.insert(x.0, Coerce::Unsize);
                } else if let (TyKind::Ref(..) | TyKind::Ptr(..), TyKind::Ptr(..), true) = (&kx, &kt, {
                    // an open source pointee against a known target pointee (`&data as *const
                    // *const ()` with data: *const ?T): the cast is the coercion, T = ()
                    let tp = match &kt { TyKind::Ptr(_, p) => self.shallow(*p), _ => st };
                    let sp = match &kx { TyKind::Ref(_, p, _) | TyKind::Ptr(_, p) => *p, _ => sx };
                    !matches!(self.tcx.tys.kind(tp), TyKind::Infer(_)) && self.has_open_infer(sp)
                }) {
                    // Check inner casts first: in `r as *mut _ as *mut ()`,
                    // the reference coercion determines `_`, not the outer cast.
                    self.deferred_casts.push((*x, xt, target));
                } else if matches!((&kx, &kt), (TyKind::Ref(..) | TyKind::Ptr(..), TyKind::Ptr(_, _))) && {
                    let tp = match &kt { TyKind::Ptr(_, p) => *p, _ => st };
                    let tp = self.shallow(tp);
                    matches!(self.tcx.tys.kind(tp), TyKind::Infer(_))
                } {
                    // `p as *mut _`: decided once the target pointee is known (an unsizing cast
                    // when it becomes a slice)
                    self.deferred_casts.push((*x, xt, target));
                } else if matches!(kt, TyKind::Infer(_)) {
                    // `v as _`: the target is known only from later uses (a closure's return
                    // through `bool::then`, a `let` annotation); rustc checks every cast at the
                    // end of typeck (check_casts), where `Arc::new(v) as _` into
                    // `Arc<dyn Send + Sync>` is the unsizing coercion
                    self.deferred_casts.push((*x, xt, target));
                } else if matches!(kt, TyKind::FnPtr(..)) && matches!(kx, TyKind::FnDef(..) | TyKind::Closure(..) | TyKind::FnPtr(..)) {
                    self.coerce_or_unify(xt, target, Some(*x), lo);
                } else if matches!(kt, TyKind::Adt(..) | TyKind::Tuple(_) | TyKind::Array(..)) {
                    // no primitive cast has these targets: only a coercion (a trivial cast `Some(4u32)
                    // as Option<u32>`, `(1, 2) as (u32, u32)` types its literals)
                    self.coerce_or_unify(xt, target, Some(*x), lo);
                } else if let (TyKind::Ref(m1, a, _), TyKind::Ref(m2, bt, _)) = (&kx, &kt) {
                    // a cast is first a coercion when one applies (rustc cast.rs
                    // try_coercion_cast): `&s as &str` is a deref coercion of &String
                    let (sa, sb) = (self.shallow(*a), self.shallow(*bt));
                    if (*m1 || !*m2) && sa != sb && !matches!(self.tcx.tys.kind(sb), TyKind::Infer(_) | TyKind::Dyn(..)) {
                        if let Some(n) = self.deref_coercion(*x, sa, sb) {
                            self.b.coerce.insert(x.0, Coerce::DerefRef(n));
                        }
                    }
                }
                self.record_cast_borrow(*x, xt, target);
                target
            }
            ExprKind::Block(b, label) => {
                if label.is_some() {
                    let l = label.map(|x| self.sym_lifetime(x));
                    self.loops.push(Loop { label: l, break_ty: expected, is_loop: true });
                    let t = self.check_block(*b, expected);
                    let lp = self.loops.pop().unwrap();
                    if let Some(bt) = lp.break_ty {
                        // a body that diverges (`'b: { break 'b v; }`) has the breaks' type
                        if self.shallow(t) == self.tcx.tys.never {
                            self.diverges = false;
                            return bt;
                        }
                        self.unify(bt, t);
                    }
                    self.diverges = false;
                    return t;
                }
                self.check_block(*b, expected)
            }
            ExprKind::Unsafe(b) => self.check_block(*b, expected),
            ExprKind::ConstBlock(b) => {
                let t = self.check_block(*b, expected);
                self.b.inline_const_types.insert(e.0, t);
                t
            },
            ExprKind::If(c, then, els) => {
                let bool_ = self.tcx.tys.bool_;
                // `if let` bindings live in the condition and the then-block only (F23)
                let saved = self.scopes.len();
                let ct = self.check_expr(*c, Some(bool_));
                self.coerce_or_unify(ct, bool_, None, lo);
                let tt = self.check_block(*then, expected);
                let then_div = self.diverges;
                self.scopes.truncate(saved);
                self.diverges = false;
                match els {
                    None => {
                        self.diverges = false;
                        if !then_div {
                            let s = self.shallow(tt);
                            if s != unit && s != self.tcx.tys.never {
                                self.unify(s, unit);
                            }
                        }
                        unit
                    }
                    Some(x) => {
                        // a diverging then-branch (`!`) is no hint for the else branch (F26)
                        let stt = self.shallow(tt);
                        // (a fn item / closure type is no hint: branches meet at a fn pointer)
                        let fnish = matches!(self.tcx.tys.kind(stt), TyKind::FnDef(..) | TyKind::Closure(..));
                        let hint = if stt == self.tcx.tys.never || fnish { expected } else { expected.or(Some(tt)) };
                        let et = self.check_expr(*x, hint);
                        let else_div = self.diverges;
                        self.diverges = then_div && else_div;
                        let ts = self.shallow(tt);
                        let es = self.shallow(et);
                        if ts == self.tcx.tys.never {
                            return et;
                        }
                        if es == self.tcx.tys.never {
                            return tt;
                        }
                        // the then-branch's value is its block's tail expression
                        let tail = match self.ast().stmts(*then).last() {
                            Some(crate::ast::Stmt::Expr(t2, false)) => vec![*t2],
                            _ => Vec::new(),
                        };
                        self.coerce_many(&tail, tt, *x, et, lo)
                    }
                }
            }
            ExprKind::Let(p, x) => {
                let t = self.check_expr(*x, None);
                // `if let true = return`: as a match scrutinee (rustc types the initializer
                // against a fresh variable, check_decl_initializer)
                let t = self.never_scrutinee(*x, t);
                self.check_pat(*p, t);
                self.tcx.tys.bool_
            }
            ExprKind::Match(x, arms) => {
                let mut st = self.check_expr(*x, None);
                if !arms.is_empty() {
                    st = self.never_scrutinee(*x, st);
                }
                // arms coerce to a known expected type (rustc _match.rs check_match:
                // CoerceMany starts from `ExpectHasType(ety)` unless it is `()`)
                let target = match expected {
                    Some(et) => {
                        let s = self.shallow(et);
                        if matches!(self.tcx.tys.kind(s), TyKind::Infer(_) | TyKind::Error) || s == unit || self.is_unsized_ty(s) {
                            None
                        } else {
                            Some(et)
                        }
                    }
                    None => None,
                };
                let mut result: Option<TyId> = target;
                let mut any_value = false;
                let mut all_div = !arms.is_empty();
                let mut seen: Vec<ExprId> = Vec::new();
                for arm in self.ast().list(*arms) {
                    if !self.active(arm.attrs) {
                        continue;
                    }
                    let saved = self.scopes.len();
                    self.check_pat(arm.pat, st);
                    if let Some(g) = arm.guard {
                        let bool_ = self.tcx.tys.bool_;
                        self.check_expr(g, Some(bool_));
                    }
                    self.diverges = false;
                    // (an earlier arm's fn item / closure type is no hint: arms meet at a fn pointer)
                    let rhint = match result {
                        Some(r) => {
                            let sr = self.shallow(r);
                            if matches!(self.tcx.tys.kind(sr), TyKind::FnDef(..) | TyKind::Closure(..)) { None } else { Some(r) }
                        }
                        None => None,
                    };
                    let bt = self.check_expr(arm.body, expected.or(rhint));
                    let div = self.diverges;
                    all_div = all_div && div;
                    let bs = self.shallow(bt);
                    if bs != self.tcx.tys.never {
                        any_value = true;
                        match result {
                            None => result = Some(bt),
                            Some(r) => {
                                let prev = seen.clone();
                                result = Some(self.coerce_many(&prev, r, arm.body, bt, ast.expr(arm.body).lo));
                            }
                        }
                        seen.push(arm.body);
                    }
                    self.scopes.truncate(saved);
                }
                self.diverges = all_div;
                match result {
                    Some(r) if any_value => r,
                    _ => self.tcx.tys.never,
                }
            }
            ExprKind::While(c, b, label) => {
                let bool_ = self.tcx.tys.bool_;
                let saved = self.scopes.len();
                let l = label.map(|x| self.sym_lifetime(x));
                // rustc_ast_lowering puts both the condition and body in the loop scope.
                self.loops.push(Loop { label: l, break_ty: None, is_loop: false });
                let was_in_condition = std::mem::replace(&mut self.in_loop_condition, true);
                self.check_expr(*c, Some(bool_));
                self.in_loop_condition = false;
                // a loop body has type `()`: an open tail type is unit (`for _ in r { zeroed() }`)
                let bt = self.check_block(*b, Some(unit));
                let sb = self.shallow(bt);
                if matches!(self.tcx.tys.kind(sb), TyKind::Infer(_)) {
                    self.unify(sb, unit);
                }
                self.loops.pop();
                self.in_loop_condition = was_in_condition;
                self.scopes.truncate(saved);
                self.diverges = false;
                unit
            }
            ExprKind::Loop(b, label) => {
                let l = label.map(|x| self.sym_lifetime(x));
                self.loops.push(Loop { label: l, break_ty: None, is_loop: true });
                let was_in_condition = std::mem::replace(&mut self.in_loop_condition, false);
                // a loop body has type `()`: an open tail type is unit (`for _ in r { zeroed() }`)
                let bt = self.check_block(*b, Some(unit));
                let sb = self.shallow(bt);
                if matches!(self.tcx.tys.kind(sb), TyKind::Infer(_)) {
                    self.unify(sb, unit);
                }
                let lp = self.loops.pop().unwrap();
                self.in_loop_condition = was_in_condition;
                match lp.break_ty {
                    Some(t) => {
                        self.diverges = false;
                        t
                    }
                    None => {
                        // a loop without `break` never yields
                        if self.loop_has_break(*b, label.map(|x| self.sym_lifetime(x))) {
                            self.diverges = false;
                            unit
                        } else {
                            self.diverges = true;
                            self.tcx.tys.never
                        }
                    }
                }
            }
            ExprKind::For(p, it, b, label) => {
                let saved = self.scopes.len();
                let item = self.check_for_iter(*it, lo);
                self.check_pat(*p, item);
                let l = label.map(|x| self.sym_lifetime(x));
                self.loops.push(Loop { label: l, break_ty: None, is_loop: false });
                let was_in_condition = std::mem::replace(&mut self.in_loop_condition, false);
                // a loop body has type `()`: an open tail type is unit (`for _ in r { zeroed() }`)
                let bt = self.check_block(*b, Some(unit));
                let sb = self.shallow(bt);
                if matches!(self.tcx.tys.kind(sb), TyKind::Infer(_)) {
                    self.unify(sb, unit);
                }
                self.loops.pop();
                self.in_loop_condition = was_in_condition;
                self.scopes.truncate(saved);
                self.diverges = false;
                unit
            }
            ExprKind::Break(label, x) => {
                if self.in_loop_condition && label.is_none() {
                    self.err(lo, "unlabeled `break` in the condition of a `while` loop".to_string());
                }
                let l = label.map(|x| self.sym_lifetime(x));
                let t = match x {
                    Some(v) => {
                        let target = self.loop_index(l);
                        let exp = match target {
                            Some(i) => self.loops[i].break_ty,
                            None => None,
                        };
                        let vt = self.check_expr(*v, exp);
                        Some(vt)
                    }
                    None => None,
                };
                if let Some(i) = self.loop_index(l) {
                    let bt = match t {
                        Some(v) => v,
                        None => unit,
                    };
                    if self.loops[i].is_loop {
                        match self.loops[i].break_ty {
                            Some(prev) => {
                                self.unify(prev, bt);
                            }
                            None => self.loops[i].break_ty = Some(bt),
                        }
                    }
                } else {
                    self.err(lo, "`break` outside of a loop".to_string());
                }
                self.tcx.tys.never
            }
            ExprKind::Continue(label) => {
                if self.in_loop_condition && label.is_none() {
                    self.err(lo, "unlabeled `continue` in the condition of a `while` loop".to_string());
                }
                self.tcx.tys.never
            }
            ExprKind::Return(x) => {
                let rt = *self.ret_stack.last().unwrap();
                match x {
                    Some(v) => {
                        let t = self.check_expr(*v, Some(rt));
                        self.coerce_or_unify(t, rt, Some(*v), lo);
                    }
                    None => {
                        self.unify(rt, unit);
                    }
                }
                self.tcx.tys.never
            }
            ExprKind::Tuple(v) => {
                let exp_elems = match expected {
                    Some(t) => {
                        let s = self.shallow_with_regions(t);
                        match self.tcx.tys.kind(s).clone() {
                            TyKind::Tuple(x) if x.len() == v.len() => Some(x),
                            _ => None,
                        }
                    }
                    None => None,
                };
                let mut ts = Vec::new();
                for (i, x) in self.ast().list(*v).iter().enumerate() {
                    let ex = match &exp_elems {
                        Some(es) => Some(es[i]),
                        None => None,
                    };
                    let t = self.check_expr(*x, ex);
                    if let Some(et) = ex {
                        self.coerce_or_unify(t, et, Some(*x), lo);
                        ts.push(et);
                    } else {
                        ts.push(t);
                    }
                }
                self.tcx.tys.intern(TyKind::Tuple(ts))
            }
            ExprKind::Array(v) => {
                let elem_exp = match expected {
                    Some(t) => {
                        let s = self.shallow_with_regions(t);
                        match self.tcx.tys.kind(s).clone() {
                            TyKind::Array(e, _) | TyKind::Slice(e) => Some(e),
                            _ => None,
                        }
                    }
                    None => None,
                };
                // an expected element type that is still open is no constraint yet
                let elem_open = elem_exp.map_or(false, |t| {
                    let st = self.shallow(t);
                    matches!(self.tcx.tys.kind(st), TyKind::Infer(_)) && !self.is_literal_var(st)
                });
                let elem = match elem_exp.filter(|_| !elem_open) {
                    Some(t) => t,
                    None => {
                        // no expected element type: the elements meet like match arms
                        // (rustc CoerceMany: `[foo, bar]` of two fn items is `[fn(); 2]`)
                        let mut res: Option<TyId> = None;
                        let mut seen: Vec<ExprId> = Vec::new();
                        for x in self.ast().list(*v) {
                            let hint = res.filter(|r| {
                                let sr = self.shallow(*r);
                                !matches!(self.tcx.tys.kind(sr), TyKind::FnDef(..) | TyKind::Closure(..))
                            });
                            let t = self.check_expr(*x, hint);
                            res = Some(match res {
                                None => t,
                                Some(r) => {
                                    let prev = seen.clone();
                                    self.coerce_many(&prev, r, *x, t, lo)
                                }
                            });
                            seen.push(*x);
                        }
                        let e = res.unwrap_or_else(|| self.fresh(0));
                        if let Some(x) = elem_exp {
                            self.unify(x, e);
                        }
                        return self.tcx.tys.intern(TyKind::Array(e, v.len() as u64));
                    }
                };
                for x in self.ast().list(*v) {
                    let t = self.check_expr(*x, Some(elem));
                    self.coerce_or_unify(t, elem, Some(*x), lo);
                }
                self.tcx.tys.intern(TyKind::Array(elem, v.len() as u64))
            }
            ExprKind::Repeat(x, n) => {
                let elem_exp = match expected {
                    Some(t) => {
                        let s = self.shallow_with_regions(t);
                        match self.tcx.tys.kind(s).clone() {
                            TyKind::Array(e, _) => Some(e),
                            _ => None,
                        }
                    }
                    None => None,
                };
                let mut t = self.check_expr(*x, elem_exp);
                // the operand is a coercion site for the expected element type (`[&[]; 4]` as
                // `[&[i16]; 4]`: &[i16; 0] -> &[i16]), as an array literal's elements are
                if let Some(et) = elem_exp {
                    let se = self.shallow(et);
                    let open = matches!(self.tcx.tys.kind(se), TyKind::Infer(_));
                    if !open && self.coerce_or_unify(t, et, Some(*x), self.ast().expr(*x).lo) {
                        t = et;
                    }
                }
                // `[x; _]`: the length is inferred (rustc generic_arg_infer)
                if crate::tcx::is_infer_len(self.ast(), *n) {
                    let v = self.fresh(0);
                    let arr = self.tcx.tys.mk_array(t, v);
                    self.deferred_repeats.push((*x, t, arr));
                    return arr;
                }
                let usize_ = self.tcx.tys.usize_;
                self.check_expr(*n, Some(usize_));
                // a constant or a const generic param of this instance (`[0; N]`)
                let env = self.env.clone();
                self.cx.state.const_wait.set(false);
                let lt = self.tcx.const_arg(&self.cx, self.prog, self.file, self.module, &env, *n);
                if lt == self.tcx.tys.error && self.cx.state.const_wait.get() {
                    // the count is a const evaluated by running it: the body is checked again
                    // once it has been (jit: resolve_const_requests)
                    self.err(self.ast().expr(*n).lo, "array repeat count waits for a constant's evaluation".to_string());
                    return self.tcx.tys.error;
                }
                if lt == self.tcx.tys.error {
                    self.err(self.ast().expr(*n).lo, "array repeat count must be a constant -- use a const item or a const generic param".to_string());
                    return self.tcx.tys.error;
                }
                let lt = self.tcx.tys.subst_for_inference(lt, &self.inst_args.clone());
                let arr = self.tcx.tys.mk_array(t, lt);
                self.deferred_repeats.push((*x, t, arr));
                arr
            }
            ExprKind::Field(x, name) => self.check_field(e, *x, *name, lo),
            ExprKind::TupleField(x, idx) => {
                let t = self.check_expr(*x, None);
                let mut cur = self.shallow_with_regions(t);
                let mut derefs = 0u8;
                loop {
                    match self.tcx.tys.kind(cur).clone() {
                        TyKind::Tuple(v) => {
                            self.b.field_idx.insert(e.0, (derefs, *idx));
                            return v.get(*idx as usize).copied().unwrap_or(error);
                        }
                        TyKind::Adt(d, args, regions) => {
                            let adt = self.tcx.adts.get(&d).cloned();
                            if let Some(adt) = adt {
                                if !adt.is_enum {
                                    if let Some(f) = adt.variants[0].fields.get(*idx as usize) {
                                        if self.field_visible(d, f) {
                                            self.b.field_idx.insert(e.0, (derefs, *idx));
                                            return self.instantiate_field_type(f.ty, adt.region_params, regions, &args);
                                        }
                                    }
                                }
                            }
                            match self.deref_step(e.0, derefs, cur) {
                                Some(i) => {
                                    cur = i;
                                    derefs += 1;
                                }
                                None => break,
                            }
                        }
                        _ => match self.deref_step(e.0, derefs, cur) {
                            Some(i) => {
                                cur = i;
                                derefs += 1;
                            }
                            None => break,
                        },
                    }
                }
                let s = self.ty_str(t);
                self.err(lo, format!("no field `{}` on `{}`", idx, s));
                error
            }
            ExprKind::Index(a, i) => {
                let ta = self.check_expr(*a, None);
                let ti = self.check_expr(*i, None);
                let mut cur = self.shallow_with_regions(ta);
                let mut derefs = 0u8;
                let tis = self.shallow(ti);
                let idx_is_range = matches!(self.tcx.tys.kind(tis), TyKind::Adt(..));
                // an integer literal index stays open until the indexing is known: `f[1]` with
                // `impl Index<isize> for Foo` is isize (rustc: the literal is typed by the
                // selected Index impl); builtin array/slice indexing makes it usize
                let lit_index = self.is_literal_var(tis);
                // an index whose type is still open (`tree[ix]`, ix from an Option filled later)
                // is fixed by the indexing selected below, not assumed usize up front (rustc
                // lookup_indexing: `T: Index<?I>`)
                let open_index = !lit_index && matches!(self.tcx.tys.kind(tis), TyKind::Infer(_));
                if !idx_is_range && !lit_index && !open_index {
                    let usize_ = self.tcx.tys.usize_;
                    self.unify(tis, usize_);
                }
                loop {
                    match self.tcx.tys.kind(cur).clone() {
                        TyKind::Array(el, _) | TyKind::Slice(el) => {
                            self.b.index_derefs.insert(e.0, derefs);
                            // an index type of the program's own (`impl<T> Index<TableIndex> for
                            // [T]`): the overloaded Index of the array, else of the slice it
                            // unsizes to (rustc method/probe.rs lookup_indexing: unsize step)
                            // (a generic index of a polymorphic body -- `I: SliceIndex<[T]>` --
                            // goes through std's `impl<T, I: SliceIndex<[T]>> Index<I> for [T]`:
                            // the result is `<I as SliceIndex<[T]>>::Output`)
                            let std_range = match self.tcx.tys.kind(tis) {
                                TyKind::Adt(d, _, _) => matches!(self.prog.name(*d), "Range" | "RangeFrom" | "RangeTo" | "RangeFull" | "RangeInclusive" | "RangeToInclusive"),
                                TyKind::Param(_) | TyKind::Assoc(..) => false,
                                _ => true,
                            };
                            if !std_range {
                                if let Some(td) = self.lang_item(&["ops", "Index"]) {
                                    let ti2 = self.deep(ti);
                                    let slice = self.tcx.tys.intern(TyKind::Slice(el));
                                    for st in [cur, slice] {
                                        let ds = self.deep(st);
                                        if !matches!(self.select_trait(td, ds, &[ti2]), SelectionResult::NoSolution) {
                                            let m = self.trait_fn(td, "index").unwrap();
                                            self.b.ov_index.insert(e.0, (m, vec![ds, ti2]));
                                            let out = self.tcx.trait_assoc(self.prog, td, self.prog.syms.get("Output").unwrap()).unwrap();
                                            let r = self.tcx.tys.intern(TyKind::Assoc(out, vec![ds, ti2], crate::types::RegionArgsId::EMPTY));
                                            return self.norm_keep(r);
                                        }
                                    }
                                }
                            }
                            if idx_is_range {
                                return self.tcx.tys.intern(TyKind::Slice(el));
                            }
                            if lit_index || open_index {
                                let usize_ = self.tcx.tys.usize_;
                                self.unify(tis, usize_);
                            }
                            return el;
                        }
                        TyKind::Str if idx_is_range => {
                            self.b.index_derefs.insert(e.0, derefs);
                            return self.tcx.tys.str_;
                        }
                        TyKind::Ref(_, x, _) | TyKind::Ptr(_, x) => {
                            cur = self.shallow_with_regions(x);
                            derefs += 1;
                        }
                        TyKind::Adt(..) => {
                            // `Index<Idx>` impl on the type, else autoderef through Deref
                            if let Some(td) = self.lang_item(&["ops", "Index"]) {
                                let dc = self.deep(cur);
                                let ti2 = self.deep(ti);
                                let mut found = self.select_trait(td, dc, &[ti2]);
                                let mut coerced_idx: Option<TyId> = None;
                                if matches!(found, SelectionResult::NoSolution) && !idx_is_range && !lit_index {
                                    // the index coerces to the impl's index type (`S[bar]` with
                                    // `impl Index<fn()> for S`: rustc coerces the index operand to
                                    // the input type of the selected impl)
                                    let wild = self.fresh(0);
                                    if let SelectionResult::Ok(selected) = self.select_trait(td, dc, &[wild]) {
                                        let (imp, iargs) = (selected.method_owner(), selected.args);
                                        if let Some(&ia) = self.tcx.impl_trait_args.get(&imp).and_then(|v| v.first()) {
                                            let want = self.tcx.tys.subst_for_inference(ia, &iargs);
                                            let snap = self.snapshot();
                                            if !self.tcx.has_param(want) && self.try_coerce(ti, want, Some(*i)) {
                                                coerced_idx = Some(want);
                                                found = self.select_trait(td, dc, &[want]);
                                            } else {
                                                self.rollback(snap);
                                            }
                                        }
                                    }
                                }
                                if !matches!(found, SelectionResult::NoSolution) {
                                    self.b.index_derefs.insert(e.0, derefs);
                                    let m = self.trait_fn(td, "index").unwrap();
                                    let index = coerced_idx.unwrap_or(ti2);
                                    self.b.ov_index.insert(e.0, (m, vec![dc, index]));
                                    let output = self.tcx.trait_assoc(self.prog, td, self.prog.syms.get("Output").unwrap()).unwrap();
                                    let projection = self.tcx.tys.intern(TyKind::Assoc(output, vec![dc, index], crate::types::RegionArgsId::EMPTY));
                                    return self.norm_keep(projection);
                                }
                            }
                            match self.deref_step(e.0, derefs, cur) {
                                Some(i) => {
                                    cur = i;
                                    derefs += 1;
                                }
                                None => break,
                            }
                        }
                        _ => break,
                    }
                }
                let s = self.ty_str(ta);
                self.err(lo, format!("cannot index `{}`", s));
                error
            }
            ExprKind::AddrOf(raw, m, x) => {
                let exp_inner = match expected {
                    Some(t) => {
                        let s = self.shallow_region_vars(t);
                        match self.tcx.tys.kind(s).clone() {
                            TyKind::Ref(_, i, _) => Some(i),
                            _ => None,
                        }
                    }
                    None => None,
                };
                // `&[a, b]` against `&[T]`: check the array with the slice's element. Otherwise an
                // unsized referent (`&str`, `&dyn T`) is only a hint for a value operand (rustc
                // check_expr_addr_of: rvalue_hint -> ExpectRvalueLikeUnsized); the coercion applies
                // to the whole `&expr` (`&if c { a } else { b }` with String branches)
                let exp_inner = match exp_inner {
                    Some(i) => {
                        let si = self.shallow(i);
                        let unsized_ref = matches!(self.tcx.tys.kind(si), TyKind::Str | TyKind::Dyn(..) | TyKind::Slice(..));
                        let operand = &self.ast().expr(*x).kind;
                        let value_operand = !matches!(operand, ExprKind::Path(_) | ExprKind::Field(..) | ExprKind::TupleField(..) | ExprKind::Index(..) | ExprKind::Unary(UnOp::Deref, _) | ExprKind::Paren(_) | ExprKind::Array(..) | ExprKind::Repeat(..));
                        // a closure still deduces its signature from the hint (rustc closure.rs
                        // check_expr_closure: `expected.to_option()` includes RvalueLikeUnsized)
                        let closure = matches!(operand, ExprKind::Closure { .. });
                        if unsized_ref && value_operand && !closure { None } else { Some(i) }
                    }
                    None => None,
                };
                let t = self.check_expr(*x, exp_inner);
                if *raw {
                    self.tcx.tys.intern(TyKind::Ptr(*m, t))
                } else {
                    self.tcx.tys.intern(TyKind::Ref(*m, t, self.fresh_region()))
                }
            }
            ExprKind::Call(f, args) => self.check_call(e, *f, self.ast().list(*args), expected, lo),
            ExprKind::MethodCall { recv, name, turbofish, args } => {
                self.method_expected = expected;
                self.check_method(e, *recv, *name, *turbofish, self.ast().list(*args), lo)
            }
            ExprKind::Struct(path, fields, base, rest) => {
                let r = self.resolve_struct_path(path);
                self.b.res.insert(e.0, r);
                let d = match r {
                    Res::Def(d) => d,
                    _ => return error,
                };
                let (adt_ty, vi) = self.adt_of_ctor(d);
                let adt_ty = self.instantiate_adt(adt_ty);
                let adt_ty = if self.prog.def(d).kind == DefKind::Variant { adt_ty } else { self.struct_path_ty(path, adt_ty) };
                // an unsized expectation (`Wrap<dyn Debug>` for `Box::new(Wrap { .. })`) is no
                // type to check against (rustc only_has_type of ExpectRvalueLikeUnsized)
                if let Some(x) = expected {
                    if !self.is_unsized_ty(x) {
                        self.unify(adt_ty, x);
                    }
                }
                let base = base.get();
                let mut given: Vec<u32> = Vec::new();
                for fe in self.ast().list(*fields).iter() {
                    let fname = self.sym(fe.name);
                    let fname = if fe.name.hi > fe.name.lo && self.text(fe.name).as_bytes()[0].is_ascii_digit() {
                        crate::ast::tuple_index(self.text(fe.name)).map_or(u32::MAX - 1, |n| n | 0x8000_0000)
                    } else {
                        fname
                    };
                    let fx = fe.expr;
                    match self.field_ty(adt_ty, vi, fname) {
                        Some((fi, ft)) => {
                            given.push(fi);
                            let t = self.check_expr(fx, Some(ft));
                            self.coerce_or_unify(t, ft, Some(fx), fe.name.lo);
                        }
                        None => {
                            self.err(fe.name.lo, format!("no field `{}`", self.text(fe.name)));
                        }
                    }
                }
                if let Some(bx) = base {
                    let t = self.check_expr(bx, Some(adt_ty));
                    self.unify(t, adt_ty);
                }
                if *rest {
                    self.struct_defaults(e, d, adt_ty, vi, &given, lo);
                }
                adt_ty
            }
            ExprKind::Range(a, b, incl) => {
                let elem = self.fresh(0);
                if let Some(a) = a {
                    let t = self.check_expr(*a, Some(elem));
                    self.unify(t, elem);
                }
                if let Some(b) = b {
                    let t = self.check_expr(*b, Some(elem));
                    self.unify(t, elem);
                }
                let name = match (a.is_some(), b.is_some(), *incl) {
                    (true, true, false) => "Range",
                    (true, true, true) => "RangeInclusive",
                    (true, false, _) => "RangeFrom",
                    (false, true, false) => "RangeTo",
                    (false, true, true) => "RangeToInclusive",
                    (false, false, _) => "RangeFull",
                };
                match self.lang_item(&["ops", name]) {
                    Some(d) => {
                        let n = self.tcx.adts.get(&d).map_or(0, |a| a.n_generics);
                        let args = if n == 0 { Vec::new() } else { vec![elem] };
                        self.tcx.tys.intern(TyKind::Adt(d, args, crate::types::RegionArgsId::EMPTY))
                    }
                    None => {
                        self.err(lo, format!("core::ops::{} not found", name));
                        error
                    }
                }
            }
            ExprKind::Closure { params, ret, body, .. } => self.check_closure(e, self.ast().list(*params), *ret, *body, expected),
            ExprKind::Mac(m) => self.check_mac(e, m, expected, lo),
            ExprKind::Try(x) => self.check_try(e, *x, lo),
            ExprKind::Async(mode, b) => self.check_async_block(e, *mode, *b),
            ExprKind::Await(x) => self.check_await(*x, lo),
            ExprKind::Yield(_) | ExprKind::Box(_) => {
                self.err(lo, "unsupported expression (yield, box)".to_string());
                error
            }
            ExprKind::Underscore => self.fresh(0),
        }
    }

    fn sym_lifetime(&self, id: Ident) -> (Sym, u32) {
        // lifetimes are not interned as idents; use the text without the quote
        let t = self.text(id);
        let t = t.trim_start_matches('\'');
        (self.prog.syms.get(t).unwrap_or(u32::MAX - 1), id.lo)
    }

    fn loop_index(&self, label: Option<(Sym, u32)>) -> Option<usize> {
        let mut i = self.loops.len();
        while i > 0 {
            i -= 1;
            match label {
                None => {
                    // unlabeled break targets the innermost real loop (not a labeled block)
                    return Some(i);
                }
                Some(l) => {
                    // labels are hygienic like locals (rustc)
                    if let Some(d) = self.loops[i].label {
                        if d.0 == l.0 && self.prog.files[self.file as usize].hyg_visible(d.1, l.1) {
                            return Some(i);
                        }
                    }
                }
            }
        }
        None
    }

    fn loop_has_break(&self, b: BlockId, label: Option<(Sym, u32)>) -> bool {
        // conservative syntactic scan: any `break` that targets this loop
        let ast = self.ast();
        let blk = ast.block(b);
        let mut found = false;
        for s in ast.list(blk.stmts) {
            match s {
                Stmt::Expr(e, _) => found = found || self.expr_has_break(*e, 0, label),
                Stmt::Let { init: Some(e), .. } => found = found || self.expr_has_break(*e, 0, label),
                _ => {}
            }
        }
        found
    }

    fn expr_has_break(&self, e: ExprId, depth: u32, label: Option<(Sym, u32)>) -> bool {
        let ast = self.ast();
        match &ast.expr(e).kind {
            ExprKind::Break(l, x) => {
                let target_ok = match l {
                    None => depth == 0,
                    Some(li) => label.map_or(false, |l| self.sym_lifetime(*li).0 == l.0),
                };
                target_ok || x.map_or(false, |v| self.expr_has_break(v, depth, label))
            }
            ExprKind::Loop(b, _) | ExprKind::While(_, b, _) | ExprKind::For(_, _, b, _) => self.block_has_break(*b, depth + 1, label),
            ExprKind::Block(b, _) | ExprKind::Unsafe(b) => self.block_has_break(*b, depth, label),
            ExprKind::If(c, t, el) => {
                self.expr_has_break(*c, depth, label) || self.block_has_break(*t, depth, label) || el.map_or(false, |x| self.expr_has_break(x, depth, label))
            }
            ExprKind::Match(x, arms) => {
                let mut r = self.expr_has_break(*x, depth, label);
                for a in self.ast().list(*arms) {
                    r = r || self.expr_has_break(a.body, depth, label);
                }
                r
            }
            ExprKind::Paren(x) => self.expr_has_break(*x, depth, label),
            _ => false,
        }
    }

    fn block_has_break(&self, b: BlockId, depth: u32, label: Option<(Sym, u32)>) -> bool {
        let ast = self.ast();
        for s in ast.stmts(b) {
            let r = match s {
                Stmt::Expr(e, _) => self.expr_has_break(*e, depth, label),
                Stmt::Let { init: Some(e), .. } => self.expr_has_break(*e, depth, label),
                _ => false,
            };
            if r {
                return true;
            }
        }
        false
    }

    /// `x?` on Option / Result: the success payload; the failure returns early (Result errors
    /// through `From::from` when the error types differ).
    fn check_try(&mut self, e: ExprId, x: ExprId, lo: u32) -> TyId {
        let error = self.tcx.tys.error;
        let t = self.check_expr(x, None);
        let t = self.shallow(t);
        let (d, args) = match self.tcx.tys.kind(t).clone() {
            TyKind::Adt(d, args, _) if Some(self.prog.def(d).krate) == self.prog.prelude_crate && matches!(self.prog.name(d), "Option" | "Result") => (d, args),
            TyKind::Error => return error,
            _ => {
                let s = self.ty_str(t);
                self.err(lo, format!("`?` needs an Option or Result, found `{}`", s));
                return error;
            }
        };
        let is_result = self.prog.name(d) == "Result";
        let ret = match self.ret_stack.last() {
            Some(r) => *r,
            None => return error,
        };
        let mut rs = self.shallow(ret);
        // `Poll<Result<T, F>>` (std's `FromResidual<Result<!, E>> for Poll<Result<T, F>>`, a
        // stream's poll): the error converts into F as for a Result return; lowering wraps the
        // Err in Poll::Ready
        if is_result {
            if let TyKind::Adt(pd, pargs, _) = self.tcx.tys.kind(rs).clone() {
                if self.prog.name(pd) == "Poll" && Some(self.prog.def(pd).krate) == self.prog.prelude_crate {
                    if let Some(&inner) = pargs.first() {
                        let inner = self.shallow(inner);
                        if matches!(self.tcx.tys.kind(inner), TyKind::Adt(id, _, _) if *id == d) {
                            rs = inner;
                        }
                    }
                }
            }
        }
        let mut conv = None;
        match self.tcx.tys.kind(rs).clone() {
            TyKind::Infer(_) => {
                // closure without a declared return type: the same carrier; its error type is
                // what the body makes it (the tail `encode(..)` returning Result<(), String>
                // after a `?` on Result<_, &str>): the `?` converts through From once it is
                // known (rustc: an `E: From<&str>` obligation, not E = &str)
                let mut a = vec![self.fresh(0)];
                if is_result {
                    let ev = self.fresh(0);
                    a.push(ev);
                    self.pending_tries.push((e.0, args[1], ev, ret));
                }
                let rt = self.tcx.tys.intern(TyKind::Adt(d, a, crate::types::RegionArgsId::EMPTY));
                self.unify(rs, rt);
            }
            TyKind::Adt(rd, rargs, _) if rd == d => {
                if is_result && matches!(self.tcx.tys.kind(self.shallow(rargs[1])), TyKind::Infer(_)) {
                    // the error type is still open (a closure whose first `?` made its return
                    // type `Result<_, ?E>`): rustc adds `?E: From<have>`, it never equates them;
                    // `.ok_or("..")?` after `eval()?` (String) must not fix ?E = &str
                    self.pending_tries.push((e.0, args[1], rargs[1], ret));
                } else if is_result {
                    let (have, want) = (args[1], rargs[1]);
                    let save = self.snapshot();
                    if !self.unify(have, want) {
                        self.rollback(save);
                        let from = self.lang_item(&["convert", "From"]);
                        let h = self.deep(have);
                        let w = self.deep(want);
                        let ok = match from {
                            Some(fd) => !matches!(self.select_trait(fd, w, &[h]), SelectionResult::NoSolution),
                            None => false,
                        };
                        if !ok {
                            let (hs, ws) = (self.ty_str(h), self.ty_str(w));
                            self.err(lo, format!("`?` cannot convert the error `{}` into `{}` (no From impl)", hs, ws));
                        } else if let Some(fm) = from.and_then(|fd| self.trait_fn(fd, "from")) {
                            conv = Some((fm, vec![w, h]));
                        }
                    }
                }
            }
            _ => {
                let s = self.ty_str(rs);
                self.err(lo, format!("`?` in a function returning `{}`", s));
            }
        }
        self.b.try_conv.insert(e.0, conv);
        args.first().copied().unwrap_or(error)
    }

    /// The `?`s of a body whose return type was open: an error type the body left open is the
    /// first `?`'s (Relax's fallback; rustc asks for an annotation), a different one is reached
    /// through `From` (or is an error when no impl converts).
    fn finish_tries(&mut self, ret: Option<TyId>) {
        self.finish_tries_at(ret, false);
    }

    /// `outermost`: the item body's end (fcx.finish): open error types take their fallback here.
    fn finish_tries_at(&mut self, ret: Option<TyId>, outermost: bool) {
        let list = std::mem::take(&mut self.pending_tries);
        let mut keep = Vec::new();
        // the body a closure's still-open `?`s move to (rustc checks a closure with its enclosing
        // body: the error type can come from code after the closure, `match f() { Err(e) => Some(e) .. }`)
        let enclosing = if outermost { None } else { self.ret_stack.last().copied() };
        for (e, have, want, r) in list {
            // a `?` of an enclosing body (its closure not finished yet) stays pending
            if !outermost && Some(r) != ret {
                keep.push((e, have, want, r));
                continue;
            }
            let ws = self.shallow(want);
            if matches!(self.tcx.tys.kind(ws), TyKind::Infer(_)) {
                if let Some(up) = enclosing {
                    keep.push((e, have, want, up));
                    continue;
                }
                self.unify(ws, have);
                continue;
            }
            let save = self.snapshot();
            if self.unify(have, want) {
                continue;
            }
            self.rollback(save);
            let from = self.lang_item(&["convert", "From"]);
            let h = self.deep(have);
            let w = self.deep(want);
            let ok = match from {
                Some(fd) => !matches!(self.select_trait(fd, w, &[h]), SelectionResult::NoSolution),
                None => false,
            };
            let lo = self.ast().expr(ExprId(e)).lo;
            if !ok {
                let (hs, wstr) = (self.ty_str(h), self.ty_str(w));
                self.err(lo, format!("`?` cannot convert the error `{}` into `{}` (no From impl)", hs, wstr));
            } else if let Some(fm) = from.and_then(|fd| self.trait_fn(fd, "from")) {
                self.b.try_conv.insert(e, Some((fm, vec![w, h])));
            }
        }
        self.pending_tries.extend(keep);
    }

    pub fn lang_item(&self, path: &[&str]) -> Option<DefId> {
        let mut key = String::with_capacity(32);
        for p in path {
            key.push_str(p);
            key.push(':');
        }
        if let Some(r) = self.tcx.core_path_items.get(&key) {
            return r;
        }
        let r = self.lang_item_uncached(path);
        self.tcx.core_path_items.insert(key, r);
        r
    }

    fn lang_item_uncached(&self, path: &[&str]) -> Option<DefId> {
        // core::<path>
        let prog = self.prog;
        let core = prog.syms.get("core")?;
        let mut cur = None;
        for c in 0..prog.crates.len() {
            if prog.crates[c].name == core {
                cur = Some(prog.mods[prog.crates[c].root_mod as usize].def);
            }
        }
        let mut cur = cur?;
        for p in path {
            let s = prog.syms.get(p)?;
            cur = match prog.lookup_in_container(cur, s, true) {
                Some(d) => d,
                None => prog.lookup_in_container(cur, s, false)?,
            };
        }
        Some(cur)
    }

    fn is_numeric(&self, t: TyId) -> bool {
        match self.tcx.tys.kind(t) {
            TyKind::Int(_) | TyKind::Float(_) | TyKind::Error => true,
            TyKind::Infer(v) => matches!(self.vars[*v as usize], VarSt::Free(1) | VarSt::Free(2)),
            _ => false,
        }
    }

    fn check_lit(&mut self, e: ExprId, k: LitKind, expected: Option<TyId>) -> TyId {
        let f = &self.prog.files[self.file as usize];
        let ex = f.ast.expr(e);
        let text = std::str::from_utf8(f.bytes(ex.lo, ex.hi)).unwrap_or("");
        match k {
            LitKind::Int | LitKind::Float => {
                if let Some(suf) = crate::consteval::int_suffix(text) {
                    for (n, p) in crate::program::PRIMS {
                        if n == suf {
                            return self.tcx.tys.prim(p);
                        }
                    }
                }
                let want_float = k == LitKind::Float;
                if let Some(x) = expected {
                    let s = self.shallow(x);
                    let ok = match self.tcx.tys.kind(s) {
                        TyKind::Int(_) => !want_float,
                        TyKind::Float(_) => true,
                        TyKind::Infer(v) => match self.vars[*v as usize] {
                            VarSt::Free(1) => !want_float,
                            VarSt::Free(2) => true,
                            _ => false,
                        },
                        _ => false,
                    };
                    if ok {
                        return s;
                    }
                }
                self.fresh(if want_float { 2 } else { 1 })
            }
            LitKind::Bool(_) => self.tcx.tys.bool_,
            LitKind::Char => self.tcx.tys.char_,
            LitKind::Byte => self.tcx.tys.u8_,
            LitKind::Str | LitKind::RawStr => self.tcx.tys.str_ref,
            LitKind::ByteStr => {
                let n = crate::lit::unescape_bytes(text).len() as u64;
                let arr = self.tcx.tys.intern(TyKind::Array(self.tcx.tys.u8_, n));
                self.tcx.tys.intern(TyKind::Ref(false, arr, crate::types::RegionId::ERASED))
            }
            // `c"..."`: &'static core::ffi::CStr (nul-terminated)
            LitKind::CStr => match self.lang_item(&["ffi", "CStr"]) {
                Some(d) => {
                    let t = self.tcx.tys.intern(TyKind::Adt(d, Vec::new(), crate::types::RegionArgsId::EMPTY));
                    self.tcx.tys.intern(TyKind::Ref(false, t, crate::types::RegionId::ERASED))
                }
                None => self.tcx.tys.error,
            },
        }
    }

    fn check_binary(&mut self, e: ExprId, op: BinOp, a: ExprId, b: ExprId, expected: Option<TyId>, lo: u32) -> TyId {
        let bool_ = self.tcx.tys.bool_;
        match op {
            BinOp::And | BinOp::Or => {
                // both operands are coerced to bool (rustc op.rs check_overloaded_binop for
                // lazy ops: demand_coerce to bool), which also fixes a generic return
                // (`v.is_empty() && msg_send![..]`)
                let ta = self.check_expr(a, Some(bool_));
                self.coerce_or_unify(ta, bool_, Some(a), self.ast().expr(a).lo);
                // `let` chains bind in the left operand; keep those scopes for the right
                let tb = self.check_expr(b, Some(bool_));
                self.coerce_or_unify(tb, bool_, Some(b), self.ast().expr(b).lo);
                self.diverges = false;
                bool_
            }
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let ta = self.check_expr(a, None);
                // non-primitive operands compare through PartialEq / PartialOrd (`v == w` on
                // Vecs calls Vec's eq, `s == "x"` with s: String uses PartialEq<&str>)
                let sa = self.shallow(ta);
                // (`&str` orders through str's PartialOrd: only its equality is built in)
                let ordering = !matches!(op, BinOp::Eq | BinOp::Ne);
                let prim_ref = match self.tcx.tys.kind(sa).clone() {
                    TyKind::Ref(_, i, _) => {
                        let i = self.shallow(i);
                        self.is_numeric(i) || matches!(self.tcx.tys.kind(i), TyKind::Bool | TyKind::Char | TyKind::FnPtr(..)) || (!ordering && matches!(self.tcx.tys.kind(i), TyKind::Str))
                    }
                    _ => false,
                };
                // a generic param or a rigid projection compares through its PartialEq /
                // PartialOrd bound too: only scalars are built in (rustc op.rs check_overloaded_binop,
                // by_ref_binop: both operands autoref'd). Typing it as a built-in comparison made the
                // capture analysis of `|kv| kv.0 == k` consume `k` (by value) in a generic body but
                // borrow it in an instance -- two closure layouts for one closure
                // unsized places compare through their impls too (`*l == *r` with l: &[T] is
                // `<[T] as PartialEq>::eq(&*l, &*r)`, rustc op.rs: only scalars are built in)
                if !prim_ref && matches!(self.tcx.tys.kind(sa), TyKind::Adt(..) | TyKind::Ref(..) | TyKind::Tuple(..) | TyKind::Array(..) | TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..) | TyKind::Param(_) | TyKind::Assoc(..)) {
                    if let Some(r) = self.check_cmp_trait(e, op, sa, b, lo, None) {
                        return r;
                    }
                }
                let tb = self.check_expr(b, Some(ta));
                // `&str != String`, `&u8 == u8`: not the built-in comparison of equal types but
                // `<&str as PartialEq<String>>` (rustc op.rs: an operator trait lookup with the
                // operand types as written)
                if prim_ref {
                    let (x, y) = (self.shallow(ta), self.shallow(tb));
                    if x != y && !matches!(self.tcx.tys.kind(y), TyKind::Infer(_)) {
                        let save = self.snapshot();
                        let same = self.unify(x, y);
                        self.rollback(save);
                        if !same {
                            if let Some(r) = self.check_cmp_trait(e, op, sa, b, lo, Some(tb)) {
                                return r;
                            }
                        }
                    }
                }
                // raw and fn pointers compare only through their `PartialEq for Self` impls, so
                // rustc's `L: PartialEq<?R>` selects ?R = L before the rhs is checked and the rhs
                // coerces to it (`fn_ptr == fn_item`, `raw == &x`, `*const T == *mut T`)
                let ptr_lhs = matches!(self.tcx.tys.kind(sa), TyKind::Ptr(..) | TyKind::FnPtr(..));
                if ptr_lhs {
                    let save = self.snapshot();
                    if self.unify(ta, tb) {
                        // already equal
                    } else {
                        self.rollback(save);
                        self.coerce_or_unify(tb, ta, Some(b), self.ast().expr(b).lo);
                    }
                } else if !self.unify(ta, tb) {
                    let (sa, sb) = (self.ty_str(ta), self.ty_str(tb));
                    self.err(lo, format!("cannot compare `{}` with `{}`", sa, sb));
                }
                bool_
            }
            BinOp::Shl | BinOp::Shr => {
                let ta = self.check_expr(a, expected);
                // `&x >> k` on primitives: core's forward-ref Shl/Shr impls, Output = the
                // primitive (rustc op.rs: only primitive operands are built in); a non-primitive
                // left operand is an operator trait call
                let sa0 = self.shallow(ta);
                let ta = self.peel_prim_refs(sa0);
                let sa = self.shallow(ta);
                if matches!(self.tcx.tys.kind(sa), TyKind::Adt(..) | TyKind::Ref(..) | TyKind::Tuple(..) | TyKind::Array(..)) {
                    self.cur_binop = e.0;
                    return self.check_op_trait(op, sa, b, lo, false);
                }
                self.check_expr(b, None);
                ta
            }
            _ => {
                let exp = match expected {
                    Some(x) => {
                        let s = self.shallow(x);
                        if self.is_numeric(s) {
                            Some(s)
                        } else {
                            None
                        }
                    }
                    None => None,
                };
                let ta = self.check_expr(a, exp);
                let sa0 = self.shallow(ta);
                // `&x op y` on primitives: built in, through the references (core's
                // forward-ref operator impls, without dispatch)
                let ta = self.peel_prim_refs(sa0);
                let sa0 = self.shallow(ta);
                if matches!(self.tcx.tys.kind(sa0), TyKind::Adt(..) | TyKind::Ref(..) | TyKind::Tuple(..) | TyKind::Array(..)) {
                    self.cur_binop = e.0;
                    return self.check_op_trait(op, sa0, b, lo, false);
                }
                let tb0 = self.check_expr(b, Some(ta));
                let sb0 = self.shallow(tb0);
                // a primitive left operand with a non-primitive right one is an operator trait
                // call too (`3u32 * duration`: `impl Mul<Duration> for u32`; rustc is_builtin_binop
                // needs both sides primitive)
                if matches!(self.tcx.tys.kind(sb0), TyKind::Adt(..)) {
                    let sa = self.shallow(ta);
                    if let Some(r) = self.prim_lhs_op(op, e, sa, sb0, lo) {
                        return r;
                    }
                }
                let tb = self.peel_prim_refs(tb0);
                let sa = self.shallow(ta);
                let sb = self.shallow(tb);
                // primitive arithmetic: both sides the same type
                if !self.unify(sa, sb) {
                    let (x, y) = (self.ty_str(sa), self.ty_str(sb));
                    self.err(lo, format!("no binary operator for `{}` and `{}`", x, y));
                }
                ta
            }
        }
    }

    /// The normalized <Iter as Iterator>::Item of the desugared next call.
    /// rustc_ast_lowering/src/expr.rs:1774-1784.
    fn iterator_item(&mut self, key: u32, t: TyId) -> Option<TyId> {
        let next = self.tcx.lang_items.get(crate::lang_items::LangItem::IteratorNext)?;
        let td = self.prog.def(next).parent;
        let dt = self.deep(t);
        match self.select_trait(td, dt, &[]) { SelectionResult::Ok(_) | SelectionResult::Ambiguous(_) => {}, SelectionResult::NoSolution => return None };
        let ad = self.tcx.trait_assoc(self.prog, td, self.prog.syms.get("Item")?)?;
        let proj = self.tcx.tys.intern(TyKind::Assoc(ad, vec![dt], crate::types::RegionArgsId::EMPTY));
        let item = self.norm(proj);
        self.b.for_next.insert(key, (next, vec![dt]));
        Some(item)
    }

    fn check_for_iter(&mut self, it: ExprId, lo: u32) -> TyId {
        let t = self.check_expr(it, None);
        if let Some(item) = self.for_into_iter_item(it.0, t) {
            return item;
        }
        let ts = self.ty_str(t);
        self.err(lo, format!("`for` over `{}`: no IntoIterator impl", ts));
        self.tcx.tys.error
    }

    fn check_field(&mut self, e: ExprId, x: ExprId, name: Ident, lo: u32) -> TyId {
        let t = self.check_expr(x, None);
        let s = self.sym(name);
        let mut cur = self.shallow_with_regions(t);
        let mut derefs = 0u8;
        loop {
            if let TyKind::Adt(d, args, regions) = self.tcx.tys.kind(cur).clone() {
                if let Some(adt) = self.tcx.adts.get(&d).cloned() {
                    if !adt.is_enum {
                        for (i, f) in adt.variants[0].fields.iter().enumerate() {
                            // a private field of a type from elsewhere is not visible: autoderef
                            // continues (`rc.0` on Rc<Shared> is Shared's field)
                            if f.name == s && self.field_visible(d, f) {
                                self.b.field_idx.insert(e.0, (derefs, i as u32));
                                if !self.b.field_uses.contains(&(d, i as u32)) {
                                    self.b.field_uses.push((d, i as u32));
                                    self.b.dependencies.push(d);
                                }
                                return self.instantiate_field_type(f.ty, adt.region_params, regions, &args);
                            }
                        }
                    }
                }
            }
            // references, raw pointers, then Deref impls (Box<T>, wrappers)
            match self.deref_step(e.0, derefs, cur) {
                Some(i) => {
                    cur = i;
                    derefs += 1;
                }
                None => break,
            }
        }
        let ts = self.ty_str(t);
        self.err(lo, format!("no field `{}` on `{}`", self.text(name), ts));
        self.tcx.tys.error
    }

    /// Is a field of ADT `d` visible here: `pub`, or we are inside the ADT's module (or below it).
    fn field_visible(&self, d: DefId, f: &crate::tcx::FieldT) -> bool {
        // (`pub` / `pub(in path)`: inside that module only)
        if f.vis_mod != u32::MAX && f.is_pub {
            return self.prog.mod_within(self.module, f.vis_mod);
        }
        if f.is_pub {
            return true;
        }
        let target = self.prog.def(d).scope;
        let mut m = Some(self.module);
        let mut guard = 0;
        while let Some(cur) = m {
            if cur == target || self.prog.mods[cur as usize].normal == target {
                return true;
            }
            let md = &self.prog.mods[cur as usize];
            m = md.lexical_parent.or(md.parent_mod);
            guard += 1;
            if guard > 256 {
                break;
            }
        }
        false
    }

    fn check_call(&mut self, e: ExprId, f: ExprId, args: &[ExprId], expected: Option<TyId>, lo: u32) -> TyId {
        let ft = self.check_expr(f, None);
        let mut fs = self.shallow_region_vars(ft);
        // `vqshlq_n_u32(v, 6)` is `vqshlq_n_u32::<6>(v)` (rustc_ast_lowering
        // lower_legacy_const_generics): those arguments become the fn's own const args
        let legacy_kept: Vec<ExprId>;
        let args: &[ExprId] = match self.tcx.tys.kind(fs).clone() {
            TyKind::FnDef(d, gargs, _) => match self.tcx.fn_item_sig(self.prog, d).map(|s| (s.legacy_const.clone(), s.n_parent_generics)) {
                Some((lc, np)) if !lc.is_empty() => {
                    let env = self.env.clone();
                    for (j, &i) in lc.iter().enumerate() {
                        if let (Some(&a), Some(&g)) = (args.get(i as usize), gargs.get(np as usize + j)) {
                            let c = self.tcx.const_arg(&self.cx, self.prog, self.file, self.module, &env, a);
                            self.unify(g, c);
                        }
                    }
                    legacy_kept = args.iter().enumerate().filter(|(i, _)| !lc.contains(&(*i as u32))).map(|(_, a)| *a).collect();
                    self.b.legacy_args.insert(e.0, lc);
                    &legacy_kept
                }
                _ => args,
            },
            _ => args,
        };
        // calls through references / smart pointers to callables (`&F`, `Box<dyn Fn()>`)
        let mut steps = 0u8;
        loop {
            match self.tcx.tys.kind(fs) {
                TyKind::FnDef(..) | TyKind::FnPtr(..) | TyKind::Closure(..) | TyKind::Dyn(..) | TyKind::Opaque(..) | TyKind::Error | TyKind::Infer(_) => break,
                _ => {}
            }
            match self.deref_step(e.0, steps, fs) {
                Some(n) => {
                    fs = n;
                    steps += 1;
                }
                None => break,
            }
        }
        if steps > 0 {
            self.b.call_derefs.insert(e.0, steps);
        }
        // A direct function/constructor path is already concrete in the generic
        // body. Only value calls need its definition-time Fn-family selection.
        let direct = matches!(self.tcx.tys.kind(fs), TyKind::FnDef(..))
            && matches!(self.b.res.get(&crate::lit::strip_paren(self.ast(), f).0), Some(Res::Def(_)));
        if !direct { self.record_call_trait(e, fs, steps); }
        let error = self.tcx.tys.error;
        let mut bounded: Option<(DefId, Vec<TyId>, Vec<TyId>)> = None;
        let mut variadic = false;
        let (params, ret) = match self.tcx.tys.kind(fs).clone() {
            TyKind::FnDef(d, gargs, _) => match self.tcx.fn_item_sig(self.prog, d).cloned() {
                Some(sig) if sig.params.iter().any(|p| self.tcx.tys.has_error(*p)) || self.tcx.tys.has_error(sig.ret) => {
                    let n = self.prog.def_path(d);
                    self.err(lo, format!("`{}` has unresolved types in its signature -- fix its signature errors first", n));
                    for a in args {
                        self.check_expr(*a, None);
                    }
                    return error;
                }
                Some(sig) => {
                    let (ps, r) = self.instantiate_call_signature(d, &gargs, &sig);
                    if self.tcx.item_clauses(self.prog, d).is_some() || self.tcx.fn_trait_bounds(self.prog, d).is_some() {
                        bounded = Some((d, gargs.clone(), sig.params.clone()));
                    }
                    variadic = sig.header.c_variadic;
                    (ps, r)
                }
                None => (Vec::new(), error),
            },
            TyKind::FnPtr(_, _, header, n) => {
                variadic = header.c_variadic;
                let vars: Vec<_> = (0..n).map(|_| self.fresh_region()).collect();
                let sig = self.instantiate_signature(fs, &vars);
                let TyKind::FnPtr(ps, r, _, _) = self.tcx.tys.kind(sig).clone() else { unreachable!() };
                (ps, r)
            },
            TyKind::Closure(_, _, sig, _, _) => {
                let TyKind::FnPtr(_, _, _, n) = self.tcx.tys.kind(sig) else { unreachable!() };
                let vars: Vec<_> = (0..*n).map(|_| self.fresh_region()).collect();
                let sig = self.instantiate_signature(sig, &vars);
                let TyKind::FnPtr(ps, r, _, _) = self.tcx.tys.kind(sig).clone() else { unreachable!() };
                (ps, r)
            },
            TyKind::Dyn(td, ..) if self.is_fn_trait(td) => {
                match self.deduce_closure_signature(fs) {
                    Some((sig, _)) => {
                        let TyKind::FnPtr(_, _, _, n) = self.tcx.tys.kind(sig) else { unreachable!() };
                        let vars: Vec<_> = (0..*n).map(|_| self.fresh_region()).collect();
                        let sig = self.instantiate_signature(sig, &vars);
                        let TyKind::FnPtr(ps, r, _, _) = self.tcx.tys.kind(sig).clone() else { unreachable!() };
                        (ps, r)
                    }
                    None => (Vec::new(), error),
                }
            },
            // `dyn Cb<T>` with `trait Cb<T>: FnOnce(&mut T)`: the Fn supertrait's signature
            TyKind::Dyn(td, targs, _, _, _, _, _) if self.dyn_super_fn_sig(td, fs, &targs).is_some() => self.dyn_super_fn_sig(td, fs, &targs).unwrap(),
            TyKind::Opaque(..) if self.opaque_fn_sig(fs).is_some() => self.opaque_fn_sig(fs).unwrap(),
            TyKind::Param(_) if self.param_fn_sig(fs).is_some() => self.param_fn_sig(fs).unwrap(),
            TyKind::Error => {
                for a in args {
                    self.check_expr(*a, None);
                }
                return error;
            }
            _ => {
                let s = self.ty_str(fs);
                self.err(lo, format!("`{}` is not callable", s));
                return error;
            }
        };
        if params.len() != args.len() && !(variadic && args.len() >= params.len()) {
            let callee = match self.tcx.tys.kind(fs).clone() {
                TyKind::FnDef(d, _, _) => Some(d),
                _ => None,
            };
            let help = self.arg_count_help(callee, &params, args, 0);
            self.err(lo, format!("E0061: this function takes {} argument{} but {} {} supplied{}", params.len(), if params.len() == 1 { "" } else { "s" }, args.len(), if args.len() == 1 { "was" } else { "were" }, help));
        }
        // the expected result can guide generic args (e.g. `Some(x)` into Option<T>)
        let mut exp_inputs: Option<Vec<Option<TyId>>> = None;
        if let Some(x) = expected {
            let rs = self.shallow(ret);
            if matches!(self.tcx.tys.kind(rs), TyKind::Adt(..)) {
                let xs = self.shallow(x);
                if matches!(self.tcx.tys.kind(xs), TyKind::Adt(..)) {
                    // rustc fn_ctxt/checks.rs expected_inputs_for_expected_output: unify the formal
                    // output with the expectation; when that makes a parameter itself unsized
                    // (`Box::new(x)` into `Box<dyn Fn() -> u32>`), undo it and use the expected
                    // inputs as hints only (a closure takes its signature from the `dyn Fn`, the
                    // argument then coerces); otherwise the unification stands (`Err(Box::new(s))`
                    // into `Result<_, Box<dyn Any>>`, `Mutex::new(b)` into `Mutex<Box<dyn Fn()>>`)
                    let mut exp_vars = Vec::new();
                    let xd = self.deep(xs);
                    self.free_vars(xd, &mut exp_vars);
                    let mut callee_vars = Vec::new();
                    for p in &params {
                        let p0 = self.deep(*p);
                        self.free_vars(p0, &mut callee_vars);
                    }
                    let save = self.snapshot();
                    if self.unify(ret, x) {
                        let ins: Vec<TyId> = params.iter().map(|p| self.resolve_region_vars(*p)).collect();
                        let unsized_param = ins.iter().any(|t| self.is_unsized_ty(*t));
                        // the probe is never committed (fudge_inference_if_ok): an input
                        // whose variables are the expectation's own is a hint; one holding
                        // the callee's fresh variables says nothing (a fresh variable)
                        let mut hints = Vec::new();
                        for t in &ins {
                            let mut fv = Vec::new();
                            self.free_vars(*t, &mut fv);
                            hints.push(if fv.iter().all(|v| exp_vars.contains(v) && !callee_vars.contains(v)) { Some(*t) } else { None });
                        }
                        self.rollback(save);
                        if unsized_param {
                            if hints.iter().all(|h| h.is_some()) {
                                exp_inputs = Some(hints);
                            }
                        } else {
                            exp_inputs = Some(hints);
                        }
                    } else {
                        self.rollback(save);
                    }
                }
            } else if matches!(self.tcx.tys.kind(rs), TyKind::Ref(..)) {
                // a reference result (`Cell::from_mut(&mut v)` into `&Cell<[T]>`): rustc's
                // expectation probe (fudged, never committed) gives the expected inputs
                // (`&mut [T]`), and the argument coerces to them (deref of the Vec)
                let xs = self.shallow(x);
                if matches!(self.tcx.tys.kind(xs), TyKind::Ref(..)) {
                    let mut exp_vars = Vec::new();
                    let xd = self.deep(xs);
                    self.free_vars(xd, &mut exp_vars);
                    let mut callee_vars = Vec::new();
                    for p in &params {
                        let p0 = self.deep(*p);
                        self.free_vars(p0, &mut callee_vars);
                    }
                    let save = self.snapshot();
                    if self.unify(ret, x) {
                        let ins: Vec<TyId> = params.iter().map(|p| self.resolve_region_vars(*p)).collect();
                        let mut fv = Vec::new();
                        for t in &ins {
                            self.free_vars(*t, &mut fv);
                        }
                        self.rollback(save);
                        if fv.iter().all(|v| exp_vars.contains(v) && !callee_vars.contains(v)) {
                            exp_inputs = Some(ins.into_iter().map(Some).collect());
                        }
                    } else {
                        self.rollback(save);
                    }
                }
            }
        }
        // rustc check_argument_types: non-closures first, then select their obligations
        // before deriving closure signatures from the call's Fn bounds.
        for check_closures in [false, true] {
            if check_closures {
                self.select_before_closures(bounded.as_ref().map(|(d, gargs, _)| (*d, gargs.as_slice())));
            }
            for (i, a) in args.iter().enumerate() {
                if matches!(self.ast().expr(*a).kind, ExprKind::Closure { .. }) != check_closures {
                    continue;
                }
                if variadic && i >= params.len() {
                    self.check_expr(*a, None);
                    continue;
                }
                let pt = if i < params.len() { self.normalize_signature(params[i]) } else { error };
                if let Some(ei) = exp_inputs.as_ref().and_then(|v| v.get(i).copied().flatten()) {
                    // rvalue_hint: an unsized expected input is only a hint (closure signatures),
                    // and the argument coerces to the formal type; a sized one is coerced to, then
                    // the formal type must equal it (checks.rs demand_compatible)
                    let unsized_hint = self.is_unsized_ty(ei);
                    let t = self.check_expr(*a, Some(ei));
                    if unsized_hint {
                        self.coerce_or_unify(t, pt, Some(*a), self.ast().expr(*a).lo);
                    } else {
                        self.coerce_or_unify(t, ei, Some(*a), self.ast().expr(*a).lo);
                        self.unify(pt, ei);
                    }
                    continue;
                }
                let t = self.check_expr(*a, Some(pt));
                if let Some((d, gargs, _)) = &bounded {
                    let (d, gargs) = (*d, gargs.clone());
                    self.select_before_coerce(d, &gargs, pt);
                }
                self.coerce_or_unify(t, pt, Some(*a), self.ast().expr(*a).lo);
            }
        }
        if let Some((d, gargs, _)) = &bounded {
            self.apply_fn_bounds(*d, gargs, lo);
        }
        let _ = e;
        self.normalize_signature(ret)
    }

    /// `async [move] { .. }`: a coroutine -- a closure type with no parameters whose state
    /// holds the captures and a frame word, and which implements Future<Output = the block's
    /// type> (rustc lowers async blocks to coroutines; captures as for closures).
    fn check_async_block(&mut self, e: ExprId, mode: u8, b: BlockId) -> TyId {
        let is_move = mode == crate::ast::ASYNC_MOVE;
        let _ = self.tcx.future_defs(self.prog);
        let saved = self.scopes.len();
        self.closure_depth.push((e.0, saved));
        let out = self.fresh(0);
        self.ret_stack.push(out);
        self.async_depth += 1;
        let save_awaits = std::mem::take(&mut self.await_count);
        let save_loops = std::mem::take(&mut self.loops);
        let save_condition = std::mem::replace(&mut self.in_loop_condition, false);
        let bt = self.check_block(b, Some(out));
        self.loops = save_loops;
        self.in_loop_condition = save_condition;
        let points = std::mem::replace(&mut self.await_count, save_awaits);
        if !self.diverges {
            self.coerce_or_unify(bt, out, None, self.ast().block(b).hi);
        }
        self.async_depth -= 1;
        let r = self.ret_stack.pop();
        self.finish_tries(r);
        self.closure_depth.pop();
        self.scopes.truncate(saved);
        self.diverges = false;
        let mut force_args = Vec::new();
        let mut force_move_if_consumes = false;
        let mut is_move = is_move;
        if mode == crate::ast::ASYNC_CLOSURE_BODY {
            if let Some(&(parent, _)) = self.closure_depth.last() {
                if let ExprKind::Closure { is_move: parent_move, .. } = self.ast().expr(ExprId(parent)).kind {
                    force_move_if_consumes = parent_move;
                    is_move |= parent_move && self.expected_closure_kinds.get(&parent) == Some(&crate::upvar::ClosureKind::FnOnce);
                }
                // Parameter bindings are explicitly transferred to the coroutine,
                // including unused / Copy arguments (rustc upvar.rs:286-321).
                force_args = self.scopes[self.closure_depth.last().unwrap().1..].iter().map(|p| p.1).collect();
            }
        }
        let caps = self.b.closure_locals.entry(e.0).or_default();
        for &li in &force_args { if !caps.contains(&li) { caps.push(li); } }
        self.coroutine_type(e.0, b, force_args, is_move, force_move_if_consumes, out, points)
    }

    /// Leave the environment tuple open until closure_analyze has processed the body.
    fn coroutine_type(&mut self, ce: u32, block: BlockId, force_args: Vec<u32>, is_move: bool, force_move_if_consumes: bool, out: TyId, points: u32) -> TyId {
        self.b.closures.push(ce);
        let up = self.fresh(0);
        self.pending_captures.push(crate::upvar::PendingCapture {
            closure: ce, upvars: up, source: crate::upvar::CaptureSource::Block(block),
            is_move, force_args, force_move_if_consumes, points: Some(points),
        });
        self.tcx.coroutines.insert((self.file, ce), ());
        let sig = self.tcx.tys.intern(TyKind::FnPtr(Vec::new(), out, FnHeader::RUST, 0));
        let owner = self.tcx.tys.intern(TyKind::FnDef(self.b.def, self.b.args.clone(), crate::types::RegionArgsId::EMPTY));
        self.tcx.tys.intern(TyKind::Closure(self.file, ce, sig, up, owner))
    }

    /// `x.await`: `IntoFuture::into_future(x)` polled to completion; its type is
    /// `<X as IntoFuture>::Output` (rustc lowering of `.await`, Reference await-expr.md).
    fn check_await(&mut self, x: ExprId, lo: u32) -> TyId {
        let t = self.check_expr(x, None);
        if self.async_depth == 0 {
            self.err(lo, "`await` is only allowed inside `async` functions and blocks (E0728)".to_string());
            return self.tcx.tys.error;
        }
        self.await_count += 1;
        // an async block / async fn body: its output is the coroutine's return type, known
        // without selection (rustc: the coroutine's Future::Output, so `A[async { 1 }.await]`
        // keeps the literal open for the index)
        let st = self.shallow(t);
        if let TyKind::Closure(f, ce, sig, _, _) = self.tcx.tys.kind(st).clone() {
            if self.tcx.coroutines.contains(&(f, ce)) {
                if let TyKind::FnPtr(_, out, _, _) = self.tcx.tys.kind(sig).clone() {
                    return out;
                }
            }
        }
        let ft = self.deep(t);
        let ad = match self.lang_item(&["future", "IntoFuture"]) {
            Some(td) => {
                let sym = self.prog.syms.get("Output").unwrap_or(u32::MAX);
                self.tcx.trait_assoc(self.prog, td, sym)
            }
            None => None,
        };
        let ad = match ad {
            Some(a) => a,
            None => {
                self.err(lo, "core::future::IntoFuture not found".to_string());
                return self.tcx.tys.error;
            }
        };
        let proj = self.tcx.tys.intern(TyKind::Assoc(ad, vec![ft], crate::types::RegionArgsId::EMPTY));
        let n = self.norm(proj);
        if matches!(self.tcx.tys.kind(n), TyKind::Assoc(..)) {
            if self.tcx.tys.has_infer(n) {
                let v = self.fresh(0);
                self.defer_proj_eq(v, n);
                return v;
            }
            let ts = self.ty_str(ft);
            self.err(lo, format!("`{}` is not a future (E0277): `.await` needs IntoFuture", ts));
            return self.tcx.tys.error;
        }
        n
    }

    fn check_closure(&mut self, e: ExprId, params: &[ClosureParam], ret: Option<crate::ast::TyId>, body: ExprId, expected: Option<TyId>) -> TyId {
        // rustc_hir_typeck::closure::deduce_closure_signature: retain the kind
        // alongside the signature. FnPtr is also used for signature-only hints
        // from generic Fn bounds here, so it cannot supply a closure kind.
        // Borrowck must check a dyn Fn closure as Fn
        // even when moving a capture would otherwise infer FnOnce.
        if let Some(expected) = expected {
            let expected = self.shallow(expected);
            let kind = match self.tcx.tys.kind(expected) {
                TyKind::Dyn(td, ..) if self.lang_item(&["ops", "Fn"]) == Some(*td) => Some(ExpectedClosureKind::Fn),
                TyKind::Dyn(td, ..) if self.lang_item(&["ops", "FnMut"]) == Some(*td) => Some(ExpectedClosureKind::FnMut),
                TyKind::Dyn(td, ..) if self.lang_item(&["ops", "FnOnce"]) == Some(*td) => Some(ExpectedClosureKind::FnOnce),
                _ => None,
            };
            if let Some(kind) = kind {
                self.b.closure_expected_kinds.insert(e.0, kind);
            }
        }
        let sigs = self.closure_signatures(e, params, ret, expected);
        let (ps, rt) = match self.tcx.tys.kind(sigs.liberated).clone() {
            TyKind::FnPtr(ps, r, _, _) => (ps, r),
            _ => unreachable!(),
        };
        self.b.closure_sigs.insert(e.0, sigs);
        let saved = self.scopes.len();
        self.closure_depth.push((e.0, saved));
        let save_async = std::mem::take(&mut self.async_depth);
        let save_awaits = std::mem::take(&mut self.await_count);
        for (p, t) in params.iter().zip(ps) {
            self.check_pat(p.pat, t);
        }
        self.ret_stack.push(rt);
        let save_loops = std::mem::take(&mut self.loops);
        let save_condition = std::mem::replace(&mut self.in_loop_condition, false);
        let bt = self.check_expr(body, Some(rt));
        self.loops = save_loops;
        self.in_loop_condition = save_condition;
        self.coerce_or_unify(bt, rt, Some(body), self.ast().expr(body).lo);
        // a coerced body keeps its own type: lowering converts it to the return type
        if !self.b.coerce.contains_key(&body.0) {
            self.set_ty(body, rt);
        }
        let r = self.ret_stack.pop();
        self.finish_tries(r);
        self.closure_depth.pop();
        self.async_depth = save_async;
        self.await_count = save_awaits;
        self.scopes.truncate(saved);
        self.diverges = false;
        self.b.closures.push(e.0);
        let sig = self.b.closure_sigs[&e.0].bound;
        let is_move = matches!(self.ast().expr(e).kind, ExprKind::Closure { is_move: true, .. });
        let up = self.fresh(0);
        self.pending_captures.push(crate::upvar::PendingCapture {
            closure: e.0, upvars: up, source: crate::upvar::CaptureSource::Expr(body),
            is_move, force_args: Vec::new(), force_move_if_consumes: false, points: None,
        });
        let owner = self.tcx.tys.intern(TyKind::FnDef(self.b.def, self.b.args.clone(), crate::types::RegionArgsId::EMPTY));
        self.tcx.tys.intern(TyKind::Closure(self.file, e.0, sig, up, owner))
    }

    /// The deferred `Copy` checks of `[x; N]` (rustc fn_ctxt/checks.rs check_repeat_exprs,
    /// run after the body and before fallback): a const item / const block operand needs none;
    /// the count must be resolved by now (all counts first, so a `Copy` side effect cannot
    /// make another repeat's count known); `Copy` is required unless the count is 0 or 1.
    fn check_repeat_exprs(&mut self) {
        let mut todo = Vec::new();
        for (x, et, arr) in std::mem::take(&mut self.deferred_repeats) {
            let mut y = x;
            while let ExprKind::Paren(i) = self.ast().expr(y).kind.clone() {
                y = i;
            }
            if matches!(self.ast().expr(y).kind, ExprKind::ConstBlock(..)) {
                continue;
            }
            if matches!(self.b.res.get(&y.0), Some(Res::Def(d)) if matches!(self.prog.def(*d).kind, DefKind::Const | DefKind::AssocConst)) {
                continue;
            }
            let arr = self.deep(arr);
            let n = match self.tcx.tys.kind(arr).clone() {
                TyKind::Array(_, n) => n,
                _ => continue,
            };
            let count = match crate::types::len_ty(n) {
                None => Some(n),
                Some(c) => {
                    let c = self.shallow(c);
                    match self.tcx.tys.kind(c).clone() {
                        TyKind::ConstVal(m) => Some(m),
                        TyKind::Infer(_) => {
                            let lo = self.ast().expr(x).lo;
                            let s = self.ty_str(arr);
                            self.err(lo, format!("E0282: type annotations needed for `{}`", s));
                            continue;
                        }
                        TyKind::Error => continue,
                        _ => None,
                    }
                }
            };
            todo.push((et, count));
        }
        let Some(td) = self.lang_item(&["marker", "Copy"]) else { return };
        for (et, count) in todo {
            if !matches!(count, Some(0) | Some(1)) {
                self.infer_from_bounds_inner(&[et], vec![(0, td, Vec::new())]);
            }
        }
    }

    fn check_method(&mut self, e: ExprId, recv: ExprId, name: Ident, turbofish: GenericArgsId, args: &[ExprId], lo: u32) -> TyId {
        // this call's expectation only (nested calls in the receiver set their own)
        let method_expected = self.method_expected.take();
        let s = self.sym(name);
        self.check_method_sym(e, recv, s, turbofish, args, None, lo, method_expected)
    }

    /// A method call by name; `extra` is the type of one more argument after `args` that has no
    /// expression (built-in macros: `write!(w, ..)` is `w.write_fmt(format_args!(..))`).
    fn check_method_sym(&mut self, e: ExprId, recv: ExprId, s: Sym, turbofish: GenericArgsId, args: &[ExprId], extra: Option<TyId>, lo: u32, method_expected: Option<TyId>) -> TyId {
        self.extra_arg = extra;
        let rt = self.check_expr(recv, None);
        if let Some(r) = self.bound_method(e, rt, s, turbofish, args, lo) {
            return r;
        }
        if let Some(r) = self.projection_method(e, rt, s, turbofish, args, lo) {
            return r;
        }
        let error = self.tcx.tys.error;
        // a receiver with open variables inside a known constructor (`x: Box<_> = 6.into()`):
        // pending obligations are selected first where they now can be (rustc probe.rs
        // structurally resolves the receiver, select_obligations_where_possible)
        {
            let d0 = self.deep(rt);
            if self.tcx.tys.has_infer(d0) && !matches!(self.tcx.tys.kind(d0), TyKind::Infer(_)) {
                self.select_literal_obligations(false);
                self.retry_goals(false);
            }
        }
        // resolved through (array lengths and nested args bound since: `&mut [i32; ?n]`)
        let dr = self.deep(rt);
        // projections inside the receiver type normalized first (rustc probe.rs works on the
        // structurally resolved, normalized self type): `&mut <usize as SliceIndex<[Vec<T>]>>::Output`
        // is `&mut Vec<T>`, so `list.last()` is the slice's method, not `Iterator for &mut I`'s
        let dr = if self.tcx.tys.has_assoc(dr) { self.tcx.normalize_for_inference(&self.cx, self.prog, dr) } else { dr };
        let mut cur = self.shallow(dr);
        let mut derefs = 0u8;
        let mut found = None;
        let mut trait_found: Option<(DefId, DefId, TyId)> = None;
        // Probe T, &T, then &mut T at each autoderef step; inherent priority applies
        // only within one adjusted receiver type (rustc pick_all_method / pick_method).
        let mut receiver_kind = 1;
        loop {
            if trait_found.is_some() {
                break;
            }
            // an integer / float literal at this step (`3.meow()`, or `r.cmp(..)` with
            // r: &{integer}): the numeric types whose trait impls in scope have the method
            // (rustc probes all integral types for an int var); one type fixes the literal,
            // several sharing one trait method leave it to the fallback
            if let Some(hits) = self.numeric_var_methods(cur, s) {
                if hits.len() == 1 {
                    self.unify(cur, hits[0].0);
                    cur = self.shallow(cur);
                } else if hits.len() > 1 && hits.iter().all(|h| h.1 == hits[0].1)
                    && self.tcx.fn_sig(self.prog, hits[0].1).map_or(false, |sg| sg.self_kind == receiver_kind) {
                    trait_found = Some((hits[0].1, crate::program::NO_DEF, cur));
                    break;
                } else if hits.is_empty() && receiver_kind == 2 {
                    // the autoref step: a by-value method of an impl for `&{integer}`'s one
                    // numeric type (`impl get for &isize`, `x.get()` with x: Box<{integer}>)
                    if let TyKind::Infer(v) = self.tcx.tys.kind(cur).clone() {
                        let prims: Vec<Prim> = match self.vars[v as usize] {
                            VarSt::Free(1) => vec![Prim::I8, Prim::I16, Prim::I32, Prim::I64, Prim::I128, Prim::Isize, Prim::U8, Prim::U16, Prim::U32, Prim::U64, Prim::U128, Prim::Usize],
                            VarSt::Free(2) => vec![Prim::F32, Prim::F64],
                            _ => Vec::new(),
                        };
                        let mut rh = Vec::new();
                        for pr in prims {
                            let pt = self.tcx.tys.prim(pr);
                            let rpt = self.tcx.tys.intern(TyKind::Ref(false, pt, crate::types::RegionId::ERASED));
                            let tm: Vec<(DefId, DefId)> = self.scoped_trait_methods(rpt, s).into_iter().filter(|(it, _)| self.tcx.fn_sig(self.prog, *it).map_or(false, |sg| sg.self_kind == 1)).collect();
                            if let Some(&(item, imp)) = tm.first() {
                                rh.push((pt, rpt, item, imp));
                            }
                        }
                        if rh.len() == 1 {
                            self.unify(cur, rh[0].0);
                            self.forced_autoref = Some(1);
                            trait_found = Some((rh[0].2, rh[0].3, rh[0].1));
                            break;
                        }
                    }
                }
            }
            let adjusted = match receiver_kind {
                2 | 3 => self.tcx.tys.intern(TyKind::Ref(receiver_kind == 3, cur, crate::types::RegionId::ERASED)),
                _ => cur,
            };
            // Inherent candidates for this adjusted receiver, including typed receivers
            // declared on a smart pointer's pointee, precede extension candidates.
            let mut px = Some(cur);
            let mut depth = 0;
            while let Some(x) = px {
                if let Some((item, imp)) = self.tcx.inherent_item(&self.cx, self.prog, x, s) {
                    // Associated functions and inaccessible methods are not candidates.
                    if self.prog.def(item).kind == DefKind::AssocFn && self.item_visible(item)
                        && self.method_receiver_matches(item, imp, x, adjusted, false) {
                        found = Some((item, imp, x));
                        break;
                    }
                }
                depth += 1;
                px = if depth <= 4 { self.receiver_pointee(x) } else { None };
            }
            if found.is_some() {
                break;
            }
            // methods whose receiver type is this step's adjusted type (rustc method/probe.rs
            // matches the receiver type at each autoderef step): `self: Box<Self>` /
            // `self: Pin<&mut Self>` methods of the pointee (`b.into_string()` on Box<str>,
            // `fut.poll(cx)` on Pin<&mut T> is T's poll, not Pin's own Future impl)
            // (Self may sit several pointers deep: `self: &Box<Rc<Self>>`)
            let mut px = self.receiver_pointee(cur);
            let mut depth = 0;
            while let Some(x) = px {
                let tm = self.scoped_trait_methods(x, s);
                if let Some(&(item, imp)) = tm.iter().find(|(item, imp)| self.method_receiver_matches(*item, *imp, x, adjusted, true)) {
                    trait_found = Some((item, imp, x));
                    break;
                }
                // an integer / float variable pointee (`Box<{integer}>` with `self: Box<Self>`
                // in `impl Tr for usize`): the numeric types whose impl's receiver matches;
                // exactly one fixes the variable
                if let Some(hits) = self.numeric_var_methods(x, s) {
                    let mut ok = Vec::new();
                    for h in hits {
                        if self.method_receiver_matches(h.1, h.2, h.0, adjusted, true) {
                            ok.push(h);
                        }
                    }
                    if ok.len() == 1 {
                        self.unify(x, ok[0].0);
                        trait_found = Some((ok[0].1, ok[0].2, ok[0].0));
                        break;
                    }
                }
                // a trait object pointee's methods (`Pin<&mut dyn Future>`.poll(cx) is the
                // virtual poll, not Pin's own Future impl; rustc's probe matches the receiver
                // type `Pin<&mut Self>` with Self = dyn Future at this step); only the step's
                // own pointee: a deeper one (`Box<Box<dyn Tr>>` with `self: Box<Self>`) is
                // reached by autoderef, which passes the inner box
                if let (0, TyKind::Dyn(td, ..)) = (depth, self.tcx.tys.kind(x).clone()) {
                    if let Some(item) = self.dyn_method(td, s) {
                        if self.method_receiver_matches(item, crate::program::NO_DEF, x, adjusted, true) {
                            trait_found = Some((item, crate::program::NO_DEF, x));
                            break;
                        }
                    }
                }
                // an opaque pointee's bound methods (`Pin<&mut impl Future>`.poll(cx) is the
                // future's poll, not Pin's own Future impl)
                if let Some((item, ta)) = self.opaque_method(x, s) {
                    if self.method_receiver_matches(item, crate::program::NO_DEF, x, adjusted, true) {
                        if !ta.is_empty() {
                            self.known_targs = Some(ta);
                        }
                        trait_found = Some((item, crate::program::NO_DEF, x));
                        break;
                    }
                }
                // a param / rigid projection pointee of a generic body: its bounds' methods
                // (`w.wake()` on Arc<W> with `W: Wake`, `fn wake(self: Arc<Self>)`)
                if matches!(self.tcx.tys.kind(x), TyKind::Param(_) | TyKind::Assoc(..)) {
                    if let Some((item, _)) = self.trait_item_for(x, s) {
                        if self.prog.def(item).kind == DefKind::AssocFn && self.method_receiver_matches(item, crate::program::NO_DEF, x, adjusted, true) {
                            trait_found = Some((item, crate::program::NO_DEF, x));
                            break;
                        }
                    }
                }
                depth += 1;
                px = if depth < 4 { self.receiver_pointee(x) } else { None };
            }
            if trait_found.is_some() {
                break;
            }
            if let TyKind::Dyn(td, ..) = self.tcx.tys.kind(cur).clone() {
                if let Some(item) = self.dyn_method(td, s) {
                    if self.method_receiver_matches(item, crate::program::NO_DEF, cur, adjusted, true) {
                        // virtual call: no impl (NO_DEF), dispatched through the vtable
                        trait_found = Some((item, crate::program::NO_DEF, cur));
                        break;
                    }
                }
            }
            // an opaque type's methods are its bounds' (rustc probe.rs assemble_inherent_candidates
            // for an alias: the item bounds act like a param's where-clauses); codegen resolves
            // the call on the hidden type
            if let Some((item, ta)) = self.opaque_method(cur, s) {
                if self.method_receiver_matches(item, crate::program::NO_DEF, cur, adjusted, true) {
                    if !ta.is_empty() {
                        self.known_targs = Some(ta);
                    }
                    trait_found = Some((item, crate::program::NO_DEF, cur));
                    break;
                }
            }
            // by-value receiver first (rustc's probe order): on `&V`, a `&self` method of V
            // matches before an autoref'd method of `&V` itself (`self.debug_fmt(f)` with
            // self: &dyn Tr is Tr's method, not a blanket impl's for `&dyn Tr`)
            // (only at the step itself: after taking it, the method is `inner`'s -- `(&&X).refm()`
            // is `<&X as RefM>::refm`, not X's one more step down)
            if receiver_kind == 1 {
                if let TyKind::Ref(m, inner, _) = self.tcx.tys.kind(cur).clone() {
                    let inner = self.shallow(inner);
                    if self.has_ref_self_method(inner, s, m) {
                        cur = inner;
                        derefs += 1;
                        receiver_kind = if m { 3 } else { 2 };
                        continue;
                    }
                }
            }
            let mut tm = self.scoped_trait_methods(cur, s);
            // `array.into_iter()` before edition 2021 (`Box<[T]>` before 2024): IntoIterator's
            // by-value impl is skipped during method dispatch, so autoref picks the slice
            // iterator (rustc #[rustc_skip_during_method_dispatch(array, boxed_slice)])
            if self.prog.syms.str(s) == "into_iter" {
                let ed = self.prog.crates[self.prog.mods[self.module as usize].krate as usize].edition;
                let skip = match self.tcx.tys.kind(cur).clone() {
                    TyKind::Array(..) => ed < 2021,
                    TyKind::Adt(d, a, _) => ed < 2024 && self.lang_item(&["boxed", "Box"]) == Some(d) && a.first().map_or(false, |x| matches!(self.tcx.tys.kind(self.shallow(*x)), TyKind::Slice(_))),
                    _ => false,
                };
                if skip {
                    if let Some(ii) = self.lang_item(&["iter", "IntoIterator"]) {
                        tm.retain(|(it, _)| self.prog.def(*it).parent != ii);
                    }
                }
            }
            // where-clauses on this step's type itself (`for<'x> &'x V: IntoIterator` makes
            // `value.into_iter()` on `&V` that trait's method: rustc's param-env candidate)
            if !matches!(self.tcx.tys.kind(cur), TyKind::Param(_) | TyKind::Infer(_) | TyKind::Error) {
                for (td, _) in self.tcx.param_env_of(&self.cx, cur) {
                    for &it in &self.prog.traits[self.prog.def(td).sub as usize] {
                        if self.prog.def(it).name == s && self.prog.def(it).kind == DefKind::AssocFn && !tm.iter().any(|x| x.0 == it) {
                            tm.insert(0, (it, crate::program::NO_DEF));
                        }
                    }
                }
            }
            // an associated fn without `self` is no method candidate (`lease.from(b)` on an
            // Arc<Lease> is Lease's inherent `from(&self, ..)` one step down, not From::from)
            tm.retain(|(it, imp)| self.method_receiver_matches(*it, *imp, cur, adjusted, true));
            if let Some(&(item, imp)) = tm.first() {
                // several impls of the trait for this type (String: Extend<char>, Extend<&str>..):
                // the trait's method with its args open; the impl follows from them (rustc probes the
                // trait candidate, not an impl: method/probe.rs assemble_extension_candidates)
                let ambiguous = tm.iter().filter(|c| c.0 == item).count() > 1;
                let imp = if ambiguous { crate::program::NO_DEF } else { imp };
                trait_found = Some((item, imp, cur));
                break;
            }
            // autoref step (rustc probe.rs pick_autorefd_method): a by-value `self` method of
            // an impl for `&U` called on U (`(&&A).m()` is `<&&&A as M>::m(&(&&A))`)
            if receiver_kind != 1 && !matches!(self.tcx.tys.kind(cur), TyKind::Infer(_) | TyKind::Error | TyKind::Param(_)) {
                let rt = adjusted;
                let tm = self.scoped_trait_methods(rt, s);
                let byval: Vec<(DefId, DefId)> = tm.into_iter().filter(|(it, imp)| self.method_receiver_matches(*it, *imp, rt, adjusted, true)).collect();
                if let Some(&(item, imp)) = byval.first() {
                    let ambiguous = byval.iter().filter(|c| c.0 == item).count() > 1;
                    let imp = if ambiguous { crate::program::NO_DEF } else { imp };
                    self.forced_autoref = Some(receiver_kind - 1);
                    trait_found = Some((item, imp, rt));
                    break;
                }
            }
            if receiver_kind < 3 {
                receiver_kind += 1;
                continue;
            }
            receiver_kind = 1;
            match self.tcx.tys.kind(cur).clone() {
                TyKind::Ref(_, i, _) => {
                    cur = self.shallow(i);
                    derefs += 1;
                }
                // method lookup never autoderefs raw pointers (`p.add(1)` is the pointer's)
                TyKind::Ptr(..) => break,
                TyKind::Array(el, _) => {
                    // arrays get slice methods by unsizing
                    cur = self.tcx.tys.intern(TyKind::Slice(el));
                }
                _ => match self.deref_step(e.0, derefs, cur) {
                    Some(i) => {
                        cur = i;
                        derefs += 1;
                    }
                    None => break,
                },
            }
        }
        if let (None, Some((item, imp, self_ty))) = (found, trait_found) {
            return self.check_trait_method_call(e, item, imp, self_ty, derefs, turbofish, args, lo, method_expected);
        }
        let (item, imp, self_ty) = match found {
            Some(x) => x,
            None => {
                let ts = self.ty_str(rt);
                let help = self.method_help(rt, s);
                self.err(lo, format!("E0599: no method named `{}` found for `{}` in the current scope{}", self.prog.syms.str(s), ts, help));
                for a in args {
                    self.check_expr(*a, None);
                }
                return error;
            }
        };
        let sig = self.tcx.fn_sig(self.prog, item).cloned().unwrap();
        let mut gargs = self.match_impl_args(imp, self_ty);
        let own = sig.n_generics - sig.n_parent_generics;
        let mut tf = Vec::new();
        if let Some(GenericArgs::Angle(v)) = self.ast().gargs(turbofish) {
            for g in self.ast().list(*v) {
                if let Some(lt) = self.generic_arg(g) {
                    tf.push(lt);
                }
            }
        }
        for i in 0..own as usize {
            if i < tf.len() {
                gargs.push(tf[i]);
            } else {
                gargs.push(self.fresh(0));
            }
        }
        let autoref = match sig.self_kind {
            2 => 1,
            3 => 2,
            _ => 0,
        };
        self.b.dependencies.push(item);
        self.b.methods.insert(e.0, MethodRes { def: item, derefs, autoref, args: gargs.clone() });
        if sig.self_kind == 0 {
            self.err(lo, format!("`{}` is an associated function, not a method", self.prog.syms.str(s)));
            return error;
        }
        let (ps, ret) = self.instantiate_call_signature(item, &gargs, &sig);
        let extra = self.extra_arg.take();
        let n_extra = extra.is_some() as usize;
        if ps.len() != args.len() + 1 + n_extra {
            let want = ps.len().saturating_sub(1);
            let help = if n_extra == 0 { let rest: Vec<TyId> = ps.iter().skip(1).copied().collect(); self.arg_count_help(Some(item), &rest, args, 0) } else { String::new() };
            self.err(lo, format!("E0061: this method takes {} argument{} but {} {} supplied{}", want, if want == 1 { "" } else { "s" }, args.len() + n_extra, if args.len() + n_extra == 1 { "was" } else { "were" }, help));
        }
        if let (Some(x), Some(&pt)) = (extra, ps.get(args.len() + 1)) {
            let pt = self.norm(pt);
            self.coerce_or_unify(x, pt, None, lo);
        }
        // rustc expected_inputs_for_expected_output, as for calls: the expected result type
        // (`let _: Option<fn()> = Foo.foo(main)`) gives the arguments' expected types; a sized
        // one is coerced to, then the formal type must equal it
        // Per input (rustc keeps the resolved formal inputs as expectations; an input that still
        // holds the callee's own variables is no hint): `opt.map_or(&[], |x| x.list())` into
        // `&[String]` checks `&[]` against `&[String]`, then unsizes `&[String; 0]`. The formal
        // output may be the method's own parameter (`U` of map_or) when the expectation is a
        // known type.
        let exp_inputs = self.method_expected_inputs(ret, &ps, method_expected);
        self.check_method_args(item, &gargs, &ps, args, exp_inputs);
        self.apply_fn_bounds(item, &gargs, lo);
        // projections in the result normalize now that the call fixed the args (rustc
        // normalizes a method's output: `opt.as_deref()` is Option<&str>, not
        // Option<&<String as Deref>::Target>, so a pattern binding gets `&str`)
        self.normalize_signature(ret)
    }

    /// `a op b` on a non-primitive left operand: core::ops trait call, result `Output`.
    /// `a == b` / `a < b` on non-primitives: `PartialEq::eq(&a, &b)` / `PartialOrd::lt(..)`.
    /// None when no impl exists (tuples/arrays of primitives compare structurally).
    fn check_cmp_trait(&mut self, e: ExprId, op: BinOp, ta: TyId, b: ExprId, lo: u32, checked_b: Option<TyId>) -> Option<TyId> {
        let (tr, m) = match op {
            BinOp::Eq => ("PartialEq", "eq"),
            BinOp::Ne => ("PartialEq", "ne"),
            BinOp::Lt => ("PartialOrd", "lt"),
            BinOp::Le => ("PartialOrd", "le"),
            BinOp::Gt => ("PartialOrd", "gt"),
            _ => ("PartialOrd", "ge"),
        };
        let td = self.lang_item(&["cmp", tr])?;
        let item = self.trait_fn(td, m)?;
        // integer/float literal variables stay open while the impl is selected (rustc falls
        // back to i32/f64 only at the end of type checking; a where-clause of the selected impl
        // may still fix them)
        let save_keep = self.keep_literal_vars;
        self.keep_literal_vars = true;
        let da = self.deep(ta);
        // the right operand's expected type: the single impl's Rhs, else Self
        // (rustc checks the right operand against a fresh variable: the left type is only a
        // hint here, and none when it names a generic param -- `x == &Unicode(y.as_ref())`
        // with x: &Unicode<S1> compares against Unicode<&str> through
        // `impl<S1, S2> PartialEq<Unicode<S2>> for Unicode<S1>`)
        // In an instance the left type is concrete but still no more than that: only an impl
        // selection that fixes `L: Cmp<?R>` gives the right operand a type (`Option<u64> ==
        // Some(10)`, one impl); several impls (`&A: PartialEq<&B>` / `<&mut B>`, String's) leave
        // it open, as rustc's fresh variable does -- `x == &Unicode(y.as_ref())` with x:
        // &Unicode<CowStr> is `Unicode<&str>`, not `Unicode<CowStr>` (op.rs check_overloaded_binop)
        let hint = if self.tcx.has_param(da) {
            None
        } else {
            let rhs = self.fresh(0);
            let mark = self.snapshot();
            let hint = match self.select_trait(td, da, &[rhs]) {
                SelectionResult::Ok(_) => {
                    let h = self.deep(rhs);
                    if self.tcx.tys.has_infer(h) { None } else { Some(h) }
                }
                SelectionResult::Ambiguous(_) => None,
                SelectionResult::NoSolution => Some(ta),
            };
            self.rollback(mark);
            hint
        };
        let tb = match checked_b {
            Some(t) => t,
            None => self.check_expr(b, hint),
        };
        let db = self.deep(tb);
        self.keep_literal_vars = save_keep;
        let selection = self.select_trait(td, da, &[db]);
        let rhs = if let SelectionResult::Ok(selected) = selection {
                    let (imp, _) = (selected.method_owner(), selected.args);
            // selecting the impl equates its trait ref with the obligation's and registers its
            // where-clauses (rustc confirm_impl_candidate): `Option<u64> == Some(10)` makes the
            // literal u64, `Vec<u16> == [5, 6]` needs `u16: PartialEq<?U>`, fixing U
            if imp == crate::tcx::DERIVED_IMPL {
                self.unify(db, da);
            } else if imp != crate::program::NO_DEF && self.tcx.tys.has_infer(db) {
                if trace_bounds() {
                    let (x, y) = (self.ty_str(da), self.ty_str(db));
                    eprintln!("bounds: cmp {} vs {} impl {}", x, y, self.prog.def_path(imp));
                }
                let save = self.snapshot();
                match self.unify_impl_trait_ref(imp, td, da, &[db]) {
                    Some(iargs) => {
                        if self.tcx.impl_trait_bounds.contains_key(&imp) {
                            self.apply_impl_predicates(imp, &iargs);
                            self.infer_from_bounds(imp, &iargs);
                        }
                    }
                    None => self.rollback(save),
                }
            }
            db
        } else if matches!(selection, SelectionResult::Ambiguous(_)) {
            db
        } else if !matches!(self.select_trait(td, da, &[da]), SelectionResult::NoSolution) {
            self.coerce_or_unify(tb, ta, Some(b), lo);
            da
        } else {
            let (x, y) = (self.ty_str(da), self.ty_str(db));
            self.err(lo, format!("no `{}` impl to compare `{}` with `{}` -- derive or impl {}", tr, x, y, tr));
            return Some(self.tcx.tys.bool_);
        };
        self.b.binops.insert(e.0, MethodRes { def: item, derefs: 0, autoref: 1, args: vec![da, rhs] });
        Some(self.tcx.tys.bool_)
    }

    /// `a op b` (or `a op= b` with `assign`) through core::ops::<Op>[Assign]
    /// `!x` / `-x` on a type with a `Not` / `Neg` impl (not a primitive): the trait call,
    /// recorded like a binary operator (`binops`, one argument).
    fn check_unop_trait(&mut self, e: ExprId, t: TyId, tr: &str, m: &str) -> Option<TyId> {
        // (a param / rigid projection with a `Neg` / `Not` bound in a generic body too)
        match self.tcx.tys.kind(t) {
            TyKind::Adt(..) | TyKind::Param(_) | TyKind::Assoc(..) => {}
            _ => return None,
        }
        let td = self.lang_item(&["ops", tr])?;
        match self.select_trait(td, t, &[]) { SelectionResult::Ok(_) | SelectionResult::Ambiguous(_) => {}, SelectionResult::NoSolution => return None };
        let ms = self.prog.syms.get(m)?;
        let item = self.prog.traits[self.prog.def(td).sub as usize].iter().copied().find(|&it| self.prog.def(it).name == ms)?;
        let args = vec![t];
        self.b.binops.insert(e.0, MethodRes { def: item, derefs: 0, autoref: 0, args: args.clone() });
        let sig = self.tcx.fn_sig(self.prog, item).cloned()?;
        let r = self.tcx.tys.subst_for_inference(sig.ret, &args);
        Some(self.norm(r))
    }

    fn check_op_trait(&mut self, op: BinOp, ta: TyId, b: ExprId, lo: u32, assign: bool) -> TyId {
        let (tr0, m0) = match op {
            BinOp::Add => ("Add", "add"),
            BinOp::Sub => ("Sub", "sub"),
            BinOp::Mul => ("Mul", "mul"),
            BinOp::Div => ("Div", "div"),
            BinOp::Rem => ("Rem", "rem"),
            BinOp::BitAnd => ("BitAnd", "bitand"),
            BinOp::BitOr => ("BitOr", "bitor"),
            BinOp::BitXor => ("BitXor", "bitxor"),
            BinOp::Shl => ("Shl", "shl"),
            BinOp::Shr => ("Shr", "shr"),
            _ => ("", ""),
        };
        let (trs, ms_) = if assign { (format!("{}Assign", tr0), format!("{}_assign", m0)) } else { (tr0.to_string(), m0.to_string()) };
        let (tr, m) = (trs.as_str(), ms_.as_str());
        let error = self.tcx.tys.error;
        let me = self.cur_binop;
        let td = match self.lang_item(&["ops", tr]) {
            Some(d) => d,
            None => {
                self.err(lo, format!("core::ops::{} not found", tr));
                return error;
            }
        };
        let rhs = self.fresh(0);
        let mark = self.snapshot();
        let exp_b = match self.select_trait(td, ta, &[rhs]) {
            SelectionResult::Ok(_) => {
                let hint = self.deep(rhs);
                if self.tcx.tys.has_infer(hint) { None } else { Some(hint) }
            }
            SelectionResult::Ambiguous(_) | SelectionResult::NoSolution => None,
        };
        self.rollback(mark);
        let mut tb = self.check_expr(b, exp_b);
        if let Some(x) = exp_b {
            // the right operand is a coercion site for the impl's Rhs (`s + &string`: &String
            // -> &str); the operator's argument is the coerced value
            if self.coerce_or_unify(tb, x, Some(b), lo) {
                tb = x;
            }
        }
        self.op_trait_call(td, m, me, ta, tb, lo)
    }

    /// The operator trait call `<ta as Op<tb>>::m` (operands already checked).
    fn op_trait_call(&mut self, td: DefId, m: &str, me: u32, ta: TyId, tb: TyId, lo: u32) -> TyId {
        let error = self.tcx.tys.error;
        let tr = self.prog.name(td).to_string();
        let tb = self.deep(tb);
        let ms = self.prog.syms.get(m).unwrap_or(u32::MAX);
        let mut item = None;
        for &it in &self.prog.traits[self.prog.def(td).sub as usize] {
            if self.prog.def(it).name == ms {
                item = Some(it);
            }
        }
        let item = match item {
            Some(i) => i,
            None => return error,
        };
        let ta = self.deep(ta);
        if matches!(self.select_trait(td, ta, &[tb]), SelectionResult::NoSolution) {
            let (x, y) = (self.ty_str(ta), self.ty_str(tb));
            self.err(lo, format!("no `{}` impl for `{}` and `{}`", tr, x, y));
            return error;
        }
        let args = vec![ta, tb];
        self.b.binops.insert(me, MethodRes { def: item, derefs: 0, autoref: 0, args: args.clone() });
        let sig = self.tcx.fn_sig(self.prog, item).cloned().unwrap();
        let r = self.tcx.tys.subst_for_inference(sig.ret, &args);
        self.norm(r)
    }

    /// `prim op adt`: the operator trait impl of the primitive for the right type. A literal
    /// left operand takes the type of the single primitive impl with that right type.
    fn prim_lhs_op(&mut self, op: BinOp, e: ExprId, sa: TyId, sb: TyId, lo: u32) -> Option<TyId> {
        let (tr, m) = match op {
            BinOp::Add => ("Add", "add"),
            BinOp::Sub => ("Sub", "sub"),
            BinOp::Mul => ("Mul", "mul"),
            BinOp::Div => ("Div", "div"),
            BinOp::Rem => ("Rem", "rem"),
            BinOp::BitAnd => ("BitAnd", "bitand"),
            BinOp::BitOr => ("BitOr", "bitor"),
            BinOp::BitXor => ("BitXor", "bitxor"),
            _ => return None,
        };
        let td = self.lang_item(&["ops", tr])?;
        let db = self.deep(sb);
        if !self.is_numeric(sa) && !matches!(self.tcx.tys.kind(sa), TyKind::Infer(_)) { return None; }
        if matches!(self.select_trait(td, sa, &[db]), SelectionResult::NoSolution) { return None; }
        Some(self.op_trait_call(td, m, e.0, sa, db, lo))
    }

    #[allow(clippy::too_many_arguments)]
    /// rustc expected_inputs_for_expected_output for a method call: per input, the type the
    /// expected result gives it (None: no hint). See check_method_sym.
    fn method_expected_inputs(&mut self, ret: TyId, ps: &[TyId], method_expected: Option<TyId>) -> Option<Vec<Option<TyId>>> {
        let mut exp_inputs: Option<Vec<Option<TyId>>> = None;
        if let Some(x) = method_expected {
            let (rs, xs) = (self.shallow(ret), self.shallow(x));
            let rs_open = matches!(self.tcx.tys.kind(rs), TyKind::Infer(_)) && !self.is_literal_var(rs);
            let xs_known = !matches!(self.tcx.tys.kind(xs), TyKind::Infer(_) | TyKind::Error);
            if (matches!(self.tcx.tys.kind(rs), TyKind::Adt(..)) && matches!(self.tcx.tys.kind(xs), TyKind::Adt(..))) || (rs_open && xs_known) {
                let mut exp_vars = Vec::new();
                let xd = self.deep(xs);
                self.free_vars(xd, &mut exp_vars);
                let save = self.snapshot();
                if self.unify(ret, x) {
                    let ins: Vec<TyId> = ps.iter().skip(1).map(|p| self.resolve_region_vars(*p)).collect();
                    let mut v = Vec::with_capacity(ins.len());
                    for t in &ins {
                        let mut fv = Vec::new();
                        self.free_vars(*t, &mut fv);
                        v.push(if fv.iter().all(|x| exp_vars.contains(x)) && !self.is_unsized_ty(*t) { Some(*t) } else { None });
                    }
                    exp_inputs = Some(v);
                }
                self.rollback(save);
            }
        }
        exp_inputs
    }

    /// The arguments of a method call (receiver excluded), checked against their expected
    /// inputs when the expected result gave them, else against the formal types.
    fn check_method_args(&mut self, item: DefId, gargs: &[TyId], ps: &[TyId], args: &[ExprId], exp_inputs: Option<Vec<Option<TyId>>>) {
        let error = self.tcx.tys.error;
        // rustc check_argument_types: non-closures first, then select their obligations
        // before deriving closure signatures from the call's Fn bounds.
        for check_closures in [false, true] {
            if check_closures {
                self.select_before_closures(Some((item, gargs)));
            }
            for (i, a) in args.iter().enumerate() {
                if matches!(self.ast().expr(*a).kind, ExprKind::Closure { .. }) != check_closures {
                    continue;
                }
                let pt = if i + 1 < ps.len() { ps[i + 1] } else { error };
                if let Some(ei) = exp_inputs.as_ref().and_then(|v| v.get(i).copied().flatten()) {
                    // a closure takes its signature from the registered bound unless the
                    // expected input is a fn pointer: then from that, and it coerces to it
                    // (`.filter(|(_, c)| ..)` into `Filter<_, fn(&(usize, &str)) -> bool>`)
                    let to_fn_ptr = matches!(self.tcx.tys.kind(self.shallow(ei)), TyKind::FnPtr(..));
                    if to_fn_ptr || !matches!(self.ast().expr(*a).kind, ExprKind::Closure { .. }) {
                        let t = self.check_expr(*a, Some(ei));
                        let snap = self.snapshot();
                        if self.try_coerce(t, ei, Some(*a)) && self.unify(pt, ei) {
                            continue;
                        }
                        self.rollback(snap);
                        self.coerce_or_unify(t, pt, Some(*a), self.ast().expr(*a).lo);
                        continue;
                    }
                }
                let xt = self.normalize_signature(pt);
                let t = self.check_expr(*a, Some(xt));
                self.select_before_coerce(item, gargs, pt);
                self.coerce_or_unify(t, pt, Some(*a), self.ast().expr(*a).lo);
            }
        }
    }

    fn check_trait_method_call(&mut self, e: ExprId, item: DefId, imp: DefId, self_ty: TyId, derefs: u8, turbofish: GenericArgsId, args: &[ExprId], lo: u32, method_expected: Option<TyId>) -> TyId {
        let error = self.tcx.tys.error;
        let mut tf = Vec::new();
        if let Some(GenericArgs::Angle(v)) = self.ast().gargs(turbofish) {
            for g in self.ast().list(*v) {
                if let Some(lt) = self.generic_arg(g) {
                    tf.push(lt);
                }
            }
        }
        let gargs = self.trait_call_args(item, imp, self_ty, &tf);
        // trait args fixed by a generic bound (bound_method): `AsRef<OsStr>`
        if let Some(ta) = self.known_targs.take() {
            for (i, t) in ta.iter().enumerate() {
                if let Some(&g) = gargs.get(1 + i) {
                    self.unify(g, *t);
                }
            }
        }
        let sig = self.tcx.fn_sig(self.prog, item).cloned().unwrap();
        let autoref = match self.forced_autoref.take() {
            Some(a) => a,
            None => match sig.self_kind {
                2 => 1,
                3 => 2,
                _ => 0,
            },
        };
        self.b.dependencies.push(item);
        self.b.methods.insert(e.0, MethodRes { def: item, derefs, autoref, args: gargs.clone() });
        let (ps, r) = self.instantiate_call_signature(item, &gargs, &sig);
        let ps: Vec<_> = ps.into_iter().map(|t| self.normalize_signature(t)).collect();
        let extra = self.extra_arg.take();
        let n_extra = extra.is_some() as usize;
        if ps.len() != args.len() + 1 + n_extra {
            let want = ps.len().saturating_sub(1);
            let help = if n_extra == 0 { let rest: Vec<TyId> = ps.iter().skip(1).copied().collect(); self.arg_count_help(Some(item), &rest, args, 0) } else { String::new() };
            self.err(lo, format!("E0061: this method takes {} argument{} but {} {} supplied{}", want, if want == 1 { "" } else { "s" }, args.len() + n_extra, if args.len() + n_extra == 1 { "was" } else { "were" }, help));
        }
        if let (Some(x), Some(&pt)) = (extra, ps.get(args.len() + 1)) {
            self.coerce_or_unify(x, pt, None, lo);
        }
        // the probe reads the formal result as written: normalizing it before the arguments are
        // checked would select an impl for a projection whose trait args are still open
        // (`allocs.index(heading_ix)` with several Index impls)
        let exp_inputs = if method_expected.is_some() { self.method_expected_inputs(r, &ps, method_expected) } else { None };
        self.check_method_args(item, &gargs, &ps, args, exp_inputs);
        // several impls of the trait for the self type and its args still open (`v.extend(it)`
        // on Vec<String>: Extend<String> and Extend<&String>): the impls whose where-clauses
        // can hold (`T: Copy` rules out the second) -- one left fixes the args (rustc selects
        // once a single candidate remains)
        if imp == crate::program::NO_DEF {
            // the expected type comes first (rustc unifies the expectation before it selects:
            // `SetCursor(cursor.into())` with `impl Into<Shape> for MouseCursor` and the blanket
            // `Into<U> for T where U: From<T>`): a result that is an open trait arg takes a
            // plain expected type
            if let Some(x) = method_expected {
                let (rs, xs) = (self.shallow(r), self.shallow(x));
                let plain = matches!(self.tcx.tys.kind(xs), TyKind::Adt(..) | TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Tuple(_) | TyKind::Array(..)) && !self.has_dyn(xs);
                if plain && matches!(self.tcx.tys.kind(rs), TyKind::Infer(_)) && !self.is_literal_var(rs) && gargs[1..].contains(&rs) {
                    let save = self.snapshot();
                    if !self.unify(rs, xs) {
                        self.rollback(save);
                    }
                }
            }
        }
        // A probe only establishes that the trait may hold, even when it found
        // one impl. Confirm the pick by retaining its trait obligation (nightly
        // rustc_hir_typeck/src/method/probe.rs:2142-2144, confirm.rs:632-647).
        self.register_method_obligation(item, &gargs);
        self.apply_fn_bounds(item, &gargs, lo);
        let _ = error;
        self.normalize_signature(r)
    }

    fn register_method_obligation(&mut self, item: DefId, gargs: &[TyId]) {
        let td = self.prog.def(item).parent;
        if self.prog.def(td).kind != DefKind::Trait || gargs.is_empty() { return; }
        let n = self.tcx.trait_generic_count(self.prog, td);
        if gargs.len() >= n + 1 {
            let goal = crate::solve::select::trait_goal(&self.cx, td, gargs[0], &gargs[1..=n]);
            self.register_goal(goal, self.last_lo);
        }
    }

    /// `norm` that leaves unresolved literal variables open.
    fn norm_keep(&mut self, t: TyId) -> TyId {
        let save = self.keep_literal_vars;
        self.keep_literal_vars = true;
        let r = self.norm(t);
        self.keep_literal_vars = save;
        r
    }

    /// Impl-driven inference: a generic arg bounded by `T: Trait<Args>` whose type is partly
    /// known (`Vec<?0>`) and has exactly one matching impl takes that impl's shape
    /// (`collect::<Vec<_>>()` gets `?0 = Item` from `impl<T> FromIterator<T> for Vec<T>`).
    fn infer_from_bounds(&mut self, d: DefId, gargs: &[TyId]) {
        let options = &self.prog.session.options;
        // measurement switch for the dialect re-evaluation (impl-driven / backward inference)
            if options.no_bound_infer {
            return;
        }
        // a fn's bounds, or a selected impl's where-clauses (its args are `gargs`)
        let bounds = match self.tcx.fn_trait_bounds(self.prog, d) {
            Some(b) => b.clone(),
            None => self.tcx.impl_trait_bounds.get(&d).cloned().unwrap_or_default(),
        };
        // literal variables are still open here (`get(&5)` learns u32 from `K: Borrow<Q>`)
        let save_keep = self.keep_literal_vars;
        self.keep_literal_vars = true;
        self.infer_from_bounds_inner(gargs, bounds);
        // where-clauses on other types (`where [T]: Concat<Item>`): their self type as an
        // extra argument
        if let Some(tyb) = self.tcx.fn_ty_bounds(self.prog, d).cloned() {
            for (st, td, targs) in tyb {
                let mut g2 = gargs.to_vec();
                let s2 = self.tcx.tys.subst_for_inference(st, gargs);
                g2.push(s2);
                self.infer_from_bounds_inner(&g2, vec![(gargs.len() as u32, td, targs)]);
            }
        }
        // `I: IntoIterator<Item = D>` with I known: D = <I as IntoIterator>::Item
        if let Some(binds) = self.tcx.fn_bound_bindings(self.prog, d).cloned() {
            for (pi, ad, targs, pat) in binds {
                let t = match gargs.get(pi as usize) {
                    Some(t) => self.shallow(*t),
                    None => continue,
                };
                if matches!(self.tcx.tys.kind(t), TyKind::Infer(_) | TyKind::Error) {
                    continue;
                }
                let want = self.tcx.tys.subst_for_inference(pat, gargs);
                let want = self.norm_keep(want);
                // either side may learn: `D` from I, or I's open literals from D
                // (`total::<I: Iterator<Item = u32>>(vec![1, 2].into_iter())` makes them u32)
                let mut pargs = vec![self.deep(t)];
                for x in &targs {
                    let y = self.tcx.tys.subst_for_inference(*x, gargs);
                    pargs.push(self.deep(y));
                }
                let proj = self.tcx.tys.intern(TyKind::Assoc(ad, pargs, crate::types::RegionArgsId::EMPTY));
                let goal = crate::solve::goal::Goal {
                    param_env: crate::solve::goal::ParamEnvId(self.cx.typing_env.param_env.index()),
                    predicate: crate::solve::goal::Predicate::AliasRelate(crate::solve::goal::Term::Ty(proj), crate::solve::goal::Term::Ty(want), crate::solve::goal::AliasRelationDirection::Equate),
                };
                self.register_goal(goal, self.last_lo);
            }
        }
        if self.prog.def(d).kind == DefKind::Impl { self.apply_impl_predicates(d, gargs); }
        self.keep_literal_vars = save_keep;
    }

    fn infer_from_bounds_inner(&mut self, gargs: &[TyId], bounds: Vec<(u32, DefId, Vec<TyId>)>) {
        for (index, td, args) in bounds {
            let Some(&self_ty) = gargs.get(index as usize) else { continue; };
            let mut inputs = Vec::new();
            for arg in args { inputs.push(self.tcx.tys.subst_for_inference(arg, gargs)); }
            let inputs = self.tcx.fill_trait_defaults(&self.cx, self.prog, td, self_ty, inputs);
            let goal = crate::solve::select::trait_goal(&self.cx, td, self_ty, &inputs);
            self.register_goal(goal, self.last_lo);
        }
    }

    /// A selected impl's `F: Fn(A..) -> R` bounds: a closure (or fn item) bound to F has that
    /// signature, which fixes impl params only the Fn bound mentions (rustc: the impl's
    /// predicates become obligations; the closure's Fn impl unifies its signature).
    fn apply_impl_predicates(&mut self, imp: DefId, iargs: &[TyId]) {
        let cx = self.cx.body();
        let goals = crate::solve::select::impl_goals(self.tcx, &cx, self, imp, iargs);
        for goal in goals { self.register_goal(goal, self.last_lo); }
    }

    /// Unifies impl `imp`'s trait ref (self type `t`, trait args with defaults filled:
    /// `impl PartialEq for u32` is PartialEq<u32>) with the wanted trait args.
    fn unify_impl_trait_ref(&mut self, imp: DefId, td: DefId, t: TyId, wants: &[TyId]) -> Option<Vec<TyId>> {
        let iargs = self.match_impl_args(imp, t);
        let itargs = self.tcx.impl_trait_args.get(&imp).cloned().unwrap_or_default();
        let st = self.tcx.impl_self.get(&imp).copied().unwrap_or(t);
        let itargs = self.tcx.fill_trait_defaults(&self.cx, self.prog, td, st, itargs);
        let mut ok = true;
        for (j, ita) in itargs.iter().enumerate() {
            if j >= wants.len() {
                break;
            }
            let have = self.tcx.tys.subst_for_inference(*ita, &iargs);
            let have = self.norm_keep(have);
            if !self.unify(have, wants[j]) {
                if trace_bounds() {
                    let (x, y) = (self.ty_str(have), self.ty_str(wants[j]));
                    eprintln!("bounds:   trait arg {} does not unify with {}", x, y);
                }
                ok = false;
            }
        }
        if ok {
            Some(iargs)
        } else {
            None
        }
    }

    /// Select the call's bounds (including APIT associated-type bindings) and obligations
    /// from already checked arguments before checking closure bodies. Unresolved obligations
    /// stay pending; this is opportunistic selection, without literal fallback.
    fn select_before_closures(&mut self, callee: Option<(DefId, &[TyId])>) {
        if let Some((d, gargs)) = callee {
            self.infer_from_bounds(d, gargs);
        }
        self.retry_goals(false);
        self.flush_projection_relations();
    }

    /// Before an argument coerces to a formal type that still has inference variables, the
    /// call's bounds are selected where possible (rustc check_argument_types: the coercion
    /// target goes through resolve_vars_with_obligations -> select_obligations_where_possible).
    /// `set.contains(&k)` with k: &u64 and `T: Borrow<Q>`: the one impl `Borrow<T> for T` makes
    /// Q = u64 first, so `&&u64` coerces to `&u64` by deref instead of fixing Q = &u64.
    fn select_before_coerce(&mut self, d: DefId, gargs: &[TyId], pt: TyId) {
        let x = self.deep(pt);
        if self.tcx.tys.has_infer(x) && (self.tcx.fn_trait_bounds(self.prog, d).is_some() || self.tcx.fn_ty_bounds(self.prog, d).is_some()) {
            self.infer_from_bounds(d, gargs);
        }
    }

    /// After the arguments are checked: callables bound to `F: Fn(A) -> R` params must
    /// have that signature (infers `R`-like generic args from closures and fn items).
    fn apply_fn_bounds(&mut self, d: DefId, gargs: &[TyId], lo: u32) {
        self.infer_from_bounds(d, gargs);
        use crate::solve::goal::{Clause, Predicate, Term};
        let clauses = self.tcx.item_clauses(self.prog, d).cloned().unwrap_or_default();
        for clause in clauses {
            let predicate = match clause {
                Clause::Trait(mut p) => {
                    for t in &mut p.trait_ref.args { *t = self.tcx.tys.subst_for_inference(*t, gargs); }
                    Predicate::Clause(Clause::Trait(p))
                }
                Clause::Projection(mut p) => {
                    for t in &mut p.alias.args { *t = self.tcx.tys.subst_for_inference(*t, gargs); }
                    if let Term::Ty(t) = &mut p.term { *t = self.tcx.tys.subst_for_inference(*t, gargs); }
                    Predicate::Clause(Clause::Projection(p))
                }
                _ => continue,
            };
            let goal = crate::solve::goal::Goal { param_env: crate::solve::goal::ParamEnvId(self.cx.typing_env.param_env.index()), predicate };
            self.register_goal(goal, lo);
        }
    }

    fn select_unspecified_trait(&mut self, td: DefId, ty: TyId) -> SelectionResult {
        let mut args = Vec::new();
        for _ in 0..self.tcx.trait_generic_count(self.prog, td) { args.push(self.fresh(0)); }
        self.select_trait(td, ty, &args)
    }

    fn select_trait(&mut self, td: DefId, ty: TyId, args: &[TyId]) -> SelectionResult {
        use crate::solve::goal::{Clause, Predicate, Certainty};
        let cx = self.cx.body();
        let goal = crate::solve::select::trait_goal(&cx, td, ty, args);
        let Predicate::Clause(Clause::Trait(predicate)) = goal.predicate.clone() else { unreachable!() };
        let mark = self.snapshot();
        let mut result = crate::solve::select::select(self.tcx, &cx, self, predicate);
        if let SelectionResult::Ok(selected) = &result {
            let mut pending = Vec::new();
            let mut failed = false;
            for goal in &selected.nested {
                match crate::solve::evaluate(self.tcx, &cx, self, goal.clone()) {
                    Ok(Certainty::Yes) => {}
                    Ok(certainty) => pending.push((goal.clone(), certainty)),
                    Err(_) => { failed = true; break; }
                }
            }
            if failed { result = SelectionResult::NoSolution; }
            else { for (goal, certainty) in pending { self.push_pending_goal(goal, self.last_lo, certainty); } }
        }
        match &result {
            SelectionResult::Ok(_) => {},
            SelectionResult::NoSolution => self.rollback(mark),
            SelectionResult::Ambiguous(cause) => {
                self.rollback(mark);
                if !self.pending_goals.iter().any(|p| p.goal == goal) {
                    self.push_pending_goal(goal, self.last_lo, Certainty::Maybe(*cause));
                }
            }
        }
        result
    }

    fn goal_string(&mut self, goal: &crate::solve::goal::Goal) -> String {
        use crate::solve::goal::{Clause, Predicate, Term};
        match &goal.predicate {
            Predicate::Clause(Clause::Trait(p)) => {
                let mut args = Vec::new();
                for t in &p.trait_ref.args { args.push(self.ty_str(*t)); }
                format!("{}<{}>", self.prog.def_path(p.trait_ref.def), args.join(", "))
            }
            Predicate::Clause(Clause::Projection(p)) => {
                let projection = self.tcx.tys.intern(TyKind::Assoc(p.alias.def, p.alias.args.clone(), crate::types::RegionArgsId::EMPTY));
                let Term::Ty(t) = p.term else { return format!("{:?}", goal); };
                let a = self.ty_str(projection); let b = self.ty_str(t);
                format!("{a} == {b}")
            }
            Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), _) => {
                let a = self.ty_str(*a); let b = self.ty_str(*b); format!("{a} == {b}")
            }
            _ => format!("{:?}", goal.predicate),
        }
    }

    fn push_pending_goal(&mut self, goal: crate::solve::goal::Goal, lo: u32, certainty: crate::solve::goal::Certainty) {
        self.push_pending(PendingGoal { goal, lo, certainty, stalled: None });
    }

    fn push_pending(&mut self, pending: PendingGoal) {
        for p in &self.pending_goals { if p.goal == pending.goal { return; } }
        self.pending_goals.push(pending);
        self.undo.push((u32::MAX - 1, VarSt::Free(0), UniverseIndex::ROOT));
    }

    fn register_goal(&mut self, goal: crate::solve::goal::Goal, lo: u32) {
        use crate::solve::goal::Certainty;
        let cx = self.cx.body();
        let goal = self.resolve_pending_goal(goal);
        let revision = self.tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire);
        for p in &self.pending_goals { if p.is_stalled(&goal, revision) { return; } }
        match crate::solve::evaluate(self.tcx, &cx, self, goal.clone()) {
            Ok(Certainty::Yes) => {}
            Ok(certainty) => {
                self.push_pending(PendingGoal { goal: goal.clone(), lo, certainty, stalled: Some((goal, revision)) });
            }
            Err(_) => {
                let message = self.goal_string(&goal); self.err(lo, format!("E0277: unsatisfied obligation {message}"));
            },
        }
    }

    fn resolve_pending_goal(&mut self, mut goal: crate::solve::goal::Goal) -> crate::solve::goal::Goal {
        use crate::solve::goal::*;
        match &mut goal.predicate {
            Predicate::Clause(Clause::Trait(p)) => for t in &mut p.trait_ref.args { *t = self.deep(*t); },
            Predicate::Clause(Clause::Projection(p)) => {
                for t in &mut p.alias.args { *t = self.deep(*t); }
                if let Term::Ty(t) = &mut p.term { *t = self.deep(*t); }
            }
            Predicate::AliasRelate(Term::Ty(a), Term::Ty(b), _) => { *a = self.deep(*a); *b = self.deep(*b); }
            _ => {}
        }
        goal
    }

    /// Service type_of_opaque dependencies after selection has unwound its probes
    /// (rustc_trait_selection/src/traits/select/mod.rs:2432-2437). Active bodies
    /// remain stalled until their own publication advances trait_input_revision.
    fn request_hidden_types(&self) {
        let requests = std::mem::take(&mut *self.cx.state.opaque_requests.borrow_mut());
        for opaque in requests { hidden_of(&self.cx, self.prog, self.tcx, opaque); }
    }

    fn retry_goals(&mut self, final_: bool) {
        use crate::solve::goal::Certainty;
        let cx = self.cx.body();
        self.request_hidden_types();
        for _ in 0..128 {
            let before = self.tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire);
            self.undo.retain(|u| u.0 != u32::MAX - 1);
            let pending = std::mem::take(&mut self.pending_goals);
            let mut progress = false;
            for mut pending in pending {
                let goal = self.resolve_pending_goal(pending.goal.clone());
                let revision = self.tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire);
                if pending.is_stalled(&goal, revision) {
                    pending.goal = goal;
                    self.push_pending(pending);
                    continue;
                }
                match crate::solve::evaluate(self.tcx, &cx, self, goal.clone()) {
                    Ok(Certainty::Yes) => { progress = true; }
                    Ok(certainty) => self.push_pending(PendingGoal { goal: goal.clone(), lo: pending.lo, certainty, stalled: Some((goal, revision)) }),
                    Err(_) => { let message = self.goal_string(&goal); self.err(pending.lo, format!("E0277: unsatisfied obligation {message}")); progress = true; },
                }
            }
            for pending in self.pending_goals.clone() {
                progress |= self.resolve_pending_goal(pending.goal.clone()) != pending.goal;
            }
            self.request_hidden_types();
            progress |= self.tcx.trait_input_revision.load(std::sync::atomic::Ordering::Acquire) != before;
            if !progress || self.pending_goals.is_empty() { break; }
        }
        if final_ {
            self.undo.retain(|u| u.0 != u32::MAX - 1);
            let pending = std::mem::take(&mut self.pending_goals);
            // rustc_trait_selection/src/error_reporting/traits/ambiguity.rs:228,
            // 345, 576: do not report inference fallout in an already erroneous body.
            if self.b.errors.is_empty() {
                for pending in pending {
                    let message = self.goal_string(&pending.goal);
                    if matches!(pending.certainty, Certainty::Maybe(crate::solve::goal::MaybeCause::Overflow { .. })) {
                        self.err(pending.lo, format!("E0275: overflow evaluating the requirement {message}"));
                    } else {
                        self.err(pending.lo, format!("E0283: ambiguous obligation {message} ({:?})", pending.certainty));
                    }
                }
            }
        }
    }

    // ------------------------------------------------------------ macros

    fn check_mac(&mut self, e: ExprId, m: &MacCall, expected: Option<TyId>, lo: u32) -> TyId {
        let ast = self.ast();
        let name = match ast.segs(m.path.segs).last() {
            Some(s) => self.text(s.name),
            None => "",
        };
        let unit = self.tcx.tys.unit;
        let never = self.tcx.tys.never;
        let bool_ = self.tcx.tys.bool_;
        if name == "cfg" {
            return bool_;
        }
        // `compile_error!("msg")` (what a failed built-in or derive leaves at its call): the
        // message is the error, as rustc reports it
        // Relax has no assembler (user decision 2026-10-05): core::arch intrinsics instead
        if matches!(name, "asm" | "global_asm" | "naked_asm") {
            self.err(lo, "inline assembly is not supported; use core::arch intrinsics".to_string());
            return self.tcx.tys.error;
        }
        if name == "compile_error" && m.toks.hi > m.toks.lo {
            let f = &self.prog.files[self.file as usize];
            let msg = crate::lit::unescape_str(f.tok_text(m.toks.lo));
            self.err(lo, msg);
            return never;
        }
        if m.args == NO_MAC_ARGS {
            self.err(lo, format!("macro `{}!` is not supported", name));
            return self.tcx.tys.error;
        }
        let margs = ast.mac_arg(m.args);
        let mexprs = ast.list(margs.exprs);
        match name {
            "assert" | "debug_assert" => {
                if let Some(&c) = mexprs.first() {
                    let t = self.check_expr(c, Some(bool_));
                    self.coerce_or_unify(t, bool_, None, lo);
                }
                self.check_fmt_args(e, &mexprs[1.min(mexprs.len())..]);
                self.diverges = false;
                unit
            }
            "assert_eq" | "assert_ne" | "debug_assert_eq" | "debug_assert_ne" => {
                if mexprs.len() >= 2 {
                    let ta = self.check_expr(mexprs[0], None);
                    let tb = self.check_expr(mexprs[1], Some(ta));
                    if !self.unify(ta, tb) {
                        let (sa, sb) = (self.ty_str(ta), self.ty_str(tb));
                        self.err(lo, format!("assert_eq of `{}` and `{}`", sa, sb));
                    }
                }
                self.check_fmt_args(e, &mexprs[2.min(mexprs.len())..]);
                self.diverges = false;
                unit
            }
            "print" | "println" | "eprint" | "eprintln" => {
                self.check_fmt_args(e, mexprs);
                unit
            }
            "panic" | "unreachable" | "todo" | "unimplemented" => {
                self.check_fmt_args(e, mexprs);
                never
            }
            "matches" => {
                if let (Some(&x), Some(p)) = (mexprs.first(), margs.pat) {
                    let t = self.check_expr(x, None);
                    let saved = self.scopes.len();
                    self.check_pat(p, t);
                    if let Some(g) = margs.guard {
                        self.check_expr(g, Some(bool_));
                    }
                    self.scopes.truncate(saved);
                }
                bool_
            }
            _ => {
                let _ = expected;
                self.err(lo, format!("macro `{}!` is not supported yet", name));
                for x in mexprs {
                    self.check_expr(*x, None);
                }
                self.tcx.tys.error
            }
        }
    }

    /// Format string + args: checks args and resolves inline `{name}` arguments.
    fn check_fmt_args(&mut self, e: ExprId, exprs: &[ExprId]) {
        if exprs.is_empty() {
            return;
        }
        let ast = self.ast();
        let first = exprs[0];
        let f = &self.prog.files[self.file as usize];
        let fe = ast.expr(first);
        if let ExprKind::Lit(LitKind::Str) | ExprKind::Lit(LitKind::RawStr) = fe.kind {
            let text = std::str::from_utf8(f.bytes(fe.lo, fe.hi)).unwrap_or("");
            let s = crate::lit::unescape_str(text);
            let pieces = crate::lit::parse_fmt(&s);
            for p in &pieces {
                if let crate::lit::FmtPiece::Arg { named: Some(n), .. } = p {
                    if let Some(sy) = self.prog.syms.get(n) {
                        match self.lookup_local(sy, fe.lo) {
                            Some(li) => {
                                self.b.fmt_named.insert((e.0, sy), Res::Local(li));
                            }
                            None => match self.prog.lookup_in_scope(self.module, sy, false) {
                                Some(d) => {
                                    self.b.fmt_named.insert((e.0, sy), Res::Def(d));
                                }
                                None => self.err(fe.lo, format!("cannot find `{}` for format string", n)),
                            },
                        }
                    } else {
                        self.err(fe.lo, format!("cannot find `{}` for format string", n));
                    }
                }
            }
            self.check_expr(first, None);
        } else {
            self.check_expr(first, None);
        }
        for x in &exprs[1..] {
            self.check_expr(*x, None);
        }
    }
}

/// Like ty_to_string with ADTs as full definition paths plus their crate and def id
/// (disambiguates "expected `LiveId`, found `LiveId`").
pub fn ty_to_string_paths(prog: &Program, tcx: &Tcx, t: TyId) -> String {
    match tcx.tys.kind(t) {
        TyKind::Adt(d, args, _) => {
            let krate = prog.syms.str(prog.crates[prog.def(*d).krate as usize].name);
            let mut s = format!("{}::{} (crate {}, def {})", krate, prog.def_path(*d), prog.def(*d).krate, d.0);
            if !args.is_empty() {
                let a: Vec<String> = args.iter().map(|x| ty_to_string_paths(prog, tcx, *x)).collect();
                s.push_str(&format!("<{}>", a.join(", ")));
            }
            s
        }
        TyKind::Ref(m, e, _) => format!("&{}{}", if *m { "mut " } else { "" }, ty_to_string_paths(prog, tcx, *e)),
        _ => ty_to_string(false, prog, tcx, t),
    }
}

/// `core::any::type_name` (rustc's printing: full paths, fn items as their path, closures as
/// `path::{{closure}}`, arguments recursively).
/// Levenshtein distance (bytes) between two names.
pub fn edit_distance(a: &str, b: &str) -> usize {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    for i in 1..=a.len() {
        let mut cur = vec![i; b.len() + 1];
        for j in 1..=b.len() {
            let c = if a[i - 1].eq_ignore_ascii_case(&b[j - 1]) { 0 } else { 1 };
            cur[j] = (prev[j] + 1).min(cur[j - 1] + 1).min(prev[j - 1] + c);
        }
        prev = cur;
    }
    prev[b.len()]
}

/// `-- import it: `use a::b::Name;`` when the program has items of that name (the paths that
/// exist, shortest first; at most 3), else nothing.
pub fn import_help(prog: &Program, module: u32, name: crate::program::Sym, ns_type: bool) -> String {
    let v = prog.import_suggestions(module, name, ns_type);
    match v.len() {
        0 => String::new(),
        1 => format!(" -- import it: `use {};`", v[0]),
        _ => format!(" -- it exists as {}", v.iter().take(3).map(|p| format!("`use {};`", p)).collect::<Vec<_>>().join(", ")),
    }
}

pub fn type_name(prog: &Program, tcx: &Tcx, t: TyId) -> String {
    let list = |v: &[TyId]| v.iter().map(|x| type_name(prog, tcx, *x)).collect::<Vec<_>>().join(", ");
    match tcx.tys.kind(t) {
        TyKind::Adt(d, args, _) => {
            let mut s = item_path(prog, tcx, *d);
            if !args.is_empty() {
                s.push_str(&format!("<{}>", list(args)));
            }
            s
        }
        TyKind::Tuple(v) => {
            if v.len() == 1 {
                format!("({},)", list(v))
            } else {
                format!("({})", list(v))
            }
        }
        TyKind::Array(e, n) => match crate::types::len_ty(*n) {
            Some(l) => format!("[{}; {}]", type_name(prog, tcx, *e), type_name(prog, tcx, l)),
            None => format!("[{}; {}]", type_name(prog, tcx, *e), n),
        },
        TyKind::Slice(e) => format!("[{}]", type_name(prog, tcx, *e)),
        TyKind::Ref(m, e, _) => format!("&{}{}", if *m { "mut " } else { "" }, type_name(prog, tcx, *e)),
        TyKind::Ptr(m, e) => format!("*{} {}", if *m { "mut" } else { "const" }, type_name(prog, tcx, *e)),
        TyKind::FnPtr(ps, r, header, _) => {
            let safety = if header.safety == Safety::Unsafe { "unsafe " } else { "" };
            let abi = if header.abi == Abi::Rust { String::new() } else { format!("extern \"{}\" ", header.abi.name()) };
            let mut params = list(ps);
            if header.c_variadic {
                if !params.is_empty() { params.push_str(", "); }
                params.push_str("...");
            }
            let unit = matches!(tcx.tys.kind(*r), TyKind::Tuple(v) if v.is_empty());
            if unit {
                format!("{}{}fn({})", safety, abi, params)
            } else {
                format!("{}{}fn({}) -> {}", safety, abi, params, type_name(prog, tcx, *r))
            }
        }
        TyKind::FnDef(d, args, _) => {
            let mut s = item_path(prog, tcx, *d);
            if !args.is_empty() {
                s.push_str(&format!("<{}>", list(args)));
            }
            s
        }
        TyKind::Closure(file, e, _, _, owner) => {
            // the enclosing fn's path, then one `{{closure}}` per closure / async block around
            // this one and itself (rustc: `krate::main::{{closure}}::{{closure}}` for an async
            // closure's future)
            let owner_def = match tcx.tys.kind(*owner) {
                TyKind::FnDef(d, _, _) => Some(*d),
                _ => None,
            };
            let mut s = match owner_def {
                Some(d) => item_path(prog, tcx, d),
                None => String::new(),
            };
            let mut depth = 1;
            if *e & crate::tcx::ASYNC_FN_BODY == 0 {
                if let (Some(d), Some(pf)) = (owner_def, prog.files.get(*file as usize)) {
                    let it = pf.ast.item(prog.def(d).item);
                    let me = pf.ast.expr(crate::ast::ExprId(*e));
                    let _ = it;
                    for i in prog.item_expr_ranges(*file, prog.def(d).item).into_iter().flat_map(|(a, b)| a..b) {
                        if i == *e || !pf.ast.has_expr(crate::ast::ExprId(i)) {
                            continue;
                        }
                        let x = pf.ast.expr(crate::ast::ExprId(i));
                        if matches!(x.kind, crate::ast::ExprKind::Closure { .. } | crate::ast::ExprKind::Async(..)) && x.lo <= me.lo && me.hi <= x.hi && (x.lo, x.hi) != (me.lo, me.hi) {
                            depth += 1;
                        }
                    }
                }
            }
            for _ in 0..depth {
                if !s.is_empty() {
                    s.push_str("::");
                }
                s.push_str("{{closure}}");
            }
            s
        }
        TyKind::Dyn(d, args, bindings, _, _, _, autos) => {
            let (head, autos) = dyn_trait_names(*d, autos, |a| item_path(prog, tcx, a));
            let mut s = format!("dyn {}", head);
            // the Fn family as rustc prints it: `Fn(u32) -> u32`
            let fn_family = matches!(prog.name(*d), "Fn" | "FnMut" | "FnOnce") && Some(prog.def(*d).krate) == prog.prelude_crate;
            match (fn_family, args.first().map(|a| tcx.tys.kind(*a))) {
                (true, Some(TyKind::FnPtr(ps, r, _, _))) => {
                    s.push_str(&format!("({})", list(ps)));
                    if !matches!(tcx.tys.kind(*r), TyKind::Tuple(v) if v.is_empty()) {
                        s.push_str(&format!(" -> {}", type_name(prog, tcx, *r)));
                    }
                }
                (true, Some(TyKind::Tuple(ps))) => {
                    s.push_str(&format!("({})", list(ps)));
                    if let Some((_, r, _)) = bindings.first() {
                        if !matches!(tcx.tys.kind(*r), TyKind::Tuple(v) if v.is_empty()) {
                            s.push_str(&format!(" -> {}", type_name(prog, tcx, *r)));
                        }
                    }
                }
                _ => {
                    if !args.is_empty() {
                        s.push_str(&format!("<{}>", list(args)));
                    }
                }
            }
            for a in autos {
                s.push_str(" + ");
                s.push_str(&a);
            }
            s
        }
        _ => ty_to_string(false, prog, tcx, t),
    }
}

/// A trait object's trait names as rustc prints them (pretty_print_dyn_existential): the
/// principal, then the auto traits sorted by path. An object of auto traits only stores its
/// first auto trait as the principal (`dyn Send + Sync`): all of them sort, the first leads.
fn dyn_trait_names(d: DefId, autos: &[DefId], path: impl Fn(DefId) -> String) -> (String, Vec<String>) {
    let auto_only = autos.contains(&d);
    let mut names: Vec<String> = autos.iter().filter(|a| auto_only || **a != d).map(|a| path(*a)).collect();
    names.sort();
    let head = if auto_only { names.remove(0) } else { path(d) };
    (head, names)
}

/// An item's path as rustc's type_name prints it: an item in a fn body is under that fn
/// (`krate::main::Wrapper`); a method's path goes through its impl's self type with the
/// impl's own parameters left open (`krate::Bar<_>::foo`).
pub fn item_path(prog: &Program, tcx: &Tcx, d: DefId) -> String {
    let def = prog.def(d);
    let name = prog.syms.str(def.name);
    // an item collected in a fn body's block module: the fn's path, then the item
    if let Some(&owner) = prog.block_owner.get(&def.scope) {
        if owner != d && matches!(def.kind, DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Fn | DefKind::Trait | DefKind::TypeAlias | DefKind::Const | DefKind::Static) && prog.def(def.parent).kind == DefKind::Mod {
            return format!("{}::{}", item_path(prog, tcx, owner), name);
        }
    }
    let parent = def.parent;
    if parent != crate::program::NO_DEF && prog.def(parent).kind == DefKind::Impl {
        if let Some(&st) = tcx.impl_self.get(&parent) {
            if let TyKind::Adt(sd, args, _) = tcx.tys.kind(st) {
                let mut s = item_path(prog, tcx, *sd);
                if !args.is_empty() {
                    s.push_str(&format!("<{}>", vec!["_"; args.len()].join(", ")));
                }
                return format!("{}::{}", s, name);
            }
        }
    }
    if parent != crate::program::NO_DEF && matches!(prog.def(parent).kind, DefKind::Trait | DefKind::Enum) {
        return format!("{}::{}", item_path(prog, tcx, parent), name);
    }
    prog.def_path(d)
}

pub fn ty_to_string(stable_closures: bool, prog: &Program, tcx: &Tcx, t: TyId) -> String {
    match tcx.tys.kind(t) {
        TyKind::Bool => "bool".to_string(),
        TyKind::Char => "char".to_string(),
        TyKind::Str => "str".to_string(),
        TyKind::Int(p) | TyKind::Float(p) => crate::types::Types::prim_name(*p).to_string(),
        TyKind::Never => "!".to_string(),
        TyKind::Tuple(v) => {
            let mut s = "(".to_string();
            for (i, x) in v.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                s.push_str(&ty_to_string(stable_closures, prog, tcx, *x));
            }
            if v.len() == 1 {
                s.push(',');
            }
            s.push(')');
            s
        }
        TyKind::Array(e, n) => match crate::types::len_ty(*n) {
            Some(l) => format!("[{}; {}]", ty_to_string(stable_closures, prog, tcx, *e), ty_to_string(stable_closures, prog, tcx, l)),
            None => format!("[{}; {}]", ty_to_string(stable_closures, prog, tcx, *e), n),
        },
        TyKind::ConstVal(v) => format!("{}", v),
        TyKind::Slice(e) => format!("[{}]", ty_to_string(stable_closures, prog, tcx, *e)),
        TyKind::Ref(m, e, _) => format!("&{}{}", if *m { "mut " } else { "" }, ty_to_string(stable_closures, prog, tcx, *e)),
        TyKind::Ptr(m, e) => format!("*{} {}", if *m { "mut" } else { "const" }, ty_to_string(stable_closures, prog, tcx, *e)),
        TyKind::Adt(d, args, _) => {
            let mut s = prog.name(*d).to_string();
            if !args.is_empty() {
                s.push('<');
                for (i, x) in args.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&ty_to_string(stable_closures, prog, tcx, *x));
                }
                s.push('>');
            }
            s
        }
        TyKind::FnPtr(ps, r, _, _) => {
            let mut s = "fn(".to_string();
            for (i, x) in ps.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                s.push_str(&ty_to_string(stable_closures, prog, tcx, *x));
            }
            s.push_str(") -> ");
            s.push_str(&ty_to_string(stable_closures, prog, tcx, *r));
            s
        }
        TyKind::FnDef(d, _, _) => format!("fn item {}", prog.def_path(*d)),
        TyKind::Param(i) => format!("T{}", i),
        TyKind::Infer(v) => format!("?{}", v),
        TyKind::Bound(d, b) => format!("^{}.{}:{:?}", d, b.var.0, b.kind),
        TyKind::Placeholder(p) => format!("!U{}.{}", p.universe.0, p.bound.0),
        TyKind::Closure(f, e, _, _, owner) => {
            if stable_closures {
                let owner = match tcx.tys.kind(*owner) {
                    TyKind::FnDef(d, _, _) => Some(*d),
                    _ => None,
                };
                crate::program::stable_closure_name(prog, *f, *e, owner)
            } else {
                format!("closure#{}", e)
            }
        }
        TyKind::Dyn(d, args, _, _, _, _, autos) => {
            let (head, autos) = dyn_trait_names(*d, autos, |a| prog.def_path(a));
            let mut s = format!("dyn {}", head);
            if !args.is_empty() {
                s.push('<');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }
                    s.push_str(&ty_to_string(stable_closures, prog, tcx, *a));
                }
                s.push('>');
            }
            for a in autos {
                s.push_str(" + ");
                s.push_str(&a);
            }
            s
        }
        TyKind::Assoc(d, args, _) => {
            let st = match args.first() {
                Some(t) => ty_to_string(stable_closures, prog, tcx, *t),
                None => "?".to_string(),
            };
            format!("<{} as {}>::{}", st, prog.name(prog.def(*d).parent), prog.name(*d))
        }
        TyKind::Opaque(d, i, _, _) => {
            let mut s = "impl ".to_string();
            if let Some(o) = tcx.opaques.get(&(*d, *i)) {
                for (k, (td, _)) in o.bounds.iter().enumerate() {
                    if k > 0 {
                        s.push_str(" + ");
                    }
                    s.push_str(prog.name(*td));
                }
            }
            s
        }
        TyKind::Error => "{error}".to_string(),
    }
}

pub fn key_of(tcx: &Tcx, t: TyId) -> TyKey {
    ty_key(&tcx.tys, t)
}

pub fn prim_of(tcx: &Tcx, t: TyId) -> Option<Prim> {
    match tcx.tys.kind(t) {
        TyKind::Int(p) | TyKind::Float(p) => Some(*p),
        TyKind::Bool => Some(Prim::Bool),
        TyKind::Char => Some(Prim::Char),
        _ => None,
    }
}

/// `..` or `name @ ..` (the rest of a slice pattern).
pub fn is_rest_pat(ast: &Ast, p: PatId) -> bool {
    match ast.pat(p) {
        Pat::Rest => true,
        Pat::Ident { sub: Some(s), .. } => matches!(ast.pat(*s), Pat::Rest),
        _ => false,
    }
}

/// RELAX_TRACE=bounds (read once: bound inference runs per call)
fn trace_bounds() -> bool {
    static T: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *T.get_or_init(|| std::env::var("RELAX_TRACE").map_or(false, |v| v.split(',').any(|x| x == "bounds")))
}

/// Walk a resolved type without allocating a set in the type-checker's hot path.
pub fn type_dependencies(tcx: &Tcx, ty: TyId, out: &mut Vec<DefId>) {
    fn walk(tcx: &Tcx, ty: TyId, out: &mut Vec<DefId>, depth: usize) {
        if depth > 64 { return; }
        match tcx.tys.kind(ty) {
            TyKind::Adt(d, a, _) | TyKind::FnDef(d, a, _) | TyKind::Assoc(d, a, _) | TyKind::Opaque(d, _, a, _) => {
                out.push(*d);
                for t in a { walk(tcx, *t, out, depth + 1); }
            }
            TyKind::Ref(_, t, _) | TyKind::Ptr(_, t) | TyKind::Slice(t) | TyKind::Array(t, _) => walk(tcx, *t, out, depth + 1),
            TyKind::Tuple(a) => for t in a { walk(tcx, *t, out, depth + 1); },
            TyKind::FnPtr(a, t, _, _) => {
                for x in a { walk(tcx, *x, out, depth + 1); }
                walk(tcx, *t, out, depth + 1);
            }
            _ => {}
        }
    }
    walk(tcx, ty, out, 0);
}

impl Body {
    /// Erase the codegen-owned copy, after borrow checking. Keep the polymorphic
    /// typeck body and its ParamEnv intact for type/region inference.
    pub fn erase_regions(&mut self, tys: &crate::types::Types) {
        if !tys.has_free_regions() { return; }
        let ty = |t: &mut TyId| *t = tys.erase_regions(*t);
        let list = |v: &mut Vec<TyId>| v.iter_mut().for_each(ty);
        list(&mut self.args);
        list(&mut self.expr_ty);
        list(&mut self.pat_ty);
        ty(&mut self.ret);
        self.locals.iter_mut().for_each(|l| ty(&mut l.ty));
        self.res_args.values_mut().for_each(list);
        self.methods.values_mut().chain(self.binops.values_mut()).for_each(|m| list(&mut m.args));
        self.ov_derefs.values_mut().chain(self.ov_index.values_mut()).chain(self.for_next.values_mut()).for_each(|(_, a)| list(a));
        self.for_into.values_mut().for_each(|(_, a, t)| { list(a); ty(t); });
        self.try_conv.values_mut().flatten().for_each(|(_, a)| list(a));
        for c in self.coerce.values_mut() {
            match c {
                Coerce::ToDyn(a, b) | Coerce::Upcast(a, b) => { ty(a); ty(b); }
                _ => {}
            }
        }
        for sig in self.closure_sigs.values_mut() {
            ty(&mut sig.bound);
            ty(&mut sig.liberated);
            if let Some((a, b)) = &mut sig.annotation_eq { ty(a); ty(b); }
        }
        self.inline_const_types.values_mut().for_each(ty);
        self.param_env = None;
    }
}

/// Allocation/metadata only. Response relations and subtype-root restoration
/// belong to T-infer. rustc_type_ir/src/infer_ctxt.rs:338-378;
/// rustc_infer/src/infer/canonical/mod.rs:86.
impl crate::solve::relate::TypeRelation for Fcx<'_> {
    fn relate(&mut self, a: TyId, b: TyId) -> bool { self.unify(a, b) }
}
impl crate::solve::canonical::InferDelegate for Fcx<'_> {
    fn snapshot(&self) -> crate::solve::canonical::Snapshot {
        crate::solve::canonical::Snapshot { bindings: self.snapshot(), relations: self.projection_relations.len() }
    }
    fn rollback(&mut self, mark: crate::solve::canonical::Snapshot) { self.rollback(mark.bindings); }
    fn fresh_ty(&mut self, kind: crate::solve::canonical::TyVariableKind) -> TyId {
        use crate::solve::canonical::TyVariableKind;
        self.fresh(match kind { TyVariableKind::General => 0, TyVariableKind::Int => 1, TyVariableKind::Float => 2 })
    }
    fn resolve_deep(&mut self, ty: TyId) -> TyId { self.deep(ty) }
    fn take_relations_since(&mut self, mark: crate::solve::canonical::Snapshot) -> Vec<(TyId, TyId)> {
        let relations = self.projection_relations.split_off(mark.relations);
        let mut write = mark.bindings;
        for read in mark.bindings..self.undo.len() {
            if self.undo[read].0 != u32::MAX {
                self.undo[write] = self.undo[read];
                write += 1;
            }
        }
        self.undo.truncate(write);
        let mut result = Vec::with_capacity(relations.len());
        for (a, b, _) in relations { result.push((a, b)); }
        result
    }
    fn is_const_arg(&self, def: DefId, index: u32) -> bool {
        let env = if let ItemKind::Trait { generics, .. } =
            &self.prog.files[self.prog.def(def).file as usize].ast.item(self.prog.def(def).item).kind
        {
            let mut env = GenEnv::default();
            env.names.push(self.prog.syms.get("Self").unwrap_or(u32::MAX));
            env.regions.next_param += 1;
            crate::tcx::push_generics(self.prog, self.prog.def(def).file, generics, &mut env);
            env
        } else { self.tcx.item_env(self.prog, def) };
        for (i, _, _) in env.consts { if i == index { return true; } }
        false
    }

    fn resolve_ty(&mut self, ty: TyId) -> TyId { self.shallow_region_vars(ty) }
    fn resolve_const(&mut self, value: TyId) -> TyId { self.shallow_region_vars(value) }
    fn resolve_region(&mut self, region: crate::types::RegionId) -> crate::types::RegionId { region }

    fn ty_variable(&self, mut var: u32) -> crate::solve::canonical::TyVariableInfo {
        use crate::solve::canonical::{TyVariableInfo, TyVariableKind};
        loop {
            match self.vars[var as usize] {
                VarSt::Bound(t) => match self.tcx.tys.kind(t) {
                    TyKind::Infer(v) => var = *v,
                    _ => panic!("metadata requested for resolved type variable"),
                },
                VarSt::Free(kind) => return TyVariableInfo {
                    root: var, sub_root: var,
                    universe: self.var_universes[var as usize],
                    kind: match kind { 0 => TyVariableKind::General, 1 => TyVariableKind::Int,
                        2 => TyVariableKind::Float, _ => unreachable!() },
                },
            }
        }
    }

    fn const_variable_root(&self, var: u32) -> u32 { self.ty_variable(var).root }
    fn const_variable_universe(&self, var: u32) -> UniverseIndex { self.ty_variable(var).universe }
    fn region_variable_root(&self, var: u32) -> u32 { var }
    fn region_variable_universe(&self, var: u32) -> UniverseIndex {
        self.region_universes.get(&var).copied().unwrap_or(UniverseIndex::ROOT)
    }
    fn universe(&self) -> UniverseIndex { self.universe }
    fn create_next_universe(&mut self) -> UniverseIndex {
        self.universe = UniverseIndex(self.universe.0.checked_add(1).expect("universe overflow"));
        self.universe
    }

    fn instantiate_var(&mut self, kind: crate::solve::canonical::CanonicalVarKind) -> crate::solve::canonical::GenericArg {
        use crate::solve::canonical::{CanonicalVarKind, GenericArg, TyVariableKind};
        use crate::types::{PlaceholderType, RegionKind};
        assert!(self.universe.can_name(kind.universe()));
        match kind {
            CanonicalVarKind::Ty { universe, kind, .. } => {
                let kind = match kind { TyVariableKind::General => 0, TyVariableKind::Int => 1, TyVariableKind::Float => 2 };
                GenericArg::Ty(self.fresh_in_universe(kind, universe))
            }
            CanonicalVarKind::Const(universe) => GenericArg::Const(self.fresh_in_universe(0, universe)),
            CanonicalVarKind::Region(universe) => {
                let r = self.fresh_region();
                let RegionKind::ReVar(var) = self.tcx.tys.region_kind(r) else { unreachable!() };
                self.region_universes.insert(var, universe);
                GenericArg::Region(r)
            }
            CanonicalVarKind::PlaceholderTy(p) => GenericArg::Ty(self.tcx.tys.intern(TyKind::Placeholder(
                PlaceholderType { universe: p.universe, bound: p.var }))),
            CanonicalVarKind::PlaceholderConst(p) => GenericArg::Const(self.tcx.tys.intern(TyKind::Placeholder(
                PlaceholderType { universe: p.universe, bound: p.var }))),
            CanonicalVarKind::PlaceholderRegion(p) => GenericArg::Region(self.tcx.tys.intern_region(
                RegionKind::RePlaceholder { universe: p.universe, var: p.var })),
        }
    }
}

#[cfg(test)]
mod solve;
