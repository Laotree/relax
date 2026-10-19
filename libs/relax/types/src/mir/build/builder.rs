//! rustc_mir_build/src/builder/mod.rs: the `Builder`, its state and local/temporary bookkeeping.
use super::scope::Scopes;
use super::thir::{LocalVarId, ThirBody};
use super::{BuildError, BuildResult, BuildRoot, Cfg, UnsupportedReason};
use crate::borrowck::body::CheckedBody;
use crate::fxhash::HashMap;
use crate::mir::{
    AllocMap, Body, BlockTailInfo, CanonicalUserTypeAnnotation, CapturedPlace, CoroutineInfo, Local, LocalDecl, LocalInfo, LocalKind,
    MirSource, Mutability, Place, SourceInfo, SourceScope, SourceScopeData, Span, VarDebugInfo,
};
use crate::region_scope::ScopeId;
use crate::types::TyId;

/// builder/mod.rs:`LocalsForNode`: a binding has one local, or, when bound in a guarded arm, a reference
/// local for the guard and a by-value/by-ref local for the arm body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalsForNode {
    One(Local),
    ForGuard { ref_for_guard: Local, for_arm_body: Local },
}
/// builder/mod.rs:`GuardFrameLocal` / `GuardFrame`: the bindings of the arm whose guard is being lowered.
#[derive(Clone, Debug)]
pub struct GuardFrameLocal {
    pub id: LocalVarId,
}
#[derive(Clone, Debug)]
pub struct GuardFrame {
    pub locals: Vec<GuardFrameLocal>,
}
/// builder/mod.rs:`ForGuard`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForGuard {
    RefWithinGuard,
    OutsideGuard,
}
/// builder/mod.rs:`BlockFrame`: what the innermost block being lowered is for (statement-expression
/// results, tail expressions and sub-expressions).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockFrame {
    /// Evaluating a statement; the result is ignored when `ignores_expr_result`.
    Statement { ignores_expr_result: bool },
    /// Evaluating the tail expression of a block.
    TailExpr { info: BlockTailInfo },
    /// Generic sub-expression.
    SubExpr,
}
/// How a closure body reaches its captures: the environment local `_1`, a reference when the closure is
/// `Fn`/`FnMut`.
#[derive(Clone, Copy, Debug)]
pub struct UpvarEnv {
    pub local: Local,
    pub by_ref: bool,
}
/// builder/mod.rs: the lifetime a temporary lives for (`temp_lifetime`, and the Edition 2024 rescope).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TempLifetime {
    pub temp_lifetime: Option<ScopeId>,
    pub backwards_incompatible: Option<ScopeId>,
}

pub struct Builder<'a> {
    pub root: &'a BuildRoot<'a>,
    pub thir: &'a ThirBody,
    pub owner: CheckedBody,
    pub source: MirSource,
    pub body_span: Span,
    pub arg_count: usize,
    pub coroutine: Option<CoroutineInfo>,
    pub cfg: Cfg,
    pub scopes: Scopes,
    pub source_scopes: Vec<SourceScopeData>,
    pub source_scope: SourceScope,
    pub guard_context: Vec<GuardFrame>,
    pub block_context: Vec<BlockFrame>,
    /// Temporaries created for an expression evaluated twice (match guards), keyed by THIR expr.
    pub fixed_temps: HashMap<super::thir::ExprId, Local>,
    pub fixed_temps_scope: Option<ScopeId>,
    pub var_indices: HashMap<LocalVarId, LocalsForNode>,
    pub local_decls: Vec<LocalDecl>,
    pub canonical_user_type_annotations: Vec<CanonicalUserTypeAnnotation>,
    pub upvars: Vec<CapturedPlace>,
    pub upvar_env: Option<UpvarEnv>,
    pub var_debug_info: Vec<VarDebugInfo>,
    pub unit_temp: Option<Place>,
    pub allocs: AllocMap,
}

impl<'a> Builder<'a> {
    /// The body of `owner` from its THIR (rustc `construct_fn` / `construct_const`).
    pub fn build(root: &'a BuildRoot<'a>, owner: CheckedBody, thir: &'a ThirBody) -> BuildResult<Body> {
        let _ = (root, thir);
        Err(BuildError::new(owner, Span::default(), UnsupportedReason::NotYetBuilt("builder")))
    }

    /// builder/mod.rs:`BlockContext::currently_in_block_tail`.
    pub fn currently_in_block_tail(&self) -> Option<BlockTailInfo> {
        for frame in self.block_context.iter().rev() {
            match frame {
                BlockFrame::SubExpr => continue,
                BlockFrame::Statement { .. } => break,
                &BlockFrame::TailExpr { info } => return Some(info),
            }
        }
        None
    }
    /// builder/mod.rs:`BlockContext::currently_ignores_tail_results`: whether the block result itself is
    /// discarded (does not skip `SubExpr` frames).
    pub fn currently_ignores_tail_results(&self) -> bool {
        match self.block_context.last() {
            None | Some(BlockFrame::SubExpr) => false,
            Some(BlockFrame::TailExpr { info: BlockTailInfo { tail_result_is_ignored, .. } }) => *tail_result_is_ignored,
            Some(BlockFrame::Statement { ignores_expr_result }) => *ignores_expr_result,
        }
    }
    pub fn error(&self, span: Span, reason: UnsupportedReason) -> BuildError {
        BuildError::new(self.owner, span, reason)
    }
    pub fn source_info(&self, span: Span) -> SourceInfo {
        SourceInfo { span, scope: self.source_scope }
    }
    /// builder/mod.rs:`new_source_scope`.
    pub fn new_source_scope(&mut self, span: Span, parent: Option<SourceScope>) -> SourceScope {
        self.source_scopes.push(SourceScopeData { span, parent_scope: parent.or(Some(self.source_scope)) });
        SourceScope(self.source_scopes.len() as u32 - 1)
    }
    /// builder/mod.rs:`temp`: a fresh temporary local.
    pub fn temp(&mut self, ty: TyId, span: Span) -> Place {
        Place::local(self.new_local(ty, Mutability::Mut, LocalKind::Temp, LocalInfo::Boring, span))
    }
    pub fn new_local(&mut self, ty: TyId, mutability: Mutability, kind: LocalKind, local_info: LocalInfo, span: Span) -> Local {
        let source_info = self.source_info(span);
        self.local_decls.push(LocalDecl { ty, mutability, user_ty: Vec::new(), source_info, kind, local_info });
        Local(self.local_decls.len() as u32 - 1)
    }
    /// builder/matches/mod.rs `var_local_id`: the local of a binding as seen inside/outside its guard.
    pub fn var_local_id(&self, id: LocalVarId, for_guard: ForGuard) -> Local {
        match self.var_indices[&id] {
            LocalsForNode::One(local) => local,
            LocalsForNode::ForGuard { ref_for_guard, for_arm_body } => match for_guard {
                ForGuard::RefWithinGuard => ref_for_guard,
                ForGuard::OutsideGuard => for_arm_body,
            },
        }
    }
    /// builder/mod.rs:`is_bound_var_in_guard`.
    pub fn is_bound_var_in_guard(&self, id: LocalVarId) -> bool {
        self.guard_context.iter().any(|frame| frame.locals.iter().any(|local| local.id == id))
    }
}
