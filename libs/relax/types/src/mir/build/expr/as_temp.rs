//! rustc_mir_build/src/builder/expr/as_temp.rs: compile an expression into a fresh temporary.
//! (Written by lane E; B owns the file.)
use super::super::builder::{BlockFrame, Builder, TempLifetime};
use super::super::cfg::{BlockAnd, BlockAndExtension};
use super::super::scope::DropKind;
use super::super::thir::{ExprId, ExprKind};
use super::super::BuildResult;
use crate::mir::{BlockTailInfo, BasicBlock, Local, LocalInfo, LocalKind, Mutability, Place, Statement, StatementKind};
use crate::region_scope::{Node, ScopeData};
use crate::types::TyKind;

impl Builder<'_> {
    /// Compile `expr` into a fresh temporary. This is used when building up rvalues so as to
    /// freeze the value that will be consumed. The only place in mir building that must worry about
    /// infinite recursion: everything else is broken up by an intermediate temporary at some point.
    /// (The build runs on the Gandalf worker's large stack; there is no stack-growth helper in this crate.)
    pub fn as_temp(&mut self, block: BasicBlock, temp_lifetime: TempLifetime, expr: ExprId, mutability: Mutability) -> BuildResult<BlockAnd<Local>> {
        self.as_temp_inner(block, temp_lifetime, expr, mutability)
    }

    fn as_temp_inner(&mut self, mut block: BasicBlock, temp_lifetime: TempLifetime, expr_id: ExprId, mutability: Mutability) -> BuildResult<BlockAnd<Local>> {
        let expr = &self.thir.thir[expr_id];
        let (expr_span, expr_ty, kind) = (expr.span, expr.ty, expr.kind.clone());
        let source_info = self.source_info(expr_span);
        if let ExprKind::Scope { region_scope, value, .. } = kind {
            return self.in_scope((region_scope, source_info), |this| this.as_temp(block, temp_lifetime, value, mutability));
        }

        let deduplicate_temps = self.fixed_temps_scope.is_some() && self.fixed_temps_scope == temp_lifetime.temp_lifetime;
        let temp = if let Some(&temp_index) = self.fixed_temps.get(&expr_id).filter(|_| deduplicate_temps) {
            temp_index
        } else {
            let local_info = match &kind {
                ExprKind::StaticRef { def, .. } => LocalInfo::StaticRef { def_id: *def, is_thread_local: false },
                ExprKind::ThreadLocalRef(def) => LocalInfo::StaticRef { def_id: *def, is_thread_local: true },
                ExprKind::NamedConst { def, .. } | ExprKind::ConstParam { def, .. } => LocalInfo::ConstRef { def_id: *def },
                // Find out whether this temp is being created within the tail expression of a block
                // whose result is ignored.
                _ if let Some(tail_info) = self.in_block_tail() => LocalInfo::BlockTailTemp(tail_info),
                _ if let Some(scope) = temp_lifetime.temp_lifetime
                    && self.root.scope_tree.scopes[scope.0 as usize].data == ScopeData::IfThenRescope
                    && let Node::Expr(if_then) = self.root.scope_tree.scopes[scope.0 as usize].node =>
                {
                    LocalInfo::IfThenRescopeTemp { if_then }
                }
                _ => LocalInfo::Boring,
            };
            self.new_local(expr_ty, if mutability == Mutability::Not { Mutability::Not } else { Mutability::Mut }, LocalKind::Temp, local_info, expr_span)
        };
        if deduplicate_temps {
            self.fixed_temps.insert(expr_id, temp);
        }
        let temp_place = Place::local(temp);

        let never_block = matches!(kind, ExprKind::Block { block: b } if {
            let b = &self.thir.thir[b];
            b.expr.is_none() && !b.targeted_by_break && matches!(self.root.cx.tcx.tys.kind(expr_ty), TyKind::Never)
        });
        match kind {
            // Don't bother with StorageLive and Dead for these temporaries, they are never assigned.
            ExprKind::Break { .. } | ExprKind::Continue { .. } | ExprKind::Return { .. } => (),
            _ if never_block => (),
            _ => {
                self.cfg.push(block, Statement { source_info, kind: StatementKind::StorageLive(temp) });

                // In constants, `temp_lifetime` is `None` for temporaries that live for the `'static`
                // lifetime. Thus we do not drop these temporaries and simply leak them.
                if let Some(temp_lifetime) = temp_lifetime.temp_lifetime {
                    self.schedule_drop(expr_span, temp_lifetime, temp, DropKind::Storage)?;
                }
            }
        }

        let BlockAnd(b, ()) = self.expr_into_dest(temp_place, block, expr_id)?;
        block = b;

        if let Some(temp_lifetime) = temp_lifetime.temp_lifetime {
            self.schedule_drop(expr_span, temp_lifetime, temp, DropKind::Value)?;
        }

        if let Some(backwards_incompatible) = temp_lifetime.backwards_incompatible {
            self.schedule_drop(expr_span, backwards_incompatible, temp, DropKind::ForLint)?;
        }

        Ok(block.and(temp))
    }

    /// builder/mod.rs:`BlockContext::currently_in_block_tail`: innermost non-sub-expression frame is a block tail.
    fn in_block_tail(&self) -> Option<BlockTailInfo> {
        for frame in self.block_context.iter().rev() {
            match *frame {
                BlockFrame::SubExpr => continue,
                BlockFrame::Statement { .. } => return None,
                BlockFrame::TailExpr { tail_result_is_ignored, span } => return Some(BlockTailInfo { tail_result_is_ignored, span }),
            }
        }
        None
    }
}
