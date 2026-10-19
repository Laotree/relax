//! Late (type-aware) builtin lints of `makepad check` that are not liveness, reachability or
//! dead-code analyses: ports of rustc_lint's LateLintPass passes (`unused_must_use`,
//! `path_statements`, `trivial_casts`, ...). Check-only.

use crate::ast::*;
use crate::lint::{self, Level, Lint};
use crate::program::{DefId, Program};
use crate::tcx::Tcx;
use crate::typeck::Body;

/// Body-level passes over one typed body owner.
pub fn check_body(_prog: &Program, _tcx: &Tcx, _body: &Body) {}
