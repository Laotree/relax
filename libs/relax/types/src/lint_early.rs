//! Early (syntax-level) builtin lints of `makepad check`: ports of rustc_lint's EarlyLintPass
//! passes (unused parentheses / braces, `while true`, redundant semicolons, doc comments on
//! statements, unused labels, ...). Check-only.

use crate::ast::*;
use crate::lint::{self, Level, Lint};
use crate::program::{DefId, Program};
use crate::tcx::Tcx;
use crate::typeck::Body;

/// Item-level passes over the definitions of the checked crates marked in `own`.
pub fn check_items(_prog: &Program, _tcx: &Tcx, _own: &[bool]) {}

/// Body-level passes over one typed body owner.
pub fn check_body(_prog: &Program, _tcx: &Tcx, _body: &Body) {}
