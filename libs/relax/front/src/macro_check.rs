//! Port of rustc_expand `mbe/macro_check.rs`: the lint `meta_variable_misuse` for the rules of a
//! `macro_rules!` definition -- a meta-variable bound twice in a nested macro's matcher, a free one,
//! one that repeats less often or with other Kleene operators than its binder -- including the
//! nested definitions the right-hand sides write (recognised by their shape, as rustc does).
//!
//! The messages are the lint diagnostics of rustc_expand errors.rs; positions are the macro's.

use crate::lexer::T;
use crate::macros::{MNode, MacroDef, TNode};
use std::collections::HashMap;

/// A token tree of either side of a rule.
enum Ct {
    Tok(T, String),
    /// a meta-variable occurrence (`$x`, or a binder of a nested macro's matcher)
    Var(String),
    /// a binder `$x:frag` of a top-level matcher
    Decl(String),
    Delim(T, Vec<Ct>),
    /// `$( .. ) sep op`: the operator
    Seq(u8, Vec<Ct>),
}

fn from_m(nodes: &[MNode]) -> Vec<Ct> {
    nodes.iter().map(|n| match n {
        MNode::Tok(t) => Ct::Tok(t.kind, t.text.clone()),
        MNode::Var(v, _) => Ct::Decl(v.clone()),
        MNode::Rep(x, _, op) => Ct::Seq(*op, from_m(x)),
        MNode::Group(o, _, x) => Ct::Delim(o.kind, from_m(x)),
    }).collect()
}

fn from_t(nodes: &[TNode]) -> Vec<Ct> {
    nodes.iter().map(|n| match n {
        TNode::Tok(t) => Ct::Tok(t.kind, t.text.clone()),
        TNode::Var(v) => Ct::Var(v.clone()),
        TNode::Rep(x, _, op) => Ct::Seq(*op, from_t(x)),
        TNode::Group(o, _, x) => Ct::Delim(o.kind, from_t(x)),
        TNode::Crate => Ct::Tok(T::Ident, "$crate".to_string()),
    }).collect()
}

/// A binder: the stack of Kleene operators it was bound under (outermost first).
type Binders = HashMap<String, Vec<u8>>;

struct MacroState<'a> {
    binders: &'a Binders,
    ops: Vec<u8>,
}

#[derive(Clone, Copy, PartialEq)]
enum Nested {
    Empty,
    MacroRules,
    MacroRulesBang,
    MacroRulesBangName,
    Macro,
    MacroName,
    MacroNameParen,
}

struct Check {
    lints: Vec<String>,
}

/// The `meta_variable_misuse` lint messages of the rules of `d`.
pub fn lints(d: &MacroDef) -> Vec<String> {
    let mut c = Check { lints: Vec::new() };
    for (lhs, rhs) in &d.arms {
        let lhs = Ct::Delim(T::OpenParen, from_m(lhs));
        let rhs = Ct::Delim(T::OpenBrace, from_t(rhs));
        let mut binders = Binders::new();
        c.check_binders(&lhs, &[], &mut binders, &mut Vec::new());
        c.check_occurrences(&rhs, &[], &binders, &mut Vec::new());
    }
    c.lints
}

fn get_binder_info<'b>(macros: &'b [MacroState<'b>], binders: &'b Binders, name: &str) -> Option<&'b Vec<u8>> {
    binders.get(name).or_else(|| macros.iter().rev().find_map(|s| s.binders.get(name)))
}

impl Check {
    fn check_binders(&mut self, lhs: &Ct, macros: &[MacroState], binders: &mut Binders, ops: &mut Vec<u8>) {
        match lhs {
            Ct::Tok(..) => {}
            Ct::Var(name) => {
                if macros.is_empty() {
                    return;
                }
                if binders.contains_key(name) {
                    self.lints.push("duplicate matcher binding".to_string());
                } else if get_binder_info(macros, binders, name).is_none() {
                    binders.insert(name.clone(), ops.clone());
                } else {
                    self.check_occurrences(lhs, macros, binders, ops);
                }
            }
            Ct::Decl(name) => {
                if !macros.is_empty() {
                    return;
                }
                // (a duplicate at the top level is the hard error of `check_rules`)
                if get_binder_info(macros, binders, name).is_none() {
                    binders.insert(name.clone(), ops.clone());
                }
            }
            Ct::Delim(_, tts) => {
                for tt in tts {
                    self.check_binders(tt, macros, binders, ops);
                }
            }
            Ct::Seq(op, tts) => {
                ops.push(*op);
                for tt in tts {
                    self.check_binders(tt, macros, binders, ops);
                }
                ops.pop();
            }
        }
    }

    fn check_occurrences(&mut self, rhs: &Ct, macros: &[MacroState], binders: &Binders, ops: &mut Vec<u8>) {
        match rhs {
            Ct::Tok(..) | Ct::Decl(_) => {}
            Ct::Var(name) => self.check_ops_is_prefix(macros, binders, ops, name),
            Ct::Delim(_, tts) => self.check_nested_occurrences(tts, macros, binders, ops),
            Ct::Seq(op, tts) => {
                ops.push(*op);
                self.check_nested_occurrences(tts, macros, binders, ops);
                ops.pop();
            }
        }
    }

    fn check_nested_occurrences(&mut self, tts: &[Ct], macros: &[MacroState], binders: &Binders, ops: &mut Vec<u8>) {
        let mut state = Nested::Empty;
        let mut nested: Vec<MacroState> = macros.iter().map(|s| MacroState { binders: s.binders, ops: s.ops.clone() }).collect();
        nested.push(MacroState { binders, ops: ops.clone() });
        let mut nested_binders = Binders::new();
        for tt in tts {
            match (state, tt) {
                (Nested::Empty, Ct::Tok(T::Ident, name)) => {
                    if name == "macro_rules" {
                        state = Nested::MacroRules;
                    } else if name == "macro" {
                        state = Nested::Macro;
                    }
                }
                (Nested::MacroRules, Ct::Tok(T::Not, _)) => state = Nested::MacroRulesBang,
                (Nested::MacroRulesBang, Ct::Tok(T::Ident | T::RawIdent, _)) => state = Nested::MacroRulesBangName,
                (Nested::MacroRulesBang, Ct::Var(_)) => {
                    state = Nested::MacroRulesBangName;
                    self.check_occurrences(tt, macros, binders, ops);
                }
                (Nested::MacroRulesBangName | Nested::MacroName, Ct::Delim(T::OpenBrace, inner)) => {
                    let macro_rules = state == Nested::MacroRulesBangName;
                    state = Nested::Empty;
                    let rest = self.check_nested_macro(macro_rules, inner, &nested);
                    self.check_nested_occurrences(&inner[rest..], macros, binders, ops);
                }
                (Nested::Macro, Ct::Tok(T::Ident | T::RawIdent, _)) => state = Nested::MacroName,
                (Nested::Macro, Ct::Var(_)) => {
                    state = Nested::MacroName;
                    self.check_occurrences(tt, macros, binders, ops);
                }
                (Nested::MacroName, Ct::Delim(T::OpenParen, _)) => {
                    state = Nested::MacroNameParen;
                    nested_binders = Binders::new();
                    self.check_binders(tt, &nested, &mut nested_binders, &mut Vec::new());
                }
                (Nested::MacroNameParen, Ct::Delim(T::OpenBrace, _)) => {
                    state = Nested::Empty;
                    self.check_occurrences(tt, &nested, &nested_binders, &mut Vec::new());
                }
                (_, tt) => {
                    state = Nested::Empty;
                    self.check_occurrences(tt, macros, binders, ops);
                }
            }
        }
    }

    /// Checks the body of a nested macro as a list of `(LHS) => {RHS}`; where the check stopped.
    fn check_nested_macro(&mut self, macro_rules: bool, tts: &[Ct], macros: &[MacroState]) -> usize {
        let n = tts.len();
        let mut i = 0;
        let separator = if macro_rules { T::Semi } else { T::Comma };
        loop {
            if i + 2 >= n || !matches!(tts[i], Ct::Delim(..)) || !matches!(tts[i + 1], Ct::Tok(T::FatArrow, _)) || !matches!(tts[i + 2], Ct::Delim(..)) {
                break;
            }
            let mut binders = Binders::new();
            self.check_binders(&tts[i], macros, &mut binders, &mut Vec::new());
            self.check_occurrences(&tts[i + 2], macros, &binders, &mut Vec::new());
            i += 3;
            if i == n || !matches!(&tts[i], Ct::Tok(k, _) if *k == separator) {
                break;
            }
            i += 1;
        }
        i
    }

    fn check_ops_is_prefix(&mut self, macros: &[MacroState], binders: &Binders, ops: &[u8], name: &str) {
        // the operator stacks from the use outwards to the state that binds the variable
        let mut acc: Vec<&[u8]> = vec![ops];
        let outer = macros.iter().rev();
        let mut found: Option<&Vec<u8>> = binders.get(name);
        if found.is_none() {
            for s in outer {
                acc.push(&s.ops);
                if let Some(b) = s.binders.get(name) {
                    found = Some(b);
                    break;
                }
            }
        }
        match found {
            Some(binder_ops) => {
                let occurrence: Vec<u8> = acc.iter().rev().flat_map(|o| o.iter().copied()).collect();
                self.ops_is_prefix(name, binder_ops, &occurrence);
            }
            None => self.lints.push(format!("unknown macro variable `{name}`")),
        }
    }

    fn ops_is_prefix(&mut self, name: &str, binder_ops: &[u8], occurrence_ops: &[u8]) {
        for (i, binder) in binder_ops.iter().enumerate() {
            if i >= occurrence_ops.len() {
                self.lints.push(format!("variable `{name}` is still repeating at this depth"));
                return;
            }
            if occurrence_ops[i] != *binder {
                self.lints.push("meta-variable repeats with different Kleene operator".to_string());
                return;
            }
        }
    }
}
