//! THIR construction tests: real sources through typeck, then `thir_body`; the shape is checked by
//! the kinds of expressions the arenas hold.
use super::Cx;
use crate::borrowck::body::{BodyKind, CheckedBody};
use crate::mir::build::pattern::tests::{named, program};
use crate::mir::build::thir::ThirBody;
use crate::mir::build::{BuildCx, BuildResult, BuildRoot};
use crate::tcx::{EvalCx, EvalState, TypingEnv};

fn build<R>(source: &str, name: &str, f: impl FnOnce(BuildResult<ThirBody>) -> R) -> R {
    let (prog, tcx) = program(source);
    let def = named(&prog, name);
    let body = tcx.typeck(&prog, def);
    assert!(body.errors.is_empty(), "{:?}", body.errors);
    let env = TypingEnv::fully_monomorphized(&prog);
    let state = EvalState::new();
    let eval = EvalCx::new(&prog, &tcx, env, &state);
    let root = BuildRoot::new(BuildCx { prog: &prog, tcx: &tcx, env, eval: &eval }, &body).unwrap();
    let cx = Cx::new(&root, CheckedBody { owner: def, kind: if name.chars().next().unwrap().is_uppercase() { BodyKind::Const } else { BodyKind::Function } });
    f(cx.thir_body())
}

fn kinds(source: &str, name: &str) -> Vec<String> {
    build(source, name, |r| {
        let t = r.unwrap_or_else(|e| panic!("{e:?}"));
        let mut out: Vec<String> = t
            .thir
            .exprs
            .iter()
            .map(|e| {
                let s = format!("{:?}", e.kind);
                s.split(|c: char| !c.is_alphanumeric()).next().unwrap().to_string()
            })
            .collect();
        out.sort();
        out.dedup();
        out
    })
}

fn has(k: &[String], names: &[&str]) {
    for n in names {
        assert!(k.iter().any(|x| x == n), "missing {n} in {k:?}");
    }
}

#[test]
fn arithmetic_and_calls() {
    let k = kinds("pub fn g(a: u8) -> u8 { a } pub fn f(x: u8, y: u8) -> u8 { let z = x + y; g(z) }", "f");
    has(&k, &["Binary", "Call", "VarRef", "Scope", "ZstLiteral"]);
}

#[test]
fn loops_branches_and_returns() {
    let k = kinds("pub fn f(mut n: u32) -> u32 { while n > 3 { n -= 1; if n == 5 { break; } } loop { return n; } }", "f");
    has(&k, &["Loop", "If", "Break", "Return", "AssignOp", "Binary"]);
}

#[test]
fn match_and_references() {
    let k = kinds("pub enum E { A(u8), B } pub fn f(e: &E) -> u8 { match e { E::A(n) => *n, E::B => 0 } }", "f");
    has(&k, &["Match", "Deref"]);
}

#[test]
fn struct_tuple_array_field_index() {
    let k = kinds("pub struct S { a: u8, b: [u8; 2] } pub fn f(s: S) -> u8 { let t = (s.a, 1u8); let S { a, b } = S { a: t.0, b: [t.1, 2] }; b[1] + a }", "f");
    has(&k, &["Adt", "Tuple", "Array", "Field", "Index"]);
}

#[test]
fn closures_capture() {
    let k = kinds("pub fn f(x: u8) -> u8 { let _c = |y: u8| x + y; x }", "f");
    has(&k, &["Closure"]);
}

#[test]
fn borrows_and_casts() {
    let k = kinds("pub fn f(x: u8) -> u64 { let r = &x; let m = &mut 3u8; *m += *r; (x as u64) + 1 }", "f");
    has(&k, &["Borrow", "Cast", "Deref"]);
}

#[test]
fn fn_body_fields_are_filled() {
    build("pub fn f(x: u8, y: u8) -> u8 { x }", "f", |r| {
        let t = r.unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(t.params.len(), 2);
        assert!(t.fn_scopes.is_some());
        assert!(t.coroutine.is_none());
    });
}

#[test]
fn const_body_has_no_fn_scopes() {
    build("pub const K: u8 = 1 + 2; pub fn f() {}", "K", |r| {
        let t = r.unwrap_or_else(|e| panic!("{e:?}"));
        assert!(t.params.is_empty());
        assert!(t.fn_scopes.is_none());
    });
}

#[test]
fn destructuring_assignment() {
    let k = kinds(
        "pub struct S { a: u8, b: u8 } pub struct T(u8, u8) ; pub enum E { V(u8, u8) } pub fn f(s: S, t: T, mut a: u8, mut b: u8, mut arr: [u8; 3]) { (a, b) = (b, a); S { a, b } = s; T(a, ..) = t; (a, _) = (1, 2); [a, .., b] = arr; (a, (b, _)) = (1, (2, 3)); let _ = E::V(1, 2); }",
        "f",
    );
    has(&k, &["Block", "Assign", "VarRef", "Tuple"]);
}

#[test]
fn destructuring_assignment_binds_in_a_remainder_scope() {
    build("pub fn f(mut a: u8, mut b: u8) { (a, b) = (b, a); }", "f", |r| {
        let t = r.unwrap_or_else(|e| panic!("{e:?}"));
        assert_eq!(t.thir.var_scopes.len(), 2);
    });
}

#[test]
fn default_field_values() {
    let k = kinds("pub struct S { a: u8 = 7, c: u8 } pub fn f() -> S { S { c: 1, .. } }", "f");
    has(&k, &["Adt", "NamedConst"]);
}
