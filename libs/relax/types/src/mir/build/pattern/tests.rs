//! Tests of the AST-to-THIR pattern lowering over real sources, and the shared harness of the
//! match-lowering tests (`matches/tests.rs`).
use crate::ast::PatId;
use crate::borrowck::body::{BodyKind, CheckedBody};
use crate::mir::build::thir::{Cx, Pat, PatKind, PatRangeBoundary, Pinnedness};
use crate::mir::build::{BuildCx, BuildRoot};
use crate::mir::{BindingMode, ByRef, Mutability};
use crate::program::{DefId, Program};
use crate::tcx::{EvalCx, EvalState, Tcx, TypingEnv};
use crate::typeck;

pub(crate) fn program(source: &str) -> (Program, Tcx) {
    let mut src = String::from("#![no_std]\n");
    src.push_str(source);
    static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);
    let dir = std::env::temp_dir().join(format!(
        "relax-mir-build-{}-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("lib.rs");
    std::fs::write(&path, src.as_bytes()).unwrap();
    let mut prog = Program::new(&std::sync::Arc::new(crate::Session::default()));
    prog.load_crate("mir_build", path.to_str().unwrap(), 2021, crate::cfg::CfgSet::host(&prog.session, &[]), Vec::new()).unwrap();
    let mut tcx = Tcx::new();
    tcx.collect(&prog);
    std::fs::remove_file(path).unwrap();
    std::fs::remove_dir(dir).unwrap();
    assert!(tcx.errors.is_empty(), "{:?}", tcx.errors);
    (prog, tcx)
}

pub(crate) fn named(prog: &Program, name: &str) -> DefId {
    for i in 0..prog.defs.len() {
        let d = DefId(i as u32);
        if prog.name(d) == name {
            return d;
        }
    }
    panic!("missing {name}")
}

/// The patterns of the typeck root that no other pattern contains, in id order.
pub(crate) fn top_patterns(prog: &Program, body: &typeck::Body) -> Vec<PatId> {
    use crate::ast::Pat as P;
    let ast = &prog.files[body.file as usize].ast;
    let all: Vec<PatId> = (0..body.pat_ty.len()).map(|i| PatId(body.pat_lo + i as u32)).collect();
    let mut inner = std::collections::HashSet::<u32>::new();
    for &p in &all {
        match *ast.pat(p) {
            P::Ident { sub: Some(s), .. } => {
                inner.insert(s.0);
            }
            P::TupleStruct(_, v) | P::Tuple(v) | P::Slice(v) | P::Or(v) => inner.extend(ast.list(v).iter().map(|p| p.0)),
            P::Struct(_, f, _) => inner.extend(ast.list(f).iter().map(|f| f.pat.0)),
            P::Ref(_, x) | P::Paren(x) | P::Box(x) => {
                inner.insert(x.0);
            }
            _ => {}
        }
    }
    all.into_iter().filter(|p| !inner.contains(&p.0) && !body.param_pats.contains(p)).collect()
}

/// Runs `f` with a THIR context of fn `name` in `source`.
pub(crate) fn with_cx<R>(source: &str, name: &str, f: impl FnOnce(&mut Cx<'_>, &typeck::Body) -> R) -> R {
    let (prog, tcx) = program(source);
    let def = named(&prog, name);
    let body = tcx.typeck(&prog, def);
    assert!(body.errors.is_empty(), "{:?}", body.errors);
    let env = TypingEnv::fully_monomorphized(&prog);
    let state = EvalState::new();
    let eval = EvalCx::new(&prog, &tcx, env, &state);
    let root = BuildRoot::new(BuildCx { prog: &prog, tcx: &tcx, env, eval: &eval }, &body).unwrap();
    let mut cx = Cx::new(&root, CheckedBody { owner: def, kind: BodyKind::Function });
    f(&mut cx, &body)
}

/// A compact rendering of a THIR pattern.
pub(crate) fn show(cx: &Cx<'_>, pat: &Pat) -> String {
    let tcx = cx.root.cx.tcx;
    let prog = cx.root.cx.prog;
    let list = |ps: &[Pat]| ps.iter().map(|p| show(cx, p)).collect::<Vec<_>>().join(", ");
    match &pat.kind {
        PatKind::Missing => "<missing>".into(),
        PatKind::Wild => "_".into(),
        PatKind::Binding { name, mode, var, subpattern, is_primary, .. } => {
            let by = match mode.0 {
                ByRef::No => "",
                ByRef::Yes(Mutability::Not) => "ref ",
                ByRef::Yes(Mutability::Mut) => "ref mut ",
            };
            let m = if mode.1 == Mutability::Mut { "mut " } else { "" };
            let sub = subpattern.as_ref().map(|s| format!(" @ {}", show(cx, s))).unwrap_or_default();
            format!("{by}{m}{}#{}{}{sub}", prog.syms.str(*name), var.0, if *is_primary { "" } else { "'" })
        }
        PatKind::Variant { adt_def, variant_index, subpatterns, .. } => {
            let a = &tcx.adts[adt_def];
            let fields = subpatterns.iter().map(|f| format!("{}: {}", f.field.0, show(cx, &f.pattern))).collect::<Vec<_>>().join(", ");
            format!("{}::{}({fields})", prog.syms.str(prog.def(*adt_def).name), prog.syms.str(a.variants[variant_index.0 as usize].name))
        }
        PatKind::Leaf { subpatterns } => {
            let fields = subpatterns.iter().map(|f| format!("{}: {}", f.field.0, show(cx, &f.pattern))).collect::<Vec<_>>().join(", ");
            format!("Leaf({fields})")
        }
        PatKind::Deref { pin, subpattern } => format!("{}*{}", if *pin == Pinnedness::Pinned { "pin " } else { "" }, show(cx, subpattern)),
        PatKind::DerefPattern { subpattern, .. } => format!("deref({})", show(cx, subpattern)),
        PatKind::Constant { value } => {
            let tys = &tcx.tys;
            match value.valtree.try_to_leaf() {
                Some(l) => format!("{}", l.to_bits(l.size())),
                None => format!("const<{}>", crate::typeck::ty_to_string(false, prog, tcx, value.ty)),
            }
            .to_string()
                + &{ let _ = tys; String::new() }
        }
        PatKind::Range(r) => {
            let b = |b: &PatRangeBoundary| match b {
                PatRangeBoundary::Finite(v) => v.try_to_leaf().map_or("?".into(), |l| format!("{}", l.to_bits(l.size()))),
                PatRangeBoundary::NegInfinity => "-inf".into(),
                PatRangeBoundary::PosInfinity => "+inf".into(),
            };
            format!("{}..{}{}", b(&r.lo), if r.end == crate::mir::build::thir::RangeEnd::Included { "=" } else { "" }, b(&r.hi))
        }
        PatKind::Slice { prefix, slice, suffix } | PatKind::Array { prefix, slice, suffix } => {
            let is_array = matches!(pat.kind, PatKind::Array { .. });
            let mut parts = vec![];
            if !prefix.is_empty() {
                parts.push(list(prefix));
            }
            if let Some(s) = slice {
                parts.push(format!("{}..", if matches!(s.kind, PatKind::Wild) { String::new() } else { format!("{} @ ", show(cx, s)) }));
            }
            if !suffix.is_empty() {
                parts.push(list(suffix));
            }
            format!("{}[{}]", if is_array { "arr" } else { "slice" }, parts.join(", "))
        }
        PatKind::Or { pats } => format!("({})", pats.iter().map(|p| show(cx, p)).collect::<Vec<_>>().join(" | ")),
        PatKind::Guard { subpattern, .. } => format!("{} if ..", show(cx, subpattern)),
        PatKind::Never => "!".into(),
        PatKind::Error(_) => "<error>".into(),
    }
}

fn lower(source: &str, name: &str) -> Vec<String> {
    with_cx(source, name, |cx, body| {
        let tops = top_patterns(cx.root.cx.prog, body);
        let mut out = Vec::new();
        for p in tops {
            let pat = cx.lower_pattern(p).unwrap_or_else(|e| panic!("{e:?}"));
            out.push(show(cx, &pat));
        }
        out
    })
}

#[test]
fn tuple_and_struct_fields() {
    let r = lower("pub struct S { a: u8, b: bool } pub fn f(x: (u8, bool), y: S) { let (p, _) = x; let S { a, b: q } = y; }", "f");
    assert_eq!(r, ["Leaf(0: p#2, 1: _)", "Leaf(0: a#3, 1: q#4)"], "{r:?}");
}

#[test]
fn rest_in_tuples_and_slices() {
    let r = lower("pub fn f(x: (u8, u8, u8), s: &[u8], a: [u8; 3]) { let (p, ..) = x; let (.., z) = x; let [h, .., t] = a; match s { [first, rest @ ..] => {} [] => {} } }", "f");
    assert_eq!(r[0], "Leaf(0: p#3)");
    assert_eq!(r[1], "Leaf(2: z#4)");
    assert_eq!(r[2], "arr[h#5, .., t#6]");
    assert_eq!(r[3], "*slice[ref first#7, ref rest#8 @ _ @ ..]");
    assert_eq!(r[4], "*slice[]");
}

#[test]
fn match_ergonomics_wraps_derefs_and_binds_by_ref() {
    let r = lower("pub enum E { A(u8), B } pub fn f(e: &&E) { match e { E::A(n) => {} E::B => {} } }", "f");
    assert_eq!(r[0], "**E::A(0: ref n#1)");
    assert_eq!(r[1], "**E::B()");
}

#[test]
fn or_patterns_share_the_variable() {
    let r = lower("pub enum E { A(u8), B(u8) } pub fn f(e: E) { match e { E::A(x) | E::B(x) => {} } }", "f");
    assert_eq!(r[0], "(E::A(0: x#1) | E::B(0: x#1'))");
}

#[test]
fn bindings_with_subpatterns_and_modes() {
    let r = lower("pub fn f(a: (u8, u8)) { let whole @ (_, mut m) = a; let (ref r, ref mut rm) = a; }", "f");
    assert_eq!(r[0], "whole#1 @ Leaf(0: _, 1: mut m#2)");
    assert_eq!(r[1], "Leaf(0: ref r#3, 1: ref mut rm#4)");
}

#[test]
fn literals_ranges_and_consts() {
    let r = lower("pub const K: u8 = 7; pub fn f(x: u8, c: char, s: &str, b: &[u8]) { match x { 0 => {} 1..=5 => {} 6..K => {} K => {} 100.. => {} _ => {} } match c { 'a'..='z' => {} _ => {} } match s { \"hi\" => {} _ => {} } match b { b\"ab\" => {} _ => {} } }", "f");
    assert_eq!(&r[..6], ["0", "1..=5", "6..7", "7", "100..=+inf", "_"]);
    assert_eq!(r[6], "97..=122");
    assert_eq!(r[8], "*const<str>");
    assert_eq!(r[10], "*slice[97, 98]");
}

#[test]
fn box_and_reference_patterns() {
    let r = lower("pub fn f(x: &(u8, bool)) { let &(a, b) = x; }", "f");
    assert_eq!(r[0], "*Leaf(0: a#1, 1: b#2)");
}

#[test]
fn spans_cover_the_pattern() {
    with_cx("pub fn f(x: (u8, u8)) { let (a, mut b) = x; }", "f", |cx, body| {
        let p = top_patterns(cx.root.cx.prog, body)[0];
        let span = cx.pat_span(p);
        let pf = &cx.root.cx.prog.files[body.file as usize];
        assert_eq!(std::str::from_utf8(pf.bytes(span.lo, span.hi)).unwrap(), "(a, mut b)");
    });
}

#[allow(dead_code)]
fn _unused(_: BindingMode) {}
