//! Small syntactic constant evaluation used before type checking (array lengths,
//! enum discriminants). Full `const` items are evaluated by running their JIT'ed
//! initializer (see jit.rs).

use crate::ast::{BinOp, ExprId, ExprKind, ItemKind, LitKind, UnOp};
use crate::program::{DefId, DefKind, Program};
use crate::tcx::Tcx;

fn f_ast_path(prog: &Program, file: u32, f: ExprId) -> Option<crate::ast::Path> {
    match &prog.files[file as usize].ast.expr(f).kind {
        ExprKind::Path(p) => Some(p.clone()),
        _ => None,
    }
}

pub fn parse_int_lit(text: &str) -> Option<u128> {
    let mut s = String::new();
    for c in text.chars() {
        if c != '_' {
            s.push(c);
        }
    }
    // strip suffix
    let (radix, digits) = if let Some(x) = s.strip_prefix("0x") {
        (16, x.to_string())
    } else if let Some(x) = s.strip_prefix("0o") {
        (8, x.to_string())
    } else if let Some(x) = s.strip_prefix("0b") {
        (2, x.to_string())
    } else {
        (10, s.clone())
    };
    let mut end = digits.len();
    for (i, c) in digits.char_indices() {
        let ok = match radix {
            16 => c.is_ascii_hexdigit(),
            _ => c.is_ascii_digit(),
        };
        if !ok {
            end = i;
            break;
        }
    }
    u128::from_str_radix(&digits[..end], radix).ok()
}

/// Integer suffix of a literal (`u8`, `usize`...), if any.
pub fn int_suffix(text: &str) -> Option<&str> {
    let hex = text.starts_with("0x");
    for suf in ["u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize", "f32", "f64"] {
        if text.ends_with(suf) {
            // hex digits can end in `f32`-like text only if that is a real suffix: rare, accept
            if hex && suf.starts_with('f') {
                continue;
            }
            return Some(suf);
        }
    }
    None
}

pub fn eval_int_literal(prog: &Program, file: u32, e: ExprId) -> Option<i128> {
    let f = &prog.files[file as usize];
    let ex = f.ast.expr(e);
    match &ex.kind {
        ExprKind::Lit(LitKind::Int) => {
            let t = std::str::from_utf8(f.bytes(ex.lo, ex.hi)).ok()?;
            parse_int_lit(t).map(|v| v as i128)
        }
        ExprKind::Unary(UnOp::Neg, x) => eval_int_literal(prog, file, *x).map(|v| -v),
        ExprKind::Paren(x) => eval_int_literal(prog, file, *x),
        ExprKind::Cast(x, _) => eval_int_literal(prog, file, *x),
        _ => None,
    }
}

/// Array lengths: literals, paths to consts with literal-like initializers, arithmetic.
pub fn eval_usize_expr(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, file: u32, module: u32, e: ExprId) -> Option<u64> {
    // the typed evaluator also knows char/bool literals, `as` casts of enum variants, `!`, `^`
    eval_i(cx, prog, tcx, file, module, e, 0).or_else(|| eval_disc(prog, file, module, e, (8, false))).map(|v| v as u64)
}

fn eval_i(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, file: u32, module: u32, e: ExprId, depth: u32) -> Option<i128> {
    if depth > 32 {
        return None;
    }
    let f = &prog.files[file as usize];
    let ex = f.ast.expr(e);
    match &ex.kind {
        ExprKind::Lit(LitKind::Int) => {
            let t = std::str::from_utf8(f.bytes(ex.lo, ex.hi)).ok()?;
            parse_int_lit(t).map(|v| v as i128)
        }
        ExprKind::Paren(x) | ExprKind::Cast(x, _) => eval_i(cx, prog, tcx, file, module, *x, depth + 1),
        ExprKind::Block(b, _) => {
            let blk = f.ast.block(*b);
            if blk.stmts.len() == 1 {
                if let crate::ast::Stmt::Expr(x, false) = f.ast.list(blk.stmts)[0] {
                    return eval_i(cx, prog, tcx, file, module, x, depth + 1);
                }
            }
            None
        }
        ExprKind::Unary(UnOp::Neg, x) => eval_i(cx, prog, tcx, file, module, *x, depth + 1).map(|v| -v),
        ExprKind::Binary(op, a, b) => {
            let a = eval_i(cx, prog, tcx, file, module, *a, depth + 1)?;
            let b = eval_i(cx, prog, tcx, file, module, *b, depth + 1)?;
            Some(match op {
                BinOp::Add => a + b,
                BinOp::Sub => a - b,
                BinOp::Mul => a * b,
                BinOp::Div => {
                    if b == 0 {
                        return None;
                    }
                    a / b
                }
                BinOp::Rem => {
                    if b == 0 {
                        return None;
                    }
                    a % b
                }
                BinOp::Shl => a << b,
                BinOp::Shr => a >> b,
                BinOp::BitAnd => a & b,
                BinOp::BitOr => a | b,
                BinOp::BitXor => a ^ b,
                BinOp::Lt => (a < b) as i128,
                BinOp::Le => (a <= b) as i128,
                BinOp::Gt => (a > b) as i128,
                BinOp::Ge => (a >= b) as i128,
                BinOp::Eq => (a == b) as i128,
                BinOp::Ne => (a != b) as i128,
                _ => return None,
            })
        }
        // `if c { a } else { b }` (a const fn's body: `const_min_usize`)
        ExprKind::If(c, t, Some(el)) => {
            let cv = eval_i(cx, prog, tcx, file, module, *c, depth + 1)?;
            if cv != 0 {
                match f.ast.stmts(*t) {
                    [crate::ast::Stmt::Expr(x, false)] => eval_i(cx, prog, tcx, file, module, *x, depth + 1),
                    _ => None,
                }
            } else {
                eval_i(cx, prog, tcx, file, module, *el, depth + 1)
            }
        }
        // a call of a `const fn` whose body is one expression over its params
        // (`_MM_SHUFFLE(2, 3, 0, 1)` as a legacy const generic argument): evaluated with the
        // arguments bound (rustc evaluates the anon const by CTFE; this covers the
        // arithmetic-only ones before the JIT exists)
        ExprKind::Call(f, args) => {
            let fp = f_ast_path(prog, file, *f)?;
            let segs = crate::program::path_segs(prog, file, &fp);
            let d = if segs.len() == 1 {
                prog.lookup_in_scope(module, segs[0].1, false)?
            } else {
                let parent = prog.resolve_mod_path(module, fp.global(), &segs[..segs.len() - 1], false, false)?;
                prog.lookup_in_container(parent, segs[segs.len() - 1].1, false)?
            };
            let def = prog.def(d);
            if def.kind != DefKind::Fn {
                return None;
            }
            let fast = &prog.files[def.file as usize].ast;
            // the body may be one the load skipped (parsed now with its file's others)
            let (sig, body) = match &fast.item(def.item).kind {
                ItemKind::Fn(sig, _, _) if fast.fn_sig(*sig).konst && fast.fn_sig(*sig).generics.params.is_empty() && fast.fn_sig(*sig).params.len() == args.len() => (fast.fn_sig(*sig), prog.fn_body(def.file, def.item).ok().flatten()?),
                _ => return None,
            };
            let tail = match fast.stmts(body) {
                [crate::ast::Stmt::Expr(x, false)] => *x,
                _ => return None,
            };
            let mut binds = Vec::new();
            for (p, a) in fast.list(sig.params).iter().zip(prog.files[file as usize].ast.list(*args)) {
                let name = match fast.pat(p.pat) {
                    crate::ast::Pat::Ident { name, sub: None, .. } => prog.syms.get(prog.files[def.file as usize].text(*name))?,
                    _ => return None,
                };
                binds.push((name, eval_i(cx, prog, tcx, file, module, *a, depth + 1)?));
            }
            let n = {
                let mut e = cx.state.call_env.borrow_mut();
                let n = e.len();
                e.push(binds);
                n
            };
            let r = eval_i(cx, prog, tcx, def.file, def.scope, tail, depth + 1);
            cx.state.call_env.borrow_mut().truncate(n);
            r
        }
        ExprKind::Path(p) => {
            let segs = crate::program::path_segs(prog, file, p);
            // a param of the const fn being evaluated
            if segs.len() == 1 && !p.global() {
                if let Some(v) = cx.state.call_env.borrow().last().and_then(|b| b.iter().find(|x| x.0 == segs[0].1).map(|x| x.1)) {
                    return Some(v);
                }
            }
            // `<T as Trait>::CONST` / `<T>::CONST` with T a concrete type
            if let Some(q) = f.ast.qself(p) {
                if segs.len() != 1 {
                    return None;
                }
                let q = q.clone();
                // `<Self as Tr>::CONST`: Self is the self type the expression is evaluated in
                let mut env = crate::tcx::GenEnv::default();
                env.self_ty = cx.state.const_self.get().map(|x| x.0);
                let (t, _) = tcx.with_errors(cx, || tcx.lower_ty(cx, prog, file, module, &env, q.ty));
                if t == tcx.tys.error || !tcx.tys.is_concrete(t) {
                    return None;
                }
                let td = match &q.trait_path {
                    Some(tp) => Some(tcx.resolve_type_path_def(prog, file, module, tp)?),
                    None => None,
                };
                return type_const_of(cx, prog, tcx, t, None, td, segs[0].1, depth + 1);
            }
            // `N::CONST` with N a param of the impl whose const is evaluated for a known type
            if segs.len() == 2 && !p.global() && segs[0].0 != crate::ast::SegKind::SelfType {
                let bound = (|| {
                    let c = cx.state.const_args.borrow();
                    let (imp, args) = c.as_ref()?;
                    let i = tcx.impl_generics.get(imp)?.names.iter().position(|n| *n == segs[0].1)?;
                    args.get(i).copied()
                })();
                if let Some(t) = bound {
                    return type_const(cx, prog, tcx, t, None, segs[1].1, depth + 1);
                }
            }
            // `Self::Assoc::CONST` (a trait default through an associated type of the impl)
            if segs.len() == 3 && segs[0].0 == crate::ast::SegKind::SelfType {
                let (st, imp) = cx.state.const_self.get()?;
                let imp = imp?;
                let td = *tcx.impl_trait.get(&imp)?;
                let ad = prog.traits[prog.def(td).sub as usize].iter().copied().find(|&it| prog.def(it).name == segs[1].1 && prog.def(it).kind == DefKind::AssocTy)?;
                let iargs = cx.state.const_args.borrow().as_ref().filter(|x| x.0 == imp).map(|x| x.1.clone()).unwrap_or_default();
                let mut args = vec![st];
                for a in tcx.impl_trait_args.get(&imp).cloned().unwrap_or_default() {
                    args.push(tcx.tys.subst(a, &iargs));
                }
                let pt = tcx.tys.intern(crate::types::TyKind::Assoc(ad, args, crate::types::RegionArgsId::EMPTY));
                let t = tcx.normalize(cx, prog, pt);
                if !tcx.tys.is_concrete(t) || matches!(tcx.tys.kind(t), crate::types::TyKind::Assoc(..) | crate::types::TyKind::Error) {
                    return None;
                }
                return type_const(cx, prog, tcx, t, None, segs[2].1, depth + 1);
            }
            // `Self::CONST` in an impl header / item (`{(Self::BITS / 8) as usize}`)
            // (a type-relative path on the self type, rustc resolve_fully_qualified_call: the
            // inherent const, else a const of any trait the type implements -- the enclosing
            // impl is a candidate only when its trait declares the const: `[u8; Self::MAX_STR_LEN]`
            // in `impl Sealed for u32` is `<u32 as Integer>::MAX_STR_LEN`)
            if segs.len() == 2 && segs[0].0 == crate::ast::SegKind::SelfType {
                let (st, imp) = cx.state.const_self.get()?;
                let imp = imp.filter(|i| impl_trait_declares_const(prog, tcx, *i, segs[1].1));
                return type_const(cx, prog, tcx, st, imp, segs[1].1, depth + 1);
            }
            let d = if segs.len() == 1 {
                prog.lookup_in_scope(module, segs[0].1, false)?
            } else {
                match prog.resolve_mod_path(module, p.global(), &segs[..segs.len() - 1], false, false).and_then(|parent| prog.lookup_in_container(parent, segs[segs.len() - 1].1, false)) {
                    Some(d) => d,
                    // `Type::CONST` (an associated const: `usize::BITS`, `Foo::N`, a trait's
                    // through the type's impl)
                    None if segs.len() == 2 => match assoc_const_of(cx, prog, tcx, module, p.global(), segs[0].1, segs[1].1) {
                        Some(d) => d,
                        None => {
                            let t = type_named(cx, prog, tcx, module, p.global(), segs[0].1)?;
                            return type_const(cx, prog, tcx, t, None, segs[1].1, depth + 1);
                        }
                    },
                    None => return None,
                }
            };
            eval_const_def(cx, prog, tcx, d, depth)
        }
        _ => None,
    }
}

/// The value of const item `d` (its initializer evaluated syntactically, else by running it:
/// requested from the JIT).
pub fn eval_const_def(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, d: DefId, depth: u32) -> Option<i128> {
    {
        {
            let def = prog.def(d);
            if def.kind != DefKind::Const && def.kind != DefKind::AssocConst {
                return None;
            }
            if let Some(v) = tcx.const_values.get(&d) {
                return Some(v as i128);
            }
            if let Some(init) = prog.const_body(def.file, def.item).ok().flatten() {
                if let Some(v) = eval_i(cx, prog, tcx, def.file, def.scope, init, depth + 1) {
                    return Some(v);
                }
            }
            // anything else (const fn calls such as `SLICE.len()`) is evaluated by running the
            // initializer (rustc CTFE): requested here, done by the JIT, then retried
            if !tcx.const_failed.contains(&d) {
                cx.state.const_wait.set(true);
                cx.state.const_asked.set(cx.state.const_asked.get() + 1);
                crate::tcx::request_const(cx, tcx, d);
            }
            None
        }
    }
}

/// A constant's value (stored unsigned) as a discriminant of type `ty`.
pub fn wrap_disc(v: i128, ty: (u32, bool)) -> i128 {
    wrap_int(v, ty.0, ty.1)
}

/// Wraps `v` to an integer type of `bytes` bytes (signed or not).
fn wrap_int(v: i128, bytes: u32, signed: bool) -> i128 {
    if bytes >= 16 {
        return v;
    }
    let bits = bytes * 8;
    let m = (1i128 << bits) - 1;
    let u = v & m;
    if signed && u >> (bits - 1) & 1 == 1 {
        u - (1i128 << bits)
    } else {
        u
    }
}

fn prim_int(text: &str) -> Option<(u32, bool)> {
    let p = crate::program::PRIMS.iter().find(|(n, _)| *n == text)?.1;
    match crate::types::Types::int_info(p) {
        (0, _) => None,
        x => Some(x),
    }
}

/// An enum discriminant expression evaluated as its discriminant type (rustc: an anonymous
/// const of the repr type, isize by default; unsuffixed literals take that type, arithmetic
/// wraps in it, `as` casts truncate). None when the expression is beyond this evaluator.
pub fn eval_disc(prog: &Program, file: u32, module: u32, e: ExprId, ty: (u32, bool)) -> Option<i128> {
    eval_t(prog, file, module, e, ty, 0)
}

fn eval_t(prog: &Program, file: u32, module: u32, e: ExprId, ty: (u32, bool), depth: u32) -> Option<i128> {
    if depth > 32 {
        return None;
    }
    let (bytes, signed) = ty;
    let w = |v: i128| wrap_int(v, bytes, signed);
    let f = &prog.files[file as usize];
    let ex = f.ast.expr(e);
    match &ex.kind {
        ExprKind::Lit(LitKind::Int) => {
            let t = std::str::from_utf8(f.bytes(ex.lo, ex.hi)).ok()?;
            let v = parse_int_lit(t)? as i128;
            // a suffixed literal has its own type; the value is then used as `ty` by the
            // surrounding expression (type errors are rustc's business, not ours)
            match int_suffix(t).and_then(prim_int) {
                Some((b, s)) => Some(wrap_int(v, b, s)),
                None => Some(w(v)),
            }
        }
        ExprKind::Lit(LitKind::Bool(b)) => Some(*b as i128),
        ExprKind::Lit(LitKind::Char) | ExprKind::Lit(LitKind::Byte) => {
            let t = std::str::from_utf8(f.bytes(ex.lo, ex.hi)).ok()?;
            let v = if matches!(ex.kind, ExprKind::Lit(LitKind::Byte)) {
                *crate::lit::unescape_bytes(t).first()? as i128
            } else {
                crate::lit::unescape_str(t).chars().next()? as i128
            };
            Some(w(v))
        }
        ExprKind::Paren(x) => eval_t(prog, file, module, *x, ty, depth + 1),
        ExprKind::Cast(x, t) => {
            // `!0 as u8`: the operand takes the cast's type as its hint (ExpectCastableToType)
            let tt = match f.ast.ty(*t) {
                crate::ast::Ty::Path(p) if p.segs.len() == 1 => {
                    let n = std::str::from_utf8(f.bytes(f.ast.segs(p.segs)[0].name.lo, f.ast.segs(p.segs)[0].name.hi)).ok()?;
                    prim_int(n)?
                }
                _ => return None,
            };
            let v = eval_t(prog, file, module, *x, tt, depth + 1)?;
            Some(w(wrap_int(v, tt.0, tt.1)))
        }
        ExprKind::Block(b, _) => {
            let blk = f.ast.block(*b);
            if blk.stmts.len() == 1 {
                if let crate::ast::Stmt::Expr(x, false) = f.ast.list(blk.stmts)[0] {
                    return eval_t(prog, file, module, x, ty, depth + 1);
                }
            }
            None
        }
        ExprKind::Unary(UnOp::Neg, x) => Some(w(-eval_t(prog, file, module, *x, ty, depth + 1)?)),
        ExprKind::Unary(UnOp::Not, x) => Some(w(!eval_t(prog, file, module, *x, ty, depth + 1)?)),
        ExprKind::Binary(op, a, b) => {
            let a = eval_t(prog, file, module, *a, ty, depth + 1)?;
            let b = eval_t(prog, file, module, *b, ty, depth + 1)?;
            Some(w(match op {
                BinOp::Add => a.wrapping_add(b),
                BinOp::Sub => a.wrapping_sub(b),
                BinOp::Mul => a.wrapping_mul(b),
                BinOp::Div if b != 0 => a / b,
                BinOp::Rem if b != 0 => a % b,
                BinOp::Shl if (0..128).contains(&b) => a << b,
                BinOp::Shr if (0..128).contains(&b) => a >> b,
                BinOp::BitAnd => a & b,
                BinOp::BitOr => a | b,
                BinOp::BitXor => a ^ b,
                BinOp::Lt => (a < b) as i128,
                BinOp::Le => (a <= b) as i128,
                BinOp::Gt => (a > b) as i128,
                BinOp::Ge => (a >= b) as i128,
                BinOp::Eq => (a == b) as i128,
                BinOp::Ne => (a != b) as i128,
                _ => return None,
            }))
        }
        ExprKind::Path(p) => {
            let segs = crate::program::path_segs(prog, file, p);
            let d = if segs.len() == 1 {
                prog.lookup_in_scope(module, segs[0].1, false)?
            } else {
                let parent = prog.resolve_mod_path(module, p.global(), &segs[..segs.len() - 1], false, false)?;
                prog.lookup_in_container(parent, segs[segs.len() - 1].1, false)?
            };
            let def = prog.def(d);
            if def.kind == DefKind::Variant {
                // another variant's discriminant (`Y = Foo::X as isize - 3`)
                let pd = prog.def(def.parent);
                let past = &prog.files[pd.file as usize].ast;
                if let ItemKind::Enum(_, vars) = &past.item(pd.item).kind {
                    // variant k: its own expression, else the previous one's + 1 (forward
                    // references `X = Y as isize * 2` are fine)
                    let mut k = def.sub as usize;
                    let mut add = 0;
                    loop {
                        match past.list(*vars).get(k)?.disc {
                            Some(de) => return Some(w(eval_t(prog, pd.file, pd.scope, de, ty, depth + 1)? + add)),
                            None if k == 0 => return Some(add),
                            None => {
                                k -= 1;
                                add += 1;
                            }
                        }
                    }
                }
                return None;
            }
            if def.kind != DefKind::Const {
                return None;
            }
            let ast = &prog.files[def.file as usize].ast;
            if let ItemKind::Const(cty, Some(init)) = &ast.item(def.item).kind {
                // the const's own type when it is a primitive integer
                let ct = match cty.map(|c| ast.ty(c)) {
                    Some(crate::ast::Ty::Path(p)) if p.segs.len() == 1 => {
                        let cf = &prog.files[def.file as usize];
                        std::str::from_utf8(cf.bytes(cf.ast.segs(p.segs)[0].name.lo, cf.ast.segs(p.segs)[0].name.hi)).ok().and_then(prim_int).unwrap_or(ty)
                    }
                    _ => ty,
                };
                let init = prog.const_body(def.file, def.item).ok().flatten().unwrap_or(*init);
                return eval_t(prog, def.file, def.scope, init, ct, depth + 1).map(w);
            }
            None
        }
        _ => None,
    }
}

/// The inherent associated const `name` of the type named `ty` (a primitive, or a non-generic
/// ADT / alias in scope).
fn assoc_const_of(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, module: u32, global: bool, ty: crate::program::Sym, name: crate::program::Sym) -> Option<DefId> {
    let t = type_named(cx, prog, tcx, module, global, ty)?;
    let (it, _) = tcx.inherent_item(cx, prog, t, name)?;
    if prog.def(it).kind == DefKind::AssocConst {
        Some(it)
    } else {
        None
    }
}

/// The type a one-segment path names (a primitive, an ADT without args, an alias).
fn type_named(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, module: u32, global: bool, ty: crate::program::Sym) -> Option<crate::types::TyId> {
    let t = match crate::program::PRIMS.iter().find(|(n, _)| prog.syms.get(n) == Some(ty)) {
        Some((_, prim)) if !global => {
            let k = match prim {
                crate::program::Prim::F32 | crate::program::Prim::F64 => crate::types::TyKind::Float(*prim),
                crate::program::Prim::Bool => crate::types::TyKind::Bool,
                crate::program::Prim::Char => crate::types::TyKind::Char,
                crate::program::Prim::Str => crate::types::TyKind::Str,
                _ => crate::types::TyKind::Int(*prim),
            };
            tcx.tys.lookup(&k)?
        }
        _ => {
            let d = prog.lookup_in_scope(module, ty, true)?;
            match prog.def(d).kind {
                DefKind::Struct | DefKind::Enum | DefKind::Union => tcx.tys.lookup(&crate::types::TyKind::Adt(d, Vec::new(), crate::types::RegionArgsId::EMPTY))?,
                DefKind::TypeAlias => tcx.alias_tys.get(&(cx.typing_env, d))?,
                _ => return None,
            }
        }
    };
    Some(t)
}

/// `T::CONST` / `Self::CONST` with T known: the inherent const, else a trait's const through
/// T's impl of it (`u64::BYTE_LEN` with `impl FixedSizeEncoding<8, 0> for u64`).
fn type_const(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, t: crate::types::TyId, imp: Option<DefId>, name: crate::program::Sym, depth: u32) -> Option<i128> {
    type_const_of(cx, prog, tcx, t, imp, None, name, depth)
}

/// type_const, optionally only through impls of trait `td` (`<T as Tr>::CONST`). A generic
/// impl applies when its self type matches `t`; its const is evaluated with the impl's params
/// bound to the matched args (the evaluation frame's const_args) and `Self` = `t`.
fn type_const_of(cx: &crate::tcx::EvalCx<'_>, prog: &Program, tcx: &Tcx, t: crate::types::TyId, imp: Option<DefId>, td: Option<DefId>, name: crate::program::Sym, depth: u32) -> Option<i128> {
    if td.is_none() {
        if let Some((it, _)) = tcx.inherent_item(cx, prog, t, name) {
            if prog.def(it).kind == DefKind::AssocConst {
                return eval_const_def(cx, prog, tcx, it, depth);
            }
        }
    }
    if cx.state.tc_depth.get() > 16 {
        return None;
    }
    // (None: keep the args already bound -- `Self::CONST` inside the impl being evaluated)
    let mut cands: Vec<(DefId, Option<Vec<crate::types::TyId>>)> = imp.into_iter().map(|i| (i, None)).collect();
    if cands.is_empty() {
        let concrete = tcx.tys.is_concrete(t);
        for im in &prog.impls {
            let Some(&itd) = tcx.impl_trait.get(&im.def) else { continue };
            if td.map_or(false, |d| d != itd) {
                continue;
            }
            let Some(&pat) = tcx.impl_self.get(&im.def) else { continue };
            let n = tcx.impl_generics.get(&im.def).map_or(0, |e| e.names.len());
            if pat == t {
                // (params the self type does not determine -- `impl<const N: usize> Tr<N> for ()`
                // -- leave the const ambiguous: rustc "depends on a generic parameter")
                if n == 0 {
                    cands.push((im.def, Some(Vec::new())));
                }
                continue;
            }
            if n == 0 || !concrete || !prog.traits[prog.def(itd).sub as usize].iter().any(|&it| prog.def(it).name == name && prog.def(it).kind == DefKind::AssocConst) {
                continue;
            }
            let mut b = vec![None; n];
            if tcx.match_ty(cx, pat, t, &mut b) && b.iter().all(|x| x.is_some()) {
                cands.push((im.def, Some(b.into_iter().flatten().collect())));
            }
        }
    }
    for (imp, args) in cands {
        cx.state.tc_depth.set(cx.state.tc_depth.get() + 1);
        let outer_self = set_const_self(cx, Some((t, Some(imp))));
        let outer_args = args.map(|a| cx.state.const_args.replace(Some((imp, a))));
        let r = tcx.impl_trait_const(cx, prog, imp, name);
        if let Some(o) = outer_args {
            *cx.state.const_args.borrow_mut() = o;
        }
        set_const_self(cx, outer_self);
        cx.state.tc_depth.set(cx.state.tc_depth.get() - 1);
        if let Some(v) = r {
            if let crate::types::TyKind::ConstVal(v) = tcx.tys.kind(v) {
                return Some(*v as i128);
            }
        }
    }
    None
}

/// Does impl `imp` implement a trait that declares associated const `name`?
fn impl_trait_declares_const(prog: &Program, tcx: &Tcx, imp: DefId, name: crate::program::Sym) -> bool {
    match tcx.impl_trait.get(&imp) {
        Some(&td) => prog.traits[prog.def(td).sub as usize].iter().any(|&it| prog.def(it).name == name && prog.def(it).kind == DefKind::AssocConst),
        None => true,
    }
}

/// Sets the `Self` (and impl) a const expression is evaluated in (Tcx::const_arg), returning
/// the previous one.
pub fn set_const_self(cx: &crate::tcx::EvalCx<'_>, v: Option<(crate::types::TyId, Option<DefId>)>) -> Option<(crate::types::TyId, Option<DefId>)> {
    cx.state.const_self.replace(v)
}
