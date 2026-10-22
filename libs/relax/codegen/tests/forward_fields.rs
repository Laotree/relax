//! forward_param_fields: loads of a noalias parameter's field that every path reaches with the
//! value known (stored on one path, loaded on the other) read it from a register; a call given the
//! pointer, or a store over the field's bytes with another type, forgets it.
use relax_backend::rir::*;
use relax_codegen::opt::forward_param_fields;

fn push(f: &mut Func, b: u32, i: Inst) {
    f.blocks[b as usize].insts.push(i);
    f.blocks[b as usize].pos.push(1);
}

/// f(p, c, x): b0: t = [p+8] (u32); branch c -> b1 / b2; b1: [p+8] = x (u32); b2: (nothing);
/// b3: [between] r = [p+8] (u32); ret r + t
fn shape(between: Option<Inst>) -> (Func, VReg) {
    let mut f = Func::new("fields".into(), 0);
    let (p, c, x) = (f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I));
    f.params = vec![p, c, x];
    f.noalias = vec![p];
    f.rets = vec![Cls::I];
    for _ in 0..4 {
        f.block();
    }
    let (t, r, s) = (f.vreg(Cls::I), f.vreg(Cls::I), f.vreg(Cls::I));
    let m = Mem::Int(4, false);
    push(&mut f, 0, Inst::Load(m, t, p, 8));
    f.blocks[0].term = Term::Branch(c, 1, 2);
    push(&mut f, 1, Inst::Store(m, p, 8, x));
    f.blocks[1].term = Term::Jump(3);
    f.blocks[2].term = Term::Jump(3);
    if let Some(i) = between {
        push(&mut f, 3, i);
    }
    push(&mut f, 3, Inst::Load(m, r, p, 8));
    push(&mut f, 3, Inst::IBin(IOp::Add, U64, s, r, t));
    f.blocks[3].term = Term::Ret(vec![s]);
    f.verify().unwrap();
    (f, r)
}

fn loads_of(f: &Func, b: usize) -> usize {
    f.blocks[b].insts.iter().filter(|i| matches!(i, Inst::Load(..))).count()
}

#[test]
fn a_field_known_on_every_path_is_not_reloaded() {
    let (mut f, r) = shape(None);
    assert!(forward_param_fields(&relax_session::Options::default(), &mut f));
    f.verify().unwrap();
    assert_eq!(loads_of(&f, 3), 0, "{}", f.dump());
    // r reads the field's variable; the store's path converts x to the u32 a load returns
    assert!(f.blocks[3].insts.iter().any(|i| matches!(i, Inst::Mov(d, _) if *d == r)));
    assert!(f.blocks[1].insts.iter().any(|i| matches!(i, Inst::Conv(Conv::IntToInt(IntTy { bits: 32, signed: false }), _, s) if *s == f.params[2])));
}

#[test]
fn a_call_given_the_pointer_forgets_the_field() {
    let (mut f, _) = shape(None);
    let p = f.params[0];
    f.blocks[3].insts.insert(0, Inst::Call(Callee::Host(Sym { id: 7, off: 0 }), vec![p], Vec::new()));
    f.blocks[3].pos.insert(0, 1);
    forward_param_fields(&relax_session::Options::default(), &mut f);
    assert_eq!(loads_of(&f, 3), 1, "{}", f.dump());
}

#[test]
fn a_call_not_given_the_pointer_keeps_the_field() {
    let (mut f, _) = shape(Some(Inst::Call(Callee::Host(Sym { id: 7, off: 0 }), Vec::new(), Vec::new())));
    assert!(forward_param_fields(&relax_session::Options::default(), &mut f));
    assert_eq!(loads_of(&f, 3), 0, "{}", f.dump());
}

#[test]
fn an_overlapping_store_of_another_type_forgets_the_field() {
    let mut fx = shape(None).0;
    let p = fx.params[0];
    let x = fx.params[2];
    // a byte store into the field's bytes
    fx.blocks[2].insts.push(Inst::Store(Mem::Int(1, false), p, 9, x));
    fx.blocks[2].pos.push(1);
    forward_param_fields(&relax_session::Options::default(), &mut fx);
    assert_eq!(loads_of(&fx, 3), 1, "{}", fx.dump());
}

#[test]
fn a_captured_pointer_is_left_alone() {
    let (mut f, _) = shape(None);
    let (p, x) = (f.params[0], f.params[2]);
    // p stored as a value through x
    f.blocks[0].insts.insert(0, Inst::Store(Mem::Int(8, false), x, 0, p));
    f.blocks[0].pos.insert(0, 1);
    assert!(!forward_param_fields(&relax_session::Options::default(), &mut f));
}
