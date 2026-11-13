// A `const fn` may move out a local it borrowed mutably once a block boundary (a call) separates
// the borrow from the move: rustc's const-check qualif join (`qualif.join(..) || borrow.join(..)`)
// drops the borrow set when it adds qualifs, so the move clears the local's NeedsNonConstDrop.
// rustc 1.100.0 accepts every function here; without the calls it rejects `taken_and_kept`.
use std::borrow::Cow;

pub struct S(pub String);

const fn mk() -> S {
    S(String::new())
}
const fn nop() {}
const fn sink(_: &mut S) {}
const fn back(r: &mut S) -> &mut S {
    r
}

pub const fn borrowed_into_a_call() -> S {
    let mut out = mk();
    sink(&mut out);
    out
}

pub const fn borrowed_then_a_call() -> S {
    let mut out = mk();
    let _r = &mut out;
    nop();
    out
}

pub const fn reborrow_kept_after_the_call() -> S {
    let mut out = mk();
    let _x = back(&mut out);
    out
}

pub const fn replaced_in_place() -> S {
    let mut out = mk();
    std::mem::forget(std::mem::replace(&mut out, mk()));
    out
}

#[derive(Debug, Clone, PartialEq)]
pub struct Info {
    pub id: Cow<'static, str>,
    pub n: u32,
}

/// The table builder of a `const` parameter list: blanks replaced in place, then returned.
pub const fn table<const N: usize>(ns: &[u32; N]) -> [Info; N] {
    const BLANK: Info = Info { id: Cow::Borrowed(""), n: 0 };
    let mut out = [BLANK; N];
    let mut i = 0;
    while i < N {
        std::mem::forget(std::mem::replace(&mut out[i], Info { id: Cow::Borrowed("x"), n: ns[i] }));
        i += 1;
    }
    out
}

const T: [Info; 3] = table(&[1, 2, 3]);

#[test]
fn a_moved_local_borrowed_before_a_call_is_no_live_drop() {
    assert!(borrowed_into_a_call().0.is_empty());
    assert!(borrowed_then_a_call().0.is_empty());
    assert!(reborrow_kept_after_the_call().0.is_empty());
    assert!(replaced_in_place().0.is_empty());
}

#[test]
fn a_const_table_is_built_in_place() {
    assert_eq!(T[2].n, 3);
    assert_eq!(T[0].id, "x");
    let rt = table(&[4, 5]);
    assert_eq!(rt[1], Info { id: Cow::Borrowed("x"), n: 5 });
}
