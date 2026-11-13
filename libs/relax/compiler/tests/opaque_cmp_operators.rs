// `==` / `!=` / `<` on an opaque type (`impl PartialEq + use<>` returned by another fn) call its
// PartialEq / PartialOrd bound, whatever the hidden type (rustc op.rs is_builtin_binop: only scalar
// operands are built in). A built-in comparison of an aggregate hidden type found two different
// values equal: an app's theme check `structure(&before) != structure(&after)` over a tuple of maps.
use std::collections::BTreeMap;
use std::fmt::Debug;

fn one(k: bool) -> impl PartialEq + Debug + use<> {
    [k as u64; 1]
}
fn tuple(k: bool) -> impl PartialEq + use<> {
    let mut m = BTreeMap::new();
    if k {
        m.insert("k".to_owned(), "v".to_owned());
    }
    (m, Vec::<String>::new(), Vec::<f32>::new())
}
fn ordered(k: u32) -> impl PartialOrd + use<> {
    (k, String::from("x"))
}
fn scalar(k: u64) -> impl PartialEq + use<> {
    k
}

#[test]
fn opaque_aggregates_compare_by_value() {
    assert!(one(false) != one(true));
    assert!(!(one(false) == one(true)));
    assert!(one(true) == one(true));
    assert!(tuple(false) != tuple(true));
    assert!(tuple(true) == tuple(true));
    assert!(ordered(1) < ordered(2));
    assert!(!(ordered(2) <= ordered(1)));
    assert!(scalar(0) != scalar(1));
}
