// Debug impls real std has (std_debug, 1.16; hash_extract_if, 1.88) that derive(Debug) on
// wrappers needs: slotmap's `#[derive(Debug)] struct Drain { inner: hash_map::Drain<..> }` and
// futures-util's Remote, whose `CatchUnwind<AssertUnwindSafe<Fut>>` derives Debug.
use std::collections::{HashMap, HashSet};
use std::panic::AssertUnwindSafe;

#[derive(Debug)]
struct Wrapped<'a> {
    inner: std::collections::hash_map::Drain<'a, u32, char>,
}

#[test]
fn map_and_set_iterators_print_their_items() {
    let mut m = HashMap::from([(1u32, 'a')]);
    let w = Wrapped { inner: m.drain() };
    assert_eq!(format!("{w:?}"), "Wrapped { inner: [(1, 'a')] }");
    drop(w);
    let mut m = HashMap::from([(2u32, 'b')]);
    assert_eq!(format!("{:?}", m.extract_if(|_, _| false)), "ExtractIf { .. }");

    let a = HashSet::from([3u8]);
    let b = HashSet::from([4u8]);
    assert_eq!(format!("{:?}", a.difference(&b)), "[3]");
    assert_eq!(format!("{:?}", a.intersection(&a)), "[3]");
    assert_eq!(format!("{:?}", a.symmetric_difference(&a)), "[]");
    assert_eq!(format!("{:?}", a.union(&a)), "[3]");
    assert_eq!(format!("{:?}", a.clone().into_iter()), "[3]");
    let mut c = a.clone();
    assert_eq!(format!("{:?}", c.drain()), "[3]");
}

#[test]
fn assert_unwind_safe_prints_as_a_tuple() {
    assert_eq!(format!("{:?}", AssertUnwindSafe(5)), "AssertUnwindSafe(5)");
    assert_eq!(format!("{:#?}", AssertUnwindSafe("x")), "AssertUnwindSafe(\n    \"x\",\n)");
}
