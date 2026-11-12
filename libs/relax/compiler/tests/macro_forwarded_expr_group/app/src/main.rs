// A fragment a macro_rules arm forwards reaches a proc macro in an invisible group
// (rustc's proc_macro bridge: `OpenInvisible(MetaVar(..))` .. `CloseInvisible` is
// `Group(Delimiter::None)`), which a macro that parses with syn reads through. sqlx's
// query_as! forwards `$query:expr` to expand_query!: `"sql" + $tail` and `x as _` there --
// before: the group was a pair of real parentheses, "expected string literal" and
// "non-primitive cast" (the `as _` was not seen).
macro_rules! source {
    ($q:expr) => { fwd_mac::joined!(source = $q) };
}
macro_rules! with_tail {
    ($tail:tt) => { source!("head " + $tail) };
}
macro_rules! arg {
    ($a:expr) => { fwd_mac::inferred!($a) };
}

fn main() {
    assert_eq!(source!("one"), "one");
    assert_eq!(source!("a" + "b"), "ab");
    assert_eq!(with_tail!("tail"), "head tail");
    assert!(arg!(1u8 as _));
    assert!(!arg!((1u8 as _)));
    assert!(!arg!(1u8));
    println!("forwarded expr group ok {} {}", with_tail!("tail"), arg!(2u8 as _));
}
