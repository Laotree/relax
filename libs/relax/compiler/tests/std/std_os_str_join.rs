// std/ffi: `[S].join(&OsStr)` — std's `Join<&OsStr>` impl (`ring`'s build.rs joins `Path`
// components with it). alloc's `&str` and `&[T]` impls are checked beside it.
use std::ffi::{OsStr, OsString};

#[test]
fn a01_join_os_str_parts() {
    let parts: [&OsStr; 3] = [OsStr::new("a"), OsStr::new("b"), OsStr::new("c")];
    let joined: OsString = parts.join(OsStr::new("/"));
    assert_eq!(joined.to_str().unwrap(), "a/b/c");
}

#[test]
fn a02_join_empty_and_single() {
    let none: [&OsStr; 0] = [];
    assert_eq!(none.join(OsStr::new("/")).to_str().unwrap(), "");
    let one: [&OsStr; 1] = [OsStr::new("x")];
    assert_eq!(one.join(OsStr::new("/")).to_str().unwrap(), "x");
}

#[test]
fn a03_join_str_and_vec_still_work() {
    assert_eq!(["x", "y"].join("-"), "x-y");
}
