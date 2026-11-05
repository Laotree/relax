// Type checking and lowering cases larger crates rely on, each as rustc does it: `?` passes the
// expected type back to its operand (`let n: i64 = -s.parse()?`), a scalar left operand compares
// with a user type through `PartialEq<User> for u16`, `&str` comparisons through their traits, a
// struct literal through a projection (`Self::Out { .. }`, `T::Out { .. }`, an alias to one), a
// precise closure capture of a nested field (the uncaptured siblings drop with their owner),
// temporaries extended through `if` and `match` arms, constant promotion (`&(1 + 2)`,
// `&CONST.field`), a constant pattern of several scalars and a single-variant enum's discriminant.
// Run with `makepad test` and rustc --test; lines "| " are compared.
use std::cell::RefCell;

thread_local! { static LOG: RefCell<Vec<String>> = RefCell::new(Vec::new()); }
fn log(s: &str) {
    LOG.with(|l| l.borrow_mut().push(s.to_string()));
}
fn take() -> String {
    LOG.with(|l| std::mem::take(&mut *l.borrow_mut())).join(",")
}
struct D(&'static str);
impl Drop for D {
    fn drop(&mut self) {
        log(self.0);
    }
}

fn negated(s: &str) -> Result<i64, std::num::ParseIntError> {
    let n: i64 = -s.parse()?;
    Ok(n)
}

#[test]
fn try_passes_the_expected_type_back() {
    println!("| {:?} {:?}", negated("5"), negated("x").is_err());
}

#[derive(Debug, Clone, Copy)]
struct Code(u16);
impl PartialEq<Code> for u16 {
    fn eq(&self, other: &Code) -> bool {
        *self == other.0
    }
}
impl PartialOrd<Code> for u16 {
    fn partial_cmp(&self, other: &Code) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.0)
    }
}

#[test]
fn scalar_left_operand_with_a_user_type() {
    let c = Code(7);
    let s: &str = "abc";
    let owned = String::from("abc");
    println!("| {} {} {} {} {} {}", 7u16 == c, 8u16 != c, 6u16 < c, s == owned, owned == s, s < "abd");
}

trait Make {
    type Out;
    fn make() -> Self::Out;
}
struct Point {
    x: i32,
    y: i32,
}
impl Make for () {
    type Out = Point;
    fn make() -> Self::Out {
        Self::Out { x: 1, y: 2 }
    }
}
fn build<T: Make<Out = Point>>() -> Point {
    T::Out { x: 3, y: 4 }
}
type Made = <() as Make>::Out;

#[test]
fn struct_literal_through_a_projection() {
    let (p, q, r) = (<() as Make>::make(), build::<()>(), Made { x: 5, y: 6 });
    println!("| {} {} {} {} {} {}", p.x, p.y, q.x, q.y, r.x, r.y);
}

struct Inner {
    name: D,
    other: D,
}
struct Outer {
    inner: Inner,
    tail: D,
}

#[test]
fn closure_owns_only_the_nested_field_it_captures() {
    let o = Outer { inner: Inner { name: D("name"), other: D("other") }, tail: D("tail") };
    let c = move || {
        let n = o.inner.name;
        log("in closure");
        drop(n);
    };
    log("before call");
    c();
    log("after call");
    drop(o.inner.other);
    log("end");
    drop(o.tail);
    println!("| {}", take());
}

#[test]
fn unused_nested_capture_drops_with_the_closure() {
    let o = Outer { inner: Inner { name: D("name2"), other: D("other2") }, tail: D("tail2") };
    let c = move || {
        let _r = &o.inner.name;
        log("seen");
    };
    c();
    drop(c);
    log("closure gone");
    drop(o.inner.other);
    drop(o.tail);
    println!("| {}", take());
}

fn make(s: &'static str) -> D {
    D(s)
}

#[test]
fn temporaries_extended_through_if_and_match() {
    for flag in [true, false] {
        let r = if flag { &make("then") } else { &make("else") };
        log(r.0);
        let m = match flag {
            true => &make("arm1"),
            false => &make("arm2"),
        };
        log(m.0);
    }
    println!("| {}", take());
}

struct Pair {
    a: [i32; 3],
    b: i32,
}
const PAIR: Pair = Pair { a: [4, 5, 6], b: 9 };
const T: (u8, u16) = (1, 2);

fn promoted() -> &'static i32 {
    &(1 + 2)
}

fn field_of_const() -> &'static [i32; 3] {
    &PAIR.a
}

#[test]
fn constants_promoted_to_static_memory() {
    let t: &'static u16 = &T.1;
    let b: &'static i32 = &PAIR.b;
    println!("| {} {:?} {} {}", promoted(), field_of_const(), t, b);
}

#[derive(PartialEq, Eq)]
struct Key {
    a: u8,
    b: u32,
}
const K: Key = Key { a: 1, b: 300 };

#[derive(Clone, Copy)]
enum One {
    Only = 5,
}

#[test]
fn constant_patterns_and_single_variant_tags() {
    let probe = |k: Key| match k {
        K => "k",
        _ => "other",
    };
    let e = One::Only;
    println!("| {} {} {} {}", probe(Key { a: 1, b: 300 }), probe(Key { a: 1, b: 301 }), e as i32, std::mem::size_of::<One>());
}
