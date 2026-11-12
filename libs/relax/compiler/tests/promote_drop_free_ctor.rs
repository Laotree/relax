// `&E::B` where E has drop glue is still promoted to a 'static when the value itself needs no
// drop (rustc qualifies promotion by value). A function can return it.
#[derive(Debug, PartialEq)]
enum Kind { Unit, Named(String), Pair(u8, u8) }

struct Wrapper { id: u32, tag: Option<String> }

fn unit() -> &'static Kind { &Kind::Unit }
fn pair() -> &'static Kind { &Kind::Pair(3, 4) }
fn wrapper() -> &'static Wrapper { &Wrapper { id: 9, tag: None } }

fn clobber() -> u64 {
    // overwrite the stack below the caller so a dangling reference shows up
    let a = [0xdead_beef_u64; 64];
    a.iter().copied().fold(0, |x, y| x ^ y)
}

#[test]
fn promoted_ctors_outlive_their_function() {
    let (u, p, w) = (unit(), pair(), wrapper());
    clobber();
    assert_eq!(*u, Kind::Unit);
    assert_eq!(*p, Kind::Pair(3, 4));
    assert_eq!(w.id, 9);
    assert!(w.tag.is_none());
    assert_ne!(*u, Kind::Named(String::from("x")));
}
