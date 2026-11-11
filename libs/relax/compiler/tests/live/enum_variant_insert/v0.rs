// Variants inserted before running ones while a live value holds one: an enum is laid out as rustc
// lays it, so an added variant restarts the app, and the held value is read as before.
//  v1: `X(u16)` inserted before the held `C`, describe() and the derived ordering reading it.
//  v2: a unit variant inserted first, `==` and `mem::discriminant` reading the held value.
//  v3: a variant inserted after `mem::discriminant` ran.
use std::cell::RefCell;

#[derive(Debug, Clone, PartialEq, PartialOrd)]
enum Mode {
    A,
    B(u32),
    C { level: u8 },
}

thread_local! {
    static HELD: RefCell<Option<Mode>> = RefCell::new(None);
}

fn describe(m: &Mode) -> String {
    match m {
        Mode::C { level } => format!("C{}", level),
        other => format!("{:?}", other),
    }
}

#[test]
fn run() {
    HELD.with(|h| {
        if h.borrow().is_none() {
            *h.borrow_mut() = Some(Mode::C { level: 4 });
        }
        let held = h.borrow();
        let held = held.as_ref().unwrap();
        println!("out held {} fresh {} ord {}", describe(held), describe(&Mode::B(7)), Mode::A < *held);
    });
}
