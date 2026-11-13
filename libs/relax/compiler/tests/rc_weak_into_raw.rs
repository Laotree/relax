// rc::Weak::into_raw / from_raw (std since 1.45): the weak count travels with the raw pointer,
// as winit's macOS run-loop observer passes a `Weak<PanicInfo>` through a C context pointer.
use std::rc::{Rc, Weak};

#[test]
fn round_trip_keeps_the_weak_count() {
    let rc = Rc::new(41u32);
    let raw = Weak::into_raw(Rc::downgrade(&rc));
    assert_eq!(Rc::weak_count(&rc), 1);
    assert_eq!(unsafe { *raw }, 41);
    let back = unsafe { Weak::from_raw(raw) };
    assert_eq!(back.upgrade().map(|v| *v + 1), Some(42));
    drop(back);
    assert_eq!(Rc::weak_count(&rc), 0);
}

#[test]
fn a_dead_value_stays_dead_and_new_round_trips() {
    let rc = Rc::new(String::from("gone"));
    let raw = Rc::downgrade(&rc).into_raw();
    drop(rc);
    let back = unsafe { Weak::from_raw(raw) };
    assert!(back.upgrade().is_none());
    let empty = unsafe { Weak::<u8>::from_raw(Weak::<u8>::new().into_raw()) };
    assert!(empty.upgrade().is_none());
    assert_eq!(empty.strong_count(), 0);
}
