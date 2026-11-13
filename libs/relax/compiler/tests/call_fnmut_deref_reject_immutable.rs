use std::cell::RefCell;

#[test]
fn shared_ref_cannot_call_fn_mut() {
    let mut count = 0;
    let callback = RefCell::new(|| { count += 1; count });
    (callback.borrow())();
}
