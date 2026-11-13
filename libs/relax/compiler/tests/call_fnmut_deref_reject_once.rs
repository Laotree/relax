use std::cell::RefCell;

#[test]
fn refmut_cannot_move_out_a_once_only_closure() {
    let text = String::from("owned");
    let callback = RefCell::new(move || drop(text));
    (callback.borrow_mut())();
}
