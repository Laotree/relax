use std::ops::Bound;

fn msg<F: FnOnce() + std::panic::UnwindSafe>(f: F) -> String {
    let e = std::panic::catch_unwind(f).unwrap_err();
    if let Some(s) = e.downcast_ref::<String>() { s.clone() } else { e.downcast_ref::<&str>().unwrap().to_string() }
}

#[test]
fn inclusive_end_at_len() {
    let v = [1, 2, 3, 4];
    assert_eq!(
        msg(|| { let _ = &v[(Bound::Unbounded, Bound::Included(4))]; }),
        "range end index 4 out of range for slice of length 4"
    );
}

#[test]
fn order_and_range() {
    let v = [1, 2, 3, 4];
    assert_eq!(
        msg(|| { let _ = &v[(Bound::Included(3), Bound::Excluded(2))]; }),
        "slice index starts at 3 but ends at 2"
    );
    assert_eq!(
        msg(|| { let _ = &v[(Bound::Included(5), Bound::Unbounded)]; }),
        "range start index 5 out of range for slice of length 4"
    );
}

#[test]
fn array_windows_len() {
    let v = [1, 2, 3];
    assert_eq!(v.as_slice().array_windows::<2>().len(), 2);
    assert_eq!(v.as_slice().array_windows::<3>().len(), 1);
    assert_eq!(v.as_slice().array_windows::<4>().len(), 0);
}
