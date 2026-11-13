use macro_dep::answer;

#[test]
fn imported_macro_in_path_child() {
    assert_eq!(answer!(), 42);
}
