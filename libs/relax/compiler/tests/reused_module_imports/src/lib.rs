#[path = "../shared/value.rs"]
mod first;
#[path = "../shared/value.rs"]
mod second;

#[test]
fn imports_follow_each_module() {
    assert_eq!(first::value(), 3);
    assert_eq!(second::value(), 3);
    assert_eq!(first::module(), "reused_module_imports::first");
    assert_eq!(second::module(), "reused_module_imports::second");
}
