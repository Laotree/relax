// A method call's user type annotation holds the arguments the call writes, and fresh variables for
// the method's own parameters it leaves out (rustc method/confirm.rs, instantiate_method_args), not
// what method probing has inferred for them. `[&f[..], &[name]].concat()` must not pin `Item` to the
// `&'static str` of `f`'s literals, or `name` would have to outlive `'static`.
fn count(names: &[&str]) -> usize {
    names.iter().map(|s| s.len()).sum()
}

pub fn concat_in_a_closure(name: &str) -> usize {
    let filter = ["ab", "cde"];
    let field = |name: &str| count(&[&filter[..], &[name]].concat());
    field(name)
}

pub fn concat_of_a_local_array(name: &str) -> usize {
    let filter = ["ab"];
    let arr = [&filter[..], &[name]];
    let v: Vec<&str> = arr.concat();
    count(&v)
}

pub fn concat_of_a_slice(name: &str) -> usize {
    let filter = ["ab"];
    let arr = [&filter[..], &[name]];
    arr[..].concat().len()
}

pub struct W;
impl W {
    pub fn id<T>(&self, t: T) -> T {
        t
    }
}

pub fn written_turbofish_still_applies(name: &str) -> usize {
    W.id::<&str>(name).len()
}

#[test]
fn concat_with_a_shorter_lived_element_type_checks() {
    let owned = String::from("wxyz");
    assert_eq!(concat_in_a_closure(&owned), 9);
    assert_eq!(concat_of_a_local_array(&owned), 6);
    assert_eq!(concat_of_a_slice(&owned), 2);
    assert_eq!(written_turbofish_still_applies(&owned), 4);
}
