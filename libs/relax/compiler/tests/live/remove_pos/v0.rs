// A method of a trait impl goes (the trait's default takes over): removing it is not applied
// live, and the refusal points into the impl, where it was (it said `v1.rs:1:1`).
trait Named {
    fn name(&self) -> u32 {
        1
    }
}
struct X;
impl Named for X {
    fn name(&self) -> u32 {
        2
    }
}

#[test]
fn run() {
    println!("out {}", X.name());
}
