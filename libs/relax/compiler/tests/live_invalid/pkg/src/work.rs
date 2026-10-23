// Not Copy, named fields, the app's own crate: a field edit applies live (M10), a layout patch.
pub struct State {
    pub a: u64,
}

impl State {
    pub fn new() -> State {
        State { a: 1 }
    }
}

#[inline(never)]
pub fn step(s: &mut State, n: u64) -> u64 {
    s.a = s.a.wrapping_add(n & 1);
    10
}
