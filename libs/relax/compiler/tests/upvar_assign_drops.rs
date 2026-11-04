// Assigning to a place a closure captured drops the value it held (rustc MIR: `Drop` of the
// place, then the write). app_main!'s event closure keeps `app_value: Option<ScriptObjectRef>`
// by move and sets it inside `cx.with_vm(|vm| ..)` on each design re-run: under Relax the old
// ref was never released, so every re-run kept the previous app tree alive.
use std::cell::Cell;

thread_local! { static DROPPED: Cell<u32> = Cell::new(0); }

struct D(u32);
impl Drop for D {
    fn drop(&mut self) {
        DROPPED.with(|d| d.set(d.get() + self.0));
    }
}

fn dropped() -> u32 {
    DROPPED.with(|d| d.replace(0))
}

fn with<R>(f: impl FnOnce() -> R) -> R {
    f()
}

#[test]
fn assign_through_a_nested_closure_drops_the_old_value() {
    dropped();
    let mut value: Option<D> = None;
    let mut handler = move |n: u32| {
        with(|| {
            value = Some(D(n));
        });
    };
    handler(1);
    assert_eq!(dropped(), 0);
    handler(10);
    assert_eq!(dropped(), 1);
    handler(100);
    assert_eq!(dropped(), 10);
    drop(handler);
    assert_eq!(dropped(), 100);
}

#[test]
fn assign_to_a_moved_capture_drops_the_old_value() {
    dropped();
    let mut value: Option<D> = None;
    let mut handler = move |n: u32| {
        value = Some(D(n));
    };
    handler(1);
    handler(10);
    assert_eq!(dropped(), 1);
    drop(handler);
    assert_eq!(dropped(), 10);
}

#[test]
fn assign_in_a_boxed_fnmut_drops_the_old_value() {
    dropped();
    let mut value: Option<D> = None;
    let mut handler: Box<dyn FnMut(u32)> = Box::new(move |n: u32| {
        if n > 0 {
            with(|| {
                if let Some(x) = Some(n) {
                    value = Some(D(x));
                }
            });
        }
    });
    handler(1);
    handler(10);
    assert_eq!(dropped(), 1);
    drop(handler);
    assert_eq!(dropped(), 10);
}
