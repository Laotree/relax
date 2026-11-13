use std::cell::{Cell, RefCell};
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::rc::Rc;

#[test]
fn owned_refmut_temporary_calls_fn_mut() {
    let mut count = 0;
    let callback = RefCell::new(|| { count += 1; count });
    assert_eq!((callback.borrow_mut())(), 1);
    assert_eq!((callback.borrow_mut())(), 2);
    drop(callback);
    assert_eq!(count, 2);
}

#[test]
fn nested_callback_calls_fn_mut_through_refmut() {
    fn invoke(f: &mut dyn FnMut() -> usize) -> usize { f() }
    let mut count = 0;
    let callback = RefCell::new(|| { count += 1; count });
    assert_eq!(invoke(&mut || (callback.borrow_mut())()), 1);
    drop(callback);
    assert_eq!(count, 1);
}

struct Traced<F> {
    callback: F,
    shared: Rc<Cell<usize>>,
    mutable: Rc<Cell<usize>>,
}

impl<F> Deref for Traced<F> {
    type Target = F;
    fn deref(&self) -> &F {
        self.shared.set(self.shared.get() + 1);
        &self.callback
    }
}

impl<F> DerefMut for Traced<F> {
    fn deref_mut(&mut self) -> &mut F {
        self.mutable.set(self.mutable.get() + 1);
        &mut self.callback
    }
}

impl<F> Index<usize> for Traced<F> {
    type Output = F;
    fn index(&self, i: usize) -> &F {
        assert_eq!(i, 0);
        self.shared.set(self.shared.get() + 1);
        &self.callback
    }
}

impl<F> IndexMut<usize> for Traced<F> {
    fn index_mut(&mut self, i: usize) -> &mut F {
        assert_eq!(i, 0);
        self.mutable.set(self.mutable.get() + 1);
        &mut self.callback
    }
}

#[test]
fn fn_mut_calls_deref_mut_not_deref() {
    let shared = Rc::new(Cell::new(0));
    let mutable = Rc::new(Cell::new(0));
    let mut count = 0;
    let mut callback = Traced {
        callback: || { count += 1; count },
        shared: shared.clone(),
        mutable: mutable.clone(),
    };
    assert_eq!(callback(), 1);
    assert_eq!(callback(), 2);
    assert_eq!(shared.get(), 0);
    assert_eq!(mutable.get(), 2);
}

#[test]
fn fn_calls_deref_not_deref_mut() {
    let shared = Rc::new(Cell::new(0));
    let mutable = Rc::new(Cell::new(0));
    let callback = Traced {
        callback: || 17,
        shared: shared.clone(),
        mutable: mutable.clone(),
    };
    assert_eq!(callback(), 17);
    assert_eq!(shared.get(), 1);
    assert_eq!(mutable.get(), 0);
}

#[test]
fn indexed_fn_mut_calls_index_mut_not_index() {
    let shared = Rc::new(Cell::new(0));
    let mutable = Rc::new(Cell::new(0));
    let mut count = 0;
    let mut callback = Traced {
        callback: || { count += 1; count },
        shared: shared.clone(),
        mutable: mutable.clone(),
    };
    assert_eq!(callback[0](), 1);
    assert_eq!(shared.get(), 0);
    assert_eq!(mutable.get(), 1);
}
