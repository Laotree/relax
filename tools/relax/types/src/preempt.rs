//! Background front-end work that gives way to a front-end writer (a live patch's commit).
//!
//! A background check holds the front end's read lock (jit::FRONT_RW) for one item; a writer
//! (a live patch committing its new file versions) waits for every reader. One background
//! type check can take seconds (a solver search at a generic owner's identity arguments), and
//! the patch waited for it. A thread that opts in (`Preemptible`) stops at the next
//! preemption point (a solver goal, an expression) while a writer waits: the work unwinds
//! with the `Preempted` payload (`std::panic::resume_unwind`: no panic hook, no message), its
//! read guard drops, and the owner of that work queues it again. Only per-check state lives
//! on the unwound frames (the EvalState, the inference tables); shared tables take finished
//! answers only.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

static WRITERS: AtomicUsize = AtomicUsize::new(0);
/// The process is ending (stop_all): opted-in work stops at its next point, for good.
static STOPPED: AtomicBool = AtomicBool::new(false);

/// The process is ending: every opted-in thread unwinds at its next preemption point, now and
/// from then on (its owner sees `is_preempted` and must not queue the work again).
pub fn stop_all() {
    STOPPED.store(true, Ordering::SeqCst);
}

/// Shutdown has begun. Safe to query even after this thread's locals were destroyed.
pub fn is_stopped() -> bool {
    STOPPED.load(Ordering::Acquire)
}

thread_local! {
    static ON: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The unwind payload of preempted work.
pub struct Preempted;

/// Held by a front-end writer while it waits for the lock: preemptible readers stop.
pub struct WriterWaiting(());
impl WriterWaiting {
    pub fn new() -> Self {
        WRITERS.fetch_add(1, Ordering::SeqCst);
        WriterWaiting(())
    }
}
impl Drop for WriterWaiting {
    fn drop(&mut self) {
        WRITERS.fetch_sub(1, Ordering::SeqCst);
    }
}

/// The calling thread's work in this scope may be preempted.
pub struct Preemptible(bool);
impl Preemptible {
    pub fn on() -> Self {
        Preemptible(ON.with(|c| c.replace(true)))
    }
}
impl Drop for Preemptible {
    fn drop(&mut self) {
        let prev = self.0;
        ON.with(|c| c.set(prev));
    }
}

/// A preemption point: unwinds with `Preempted` when a writer waits and this thread opted in.
#[inline]
pub fn point() {
    if (WRITERS.load(Ordering::Relaxed) != 0 || STOPPED.load(Ordering::Relaxed)) && ON.with(|c| c.get()) {
        std::panic::resume_unwind(Box::new(Preempted));
    }
}

/// Whether a caught unwind payload is a preemption (not a failure).
pub fn is_preempted(payload: &(dyn std::any::Any + Send)) -> bool {
    payload.is::<Preempted>()
}

#[cfg(test)]
mod tests {
    #[test]
    fn point_unwinds_only_opted_in_threads_while_a_writer_waits() {
        super::point();
        let _on = super::Preemptible::on();
        super::point();
        let w = super::WriterWaiting::new();
        let r = std::panic::catch_unwind(super::point);
        assert!(r.is_err_and(|p| super::is_preempted(&*p)));
        let other = std::thread::spawn(|| std::panic::catch_unwind(super::point).is_ok()).join().unwrap();
        assert!(other, "a thread that did not opt in was preempted");
        drop(w);
        super::point();
    }
}
