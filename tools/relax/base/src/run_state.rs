//! Native run observers share the compiler's diagnostics. No UI or HAL dependency.
use crate::diag::Diagnostic;
use std::sync::{Arc, OnceLock};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(usize)]
pub enum Phase {
    #[default]
    Resolve,
    Parse,
    Typecheck,
    Codegen,
    Link,
    FirstFrame,
}

impl Phase {
    pub fn name(self) -> &'static str {
        match self {
            Self::Resolve => "resolve",
            Self::Parse => "parse",
            Self::Typecheck => "typecheck",
            Self::Codegen => "codegen",
            Self::Link => "link",
            Self::FirstFrame => "first_frame",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParkedPanic {
    pub id: String,
    pub message: String,
    pub location: String,
    /// Exactly the choices advertised by inspect's panic event.
    pub choices: Vec<String>,
}

/// Target-neutral snapshot consumed by native run presenters.
#[derive(Clone, Debug, Default)]
pub struct State {
    pub app: String,
    pub phase: Phase,
    pub done: Option<u64>,
    pub total: Option<u64>,
    pub current: String,
    pub warm: bool,
    pub elapsed: f64,
    pub progress: f64,
    pub diagnostics: Arc<[Diagnostic]>,
    pub parked: Option<ParkedPanic>,
    pub domain: String,
    pub can_retry: bool,
    pub can_restart: bool,
}

#[derive(Clone, Debug)]
pub enum Event {
    Progress {
        domain: Option<u32>,
        phase: Phase,
        done: Option<u64>,
        total: Option<u64>,
        item: String,
    },
    Warm {
        domain: Option<u32>,
        warm: bool,
    },
    Diagnostic {
        domain: Option<u32>,
        record: Diagnostic,
    },
    /// An edit replaces the previous edit's diagnostics, including an empty successful result.
    Diagnostics {
        domain: Option<u32>,
        records: Arc<[Diagnostic]>,
    },
}

static OBSERVER: OnceLock<fn(Event)> = OnceLock::new();

pub fn set_observer(observer: fn(Event)) {
    let _ = OBSERVER.set(observer);
}
pub fn observed() -> bool {
    OBSERVER.get().is_some()
}
pub fn emit(event: Event) {
    if let Some(observer) = OBSERVER.get() {
        observer(event);
    }
}

pub fn progress(
    domain: Option<u32>,
    phase: Phase,
    done: Option<u64>,
    total: Option<u64>,
    item: &str,
) {
    if observed() {
        emit(Event::Progress {
            domain,
            phase,
            done,
            total,
            item: item.into(),
        });
    }
}

pub fn diagnostic(domain: Option<u32>, record: Diagnostic) {
    emit(Event::Diagnostic { domain, record });
}
