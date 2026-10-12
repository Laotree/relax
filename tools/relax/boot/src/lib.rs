//! A native Makepad app hosted by Relax's session 0. Layout and shaders live in the
//! document; this crate only binds plain run data and returns plain user actions.
pub use makepad_widgets;
use makepad_widgets::*;
pub use relax_base::{
    diag::Diagnostic,
    run_state::{ParkedPanic, Phase, State},
};
use std::{
    path::PathBuf,
    sync::{Arc, Mutex},
};

pub const DEFAULT_DOCUMENT: &str = include_str!("../resources/boot.splash");

#[derive(Clone, Debug)]
pub enum Action {
    RetryCompile,
    RestartDomain,
    Resume {
        panic: String,
        choice: String,
        value: String,
    },
    Copy(String),
    OpenFile {
        file: String,
        line: u32,
        col: u32,
    },
    DocumentErrors(Vec<Diagnostic>),
}

#[derive(Clone)]
pub struct Document {
    pub path: PathBuf,
    pub source: Arc<str>,
}

impl Document {
    pub fn bundled() -> Self {
        Self {
            path: PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("resources/boot.splash"),
            source: DEFAULT_DOCUMENT.into(),
        }
    }
}

struct Bridge {
    state: Arc<State>,
    document: Document,
    actions: Vec<Action>,
    value: Option<ScriptObjectRef>,
    geometry: [f32; 4],
    window: Option<WindowId>,
    document_errors: Vec<Diagnostic>,
}

fn script_diagnostics(errors: Vec<ScriptErrorRecord>) -> Vec<Diagnostic> {
    errors
        .into_iter()
        .map(|e| {
            let (file, line, col) = e
                .loc
                .map_or((String::new(), 0, 0), |at| (at.file, at.line, at.col));
            Diagnostic::new("parse", file, line, col, e.message)
        })
        .collect()
}

script_mod! {
    use mod.prelude.widgets_internal.*
    mod.boot = {
        App: #(App::script_component(vm))
        RunView: set_type_default() do #(RunView::register_widget(vm)){
            width: Fill height: Fill
        }
    }
}

#[derive(Script, ScriptHook)]
struct App {
    #[live]
    ui: WidgetRef,
}

impl AppMain for App {
    fn script_mod(vm: &mut ScriptVm) -> ScriptValue {
        makepad_widgets::script_mod(vm);
        self::script_mod(vm);
        let document = vm.cx_mut().get_global::<Bridge>().document.clone();
        let eval = |vm: &mut ScriptVm, source: &str, path: &std::path::Path| {
            vm.eval(ScriptMod::new(
                path.parent()
                    .unwrap_or(std::path::Path::new(""))
                    .to_str()
                    .unwrap_or(""),
                "relax_boot_document",
                &path.to_string_lossy(),
                0,
                0,
                source,
                &[],
            ))
        };
        let previous_sink = vm.bx.captured_errors.replace(Vec::new());
        let mut value = eval(vm, &document.source, &document.path);
        vm.drain_errors();
        let mut errors = script_diagnostics(vm.bx.captured_errors.take().unwrap_or_default());
        vm.bx.captured_errors = previous_sink;
        // A document must supply the host window; a successful evaluation returning
        // nil or an unrelated object must not leave the compiler waiting forever.
        let valid = value.as_object().is_some_and(|app| {
            use makepad_widgets::makepad_script::object_heap::OBJ_GET_VALUE;
            let heap = vm.heap();
            if !heap.type_matches_id(app, App::script_type_id_static()) {
                return false;
            }
            let Some(root) = heap
                .obj_get(OBJ_GET_VALUE, app, id!(ui).into(), NoTrap)
                .value
                .as_object()
            else {
                return false;
            };
            heap.obj_get(OBJ_GET_VALUE, root, id!(main_window).into(), NoTrap)
                .value
                .as_object()
                .is_some_and(|window| heap.type_matches_id(window, Window::script_type_id_static()))
        });
        if !valid {
            errors.push(Diagnostic::new(
                "parse",
                document.path.to_string_lossy(),
                1,
                1,
                "Boot document must return mod.boot.App with ui.main_window := Window{…}",
            ));
        }
        let bridge = vm.cx_mut().get_global::<Bridge>();
        bridge.document_errors = errors.clone();
        bridge.actions.push(Action::DocumentErrors(errors.clone()));
        if !errors.is_empty() {
            if let Some(previous) = vm.cx_mut().get_global::<Bridge>().value.as_ref() {
                return previous.as_object().into();
            }
            value = eval(vm, DEFAULT_DOCUMENT, &Document::bundled().path);
        }
        if let Some(object) = value.as_object() {
            let root = vm.heap_mut().new_object_ref(object);
            vm.cx_mut().get_global::<Bridge>().value = Some(root);
        }
        value
    }

    fn handle_event(&mut self, cx: &mut Cx, event: &Event) {
        if matches!(event, Event::Startup) {
            let bridge = cx.get_global::<Bridge>();
            let geometry = bridge.geometry;
            let title = bridge.state.app.clone();
            let window = self.ui.window(cx, ids!(main_window));
            let size = dvec2(geometry[2] as f64, geometry[3] as f64);
            script_apply_eval!(cx, window, {window.inner_size: #(size)});
            if geometry[0].is_finite() && geometry[1].is_finite() {
                let position = dvec2(geometry[0] as f64, geometry[1] as f64);
                script_apply_eval!(cx, window, {window.position: #(position)});
            }
            window.set_title(cx, &title);
            cx.get_global::<Bridge>().window = window.window_id();
        }
        self.ui.handle_event(cx, event, &mut Scope::empty());
    }
}

#[derive(Script, ScriptHook, Widget)]
pub struct RunView {
    #[deref]
    view: View,
    #[rust]
    applied: Option<Arc<State>>,
    #[rust]
    progress: f64,
    #[rust]
    next: NextFrame,
    #[rust]
    drawn: Arc<[Diagnostic]>,
}

fn diagnostic_text(d: &Diagnostic) -> String {
    let severity = match d.severity {
        relax_base::diag::Severity::Error => "error",
        relax_base::diag::Severity::Warning => "warning",
        relax_base::diag::Severity::Note => "note",
    };
    let mut text = format!("{severity} {}", d.code);
    if !d.file.is_empty() {
        text.push_str(&format!(" · {}:{}:{}", d.file, d.line, d.col));
    }
    text.push('\n');
    text.push_str(&d.message);
    if let Some(item) = &d.item {
        text.push('\n');
        text.push_str(item);
    }
    for note in &d.notes {
        text.push_str("\nnote: ");
        text.push_str(note);
    }
    if let Some(suggestion) = &d.suggestion {
        text.push_str("\nhelp: ");
        text.push_str(&suggestion.message);
    }
    text
}

impl RunView {
    fn bind(&mut self, cx: &mut Cx) {
        let state = cx.get_global::<Bridge>().state.clone();
        if self
            .applied
            .as_ref()
            .is_some_and(|old| Arc::ptr_eq(old, &state))
        {
            return;
        }
        self.view.label(cx, ids!(app_name)).set_text(cx, &state.app);
        let units = match (state.done, state.total) {
            (Some(done), Some(total)) => format!(" · {done}/{total}"),
            (Some(done), None) => format!(" · {done}"),
            _ => String::new(),
        };
        self.view.label(cx, ids!(status)).set_text(
            cx,
            &format!(
                "{}{} · {} · {:.1}s · {}",
                state.phase.name(),
                units,
                if state.warm { "warm" } else { "cold" },
                state.elapsed,
                state.current
            ),
        );
        self.view
            .label(cx, ids!(domain_state))
            .set_text(cx, &state.domain);
        self.view
            .button(cx, ids!(retry))
            .set_visible(cx, state.can_retry);
        self.view
            .button(cx, ids!(restart))
            .set_visible(cx, state.can_restart);
        self.view
            .view(cx, ids!(panic))
            .set_visible(cx, state.parked.is_some());
        if let Some(panic) = &state.parked {
            self.view.label(cx, ids!(panic_message)).set_text(
                cx,
                &format!("{} · {}\n{}", panic.id, panic.location, panic.message),
            );
            for (id, choice) in [
                (id!(resume), "panic"),
                (id!(panic_retry), "retry"),
                (id!(panic_restart), "restart"),
                (id!(panic_return), "return"),
            ] {
                self.view
                    .button(cx, &[id])
                    .set_visible(cx, panic.choices.iter().any(|c| c == choice));
            }
            self.view
                .text_input(cx, ids!(return_value))
                .set_visible(cx, panic.choices.iter().any(|c| c == "return"));
        }
        if state.progress != self.progress || self.applied.is_none() {
            let progress = self.view.view(cx, ids!(progress));
            // A new compile starts a new bar; easing itself lives only in Splash.
            let from = self.progress.min(state.progress) as f32;
            let target = state.progress as f32;
            let changed = cx.seconds_since_app_start() as f32;
            script_apply_eval!(cx, progress, {draw_bg +: {from: #(from) target: #(target) changed: #(changed)}});
            self.progress = state.progress;
        }
        self.applied = Some(state);
        self.view.redraw(cx);
    }
}

impl Widget for RunView {
    fn handle_event(&mut self, cx: &mut Cx, event: &Event, scope: &mut Scope) {
        if matches!(event, Event::Startup | Event::Signal | Event::LiveEdit) {
            if matches!(event, Event::LiveEdit) {
                self.applied = None;
            }
            self.bind(cx);
        }
        if matches!(event, Event::Startup) || self.next.is_event(event).is_some() {
            self.view.view(cx, ids!(progress)).redraw(cx);
            self.next = cx.new_next_frame();
        }
        self.view.handle_event(cx, event, scope);
        let Event::Actions(actions) = event else {
            return;
        };
        let Some(state) = self.applied.clone() else {
            return;
        };
        let mut out = Vec::new();
        if self.view.button(cx, ids!(retry)).clicked(actions) {
            out.push(Action::RetryCompile);
        }
        if self.view.button(cx, ids!(restart)).clicked(actions) {
            out.push(Action::RestartDomain);
        }
        if let Some(panic) = &state.parked {
            for (id, choice) in [
                (id!(resume), "panic"),
                (id!(panic_retry), "retry"),
                (id!(panic_restart), "restart"),
                (id!(panic_return), "return"),
            ] {
                if panic.choices.iter().any(|c| c == choice)
                    && self.view.button(cx, &[id]).clicked(actions)
                {
                    out.push(Action::Resume {
                        panic: panic.id.clone(),
                        choice: choice.into(),
                        value: self.view.text_input(cx, ids!(return_value)).text(),
                    });
                }
            }
        }
        for (index, item) in self
            .view
            .portal_list(cx, ids!(diagnostics))
            .items_with_actions(actions)
        {
            let Some(d) = self.drawn.get(index) else {
                continue;
            };
            if item.button(cx, ids!(copy)).clicked(actions) {
                out.push(Action::Copy(diagnostic_text(d)));
            }
            if item.button(cx, ids!(open)).clicked(actions) && !d.file.is_empty() {
                out.push(Action::OpenFile {
                    file: d.file.clone(),
                    line: d.line,
                    col: d.col,
                });
            }
        }
        cx.get_global::<Bridge>().actions.extend(out);
    }

    fn draw_walk(&mut self, cx: &mut Cx2d, scope: &mut Scope, walk: Walk) -> DrawStep {
        let state = cx.get_global::<Bridge>().state.clone();
        self.drawn = state.diagnostics.clone();
        while let Some(step) = self.view.draw_walk(cx, scope, walk).step() {
            if let Some(mut list) = step.as_portal_list().borrow_mut() {
                list.set_item_range(cx, 0, state.diagnostics.len());
                while let Some(index) = list.next_visible_item(cx) {
                    let Some(d) = state.diagnostics.get(index) else {
                        continue;
                    };
                    let item = list.item(cx, index, id!(Diagnostic));
                    item.button(cx, ids!(open))
                        .set_text(cx, &format!("{}:{}:{}", d.file, d.line, d.col));
                    item.button(cx, ids!(open))
                        .set_visible(cx, !d.file.is_empty());
                    item.label(cx, ids!(message))
                        .set_text(cx, &diagnostic_text(d));
                    item.draw_all(cx, scope);
                }
            }
        }
        DrawStep::done()
    }
}

/// Own this on one host UI thread. The OS loop stays on the process main thread.
pub struct Boot {
    cx: Cx,
    updates: DocumentUpdates,
}

/// A worker owns the watcher, including its blocking startup/shutdown. The UI
/// only takes the latest source from a briefly held slot.
#[derive(Clone)]
pub struct DocumentUpdates {
    document: Document,
    changed: Arc<Mutex<Option<Arc<str>>>>,
}

impl DocumentUpdates {
    pub fn watch(&self) -> Option<makepad_live_reload_core::LiveReloadWatcherHandle> {
        let document = &self.document;
        document
            .path
            .parent()
            .filter(|p| p.is_dir())
            .and_then(|root| {
                use makepad_live_reload_core::*;
                let path = normalize_path_string(&document.path);
                let root_name = normalize_path_string(root);
                let plan = LiveReloadWatchPlan {
                    roots: vec![WatchRoot {
                        mount: root_name.clone(),
                        path: root.into(),
                    }],
                    files_by_root: [(root_name, vec![path.clone()])].into(),
                    initial_contents: [(path, document.source.to_string())].into(),
                };
                let changed = self.changed.clone();
                match start_live_reload_watcher(
                    plan,
                    move |change| {
                        let source = Arc::from(change.content);
                        let old = changed
                            .lock()
                            .unwrap_or_else(|e| e.into_inner())
                            .replace(source);
                        drop(old);
                        makepad_hal::Hal::global().wake_session(makepad_hal::session::HOST);
                        Ok(())
                    },
                    LiveReloadLogger::new(|_| {}, |e| eprintln!("relax boot: {e}")),
                ) {
                    Ok(w) => Some(w),
                    Err(e) => {
                        eprintln!("relax boot: {e}");
                        None
                    }
                }
            })
    }
}

impl Boot {
    pub fn new(
        info: makepad_hal::HalInfo,
        document: Document,
        state: State,
        geometry: [f32; 4],
    ) -> Self {
        let mut cx = Cx::new(makepad_widgets::makepad_platform::_app_main_event_closure!(
            App
        ));
        cx.set_font_set(FontSet::International);
        cx.freeze_font_set();
        cx.set_global(Bridge {
            state: Arc::new(state),
            document: document.clone(),
            actions: Vec::new(),
            value: None,
            geometry,
            window: None,
            document_errors: Vec::new(),
        });
        cx.init_cx_os();
        cx.init_websockets(&makepad_widgets::makepad_platform::resolve_studio_http());
        cx.hal_attach_session(info);
        Self {
            cx,
            updates: DocumentUpdates {
                document,
                changed: Arc::new(Mutex::new(None)),
            },
        }
    }

    pub fn document_updates(&self) -> DocumentUpdates {
        self.updates.clone()
    }

    pub fn update(&mut self, state: State) {
        self.cx.get_global::<Bridge>().state = Arc::new(state);
    }
    pub fn window(&mut self) -> Option<makepad_hal::Id> {
        self.cx
            .get_global::<Bridge>()
            .window
            .map(|id| makepad_hal::Id::new(id.0 as u32, id.1 as u32))
    }
    pub fn turn(&mut self, timeout_ns: u64, present: bool) -> bool {
        let source = self
            .updates
            .changed
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .take();
        if let Some(source) = source {
            self.cx.get_global::<Bridge>().document.source = source;
            self.cx.request_live_edit();
        }
        let previous_sink = self
            .cx
            .with_vm(|vm| vm.bx.captured_errors.replace(Vec::new()));
        let alive = self.cx.hal_session_turn(timeout_ns, present);
        let mut errors = self.cx.with_vm(|vm| {
            vm.drain_errors();
            let errors = script_diagnostics(vm.bx.captured_errors.take().unwrap_or_default());
            vm.bx.captured_errors = previous_sink;
            errors
        });
        if let Some(error) = makepad_widgets::makepad_platform::shader_error::take() {
            let path = self
                .cx
                .get_global::<Bridge>()
                .document
                .path
                .to_string_lossy()
                .into_owned();
            errors.push(Diagnostic::new("codegen", path, 0, 0, error));
        }
        if !errors.is_empty() {
            let bridge = self.cx.get_global::<Bridge>();
            bridge.document_errors.extend(errors);
            bridge
                .actions
                .push(Action::DocumentErrors(bridge.document_errors.clone()));
        }
        alive
    }
    pub fn actions(&mut self) -> Vec<Action> {
        std::mem::take(&mut self.cx.get_global::<Bridge>().actions)
    }
    pub fn copy(&mut self, text: &str) {
        self.cx.copy_to_clipboard(text);
    }
    pub fn open_file(&mut self, file: String, line: u32, col: u32) -> Result<(), String> {
        if !Cx::has_studio_web_socket() {
            return Err("Connect an editor through Studio to open source locations".into());
        }
        Cx::send_studio_message(
            makepad_widgets::makepad_platform::studio::AppToStudio::JumpToFile(
                makepad_widgets::makepad_platform::studio::JumpToFile {
                    file_name: file,
                    line,
                    column: col,
                },
            ),
        );
        Ok(())
    }
}
