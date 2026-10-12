//! Session 0's text/pass renderer. No platform client, draw tree, widgets or Cx.
mod document;
mod gpu;
mod text;

use document::{Program, Role, BACKGROUND, ERROR_BAND, GLYPH, PROGRESS};
use makepad_hal::{
    backend_id, buffer_kind, dialect, font::wire, lifecycle, pass_load, session::HOST, target,
    window_kind, Attr, CmdWriter, EventBuf, EventQueue, FrameMeta, Hal, HalEvent, HalInfo, Id,
    Pass, RawEvent,
};
use makepad_script::{id, LiveId};
pub use relax_base::{
    diag::Diagnostic,
    run_state::{Mode, State},
};
use std::{path::PathBuf, sync::Arc, time::Instant};

pub const DEFAULT_DOCUMENT: &str = include_str!("../resources/boot.splash");

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

/// Input is interpreted by Relax itself, never by the document or renderer.
pub enum Event {
    KeyDown(RawEvent),
    Text(String),
    DocumentErrors(Vec<Diagnostic>),
}

pub fn diagnostic_text(diagnostic: &Diagnostic) -> String {
    let mut text = if diagnostic.file.is_empty() {
        diagnostic.message.clone()
    } else {
        format!(
            "{}:{}:{} {}",
            diagnostic.file, diagnostic.line, diagnostic.col, diagnostic.message
        )
    };
    if let Some(item) = &diagnostic.item {
        text.push('\n');
        text.push_str(item);
    }
    for note in &diagnostic.notes {
        text.push_str("\nnote: ");
        text.push_str(note);
    }
    if let Some(help) = &diagnostic.suggestion {
        text.push_str("\nhelp: ");
        text.push_str(&help.message);
    }
    text
}

struct TextLine {
    run: Arc<text::Shaped>,
    position: [f32; 2],
    style: document::Line,
    error: Option<usize>,
    fixed: bool,
}

#[derive(Default)]
struct Layout {
    panel: [f32; 4],
    clip: [f32; 4],
    text: Vec<TextLine>,
    progress: Option<[f32; 4]>,
    content_height: f32,
}

struct Renderer {
    active: Option<Program>,
    pending: Option<Program>,
    generation: u32,
    text: text::Text,
    layout: Layout,
    dirty: bool,
    redraw: bool,
    from: f32,
    target: f32,
    changed: f32,
    began: Instant,
    input: Option<String>,
    selected: usize,
    reveal_selection: bool,
    scroll: f32,
    dialect: u32,
    bundled: bool,
    clear_errors_on_install: bool,
    function_failed: bool,
}

pub struct Boot {
    window: Option<Id>,
    geometry: [f32; 4],
    dpi: f32,
    frame: u64,
    queue: EventQueue,
    events: Vec<Event>,
    state: State,
    renderer: Option<Renderer>,
    overlay: Option<[f32; 4]>,
}

impl Boot {
    pub fn new(
        info: HalInfo,
        document: Document,
        state: State,
        geometry: [f32; 4],
    ) -> Result<Self, String> {
        let mut boot = Self {
            window: None,
            geometry,
            dpi: info.dpi.max(1.0),
            frame: 0,
            queue: EventQueue::new(),
            events: Vec::new(),
            state,
            renderer: None,
            overlay: None,
        };
        // A backend without a shader dialect has no native HAL window to draw into.
        // In particular Linux/Windows do not manufacture a clear-only fake window.
        if info.backend == backend_id::HEADLESS || info.dialect == dialect::NONE {
            return Ok(boot);
        }
        let (program, bundled, clear_errors_on_install) =
            match Program::compile(&document, info.dialect, 0, 1) {
                Ok(program) => (program, document.source.as_ref() == DEFAULT_DOCUMENT, true),
                Err(errors) => {
                    boot.events.push(Event::DocumentErrors(errors));
                    (
                        Program::compile(&Document::bundled(), info.dialect, 0, 1).map_err(
                            |errors| {
                                errors
                                    .iter()
                                    .map(diagnostic_text)
                                    .collect::<Vec<_>>()
                                    .join("\n")
                            },
                        )?,
                        true,
                        false,
                    )
                }
            };
        let hal = Hal::global();
        let window = hal.with_world(|world| world.host_window(geometry));
        let mut writer = CmdWriter::new(HOST);
        writer.window_create(window, window_kind::NORMAL, Id::NONE, geometry, false);
        writer.str_def(1, boot.state.app.as_bytes());
        writer.window_title(window, 1);
        let vertices: Vec<u8> = [0.0_f32, 0.0, 1.0, 0.0, 1.0, 1.0, 0.0, 1.0]
            .iter()
            .flat_map(|v| v.to_le_bytes())
            .collect();
        let indices: Vec<u8> = [0_u32, 1, 2, 0, 2, 3]
            .iter()
            .flat_map(|v| v.to_le_bytes())
            .collect();
        writer.buffer_create(
            gpu::VERTICES,
            buffer_kind::VERTEX,
            vertices.len() as u64,
            Attr::default(),
        );
        writer.buffer_update(gpu::VERTICES, 0, &vertices);
        writer.buffer_create(
            gpu::INDICES,
            buffer_kind::INDEX,
            indices.len() as u64,
            Attr::default(),
        );
        writer.buffer_update(gpu::INDICES, 0, &indices);
        let text = text::Text::new(&mut writer)?;
        program.create(&mut writer, info.dialect);
        hal.submit(&writer.buf());
        boot.window = Some(window);
        boot.renderer = Some(Renderer {
            active: None,
            pending: Some(program),
            generation: 1,
            text,
            layout: Layout::default(),
            dirty: true,
            redraw: true,
            from: 0.0,
            target: 0.0,
            changed: 0.0,
            began: Instant::now(),
            input: None,
            selected: 0,
            reveal_selection: false,
            scroll: 0.0,
            dialect: info.dialect,
            bundled,
            clear_errors_on_install,
            function_failed: false,
        });
        Ok(boot)
    }

    pub fn window(&self) -> Option<Id> {
        self.window
    }
    pub fn events(&mut self) -> Vec<Event> {
        std::mem::take(&mut self.events)
    }

    pub fn reload(&mut self, document: Document) {
        self.replace_document(document, true);
    }

    fn replace_document(&mut self, document: Document, clear_errors: bool) {
        let Some(renderer) = &mut self.renderer else {
            return;
        };
        renderer.generation += 1;
        let bank = renderer
            .active
            .as_ref()
            .map_or(0, |p| if p.pipes[0].id.index == 0 { 4 } else { 0 });
        match Program::compile(&document, renderer.dialect, bank, renderer.generation) {
            Ok(program) => {
                let mut writer = CmdWriter::new(HOST);
                if let Some(old) = renderer.pending.take() {
                    old.destroy(&mut writer);
                }
                renderer.bundled = document.source.as_ref() == DEFAULT_DOCUMENT;
                program.create(&mut writer, renderer.dialect);
                renderer.pending = Some(program);
                renderer.clear_errors_on_install = clear_errors;
                Hal::global().submit(&writer.buf());
            }
            Err(errors) => {
                // A newer invalid edit supersedes any earlier pending reload.
                // At startup, keep the only renderable document as the fallback.
                if renderer.active.is_some() {
                    if let Some(old) = renderer.pending.take() {
                        let mut writer = CmdWriter::new(HOST);
                        old.destroy(&mut writer);
                        Hal::global().submit(&writer.buf());
                    }
                }
                renderer.clear_errors_on_install = false;
                self.events.push(Event::DocumentErrors(errors));
            }
        }
    }

    pub fn update(&mut self, state: State) {
        if state.mode != Mode::Overlay {
            self.set_overlay(None);
        }
        if let Some(renderer) = &mut self.renderer {
            let reset = state.elapsed < self.state.elapsed;
            if reset {
                renderer.from = 0.0;
                renderer.target = 0.0;
                renderer.changed = 0.0;
                renderer.began = Instant::now();
                renderer.scroll = 0.0;
            }
            if let Some(program) = renderer
                .active
                .as_mut()
                .filter(|_| !renderer.function_failed)
            {
                let now = renderer.began.elapsed().as_secs_f32();
                let values = [
                    renderer.target as f64,
                    state.completed_weight,
                    state.phase_weight,
                    state.total_weight,
                    state.done.unwrap_or(0) as f64,
                    state.total.unwrap_or(0) as f64,
                    state.phase_elapsed,
                ];
                match program.call(id!(phase_target), &values) {
                    Ok(target) if target != renderer.target => {
                        match program.call(
                            id!(ease),
                            &[
                                renderer.from as f64,
                                renderer.target as f64,
                                (now - renderer.changed) as f64,
                            ],
                        ) {
                            Ok(from) => renderer.from = from,
                            Err(errors) => {
                                renderer.function_failed = true;
                                self.events.push(Event::DocumentErrors(errors));
                            }
                        }
                        renderer.target = target;
                        renderer.changed = now;
                    }
                    Ok(_) => {}
                    Err(errors) => {
                        renderer.function_failed = true;
                        self.events.push(Event::DocumentErrors(errors));
                    }
                }
            }
            renderer.dirty |= state.mode != self.state.mode
                || state.app != self.state.app
                || state.phase != self.state.phase
                || state.done != self.state.done
                || state.total != self.state.total
                || state.current != self.state.current
                || state.warm != self.state.warm
                || state.domain != self.state.domain
                || state.parked != self.state.parked
                || state.can_retry != self.state.can_retry
                || state.can_restart != self.state.can_restart
                || !Arc::ptr_eq(&state.diagnostics, &self.state.diagnostics);
        }
        self.state = state;
    }

    pub fn select(&mut self, diagnostic: usize) {
        if let Some(renderer) = &mut self.renderer {
            renderer.selected = diagnostic;
            renderer.reveal_selection = true;
            renderer.dirty = true;
        }
    }

    pub fn scroll(&mut self, pages: f32) {
        if let Some(renderer) = &mut self.renderer {
            renderer.scroll = (renderer.scroll + pages * renderer.layout.clip[3]).max(0.0);
            renderer.redraw = true;
        }
    }

    pub fn input(&mut self, input: Option<String>) {
        if let Some(renderer) = &mut self.renderer {
            if renderer.input.is_some() != input.is_some() {
                if let Some(window) = self.window {
                    let mut writer = CmdWriter::new(HOST);
                    if input.is_some() {
                        writer.ime_show(window, renderer.layout.panel, 0);
                    } else {
                        writer.ime_hide(window);
                    }
                    Hal::global().submit(&writer.buf());
                }
            }
            renderer.input = input;
            renderer.dirty = true;
        }
    }

    fn set_overlay(&mut self, rect: Option<[f32; 4]>) {
        if self.overlay == rect {
            return;
        }
        self.overlay = rect;
        if let Some(window) = self.window {
            let mut writer = CmdWriter::new(HOST);
            writer.window_overlay(window, rect.is_some(), rect.unwrap_or_default());
            if rect.is_some()
                && self
                    .renderer
                    .as_ref()
                    .is_some_and(|renderer| renderer.input.is_none())
            {
                writer.ime_hide(window);
            }
            Hal::global().submit(&writer.buf());
        }
    }

    pub fn turn(&mut self, timeout_ns: u64, present: bool) -> bool {
        let hal = Hal::global();
        // Pump backend completions, then take session 0's owned queue. A zero-cap
        // pump leaves the events queued. Taking the arena avoids truncating large
        // diagnostics/pastes at an arbitrary EventStore capacity.
        hal.pump(
            timeout_ns,
            &mut EventBuf {
                session: HOST,
                ..Default::default()
            },
        );
        let mut queue = std::mem::take(&mut self.queue);
        let live = hal.with_world(|world| {
            let Some(session) = world.session_mut(HOST) else {
                return false;
            };
            std::mem::swap(&mut queue, &mut session.events);
            true
        });
        if !live {
            return false;
        }
        let mut alive = true;
        queue.drain_with(|mut raw, payload| {
            raw.data.off = 0;
            let Some(event) = raw.decode(payload) else {
                return;
            };
            if let Some(renderer) = &mut self.renderer {
                match renderer.text.event(&event) {
                    Ok(changed) => renderer.redraw |= changed,
                    Err(error) => {
                        eprintln!("relax boot: {error}");
                        alive = false;
                    }
                }
            }
            match event {
                HalEvent::KeyDown { window, .. } if Some(window) == self.window => {
                    self.events.push(Event::KeyDown(raw))
                }
                HalEvent::Text { window, text, .. } if Some(window) == self.window => self
                    .events
                    .push(Event::Text(String::from_utf8_lossy(text).into_owned())),
                HalEvent::Ime {
                    window,
                    kind: makepad_hal::input::ime::COMMIT,
                    text,
                    ..
                } if Some(window) == self.window => self
                    .events
                    .push(Event::Text(String::from_utf8_lossy(text).into_owned())),
                HalEvent::Geom {
                    window,
                    x,
                    y,
                    w,
                    h,
                    dpi,
                    ..
                } if Some(window) == self.window => {
                    self.geometry = [x as f32, y as f32, w as f32, h as f32];
                    self.dpi = dpi.max(f32::MIN_POSITIVE);
                    if let Some(renderer) = &mut self.renderer {
                        renderer.dirty = true;
                    }
                }
                HalEvent::PipelineReady { pipeline } => {
                    if let Some(renderer) = &mut self.renderer {
                        if let Some(program) = &mut renderer.pending {
                            for pipe in &mut program.pipes {
                                if pipe.id == pipeline {
                                    pipe.ready = true;
                                }
                            }
                        }
                    }
                }
                HalEvent::PipelineFailed { pipeline, log } => {
                    let Some(renderer) = &mut self.renderer else {
                        return;
                    };
                    if renderer
                        .pending
                        .as_ref()
                        .is_some_and(|p| p.pipes.iter().any(|p| p.id == pipeline))
                    {
                        let program = renderer.pending.take().unwrap();
                        let mut writer = CmdWriter::new(HOST);
                        program.destroy(&mut writer);
                        hal.submit(&writer.buf());
                        self.events.push(Event::DocumentErrors(vec![Diagnostic::new(
                            "codegen",
                            program.path.to_string_lossy(),
                            1,
                            1,
                            String::from_utf8_lossy(log),
                        )]));
                        if renderer.active.is_none() {
                            if renderer.bundled {
                                alive = false;
                            } else {
                                self.replace_document(Document::bundled(), false);
                            }
                        }
                    }
                }
                HalEvent::CloseRequested { window } | HalEvent::Closed { window }
                    if Some(window) == self.window =>
                {
                    alive = false
                }
                HalEvent::Lifecycle {
                    kind: lifecycle::QUIT_REQUESTED,
                }
                | HalEvent::DeviceLost {} => alive = false,
                _ => {}
            }
        });
        self.queue = queue;
        if !alive {
            return false;
        }
        if let Some(renderer) = &mut self.renderer {
            if renderer.pending.as_ref().is_some_and(Program::ready) {
                let mut writer = CmdWriter::new(HOST);
                if let Some(old) = renderer.active.take() {
                    old.destroy(&mut writer);
                }
                renderer.active = renderer.pending.take();
                renderer.dirty = true;
                renderer.function_failed = false;
                hal.submit(&writer.buf());
                if renderer.clear_errors_on_install {
                    self.events.push(Event::DocumentErrors(Vec::new()));
                }
            }
        }
        if present {
            self.present();
        }
        true
    }

    fn present(&mut self) {
        let Some(window) = self.window else { return };
        let Some(renderer) = &mut self.renderer else {
            return;
        };
        if renderer.active.is_none() {
            return;
        }
        if self.state.mode == Mode::Overlay && !renderer.redraw && !renderer.dirty {
            return;
        }
        if renderer.dirty {
            renderer.layout(&self.state, [self.geometry[2], self.geometry[3]]);
            renderer.dirty = false;
        }
        let rect = (self.state.mode == Mode::Overlay).then_some(renderer.layout.panel);
        self.set_overlay(rect);
        let renderer = self.renderer.as_mut().unwrap();
        let program = renderer.active.as_ref().unwrap();
        let build_start_ns = makepad_hal::clock_ns();
        let mut writer = CmdWriter::new(HOST);
        let mut data: [Vec<f32>; 4] = Default::default();
        program.pipes[BACKGROUND].instances.write(
            &[(id!(rect), &renderer.layout.panel)],
            &mut data[BACKGROUND],
        );
        let max_scroll = (renderer.layout.content_height - renderer.layout.clip[3]).max(0.0);
        renderer.scroll = renderer.scroll.min(max_scroll);
        let scroll = renderer.scroll;
        let clip = renderer.layout.clip;
        if let Some(mut rect) = renderer.layout.progress {
            rect[1] -= scroll;
            program.pipes[PROGRESS]
                .instances
                .write(&[(id!(rect), &rect)], &mut data[PROGRESS]);
        }
        renderer.text.begin_frame();
        let mut requests = Vec::new();
        // The validated document ends in the fixed hint line. Content lines are
        // ordered vertically, so a large diagnostic list costs only a binary
        // search plus its visible lines per frame.
        let (hints, content) = renderer.layout.text.split_last().unwrap();
        let start = content.partition_point(|line| {
            line.position[1] + line.run.rows as f32 * line.style.height < clip[1] + scroll
        });
        let visible = content[start..]
            .iter()
            .take_while(|line| line.position[1] <= clip[1] + clip[3] + scroll);
        for line in visible.chain(std::iter::once(hints)) {
            let y = line.position[1] - if line.fixed { 0.0 } else { scroll };
            let height = line.run.rows as f32 * line.style.height;
            if !line.fixed && (y + height < clip[1] || y > clip[1] + clip[3]) {
                continue;
            }
            if line.error == Some(renderer.selected) {
                let rect = [clip[0], y, clip[2], height];
                program.pipes[ERROR_BAND]
                    .instances
                    .write(&[(id!(rect), &rect)], &mut data[ERROR_BAND]);
            }
            let bounds = if line.fixed {
                renderer.layout.panel
            } else {
                clip
            };
            for glyph in line.run.visible(
                bounds[1] - y,
                bounds[1] + bounds[3] - y,
                line.style.size,
                line.style.height,
            ) {
                let baseline = [line.position[0] + glyph.x, y + glyph.y];
                if !line.fixed
                    && (baseline[1] + line.style.size < clip[1]
                        || baseline[1] - line.style.size > clip[1] + clip[3])
                {
                    continue;
                }
                let Some(entry) =
                    renderer
                        .text
                        .lookup(glyph.id, line.style.size, self.dpi, &mut requests)
                else {
                    continue;
                };
                if entry.atlas_kind == wire::glyph::EMPTY {
                    continue;
                }
                let (rect, uv) = renderer.text.quad(entry, baseline, line.style.size);
                // Clip in the vertex shader's coordinate space by cropping rect
                // and UV together, so fixed key hints can share one glyph draw.
                let (rect, uv) = crop(rect, uv, bounds);
                if rect[2] <= 0.0 || rect[3] <= 0.0 {
                    continue;
                }
                program.pipes[GLYPH].instances.write(
                    &[
                        (id!(rect), &rect),
                        (id!(uv), &uv),
                        (id!(color), &line.style.color),
                        (id!(atlas_plane), &[entry.plane as f32]),
                        (
                            id!(color_glyph),
                            &[if entry.atlas_kind == wire::glyph::COLOR {
                                1.0
                            } else {
                                0.0
                            }],
                        ),
                    ],
                    &mut data[GLYPH],
                );
            }
        }
        let ready = renderer.text.finish_frame(&mut writer, &requests);
        if !ready {
            // Submit glyph requests without a FramePacket; retain the last image
            // and retry on later turns while input and completions keep flowing.
            Hal::global().submit(&writer.buf());
            return;
        }
        let viewport = [self.geometry[2], self.geometry[3]];
        let mut uniforms: [Vec<f32>; 4] = Default::default();
        let sdf = makepad_font_core::raster::Settings::default().sdfer;
        for (i, pipe) in program.pipes.iter().enumerate() {
            pipe.uniforms.write(
                &[
                    (id!(viewport), &viewport),
                    (id!(time), &[renderer.began.elapsed().as_secs_f32()]),
                    (id!(from), &[renderer.from]),
                    (id!(previous), &[renderer.target]),
                    (id!(changed), &[renderer.changed]),
                    (id!(completed), &[self.state.completed_weight as f32]),
                    (id!(weight), &[self.state.phase_weight as f32]),
                    (id!(total_weight), &[self.state.total_weight as f32]),
                    (id!(done), &[self.state.done.unwrap_or(0) as f32]),
                    (id!(total), &[self.state.total.unwrap_or(0) as f32]),
                    (id!(phase_elapsed), &[self.state.phase_elapsed as f32]),
                    (id!(radius), &[sdf.radius]),
                    (id!(cutoff), &[sdf.cutoff]),
                ],
                &mut uniforms[i],
            );
        }
        self.frame += 1;
        writer.frame_begin(
            self.frame,
            FrameMeta {
                build_start_ns,
                ..Default::default()
            },
        );
        writer.pass(Pass {
            load: [pass_load::CLEAR; 5],
            clear: [[0.0; 4]; 4],
            viewport: [0.0, 0.0, viewport[0] * self.dpi, viewport[1] * self.dpi],
            dpi: self.dpi,
            ..Default::default()
        });
        for i in 0..program.pipes.len() {
            let rect = if i == PROGRESS || i == ERROR_BAND {
                clip
            } else {
                renderer.layout.panel
            };
            program.pipes[i].draw(
                &mut writer,
                &data[i],
                &uniforms[i],
                renderer.text.atlas(),
                rect.map(|v| v * self.dpi),
            );
        }
        writer.frame_set_build_end(makepad_hal::clock_ns());
        writer.frame_end(window, target::WINDOW);
        Hal::global().submit(&writer.buf());
        renderer.redraw = false;
    }
}

impl Renderer {
    fn layout(&mut self, state: &State, size: [f32; 2]) {
        let program = self.active.as_ref().unwrap();
        let style = program.layout(state.mode);
        let margin = style
            .margin
            .min((size[0].min(size[1]) * 0.5 - 1.0).max(0.0));
        let width = (size[0] - margin * 2.0).max(1.0);
        let height = (size[1] - margin * 2.0).max(1.0);
        let panel = [
            margin,
            margin,
            if style.max_width > 0.0 {
                width.min(style.max_width)
            } else {
                width
            },
            if style.max_height > 0.0 {
                height.min(style.max_height)
            } else {
                height
            },
        ];
        let padding = style
            .padding
            .min((panel[2].min(panel[3]) * 0.5 - 1.0).max(0.0));
        let x = panel[0] + padding;
        let top = panel[1] + style.top.min((panel[3] - padding - 1.0).max(0.0));
        let width = (panel[2] - 2.0 * padding).max(1.0);
        let mut y = top;
        let mut text = Vec::new();
        let mut progress = None;
        let mut hints_height = 0.0;
        self.text.begin_layout();
        for line in &program.lines {
            let lines: Vec<(String, Option<usize>)> = match line.role {
                Role::App => vec![(state.app.clone(), None)],
                Role::Progress => {
                    if state.mode == Mode::Boot {
                        progress = Some([x, y, width, line.height]);
                        y += line.height + line.gap;
                    }
                    continue;
                }
                Role::Status if state.mode == Mode::Overlay => continue,
                Role::Status => vec![(
                    format!(
                        "{} · {} · {}{}",
                        state.phase.name(),
                        if state.warm { "warm" } else { "cold" },
                        state.current,
                        match (state.done, state.total) {
                            (Some(done), Some(total)) => format!(" · {done}/{total}"),
                            _ => String::new(),
                        }
                    ),
                    None,
                )],
                Role::Domain => vec![(
                    if state.mode == Mode::Overlay {
                        if state.parked.is_some() {
                            "Panic parked".into()
                        } else {
                            state.domain.clone()
                        }
                    } else {
                        state.domain.clone()
                    },
                    None,
                )],
                Role::Errors => state
                    .diagnostics
                    .iter()
                    .enumerate()
                    .map(|(i, d)| (diagnostic_text(d), Some(i)))
                    .collect(),
                Role::Panic => state
                    .parked
                    .as_ref()
                    .map(|p| vec![(format!("{} {}\n{}", p.id, p.location, p.message), None)])
                    .unwrap_or_default(),
                Role::Hints => vec![(program.hints(state, self.input.as_deref()), None)],
            };
            for (value, error) in lines {
                let run = self.text.shape(&value, line.size, width, line.height);
                let height = run.rows as f32 * line.height;
                let fixed = matches!(line.role, Role::Hints);
                let at = if fixed {
                    (panel[1] + panel[3] - padding - height).max(panel[1])
                } else {
                    y
                };
                text.push(TextLine {
                    run,
                    position: [x, at],
                    style: *line,
                    error,
                    fixed,
                });
                if fixed {
                    hints_height += height + line.gap;
                } else {
                    y += height + line.gap;
                }
            }
        }
        self.text.end_layout();
        let clip = [
            x,
            top,
            width,
            (panel[1] + panel[3] - padding - hints_height - top).max(0.0),
        ];
        if self.reveal_selection {
            if let Some(line) = text.iter().find(|line| line.error == Some(self.selected)) {
                self.scroll = (line.position[1] - top).max(0.0);
            }
            self.reveal_selection = false;
        }
        self.layout = Layout {
            panel,
            clip,
            text,
            progress,
            content_height: y - top,
        };
    }
}

fn crop(mut rect: [f32; 4], mut uv: [f32; 4], clip: [f32; 4]) -> ([f32; 4], [f32; 4]) {
    if rect[2] <= 0.0 || rect[3] <= 0.0 {
        return (rect, uv);
    }
    for axis in 0..2 {
        let start = rect[axis].max(clip[axis]);
        let end = (rect[axis] + rect[axis + 2]).min(clip[axis] + clip[axis + 2]);
        let scale = (uv[axis + 2] - uv[axis]) / rect[axis + 2];
        uv[axis + 2] = uv[axis] + (end - rect[axis]) * scale;
        uv[axis] += (start - rect[axis]) * scale;
        rect[axis] = start;
        rect[axis + 2] = (end - start).max(0.0);
    }
    (rect, uv)
}
