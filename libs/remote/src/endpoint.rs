//! The endpoint: the service registry of one process, its capability list, the replay ring and
//! the carriers that accept connections. Hosts register services (`cmd` with their dispatch,
//! `watch`, `stream`, others later); Relax registers its inspect dispatch as the `cmd` service.

use crate::cmd::{self, Out, Req};
use crate::conn::{Conn, Hooks, Io, Open, OpenHandler, CLOSE_UNSUPPORTED};
use crate::frame::FrameReader;
use crate::hello::{self, Hello, HandshakeError};
use crate::ring::{Ring, DEFAULT_RING_BYTES};
use crate::stream::StreamSink;
use crate::watch::WatchSink;
use std::io::Write;
use std::sync::{Arc, Mutex, RwLock};

/// Opens one channel of a service: takes the channel (usually into a thread) or refuses with a
/// CLOSE code and reason.
pub type Factory = Arc<dyn Fn(&Conn, Open) -> Result<(), (u16, String)> + Send + Sync>;

struct Service {
    name: String,
    version: u32,
    factory: Factory,
}

struct Inner {
    app: String,
    services: RwLock<Vec<Service>>,
    hooks: Mutex<Hooks>,
    ring: Arc<Ring>,
}

#[derive(Clone)]
pub struct Endpoint(Arc<Inner>);

impl Endpoint {
    pub fn new(app: &str) -> Endpoint {
        Endpoint::with_ring(app, DEFAULT_RING_BYTES)
    }

    /// An endpoint whose replay ring holds `ring_bytes` of stream chunks.
    pub fn with_ring(app: &str, ring_bytes: usize) -> Endpoint {
        Endpoint(Arc::new(Inner { app: app.to_string(), services: RwLock::new(Vec::new()), hooks: Mutex::new(Hooks::default()), ring: Arc::new(Ring::new(ring_bytes)) }))
    }

    /// Listens on this process's Unix socket and writes the discovery file (register the services
    /// first: the caps are written now). `extra`: already-serialised `,"key":value` fields.
    pub fn listen_unix(&self, extra: &str) -> std::io::Result<std::path::PathBuf> {
        crate::carrier::unix::listen(self, extra)
    }

    pub fn app(&self) -> &str {
        &self.0.app
    }

    /// Hooks that run first / last on every thread the endpoint starts (set before serving).
    pub fn set_hooks(&self, hooks: Hooks) {
        *self.0.hooks.lock().unwrap() = hooks;
    }

    pub fn hooks(&self) -> Hooks {
        *self.0.hooks.lock().unwrap()
    }

    /// Registers (or replaces) a service.
    pub fn register(&self, name: &str, version: u32, factory: Factory) {
        let mut s = self.0.services.write().unwrap();
        s.retain(|x| x.name != name);
        s.push(Service { name: name.to_string(), version, factory });
    }

    /// The `cmd` service, answered by `dispatch`.
    pub fn register_cmd(&self, dispatch: fn(&Req, &mut Out)) {
        self.register("cmd", 1, cmd::service(dispatch));
    }

    /// The `watch` service; events are published through the returned sink.
    pub fn register_watch(&self) -> WatchSink {
        self.register("watch", 1, crate::watch::service(self.0.ring.clone()));
        WatchSink(self.0.ring.clone())
    }

    /// The `watch` service, calling `opened` / `closed` as channels start and stop following.
    pub fn register_watch_with(&self, opened: fn(), closed: fn()) -> WatchSink {
        self.register("watch", 1, crate::watch::service_with(self.0.ring.clone(), opened, closed));
        WatchSink(self.0.ring.clone())
    }

    /// The `stream` service; chunks are published through the returned sink.
    pub fn register_stream(&self) -> StreamSink {
        self.register("stream", 1, crate::stream::service(self.0.ring.clone()));
        StreamSink(self.0.ring.clone())
    }

    pub fn ring(&self) -> &Arc<Ring> {
        &self.0.ring
    }

    /// `service/version` of every registered service.
    pub fn caps(&self) -> Vec<String> {
        self.0.services.read().unwrap().iter().map(|s| format!("{}/{}", s.name, s.version)).collect()
    }

    fn handler(&self) -> OpenHandler {
        let ep = self.clone();
        Arc::new(move |conn, open| {
            let found = ep.0.services.read().unwrap().iter().find(|s| s.name == open.service).map(|s| (s.factory.clone(), format!("{}/{}", s.name, s.version)));
            match found {
                Some((factory, caps)) => factory(conn, open).map(|_| caps),
                None => Err((CLOSE_UNSUPPORTED, format!("unsupported service {}", open.service))),
            }
        })
    }

    /// Runs the endpoint side of the handshake on a carrier and, if the peer is acceptable, starts
    /// the connection. A different protocol major version is refused with a message that names
    /// both versions.
    pub fn serve(&self, mut reader: FrameReader, mut writer: Box<dyn Write + Send>, shutdown: Box<dyn Fn() + Send + Sync>) -> Result<Conn, HandshakeError> {
        reader.deadline = Some(std::time::Instant::now() + std::time::Duration::from_secs(10));
        let own = Hello { name: self.0.app.clone(), caps: self.caps(), ..Hello::default() };
        let peer = match hello::server_handshake(&mut reader, &mut *writer, &own) {
            Ok(p) => p,
            Err(e) => {
                shutdown();
                return Err(e);
            }
        };
        Ok(Conn::start(Io { reader, writer, shutdown }, peer, false, Some(self.handler()), self.hooks()))
    }
}
