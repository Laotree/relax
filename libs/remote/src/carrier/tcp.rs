//! The network carrier: TLS on each OS's own stack with the tunnel's pre-shared-key proof, both
//! from makepad-network (the CI bridge uses the same). It is only opened by an explicit call:
//! [`listen`] for an endpoint that accepts paired peers, [`dial`] for a client. Nothing in this
//! crate opens a TCP port by default.
//!
//! The TLS streams cannot be split between a reader and a writer thread, so both share one
//! mutex-guarded stream and the reader uses a short read timeout (a resumable `WouldBlock`),
//! releasing the lock between reads.

use super::Carrier;
use crate::endpoint::Endpoint;
use crate::frame::FrameReader;
use makepad_network::tls::{TlsIdentity, TlsServer, TlsStream};
use makepad_network::tunnel::{connect_with_credentials, server_authenticate, ClientCredentials, Psk, TunnelConn};
use std::io::{self, Read, Write};
use std::net::{Shutdown, TcpListener, ToSocketAddrs};
use std::sync::{Arc, Mutex};
use std::time::Duration;

const POLL: Duration = Duration::from_millis(20);
const HANDSHAKE: Duration = Duration::from_secs(10);

struct LockedRead<S>(Arc<Mutex<S>>);
struct LockedWrite<S>(Arc<Mutex<S>>);

fn would_block(e: &io::Error) -> bool {
    matches!(e.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut | io::ErrorKind::Interrupted)
}

impl<S: Read> Read for LockedRead<S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let r = self.0.lock().unwrap().read(buf);
        if r.as_ref().is_err_and(would_block) {
            // let a waiting writer take the lock
            std::thread::sleep(Duration::from_millis(1));
        }
        r
    }
}

impl<S: Write> Write for LockedWrite<S> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        loop {
            match self.0.lock().unwrap().write(buf) {
                Err(e) if would_block(&e) => std::thread::sleep(Duration::from_millis(1)),
                r => return r,
            }
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        loop {
            match self.0.lock().unwrap().flush() {
                Err(e) if would_block(&e) => std::thread::sleep(Duration::from_millis(1)),
                r => return r,
            }
        }
    }
}

/// Connects to a paired endpoint at `addr` (`host:port`): TLS, pinned certificate, key proof.
pub fn dial(addr: &str, creds: &ClientCredentials) -> io::Result<Carrier> {
    let conn = connect_with_credentials(addr, creds)?;
    conn.set_read_timeout(Some(POLL))?;
    let shared: Arc<Mutex<TunnelConn>> = Arc::new(Mutex::new(conn));
    let closer = shared.clone();
    Ok(Carrier {
        reader: FrameReader::new(Box::new(LockedRead(shared.clone()))),
        writer: Box::new(LockedWrite(shared)),
        shutdown: Box::new(move || {
            if let Ok(mut c) = closer.lock() {
                c.shutdown();
            }
        }),
    })
}

/// Accepts paired peers on `bind` (`host:port`): each connection does the TLS handshake with
/// `identity` and must prove one of `keys` before anything else is read. Peers that fail are
/// dropped and logged. Returns the bound address.
pub fn listen(endpoint: &Endpoint, bind: &str, identity: TlsIdentity, keys: Vec<Psk>) -> io::Result<std::net::SocketAddr> {
    let addr = bind.to_socket_addrs()?.next().ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "no address to bind"))?;
    let listener = TcpListener::bind(addr)?;
    let local = listener.local_addr()?;
    let fingerprint = identity.fingerprint;
    let tls = Arc::new(TlsServer::new(identity)?);
    let ep = endpoint.clone();
    let hooks = ep.hooks();
    let _ = std::thread::Builder::new().name("makepad-remote-accept".into()).spawn(move || {
        (hooks.enter)();
        for tcp in listener.incoming() {
            let Ok(tcp) = tcp else { continue };
            let (ep, tls, keys) = (ep.clone(), tls.clone(), keys.clone());
            let _ = std::thread::Builder::new().name("makepad-remote-hello".into()).spawn(move || {
                let hooks = ep.hooks();
                (hooks.enter)();
                let peer = tcp.peer_addr().map(|a| a.to_string()).unwrap_or_default();
                if let Err(e) = accept_one(&ep, &tls, &keys, &fingerprint, tcp) {
                    eprintln!("makepad-remote: tcp peer {peer} dropped: {e}");
                }
                (hooks.exit)();
            });
        }
    });
    Ok(local)
}

fn accept_one(ep: &Endpoint, tls: &TlsServer, keys: &[Psk], fingerprint: &[u8; 32], tcp: std::net::TcpStream) -> io::Result<()> {
    tcp.set_read_timeout(Some(HANDSHAKE))?;
    tcp.set_write_timeout(Some(HANDSHAKE))?;
    let mut stream: TlsStream = tls.accept(tcp)?;
    server_authenticate(&mut stream, keys, fingerprint).map_err(|e| io::Error::new(io::ErrorKind::PermissionDenied, e.to_string()))?;
    let raw = stream.try_clone_tcp()?;
    stream.set_write_timeout(None)?;
    stream.set_read_timeout(Some(POLL))?;
    let shared = Arc::new(Mutex::new(stream));
    ep.serve(
        FrameReader::new(Box::new(LockedRead(shared.clone()))),
        Box::new(LockedWrite(shared)),
        Box::new(move || {
            let _ = raw.shutdown(Shutdown::Both);
        }),
    )
    .map(|_| ())
    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e.to_string()))
}
