//! Carriers: what a connection runs over. Each produces a `FrameReader`, a writer and a shutdown
//! function; the handshake and everything above are the same for all of them.

pub mod loopback;
pub mod stdio;
#[cfg(not(target_arch = "wasm32"))]
pub mod tcp;
pub mod unix;

use crate::frame::FrameReader;
use std::io::Write;

/// What `accept` returned stays in this process. A socket std makes itself is not inheritable, but
/// the one `accept` returns is on Windows, and `Command` passes every inheritable handle on: a run
/// that outlived its hub kept that hub's links open, so the peer heard no close and called a
/// process that was gone until the run ended (a Windows node "down" for up to 10 min per hub
/// restart, 11-04). Elsewhere `accept` closes on exec.
pub fn keep_from_runs(s: &std::net::TcpStream) {
    #[cfg(windows)]
    {
        use std::os::windows::io::AsRawSocket;
        use windows::Win32::Foundation::{SetHandleInformation, HANDLE, HANDLE_FLAGS, HANDLE_FLAG_INHERIT};
        if let Err(e) = unsafe { SetHandleInformation(HANDLE(s.as_raw_socket() as *mut core::ffi::c_void), HANDLE_FLAG_INHERIT.0, HANDLE_FLAGS(0)) } {
            eprintln!("makepad-remote: a run would hold this connection: {e}");
        }
    }
    #[cfg(not(windows))]
    let _ = s;
}

/// The halves of a carrier before the handshake.
pub struct Carrier {
    pub reader: FrameReader,
    pub writer: Box<dyn Write + Send>,
    pub shutdown: Box<dyn Fn() + Send + Sync>,
}

#[cfg(all(test, windows))]
mod tests {
    use std::io::Read;
    use std::process::{Command, Stdio};

    /// The peer of a connection this process accepted hears its close at once, whatever this
    /// process started meanwhile. A run that inherited the socket holds it open instead.
    #[test]
    fn a_run_holds_no_accepted_connection() {
        let listener = std::net::TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let addr = listener.local_addr().unwrap();
        let closes = |keep: bool| {
            let mut peer = std::net::TcpStream::connect(addr).unwrap();
            let (accepted, _) = listener.accept().unwrap();
            if keep {
                super::keep_from_runs(&accepted);
            }
            let mut run = Command::new("ping").args(["-n", "30", "127.0.0.1"]).stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null()).spawn().unwrap();
            drop(accepted);
            peer.set_read_timeout(Some(std::time::Duration::from_secs(2))).unwrap();
            let closed = peer.read(&mut [0u8; 1]).is_ok_and(|n| n == 0);
            let _ = run.kill();
            let _ = run.wait();
            closed
        };
        assert!(!closes(false), "what accept returns is inheritable here: the run holds it");
        assert!(closes(true));
    }
}
