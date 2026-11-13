//! `Debug` for the listeners' `Incoming` iterators and `IntoIterator for &UnixListener`, as real
//! std has them.
use std::net::TcpListener;
#[cfg(unix)]
use std::os::unix::net::UnixListener;

#[cfg(unix)]
#[test]
fn incoming_debug_and_unix_listener_iter() {
    let tcp = TcpListener::bind("127.0.0.1:0").unwrap();
    let text = format!("{:?}", tcp.incoming());
    assert!(text.starts_with("Incoming { listener: TcpListener"), "{text}");

    let path = std::env::temp_dir().join(format!("relax-unix-listener-{}.sock", std::process::id()));
    let _ = std::fs::remove_file(&path);
    let unix = UnixListener::bind(&path).unwrap();
    let text = format!("{:?}", unix.incoming());
    assert!(text.starts_with("Incoming { listener: UnixListener"), "{text}");
    let _it = (&unix).into_iter();
    let _ = std::fs::remove_file(&path);
}
