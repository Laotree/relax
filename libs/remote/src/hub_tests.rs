//! The hub and the relay, in process: a dial-style link over a socket pair, clients over another.

use crate::carrier::Carrier;
use crate::conn::{Channel, Conn, Event, CLOSE_REFUSED};
use crate::endpoint::Endpoint;
use crate::frame::FrameReader;
use crate::hosts::{Host, Hosts, Via};
use crate::hub::Hub;
use crate::relay;
use crate::tests::{pair, shared};
use std::os::unix::net::UnixStream;
use std::time::Duration;

const WAIT: Duration = Duration::from_secs(15);

fn carrier(s: UnixStream) -> Carrier {
    let (r, w) = (s.try_clone().unwrap(), s.try_clone().unwrap());
    Carrier {
        reader: FrameReader::new(Box::new(r)),
        writer: Box::new(w),
        shutdown: Box::new(move || {
            let _ = s.shutdown(std::net::Shutdown::Both);
        }),
    }
}

fn hosts() -> Hosts {
    Hosts { hosts: vec![Host { name: "d".into(), via: Via::Dial { key: "00".repeat(32), fingerprint: String::new() } }] }
}

fn relay_endpoint() -> Endpoint {
    relay::endpoint(relay::Config { name: "d".into(), launch: vec!["/bin/sleep".into()], env: vec![("SANDBOX_MUTE".into(), "1".into())] })
}

/// A relay named `d` links itself to the hub over a socket pair.
fn link(hub: &Hub, relay: &Endpoint) -> Conn {
    let (a, b) = UnixStream::pair().unwrap();
    let h = hub.clone();
    std::thread::spawn(move || {
        let _ = h.accept_dialed(carrier(a));
    });
    relay.connect(carrier(b), "test-link").unwrap()
}

fn client(hub: &Hub) -> Conn {
    pair(&hub.client_endpoint())
}

fn lines_of(ch: &Channel) -> Vec<String> {
    let mut out = Vec::new();
    loop {
        match ch.recv_timeout(WAIT) {
            Ok(Event::Data(d)) => {
                for l in String::from_utf8_lossy(&d).lines() {
                    if l.starts_with("{\"end\":") {
                        return out;
                    }
                    out.push(l.to_string());
                }
            }
            other => panic!("no end line, got {other:?} after {out:?}"),
        }
    }
}

fn request(c: &Conn, route: &str, line: &str) -> Vec<String> {
    let ch = c.open("route", route).unwrap();
    ch.send(line.as_bytes().to_vec()).unwrap();
    lines_of(&ch)
}

#[test]
fn list_and_cmd_round_trip_through_the_hub() {
    let (_, _) = shared();
    let hub = Hub::new(&hosts());
    let _relay_conn = link(&hub, &relay_endpoint());
    let c = client(&hub);
    let me = std::process::id();
    let list = request(&c, "d list", "list");
    assert!(list.iter().any(|l| l.contains(&format!("\"pid\":{me},")) && l.contains("makepad-remote-test")), "{list:?}");
}

#[test]
fn cmd_goes_to_the_endpoint() {
    let (_, _) = shared();
    let hub = Hub::new(&hosts());
    let _relay_conn = link(&hub, &relay_endpoint());
    let c = client(&hub);
    let me = std::process::id();
    for target in [format!("d:makepad-remote-test"), format!("d:{me}"), format!("d:x#{me}")] {
        let ch = c.open("route", &format!("{target} cmd")).unwrap();
        ch.send(b"ping".to_vec()).unwrap();
        assert_eq!(lines_of(&ch), vec!["{\"pong\":1}".to_string()], "{target}");
        // a second request on the same channel
        ch.send(b"ping".to_vec()).unwrap();
        assert_eq!(lines_of(&ch), vec!["{\"pong\":1}".to_string()]);
    }
}

#[test]
fn unknown_host_and_unknown_app_are_errors() {
    let (_, _) = shared();
    let hub = Hub::new(&hosts());
    let _relay_conn = link(&hub, &relay_endpoint());
    let c = client(&hub);
    let e = c.open("route", "nope cmd").err().unwrap();
    assert_eq!(e.0, CLOSE_REFUSED);
    assert!(e.1.contains("unknown host `nope`") && e.1.contains("known: d"), "{}", e.1);
    let ch = c.open("route", "d:no-such-app cmd").unwrap();
    match ch.recv_timeout(WAIT) {
        Ok(Event::Closed(_, why)) => assert!(why.contains("no running makepad-remote endpoint `no-such-app`"), "{why}"),
        other => panic!("{other:?}"),
    }
}

#[test]
fn unreachable_dial_host_says_so() {
    let hub = Hub::new(&hosts());
    let c = client(&hub);
    let ch = c.open("route", "d cmd").unwrap();
    match ch.recv_timeout(WAIT) {
        Ok(Event::Closed(_, why)) => assert!(why.contains("not connected"), "{why}"),
        other => panic!("{other:?}"),
    }
}

#[test]
fn hosts_report_shows_state_and_rtt() {
    let hub = Hub::new(&hosts());
    let c = client(&hub);
    let ch = c.open("hosts", "").unwrap();
    ch.send(b"hosts".to_vec()).unwrap();
    let l = lines_of(&ch);
    assert!(l[0].contains("\"host\":\"d\"") && l[0].contains("\"state\":\"waiting\""), "{l:?}");
    let _relay_conn = link(&hub, &relay_endpoint());
    // the hub registers the link on its own thread: give it a moment
    let mut l = Vec::new();
    for _ in 0..50 {
        ch.send(b"hosts".to_vec()).unwrap();
        l = lines_of(&ch);
        if l[0].contains("\"state\":\"up\"") {
            break;
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    assert!(l[0].contains("\"state\":\"up\"") && l[0].contains("\"rtt_ms\":"), "{l:?}");
}

#[test]
fn session_launch_and_kill_only_own_pids() {
    let hub = Hub::new(&hosts());
    let _relay_conn = link(&hub, &relay_endpoint());
    let c = client(&hub);
    let ch = c.open("route", "d session").unwrap();
    let ask = |line: &str| {
        ch.send(line.as_bytes().to_vec()).unwrap();
        lines_of(&ch)
    };
    let launched = ask("launch 30");
    assert!(launched[0].starts_with("{\"launched\":"), "{launched:?}");
    let pid: u32 = launched[0]["{\"launched\":".len()..].split(',').next().unwrap().parse().unwrap();
    assert!(ask("launched")[0].contains("\"state\":\"running\""));
    let other = ask(&format!("kill {}", std::process::id()));
    assert!(other[0].contains("was not launched by this relay"), "{other:?}");
    assert_eq!(ask(&format!("kill {pid}"))[0], format!("{{\"killed\":{pid}}}"));
    let mut state = String::new();
    for _ in 0..100 {
        state = ask("launched")[0].clone();
        if state.contains("exited") {
            break;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    assert!(state.contains("exited"), "{state}");
}

#[test]
fn a_dropped_link_resumes_the_watch_feed_with_a_gap_marker() {
    let (_, watch) = shared();
    let hub = Hub::new(&hosts());
    let relay_ep = relay_endpoint();
    let first = link(&hub, &relay_ep);
    let c = client(&hub);
    let me = std::process::id();
    let w = c.open("route", &format!("d:{me} watch")).unwrap();
    std::thread::sleep(Duration::from_millis(300));
    watch.emit("{\"hub\":1}");
    let mut seen = Vec::new();
    let next = |seen: &mut Vec<String>| match w.recv_timeout(WAIT) {
        Ok(Event::Data(d)) => {
            let l = String::from_utf8_lossy(&d[8..]).into_owned();
            seen.push(l.clone());
            l
        }
        other => panic!("{other:?}"),
    };
    while !next(&mut seen).contains("\"hub\":1") {}
    // the link drops; an event happens while it is down; the relay comes back
    first.close("test drop");
    first.wait_closed();
    std::thread::sleep(Duration::from_millis(300));
    watch.emit("{\"hub\":2}");
    let again = relay_ep.clone();
    let h = hub.clone();
    let t = std::thread::spawn(move || link(&h, &again));
    let mut tail = Vec::new();
    loop {
        let l = next(&mut tail);
        if l.contains("\"hub\":2") {
            break;
        }
    }
    let gap = tail.iter().position(|l| l.contains("\"event\":\"gap\"")).expect("gap marker");
    assert!(gap < tail.len() - 1, "the gap marker comes before the event that happened while down: {tail:?}");
    assert_eq!(tail.iter().filter(|l| l.contains("\"hub\":1")).count(), 0, "no replay of what was delivered: {tail:?}");
    let _keep = t.join().unwrap();
}

#[test]
fn dial_mode_over_loopback_tls() {
    let _ = shared();
    use makepad_network::tls::TlsIdentity;
    use makepad_network::tunnel::{ClientCredentials, Psk};
    let dir = std::env::temp_dir().join(format!("makepad-remote-hub-tls-{}", std::process::id()));
    let identity = TlsIdentity::load_or_create(&dir, "makepad-remote-test").unwrap();
    let fp = identity.fingerprint;
    let key = Psk::generate().unwrap();
    let hosts = Hosts { hosts: vec![Host { name: "d".into(), via: Via::Dial { key: key.to_hex(), fingerprint: String::new() } }] };
    let hub = Hub::new(&hosts);
    let addr = crate::carrier::tcp::listen(&hub.dial_endpoint(), "127.0.0.1:0", identity, hosts.dial_keys()).unwrap().to_string();
    let relay_ep = relay_endpoint();
    let a2 = addr.clone();
    std::thread::spawn(move || {
        let creds = ClientCredentials { keys: vec![key], known_hosts: None, expect: Some(fp) };
        relay::dial_forever(&relay_ep, &a2, &creds)
    });
    let c = client(&hub);
    let me = std::process::id();
    let l = request(&c, "d list", "list");
    assert!(l.iter().any(|l| l.contains(&format!("\"pid\":{me},"))), "{l:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn hosts_registry_round_trips() {
    let text = "[host.149]\nvia = \"ssh\"\nssh = \"arch@192.0.2.16\"\nrelax = \"/opt/relax\"\n\n[host.phone]\nvia = \"dial\"\nkey = \"ab\"\nfingerprint = \"cd\"\n";
    let h = Hosts::parse(text).unwrap();
    assert_eq!(h.names(), vec!["149", "phone"]);
    assert_eq!(Hosts::parse(&h.to_text()).unwrap(), h);
    assert!(Hosts::parse("[host.x]\nvia = \"carrier-pigeon\"\n").unwrap_err().contains("via must be"));
    assert!(Hosts::parse("[host.x]\nvia = \"ssh\"\n").unwrap_err().contains("needs ssh"));
}
