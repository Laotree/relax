//! `relax hub`, `relax remote-relay` and `relax remote ...`: the command line of the remote hub
//! (routing and links live in libs/remote: hub.rs, relay.rs, pair.rs, hosts.rs).

use makepad_remote::hosts::{self, Host, Hosts, Via};

fn flag<'a>(args: &'a [String], name: &str) -> Option<&'a str> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).map(String::as_str)
}

fn registry() -> Result<Hosts, String> {
    Hosts::load(&hosts::registry_path()).map_err(|e| e.to_string())
}

/// `relax hub [--listen <addr>]`: the router `relax inspect <host>:...` starts on demand. It exits
/// 60 s after its last client; with `--listen` (paired devices dial this address) it keeps running.
pub fn hub(args: &[String]) -> i32 {
    #[cfg(unix)]
    {
        let hosts = match registry() {
            Ok(h) => h,
            Err(e) => {
                eprintln!("relax hub: {e}");
                return 1;
            }
        };
        match makepad_remote::hub::serve(hosts, flag(args, "--listen")) {
            Ok(true) => 0,
            Ok(false) => {
                eprintln!("relax hub: one is already running");
                0
            }
            Err(e) => {
                eprintln!("relax hub: {e}");
                1
            }
        }
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        eprintln!("relax hub: not available on Windows yet");
        2
    }
}

/// `relax remote-relay [--dial <hub host:port> --key-file <path> [--name <n>] [--fingerprint <hex>]]`:
/// serves this machine's endpoints to a hub, over stdin/stdout (run through ssh) or by dialling.
pub fn relay(args: &[String]) -> i32 {
    #[cfg(unix)]
    {
        use makepad_remote::relay;
        let Ok(exe) = std::env::current_exe() else {
            eprintln!("remote-relay: cannot find the relax executable");
            return 1;
        };
        let name = flag(args, "--name").unwrap_or("relay").to_string();
        let cfg = relay::Config {
            name,
            launch: vec![exe.display().to_string(), "run".into()],
            env: vec![("MAKEPAD_HIDE_WINDOWS".into(), "1".into()), ("SANDBOX_MUTE".into(), "1".into())],
        };
        let ep = relay::endpoint(cfg);
        let Some(addr) = flag(args, "--dial") else {
            return match relay::serve_stdio(&ep) {
                Ok(()) => 0,
                Err(e) => {
                    eprintln!("remote-relay: {e}");
                    1
                }
            };
        };
        let Some(key_file) = flag(args, "--key-file") else {
            eprintln!("remote-relay: --dial needs --key-file <path>");
            return 2;
        };
        let creds = match relay::credentials(std::path::Path::new(key_file), flag(args, "--fingerprint").unwrap_or(""), hosts::config_dir().join("known_hosts")) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("remote-relay: {key_file}: {e}");
                return 1;
            }
        };
        relay::dial_forever(&ep, addr, &creds)
    }
    #[cfg(not(unix))]
    {
        let _ = args;
        eprintln!("remote-relay: not available on Windows yet");
        2
    }
}

fn remote_usage() -> i32 {
    eprintln!("usage: relax remote add <name> --ssh <user@host> [--relax <path on that host>]");
    eprintln!("       relax remote pair <name> [--hub <host:port>] [--print | --adb | --ssh <user@host>]");
    eprintln!("       relax remote list");
    2
}

/// `relax remote add|pair|list`: the hosts registry (`~/.config/makepad/remote/hosts.toml`).
pub fn remote(args: &[String]) -> i32 {
    let run = || -> Result<(), String> {
        match args.first().map(String::as_str) {
            Some("add") => {
                let name = args.get(1).ok_or("add: a host name")?;
                let ssh = flag(args, "--ssh").ok_or("add: --ssh <user@host>")?;
                if !hosts::valid_name(name) {
                    return Err(format!("host name `{name}`: use letters, digits, `-` and `_`"));
                }
                let mut reg = registry()?;
                reg.set(Host { name: name.clone(), via: Via::Ssh { ssh: ssh.to_string(), relax: flag(args, "--relax").unwrap_or("relax").to_string() } });
                reg.save(&hosts::registry_path()).map_err(|e| e.to_string())
            }
            Some("pair") => {
                use makepad_remote::pair::{pair, Delivery};
                let name = args.get(1).ok_or("pair: a host name")?;
                let delivery = if args.iter().any(|a| a == "--adb") {
                    Delivery::Adb
                } else if let Some(t) = flag(&args[2..], "--ssh") {
                    Delivery::Ssh(t.to_string())
                } else {
                    Delivery::Print
                };
                let hub = flag(args, "--hub").unwrap_or(if matches!(delivery, Delivery::Adb) { "127.0.0.1:7907" } else { "" });
                if hub.is_empty() {
                    return Err("pair: --hub <host:port> (the address the device dials; the hub runs `relax hub --listen` on it)".into());
                }
                let cmd = pair(name, hub, delivery).map_err(|e| e.to_string())?;
                println!("{cmd}");
                eprintln!("paired `{name}`; (re)start `relax hub --listen {hub}` to accept it");
                Ok(())
            }
            Some("list") => {
                for h in registry()?.hosts {
                    match h.via {
                        Via::Ssh { ssh, relax } => println!("{} ssh {ssh} {relax}", h.name),
                        Via::Dial { .. } => println!("{} dial", h.name),
                    }
                }
                Ok(())
            }
            _ => Err(String::new()),
        }
    };
    match run() {
        Ok(()) => 0,
        Err(e) if e.is_empty() => remote_usage(),
        Err(e) => {
            eprintln!("relax remote: {e}");
            1
        }
    }
}
