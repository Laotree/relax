// `--empty`: started with a cleared environment, the program has none (its own reads, a list of
// them, a shell's). `--nested`: starts itself (current_exe) with a cleared environment.
fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "--empty") {
        for name in ["HOME", "PATH", "PREPARED_TOKEN", "CARGO_HOME", "RUSTUP_HOME"] {
            assert!(std::env::var_os(name).is_none(), "the program reads {name}");
            assert!(!std::env::vars_os().any(|(k, _)| k == name), "the program lists {name}");
        }
        #[cfg(unix)]
        {
            let out = std::process::Command::new("/bin/sh").args(["-c", "printf '%s:%s' \"${HOME-unset}\" \"${PREPARED_TOKEN-unset}\""]).output().unwrap();
            assert_eq!(String::from_utf8_lossy(&out.stdout), "unset:unset", "a shell the program starts has variables it was not given");
        }
    }
    if args.iter().any(|a| a == "--nested") {
        let child = std::process::Command::new(std::env::current_exe().unwrap()).arg("--empty").env_clear().output().unwrap();
        assert!(child.status.success(), "its own executable, started with a cleared environment: {}", String::from_utf8_lossy(&child.stderr));
        assert_eq!(String::from_utf8_lossy(&child.stdout), format!("{} 5\n", env!("PREPARED_BUILD")));
    }
    println!("{} {}", env!("PREPARED_BUILD"), pc_native::add(2, 3));
}
