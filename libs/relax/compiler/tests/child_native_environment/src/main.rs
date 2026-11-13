fn main() {
    let cargo = std::path::Path::new(env!("CARGO"));
    assert!(cargo.is_absolute() && cargo.is_file());
    assert!(cfg!(fixture_built));
    assert!(cfg!(home_configured));
    assert_eq!(env!("CHILD_FIXTURE_BUILD"), "prepared");
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|arg| arg == "--live-native") {
        if std::env::var_os("LIVE_NATIVE_REENTERED").is_none() {
            use std::os::unix::process::CommandExt;
            let error = std::process::Command::new(std::env::current_exe().unwrap())
                .args(std::env::args_os().skip(1)).env("LIVE_NATIVE_REENTERED", "1").exec();
            panic!("exec failed: {error}");
        }
        println!("{}:{}:{}", cnative::add(2, 3), env!("ROOT_VERSION"), std::env::var("ROOT_VERSION").unwrap_or_default());
        if args.iter().any(|arg| arg == "--once") { return; }
        loop { std::thread::sleep(std::time::Duration::from_millis(25)); }
    }
    if args.iter().any(|arg| arg == "--empty") {
        assert!(cnative::home_is_unset(), "native C sees a HOME the child was not given");
        for name in ["HOME", "PATH", "CARGO", "CARGO_HOME", "RUSTUP_HOME", "RELAX_BUILD_ENV", "CHILD_FIXTURE_BUILD", "ROOT_VERSION"] {
            assert!(std::env::var_os(name).is_none(), "unexpected {name}");
            assert!(!std::env::vars_os().any(|(key, _)| key == name), "listed {name}");
        }
        let output = std::process::Command::new("/bin/sh").args(["-c", "printf '%s' ${HOME-unset}:${PATH-unset}:${CARGO_HOME-unset}"]).output().unwrap();
        // Shells may initialize PATH themselves. HOME and CARGO_HOME must remain absent.
        assert!(output.stdout.starts_with(b"unset:"));
        assert!(output.stdout.ends_with(b":unset"));
        use std::os::unix::fs::PermissionsExt;
        let directory = std::env::temp_dir().join(format!("child-native-helper-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let helper = directory.join("helper");
        std::fs::write(&helper, "#!/bin/sh\nprintf 'helper\\n'\n").unwrap();
        std::fs::set_permissions(&helper, std::fs::Permissions::from_mode(0o755)).unwrap();
        std::env::set_var("PATH", &directory);
        let output = std::process::Command::new("helper").output().unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, b"helper\n");
        std::fs::remove_dir_all(directory).unwrap();
    }
    if args.iter().any(|arg| arg == "--nested") {
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .arg("--empty").env_clear().output().unwrap();
        assert!(child.status.success(), "{}", String::from_utf8_lossy(&child.stderr));
        assert_eq!(child.stdout, b"5\n");
    }
    if args.iter().any(|arg| arg == "--shell-nested") {
        let child = std::process::Command::new("/bin/sh")
            .args(["-c", "exec \"$1\" --empty", "fixture-shell"])
            .arg(std::env::current_exe().unwrap()).env_clear().output().unwrap();
        assert!(child.status.success(), "{}", String::from_utf8_lossy(&child.stderr));
        assert_eq!(child.stdout, b"5\n");
    }
    println!("{}", cnative::add(2, 3));
}
