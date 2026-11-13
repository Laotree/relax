fn prepared_value() {
    assert_eq!(cnative::value(), 7);
}

fn start_child(args: &[&str]) {
    prepared_value();
    std::fs::write(std::env::var_os("COMPILER_GONE").unwrap(), b"gone").unwrap();
    let child = std::process::Command::new(std::env::current_exe().unwrap())
        .args(args).env_clear().output().unwrap();
    assert!(child.status.success(), "prepared child needed its compiler: {}", String::from_utf8_lossy(&child.stderr));
}

fn main() {
    if std::env::args().any(|a| a == "--live-native") {
        if std::env::var_os("LIVE_REENTERED").is_none() {
            use std::os::unix::process::CommandExt;
            let error = std::process::Command::new(std::env::current_exe().unwrap())
                .args(std::env::args_os().skip(1)).env("LIVE_REENTERED", "1").exec();
            panic!("exec failed: {error}");
        }
        println!("{}", cnative::value());
        if std::env::args().any(|a| a == "--once") { return; }
        loop { std::thread::sleep(std::time::Duration::from_millis(25)); }
    }
    if std::env::args().any(|a| a == "--child") {
        prepared_value();
    } else {
        start_child(&["--child"]);
        println!("ok");
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn child() { super::prepared_value(); }

    #[test]
    fn prepared_self_exec_needs_no_compiler() {
        super::start_child(&["--exact", "tests::child"]);
    }
}
