use std::process::{Command, Output};

fn helper(output: Output) {
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(String::from_utf8_lossy(&output.stdout).contains("helper ran"));
}

#[test]
fn self_through_another_program() {
    if std::env::var("SELF_EXE_CHILD").as_deref() == Ok("1") {
        println!("helper ran");
        return;
    }
    let exe = std::env::current_exe().unwrap();
    let args = ["--exact", "self_through_another_program", "--nocapture"];
    helper(Command::new(&exe).args(args).env("SELF_EXE_CHILD", "1").output().unwrap());
    helper(Command::new(env!("CARGO_BIN_EXE_self-exe-artifacts"))
        .arg("--launch").arg(&exe).args(args).env("SELF_EXE_CHILD", "1").output().unwrap());
}

#[cfg(unix)]
#[test]
fn self_through_shell() {
    if std::env::var("SELF_EXE_CHILD").as_deref() == Ok("1") {
        println!("helper ran");
        return;
    }
    let exe = std::env::current_exe().unwrap();
    let args = ["--exact", "self_through_shell", "--nocapture"];
    helper(Command::new(&exe).args(args).env("SELF_EXE_CHILD", "1").output().unwrap());
    helper(Command::new("/bin/sh")
        .args(["-c", "exec \"$SELF_EXE\" \"$@\"", "sh"]).args(args)
        .env("SELF_EXE", &exe).env("SELF_EXE_CHILD", "1").output().unwrap());
}

#[test]
fn cargo_binary_launch() {
    let direct = Command::new(env!("CARGO_BIN_EXE_self-exe-artifacts")).output().unwrap();
    assert!(direct.status.success());
    assert_eq!(direct.stdout, b"artifact ran\n");
}

#[test]
fn package_binary_beside_test_artifacts() {
    let exe = std::env::current_exe().unwrap();
    // Cargo 1.100 runs tests in build/<package>/<hash>/out; earlier Cargo uses deps/.
    let depth = if exe.parent().unwrap().file_name() == Some(std::ffi::OsStr::new("out")) { 5 } else { 2 };
    let binary = exe.ancestors().nth(depth).unwrap().join(format!("self-exe-artifacts{}", std::env::consts::EXE_SUFFIX));
    let sibling = Command::new(&binary).output().unwrap_or_else(|e| panic!("{}: {e}", binary.display()));
    assert!(sibling.status.success(), "{}", String::from_utf8_lossy(&sibling.stderr));
    assert_eq!(sibling.stdout, b"artifact ran\n");
    let argv0 = Command::new(&binary).arg("--argv0").output().unwrap();
    assert!(argv0.status.success());
    assert_eq!(String::from_utf8(argv0.stdout).unwrap().trim_end(), binary.to_str().unwrap());
}

#[cfg(unix)]
#[test]
fn self_after_loader_replaced() {
    if std::env::var("SELF_EXE_CHILD").as_deref() == Ok("1") {
        println!("helper ran");
        return;
    }
    let exe = std::env::current_exe().unwrap();
    if let Some(loader) = std::env::var_os("SELF_EXE_REPLACE_LOADER") {
        std::fs::remove_file(&loader).unwrap();
        std::fs::write(&loader, b"replacement loader").unwrap();
    }
    let args = ["--exact", "self_after_loader_replaced", "--nocapture"];
    helper(Command::new(&exe).args(args).env("SELF_EXE_CHILD", "1").output().unwrap());
    helper(Command::new("/bin/sh")
        .args(["-c", "exec \"$SELF_EXE\" \"$@\"", "sh"]).args(args)
        .env("SELF_EXE", &exe).env("SELF_EXE_CHILD", "1").output().unwrap());
}

#[cfg(unix)]
#[test]
#[ignore = "exec replaces the harness; run in its own process"]
fn self_after_exec() {
    use std::os::unix::process::CommandExt;
    if std::env::var("SELF_EXE_EXEC_STAGE").as_deref() == Ok("child") {
        println!("helper ran");
        return;
    }
    let exe = std::env::current_exe().unwrap();
    let args = ["--ignored", "--exact", "self_after_exec", "--nocapture"];
    if std::env::var("SELF_EXE_EXEC_STAGE").as_deref() != Ok("replaced") {
        let mut command = if std::env::var_os("SELF_EXE_EXEC_SHELL").is_some() {
            let mut shell = Command::new("/bin/sh");
            shell.args(["-c", "exec \"$SELF_EXE\" \"$@\"", "sh"]).env("SELF_EXE", &exe);
            shell
        } else { Command::new(&exe) };
        let error = command.args(args).env("SELF_EXE_EXEC_STAGE", "replaced").exec();
        panic!("exec returned: {error}");
    }
    helper(Command::new(&exe).args(args).env("SELF_EXE_EXEC_STAGE", "child").output().unwrap());
}
