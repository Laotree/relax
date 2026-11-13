use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::process::Command;
fn control() {
    let output = Command::new(env!("CARGO_BIN_EXE_non-unicode-launch")).env_clear().output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"ready\n");
    assert!(output.stderr.is_empty());
}
#[test]
fn program_receives_non_unicode_arguments() {
    control();
    let output = Command::new(env!("CARGO_BIN_EXE_non-unicode-launch")).env_clear()
        .arg(OsString::from_vec(vec![0xff])).output().unwrap();
    assert_eq!(output.status.code(), Some(2), "{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.stdout.is_empty());
    assert_eq!(output.stderr, b"invalid argument\n");
}
#[test]
fn program_receives_non_unicode_environment_values() {
    control();
    let output = Command::new(env!("CARGO_BIN_EXE_non-unicode-launch")).env_clear()
        .env("NON_UNICODE_VALUE", OsString::from_vec(vec![0xfe])).output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(output.stdout, b"ready\n");
    assert!(output.stderr.is_empty());
}
