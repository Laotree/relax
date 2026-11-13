use std::process::Command;
fn control() {
    let out = Command::new(env!("CARGO_BIN_EXE_child-native-fixture")).output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(out.stdout, b"5\n");
}
#[test]
fn removing_the_flag_does_not_change_the_prepared_binary() {
    control();
    let out = Command::new(env!("CARGO_BIN_EXE_child-native-fixture"))
        .env_remove("RELAX_ALLOW_C").output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(out.stdout, b"5\n");
}
#[test]
fn cleared_environment_keeps_the_prepared_binary_usable() {
    control();
    let out = Command::new(env!("CARGO_BIN_EXE_child-native-fixture"))
        .arg("--empty").env_clear().output().unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    assert_eq!(out.stdout, b"5\n");
}

#[test]
fn cleared_environment_survives_a_self_exec_grandchild() {
    control();
    let child = std::process::Command::new(env!("CARGO_BIN_EXE_child-native-fixture"))
        .arg("--nested").env_clear().output().unwrap();
    assert!(child.status.success(), "{}", String::from_utf8_lossy(&child.stderr));
    assert_eq!(child.stdout, b"5\n");
}

#[test]
fn inherited_self_exec_can_later_clear_its_environment() {
    control();
    let child = std::process::Command::new(env!("CARGO_BIN_EXE_child-native-fixture"))
        .arg("--nested").output().unwrap();
    assert!(child.status.success(), "{}", String::from_utf8_lossy(&child.stderr));
    assert_eq!(child.stdout, b"5\n");
}
