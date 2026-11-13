use std::io::{Read, Write};
#[test]
fn prepared_binary_survives_a_failed_refresh() {
    let original = std::path::PathBuf::from(env!("CARGO_BIN_EXE_native-publication"));
    let binary = if let Some(archive) = std::env::var_os("ARCHIVE_BIN") {
        let archive = std::path::PathBuf::from(archive);
        std::fs::copy(&original, &archive).unwrap();
        archive
    } else { original };
    if let (Some(ready), Some(release)) = (std::env::var_os("PREPARED_READY"), std::env::var_os("PREPARED_RELEASE")) {
        std::fs::File::create(ready).unwrap().write_all(b"1").unwrap();
        std::fs::File::open(release).unwrap().read_exact(&mut [0]).unwrap();
    }
    let output = std::process::Command::new(binary).output().unwrap();
    assert!(output.status.success(), "prepared binary failed after refresh: {}", String::from_utf8_lossy(&output.stderr));
    match std::env::var("NATIVE_TEST_CASE").as_deref() {
        Ok("edited") => assert_eq!(output.stdout, b"9\n"),
        Ok("salted") => assert_eq!(output.stdout, b"107\n"),
        _ => assert_eq!(output.stdout, b"7\n"),
    }
}
