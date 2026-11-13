#![cfg(unix)]
use std::fs;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{chown, symlink, MetadataExt};
use std::path::PathBuf;

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("relax-chown-{}-{name}", std::process::id()))
}

#[test]
fn none_preserves_the_owner_and_group() {
    let p = path("preserve");
    fs::write(&p, b"data").unwrap();
    let before = fs::metadata(&p).unwrap();
    chown(&p, None, None).unwrap();
    let after = fs::metadata(&p).unwrap();
    assert_eq!((after.uid(), after.gid()), (before.uid(), before.gid()));
    assert_eq!(fs::read(&p).unwrap(), b"data");
    fs::remove_file(p).unwrap();
}

#[test]
fn explicit_current_owner_and_group_are_accepted() {
    let p = path("explicit");
    fs::write(&p, b"data").unwrap();
    let before = fs::metadata(&p).unwrap();
    chown(&p, Some(before.uid()), None).unwrap();
    chown(&p, None, Some(before.gid())).unwrap();
    chown(&p, Some(before.uid()), Some(before.gid())).unwrap();
    let after = fs::metadata(&p).unwrap();
    assert_eq!((after.uid(), after.gid()), (before.uid(), before.gid()));
    fs::remove_file(p).unwrap();
}

#[test]
fn follows_symlinks() {
    let target = path("target");
    let link = path("link");
    fs::write(&target, b"data").unwrap();
    symlink(&target, &link).unwrap();
    chown(&link, None, None).unwrap();
    fs::remove_file(&target).unwrap();
    assert_eq!(chown(&link, None, None).unwrap_err().kind(), std::io::ErrorKind::NotFound);
    fs::remove_file(link).unwrap();
}

#[test]
fn missing_paths_return_an_os_error() {
    let p = path("missing");
    assert_eq!(chown(p, None, None).unwrap_err().kind(), std::io::ErrorKind::NotFound);
}

#[test]
fn nul_paths_return_invalid_input() {
    let path = std::ffi::OsStr::from_bytes(b"bad\0path");
    assert_eq!(chown(path, None, None).unwrap_err().kind(), std::io::ErrorKind::InvalidInput);
}
