use std::os::unix::ffi::OsStrExt;
fn main() {
    if let Some(value) = std::env::var_os("NON_UNICODE_VALUE") { assert_eq!(value.as_bytes(), &[0xfe]); }
    if std::env::args_os().nth(1).is_some_and(|a| a.as_bytes() == [0xff]) {
        eprintln!("invalid argument");
        std::process::exit(2);
    }
    println!("ready");
}
