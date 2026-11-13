//! Tool locations retained by integration-test binary wrappers. Never change the application's
//! process environment: native C libraries read it directly, outside the program overlay.
use std::ffi::{OsStr, OsString};
use std::sync::OnceLock;

const NAMES: [&str; 8] = ["PATH", "HOME", "USERPROFILE", "CARGO", "CARGO_HOME", "RUSTUP_HOME", "RUSTUP_TOOLCHAIN", "CARGO_NET_OFFLINE"];
static SETTINGS: OnceLock<crate::progenv::Own> = OnceLock::new();

fn os(value: &[u8]) -> OsString {
    #[cfg(unix)]
    { use std::os::unix::ffi::OsStringExt; OsString::from_vec(value.to_vec()) }
    #[cfg(windows)]
    { use std::os::windows::ffi::OsStringExt; OsString::from_wide(&crate::progenv::wide(value)) }
}

pub const ARG_PREFIX: &str = "--bin-build-env=";
pub const NATIVE_RECEIPT: &str = "RELAX_BIN_NATIVE_RECEIPT";

fn decode(encoded: &str) -> crate::progenv::Own {
    let bytes: Vec<u8> = encoded.as_bytes().chunks(2).map(|b| {
        assert_eq!(b.len(), 2, "prepared build environment: incomplete hex byte");
        u8::from_str_radix(std::str::from_utf8(b).expect("build environment hex"), 16).expect("build environment hex byte")
    }).collect();
    let settings = crate::progenv::parse(&bytes).expect("prepared build environment");
    assert!(settings.iter().all(|(n, _)| n == NATIVE_RECEIPT.as_bytes() || NAMES.iter().any(|s| n == s.as_bytes())), "unsupported build environment name");
    settings
}

fn encode(settings: &crate::progenv::Own) -> String {
    crate::progenv::encode(settings).iter().map(|b| format!("{b:02x}")).collect()
}

pub fn init_args(args: &[String]) {
    let Some(encoded) = args.iter().take_while(|a| a.as_str() != "--").find_map(|a| a.strip_prefix(ARG_PREFIX)) else { return };
    let settings = crate::zone_alloc::kept_with(|| decode(encoded));
    let _ = SETTINGS.set(settings);
}

pub fn is_prepared() -> bool { SETTINGS.get().is_some() }

/// A captured native value (including an explicit absence), or no captured value for a
/// program whose native build is inherited through the host's self-exec metadata.
pub fn native_receipt() -> Option<Option<&'static str>> {
    SETTINGS.get()?.iter().find(|(n, _)| n == NATIVE_RECEIPT.as_bytes()).map(|(_, v)| {
        v.as_deref().map(|v| std::str::from_utf8(v).expect("prepared native receipt path"))
    })
}

pub fn with_native(encoded: &str, receipt: &str) -> String {
    let mut settings = decode(encoded);
    let value = (!receipt.is_empty()).then(|| receipt.as_bytes().to_vec());
    if let Some((_, native)) = settings.iter_mut().find(|(n, _)| n == NATIVE_RECEIPT.as_bytes()) {
        *native = value;
    } else {
        settings.push((NATIVE_RECEIPT.as_bytes().to_vec(), value));
    }
    encode(&settings)
}

pub fn get(name: &str) -> Option<OsString> {
    if let Some((_, value)) = SETTINGS.get().and_then(|s| s.iter().find(|(n, _)| if cfg!(windows) { n.eq_ignore_ascii_case(name.as_bytes()) } else { n == name.as_bytes() })) {
        value.as_deref().map(os)
    } else {
        std::env::var_os(name)
    }
}

pub fn capture() -> String {
    let settings: crate::progenv::Own = NAMES.iter().map(|n| {
        let value = if *n == "CARGO" { crate::dirs::cargo_exe().map(OsString::from) } else { get(n) };
        (n.as_bytes().to_vec(), value.map(OsString::into_encoded_bytes))
    }).collect();
    encode(&settings)
}

pub fn command(program: impl AsRef<OsStr>) -> std::process::Command {
    let mut command = std::process::Command::new(program);
    for name in NAMES {
        match get(name) {
            Some(value) => { command.env(name, value); }
            None => { command.env_remove(name); }
        }
    }
    command
}
