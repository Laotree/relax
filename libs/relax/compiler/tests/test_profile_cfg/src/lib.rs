#[test]
fn profile_cfg() {
    assert_eq!(cfg!(debug_assertions), cfg!(feature = "debug"));
    assert_eq!(profile_dep::debug_enabled(), cfg!(feature = "dep-debug"));
    assert_eq!(profile_macros::host_debug!(), (cfg!(feature = "macro-debug"), cfg!(feature = "host-dep-debug")));
    assert_eq!(env!("BUILD_DEBUG"), if cfg!(feature = "build-debug") { "true" } else { "false" });
    let mut checks = 0;
    debug_assert!({ checks += 1; true });
    assert_eq!(checks, if cfg!(feature = "debug") { 1 } else { 0 });
    #[cfg(feature = "native")]
    assert_eq!(profile_native::value(), 7);
}

#[cfg(debug_assertions)]
#[test]
fn debug_only() {
    assert!(cfg!(feature = "debug"));
}

#[cfg(not(debug_assertions))]
#[test]
fn release_only() {
    assert!(!cfg!(feature = "debug"));
}
