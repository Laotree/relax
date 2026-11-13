fn main() {
    let mut args = std::env::args_os().skip(1);
    let mode = args.next();
    if mode.as_deref() == Some(std::ffi::OsStr::new("--argv0")) {
        println!("{}", std::env::args().next().unwrap());
        return;
    }
    if mode.as_deref() == Some(std::ffi::OsStr::new("--launch")) {
        let status = std::process::Command::new(args.next().unwrap()).args(args).status().unwrap();
        std::process::exit(status.code().unwrap_or(1));
    }
    println!("artifact ran");
}
