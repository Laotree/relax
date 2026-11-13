use std::os::unix::process::CommandExt;
#[inline(never)]
fn value() -> usize { 1 }
fn main() {
    if std::env::var_os("REENTERED").is_none() {
        let error = std::process::Command::new(std::env::current_exe().unwrap())
            .args(std::env::args_os().skip(1)).env("REENTERED", "1").exec();
        panic!("exec failed: {error}");
    }
    let once = std::env::args().any(|arg| arg == "--once");
    let mut previous = 0;
    loop {
        let current = std::hint::black_box(value());
        if current != previous { println!("{current}"); previous = current; }
        if once { return; }
        std::thread::sleep(std::time::Duration::from_millis(25));
    }
}
