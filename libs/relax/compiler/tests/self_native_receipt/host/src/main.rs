use std::sync::atomic::{AtomicBool, Ordering};

static NEXT: AtomicBool = AtomicBool::new(false);

fn hosted(args: &[String]) -> i32 {
    std::env::set_current_dir(&args[0]).unwrap();
    let exe = std::env::args_os().next().unwrap().into_encoded_bytes();
    let mut words = vec![exe];
    words.extend(["run", "--allow-c", "self-native-receipt", "--", "--live-native", "--once"].map(|a| a.as_bytes().to_vec()));
    relax_compiler::os::proc::set_args(words);
    relax_compiler::run::set_main_host(relax_compiler::run::MainHost {
        domain_zero: true,
        run: |mut run| {
            assert_eq!(run(), 0);
            let source = std::path::Path::new("cnative/build.rs");
            let before = std::fs::read_to_string(source).unwrap();
            std::fs::write(source, before.replace("const SALT: i32 = 0;", "const SALT: i32 = 2;")).unwrap();
            relax_compiler::run_end::restart("changed native input".into(), None).unwrap();
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(60);
            while !NEXT.load(Ordering::Acquire) {
                assert!(std::time::Instant::now() < deadline, "hosted restart did not finish");
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
            assert_eq!(run(), 0);
            0
        },
        open: |_, _| Ok(()),
        start: |_| Err("unexpected app domain".into()),
        batch: || {},
        status: |_| {},
        end_app: || {},
        next_run: || { NEXT.store(true, Ordering::Release); true },
    });
    let words = ["self-native-receipt", "--", "--live-native", "--once"].map(String::from).to_vec();
    relax_compiler::run::cmd_run_app("self-native-receipt", words,
        Box::new(|| Ok(relax_compiler::session_from_env(&["--allow-c".into()])))).unwrap()
}

fn main() {
    static HOST: relax_runner::Host = relax_runner::Host {
        commands: &[relax_runner::HostCommand {
            name: "receipt-hosted", row: ("receipt-hosted DIR", "Check hosted native relaunch"),
            title: "Hosted native relaunch", page: &[], main: hosted,
        }],
        ..relax_runner::BARE
    };
    relax_runner::main(&HOST);
}
