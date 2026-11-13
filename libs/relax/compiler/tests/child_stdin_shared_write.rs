use std::io::Write;
use std::process::{ChildStdin, Command, Stdio};

#[test]
fn shared_child_stdin_implements_write() {
    fn assert_write<T: Write>() {}
    assert_write::<&ChildStdin>();
}

#[cfg(unix)]
#[test]
fn write_fmt_through_a_shared_child_stdin() {
    let mut child = Command::new("cat").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let input = child.stdin.take().unwrap();
    writeln!(&input, "hello {}", 42).unwrap();
    drop(input);
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, b"hello 42\n");
}

#[cfg(unix)]
#[test]
fn shared_and_owned_writes_use_the_same_pipe() {
    let mut child = Command::new("cat").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
    let mut input = child.stdin.take().unwrap();
    input.write_all(b"owned ").unwrap();
    let mut shared = &input;
    shared.write_all(b"shared").unwrap();
    shared.flush().unwrap();
    drop(input);
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert_eq!(output.stdout, b"owned shared");
}

#[cfg(unix)]
#[test]
fn shared_write_preserves_broken_pipe_errors() {
    let mut child = Command::new("sh").args(["-c", "exit 0"]).stdin(Stdio::piped()).spawn().unwrap();
    let input = child.stdin.take().unwrap();
    assert!(child.wait().unwrap().success());
    assert_eq!((&input).write(b"closed").unwrap_err().kind(), std::io::ErrorKind::BrokenPipe);
}
