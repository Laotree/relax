mod logs {
    #[macro_export]
    macro_rules! logit { ($($t:tt)*) => { println!("out logged {}", format!($($t)*)) } }
}
#[test]
fn run() { println!("out logged x 1"); }
