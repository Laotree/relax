// M10: a fieldless enum read as a number (`as`) by running code.
//  v1: a variant added after the running ones: an enum is laid out as rustc lays it, so an added
//      variant restarts the app.
//  v2: a variant inserted before a running one moves its number, which running code may have
//      kept: the restart rung, naming both.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Level {
    Low,
    High,
}

fn index(l: Level) -> usize {
    l as usize
}

#[test]
fn run() {
    println!("out index {} {:?}", index(Level::High), Level::Low);
}
