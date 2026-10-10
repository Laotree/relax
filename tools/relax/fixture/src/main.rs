//! The fixture's program: `cargo run -p relax-provided-fixture` (all rustc) and
//! `relax run relax-provided-fixture` (this file by Relax, the lib bound to the loader) print
//! the same lines except `bound`.
use relax_provided_fixture::*;

fn main() {
    println!("bound {}", bound());
    println!("add {}", add(-3, 1 << 40));
    println!("mix {}", mix(1.5, 2.25, 3, true, 'a'));
    println!("scale {:?}", scale(P { x: 1.0, y: -2.0 }, 3.0));
    let b = big_make(10);
    println!("big {:?} {}", b.a, big_sum(b));
    println!("text_len {}", text_len("héllo"));
    println!("sum {}", sum(&[1, 2, 3, 4_000_000_000]));
    println!("flip {:?} {:?}", flip(Kind::A), flip(Kind::B));
    {
        let mut r = Registry::new();
        println!("empty {}", r.is_empty());
        println!("ids {} {} {}", r.add("one"), r.add("two"), r.add("one"));
        println!("add_all {}", r.add_all(["three", "four", "two"]));
        println!("len {} name_len {}", r.len(), r.name_len(2));
        let moved = r;
        let boxed = Box::new(moved);
        println!("boxed len {}", boxed.len());
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| boxed.boom(7)));
        println!("caught {}", caught.is_err());
        println!("still {}", boxed.boom(0));
    }
    let v = vec![Registry::default(), Registry::new()];
    drop(v);
    println!("drops {}", drops());
    println!("maybe {:?} {:?}", maybe(0), maybe(5));
    for io in ios() { println!("io {:?} {:?}", io.buffer_index(), io); }
    {
        use std::hash::{Hash, Hasher};
        let (a, b) = (site("a.rs", 3), site("b.rs", 4));
        let mut set = std::collections::HashSet::new();
        set.insert(a.clone());
        set.insert(b.clone());
        set.insert(a.clone());
        println!("sites {} {} {}", set.len(), set.contains(&b), set.contains(&site("c.rs", 1)));
        // the value is std's hasher's (Relax's std hashes differently from rustc's): equal
        // values hash alike, unequal ones differ
        let hash = |x: &dyn Fn(&mut std::collections::hash_map::DefaultHasher)| {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            x(&mut h);
            h.finish()
        };
        let ha = hash(&|h| a.hash(h));
        println!("site hash {} {}", ha == hash(&|h| a.clone().hash(h)), ha == hash(&|h| b.hash(h)));

        println!("site {:?} {} {:#?}", a, b, b);
    }
}
