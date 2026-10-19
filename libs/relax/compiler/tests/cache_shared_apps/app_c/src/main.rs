use sc_fw::*;

fn own_c(x: u32) -> u32 { x * 11 + 3 }

fn main() {
    let s = Shape::new(4, 6);
    let r = [area(&s), add(7, 8), describe(&s) as u32, scaled(5u32) as u32, unrelated(), uses_unrelated(), sum_to(20), from_macro(), pow_std(2), cfg_macro(), gated(), own_c(2)];
    let t: Vec<String> = r.iter().map(|x| x.to_string()).collect();
    println!("shared_apps result {}", t.join(" "));
}
