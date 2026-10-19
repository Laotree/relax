use sc_fw::*;

fn own_a(x: u32) -> u32 { x * 9 + 2 }

fn main() {
    let s = Shape::new(3, 5);
    let r = [add(2, 3), scaled(4u32) as u32, area(&s), describe(&s) as u32, cfg_macro(), gated(), uses_unrelated(), sum_to(10), pow_std(3), from_macro(), own_a(6), fast_only()];
    let t: Vec<String> = r.iter().map(|x| x.to_string()).collect();
    println!("shared_apps result {}", t.join(" "));
}
