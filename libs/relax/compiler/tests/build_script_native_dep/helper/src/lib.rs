include!(concat!(env!("OUT_DIR"), "/generated.rs"));

pub fn generated() -> i32 {
    GENERATED
}
