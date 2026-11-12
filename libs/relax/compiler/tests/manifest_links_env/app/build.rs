// cargo sets CARGO_MANIFEST_LINKS for a package that declares `links`.
fn main() {
    let links = std::env::var("CARGO_MANIFEST_LINKS").expect("CARGO_MANIFEST_LINKS is set");
    println!("cargo:rustc-env=MLE_LINKS={}", links);
}
