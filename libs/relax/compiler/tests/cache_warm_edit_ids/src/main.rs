// See run.sh: cold, warm, then edits of wf-edit and wf-host interleaved, each a fresh run on one
// disk cache. Every run must print the same result.
fn main() {
    let mut h = wf_host::Host::new();
    for cb in wf_edit::callbacks() {
        h.add(cb);
    }
    let e = wf_edit::eval(5);
    let p = wf_host::apply(|x| wf_edit::eval(x) + 1, 3);
    let r = h.run(10) + e + p + wf_host::host_open(3) + wf_host::bump(4) + wf_edit::Item(2).later();
    println!("cache_warm_edit_ids result {}", r);
}
