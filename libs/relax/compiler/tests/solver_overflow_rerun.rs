// A goal deeper than the recursion limit but within twice it. The old solver reads a cached
// answer whatever depth it took, the next solver checks that depth, so rustc evaluates a root
// goal that overflows again at twice the limit (rustc 1.100 rustc_next_trait_solver
// eval_ctxt/mod.rs, `maybe_evaluate_root_goal_with_higher_recursion_limit`). Stable rustc
// accepts `Outer: Send` below by reusing `Inner: Send`; Relax's next solver reported E0275
// (egui_wgpu's `HashMap<TextureId, Texture>` inside a struct, at the default limit).
#![recursion_limit = "32"]

struct W<T>(T);
// 25 levels
type Inner = W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<u8>>>>>>>>>>>>>>>>>>>>>>>>>;
// 20 more
type Outer = W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<W<Inner>>>>>>>>>>>>>>>>>>>>;

// no value of either type: dropping one needs drop-check rules this deep too (E0320)
fn send<T: Send>() -> bool { true }

#[test]
fn inner_is_send() {
    assert!(send::<Inner>());
}

#[test]
fn outer_is_send() {
    assert!(send::<Outer>());
    assert!(send::<(Outer, Inner)>());
}
