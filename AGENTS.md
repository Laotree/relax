# Agents working in this repository

Relax is slaved to the `work` branch of [makepad/makepad](https://github.com/makepad/makepad).

- **Source of truth.** Every carried path below comes from the same path in makepad/makepad's `work`
  branch. This repository is a projection of that branch, not a place to develop.
- **Changes.** Make every code change in makepad/makepad on `work`, following that repository's
  `AGENTS.md`. Land it there, then carry the same diff here, limited to the carried paths. A change
  made only here is overwritten by the next carry.
- **Issues.** An issue filed here is fixed in makepad `work` first. The commit that carries the fix
  here says `Fixes #N` and closes the issue.
- **Pull requests.** A pull request here is ported into makepad `work` and carried back. It is not
  merged here directly.
- **Files that live only here.** `README.md`, `LICENSE`, `Cargo.toml`, `AGENTS.md`, `.gitignore`,
  `.nojekyll` and the website (`index.html`, `zh/`, `retro/`, `favicon.*`, `apple-touch-icon.png`)
  are kept in this repository.

## Carried paths

```
libs/apple_sys
libs/core_util
libs/error_log
libs/gpu_trace
libs/live_id
libs/micro_proc_macro
libs/micro_serde
libs/objc-sys
libs/prof_stream
libs/relax                      (except libs/relax/compiler/bench_rt and libs/relax/compiler/rwbench)
libs/relax_api
libs/remote
libs/strict_json
libs/toml_parser                (except libs/toml_parser/tests/manifests.rs)
libs/windows/sys
platform/build.rs
platform/build_gen.rs
platform/cpu_budget
platform/network
platform/script/derive
platform/script/derive_impl
platform/src/restart.rs
platform/src/thread.rs
tools/run/light_http
tools/run/runner
widgets/derive_widget
widgets/derive_widget_impl
```

When a carried crate starts to depend on a path that is not in this list, add the path here and
carry it in the same commit.

## Building and testing

See `README.md` ("Try it") and `libs/relax/CONTRIBUTING.md`. From a fresh clone the repository builds
and its tests pass on Linux x86-64 and macOS arm64.
