# Relax

### Rust without the wait.

**rustc builds your program, then you run it. Relax runs your program while it builds it.**

Relax is a live compiler and JIT runtime for Rust, written in Rust. It runs a Cargo package straight
from source, with no rustc, LLVM or linker in the loop: it compiles each function when it is first
called, optimises the hot ones while the program runs, and patches your edits into the running process.

## Relax vs cargo and rustc

| | cargo + rustc | **Relax** |
| --- | --- | --- |
| **Large 3D game, clean checkout → first frame** | ~3 min build, then start | **11 s** on an M4 MacBook, straight from source |
| **Same game, second run → first frame** | start the built binary | **1.15 s** on an M4 MacBook, nothing recompiled |
| **Small app → first frame** | build it first | **3.7 s** cold, **0.41 s** warm (M4 MacBook) |
| **Change one function in a running program** | rebuild, relink, restart: state lost | **patched in**: state kept |
| **Save a file → 92 tests re-run** | rebuild the test binary first | **2.2 s** after the save |
| **Type and borrow check** | `cargo check`; a build checks everything first | `relax check`; a run type-checks each function before it runs and borrow-checks in the background |
| **Speed of optimised code** | 1.00× (`--release` for the native CPU) | **1.14–1.26×** the time; 2.3× on dense numeric loops |
| **Needs** | rustc, LLVM, a linker | **one Rust library**: 438k lines, 0 crates.io dependencies |

Code generation for x86-64 and AArch64; from a fresh clone the repository
builds and its tests pass on Linux x86-64 and macOS arm64. Windows isn't tested.

## The tradeoffs

- **Slower optimised code.** 1.14–1.26× the time of `--release` built for the native CPU on the
  workloads we profile most, 2.3× on dense numeric loops, which Relax doesn't vectorise yet. A broader
  run of 18 workloads came out slower and is being re-measured: see
  [where LLVM still wins](#where-llvm-still-wins).
- **More memory.** The compiler, its caches and every code version it publishes share your program's
  process, and JIT code is append-only. `relax inspect <pid> memory` shows the split, `code` the growth.
  The code cache in a package's `target/makepad-run` takes 120 to 190 MB for `hello`.
- **`relax check` isn't faster than `cargo check` yet.** On a large package a cold check takes longer
  and uses more memory than `cargo check`, and an edit can re-check more than it needs to. We're
  working on it.
- **Not every crate runs yet.** [libs/relax/KNOWN_GAPS.md](libs/relax/KNOWN_GAPS.md) lists the open
  gaps, each with a repro.
- **Not every edit patches live.** Function bodies do. A changed struct layout, import, trait or impl
  header, or macro waits for a restart, which Relax offers: `relax inspect <pid> session relaunch`.
- **The borrow checker runs beside the program.** A run type-checks each function before it runs and
  borrow-checks in the background; `relax run --check-first` waits for the borrow checker instead.
- **Not a release build.** Relax is for the edit-run loop. Ship what `cargo build --release` builds.

## What you get from a JIT

`relax run` prints a `relax-remote: pid <pid>` line. Every command below except `run` and `test` is
`relax inspect <pid> <command>`, a question the running program answers while it runs.

| | What it does | Command |
| --- | --- | --- |
| **Hot patching, state kept** | Save a file: the changed functions are rechecked, recompiled and swapped into the running program. A call into code that doesn't compile waits until an edit fixes it. | `relax run <package>` |
| **Tests on save** | Keeps the tests warm and re-runs the ones that entered the functions you changed. | `relax test --live <package>` |
| **Pause on panic** | A panic parks its thread with the stack intact: up to 10 minutes at a terminal, 2 s when nothing is attached. Read its locals, evaluate Rust in its frame, then let it unwind, or rerun a `restartable` function from its entry. | `panics`, `locals panic=P1`, `eval <expr>`, `resume P1 panic` |
| **Breakpoints, no debugger** | A hit parks the thread at the call with its stack intact. | `break <file>:<line>`, `locals break=K1`, `continue` |
| **Hangs explained** | Deadlock, blocked, busy or idle: the verdict, the wait chain and the stacks of the threads in it. | `why-hung` |
| **Profiling** | Samples JIT and native frames: CPU per thread, the top functions with their hottest line, a call tree with each frame's tier, folded stacks for flame graphs. | `prof s=3`, `prof view=tree`, `why-slow` |
| **Flight recorder** | Always on, in bounded memory: the last minutes of threads, waits, compiles and events, saved by itself on a panic, a fault or a hitch over 1 s. | `rec save` |
| **Memory and leaks** | Where the memory is (RSS by kind, malloc in use and held free, Relax's own share), and the program's heap by allocation stack, with leak candidates between snapshots. Heap tracking runs on Linux x86-64 and macOS arm64 only. | `memory`, `heap start`, `heap snap a`, `heap diff a now` |

`relax inspect <pid> help` lists the rest, among them `asm <fn> vs=rustc` (the JIT's machine code
beside rustc's), `count <fn>` (exact call counts) and `counters` (hardware counters).

## Try it

From a fresh clone, build `relax` and run a new package through the JIT:

```sh
git clone https://github.com/makepad/relax
cargo build --release --manifest-path relax/Cargo.toml -p relax-runner --bin relax

cargo new hello
cd hello
../relax/target/release/relax run --quiet hello    # run main under the JIT
../relax/target/release/relax test hello           # run its #[test] fns
../relax/target/release/relax check hello          # type- and borrow-check only
```

Run `relax` in the package's folder and give it the package's name, not a path. It reads Relax's std
from the checkout it was built in, so keep the `relax` folder where it is.

Measured from a fresh clone: building `relax` took 53 s on a 16-core x86-64 Linux box and 78 s on a
10-core arm64 Mac with cargo held to 4 jobs. The first `relax run` of `hello` took 0.24 s and 0.97 s,
the next ones 0.01 to 0.07 s. Relax keeps what it compiles in the package's `target/makepad-run`
(`relax clean` removes it), so each new package starts cold.

**Network.** A package with no dependencies, like `hello`, needs none. For a crates.io dependency Relax
takes the package from `~/.cargo`'s registry when it is there, and otherwise downloads it from
crates.io itself, checked against the index's SHA-256. With `MAKEPAD_RUN_OFFLINE=1` or cargo's
`CARGO_NET_OFFLINE` it never downloads. `relax fetch <git-url>` (`tools/run/runner/src/fetch.rs`)
stores a git repository as one file under `~/.makepad-run`.

---

## What it took: a new Rust toolchain

Relax isn't a wrapper around rustc or a plugin for LLVM. It replaces both, and the parts of Cargo and
the linker in between, with one Rust library.

| The job | In the usual toolchain | **In Relax** |
| --- | --- | --- |
| Lex, parse and expand macros, `macro_rules!` and procedural | rustc | **relax-lex, relax-front** |
| Resolve names, solve traits, infer types, check borrows, evaluate constants | rustc | **relax-types** |
| Optimise: inlining, folding, loops, ranges | rustc's MIR passes + LLVM | **relax-codegen** (O1 and O3) |
| Allocate registers, emit x86-64 and AArch64 machine code | LLVM | **relax-backend** |
| Link and load | the system linker and loader | **relax-compiler**, straight into executable memory |
| Read manifests and resolve the crate graph | Cargo | **relax-base** |
| Build `core`, `alloc` and `std` | shipped prebuilt | **compiled from source by Relax** (134k lines) |

| | cargo + rustc | **Relax** |
| --- | --- | --- |
| **Compiling** | Whole crates, ahead of time. | **One function at a time, when it is first called.** Hot functions move up in the background: interpreter → O1 → O3. `#[relax(O2)]` / `#[relax(O3)]` ask for a level ahead of time; under rustc the attribute does nothing. |
| **Caching** | Incremental artefacts that can go stale. | **Every result keyed by the hashes of its inputs**: a hit is what a fresh compile would produce, so there's no `cargo clean`. |
| **Procedural macros** | Built as native dylibs, then loaded. | **Run natively when they match a linked build, otherwise on the JIT.** |
| **Native code** | Everything is native. | **Crates that must stay native (OS layers, GPU, audio) export an interface with `#[relax_api]`**, which JIT code calls through the C ABI. |

## Built for AI agents

An AI agent can't feel a slow build, but it pays for every one in tokens, wall-clock and lost context.
[Makepad](https://github.com/makepad/makepad) builds its apps with many AI agents working in parallel,
and its dev hub, **devhub**, keeps each agent's app or test run alive under Relax on a warm machine.

| An agent's iteration | With cargo + rustc | **With Relax + devhub** |
| --- | --- | --- |
| **Edit reaches the program** | rebuild and relink: minutes on a large app | **synced and patched in milliseconds** (~50–200 ms to the box) |
| **Test verdict** | rebuild the test binary, then run | **92 tests back 2.2 s after the save** |
| **See the UI** | rebuild, relaunch, navigate back | **a frame of the live app, grabbed as a PNG** |
| **New worker** | cold build | **starts warm**: every machine keeps a warm cache at the tip |

In practice nine agent lanes run side by side, devhub handles more than 300 build and test jobs an
hour, and dozens of changes land every day, each checked under Relax before it merges.

## Where LLVM still wins

In steady state LLVM's code is still faster. Our measurements: warm JIT against a native build of the
same source and inputs, as wall-clock ratios (lower is better, 1.00× = LLVM).

| Workload | CPU | vs `--release`, native CPU | Measured |
| --- | --- | --- | --- |
| 3D-print slicer, first slice of a part, 4 threads | x86-64 (Zen 4) | **1.14×** (cycles 1.15×, instructions 1.26×) | 2026-11-11 |
| Same, 8 threads | x86-64 (Zen 4) | **1.17×** | 2026-11-11 |
| Same, 4 threads | AArch64 (Apple M4) | **1.24×** (before this week's x86 gains were ported) | 2026-11-09 |
| CAD B-rep modelling round | x86-64 (Zen 4) | **1.26×** | 2026-11-10 |
| Script VM interpreter loop | x86-64 (Zen 4) | **1.19×** | 2026-11-11 |
| Dense numeric kernel (Cholesky factorisation) | x86-64 (Zen 4) | **2.29×**: LLVM vectorises it with AVX-512, Relax doesn't vectorise loops yet | 2026-11-10 |
| Any workload against plain `--release` (portable CPU baseline) | | **not measured yet** | |

These are the workloads we profile most. A broader run of 18 workloads this week came out slower than
these, and slower than in October; we're finding out why and will update this section.

**Which `--release`?** These numbers are against `--release` with `-C target-cpu=native`, where LLVM may
use every instruction the machine has. Most Rust ships with plain `--release` for a portable baseline
CPU; Relax always compiles for the CPU it runs on, so against that the gaps shrink, and on vector-heavy
code they can flip. That comparison hasn't been measured yet.

**Where the gap comes from**, from instruction-level comparisons of the same functions: extra
instructions rather than stalls (1.26× the instructions cost 1.15× the cycles).

| Cause | Extra instructions (slicer run) |
| --- | --- |
| Compares kept as bool registers and recomputed | ~25 G |
| Register copies (two-address form, coalescing misses) | ~23 G |
| Stack traffic: loop state kept in stack slots; 12 allocatable registers against rustc's 15 | ~22 G |
| Extra loop-control and check branches, invariant tests left inside loops | ~13 G |
| Loads not folded into compares, i128 arithmetic, rematerialised constants, smaller items | ~33 G |
| Runtime outside the generated code (memcpy, allocator wrappers, TLS access, stubs) | ~40 G |
| No loop vectorisation, shallow unrolling | most of the numeric-kernel gap |

Inlining isn't a cause: Relax inlines more than rustc does. Every row is a work item, and the slicer
gap went from 1.26× to 1.14× in the last three days.

## Architecture

Relax owns the whole pipeline, from source bytes to executable memory, in one process. It is a stack
of layers, each its own crate, building only on the ones below; the layers compile in parallel, and a
change in an upper layer never rebuilds the ones below.

| Crate | Path | Role | In the rustc world |
| --- | --- | --- | --- |
| `relax-lex` | `libs/relax/lex` | The lexer and token model for Rust (every edition), and the one procedural macros see. | the lexer and `proc_macro` |
| `relax-base` | `libs/relax/base` | Hashing, memory accounting and arenas, the syntax tree, `cfg`, manifests, the git read path and source mounts. | parts of Cargo and rustc's shared infrastructure |
| `relax-session` | `libs/relax/session` | The inputs of a compilation and their stable hashes: the keys every cache is built on. | the session and incremental keys |
| `relax-front` | `libs/relax/front` | Parsing, the crate graph, name resolution and macro expansion. | parser, resolver, macro expansion |
| `relax-types` | `libs/relax/types` | Types, impls, type checking, layouts, constant evaluation and the borrow checker. | type checker, borrow checker, const eval |
| `relax-codegen` | `libs/relax/codegen` | The middle end on RIR (Relax IR): the O1 and O3 optimisers and the threaded interpreter. | MIR optimisations and LLVM's optimiser |
| `relax-backend` | `libs/relax/backend` | Register allocation, x86-64 and AArch64 machine code, the C ABI planner and executable memory. | LLVM's code generator and the linker |
| `relax-compiler` | `libs/relax/compiler` | The JIT runtime and std: lazy compilation, tiering, live edits, caches, the proc-macro host, the test runner and `relax inspect`. | Cargo, the rustc driver, the test harness and the OS loader |
| `relax-native-macros` | `libs/relax/native_macros` | Natively linked procedural macros, checked against their source. | proc-macro dylibs |
| attribute | `libs/relax/attr` | `#[relax(O2)]` / `#[relax(O3)]`: the optimisation-level attribute; a no-op under rustc. | `opt-level` per profile |
| `relax_api` | `libs/relax_api` | `#[relax_api]`: the interface a native crate offers to JIT code, and per-thread heap routing. | (no equivalent: everything is native) |

**A function's life.** Before `main`, the program's own crates are type-checked. The first call of a
function compiles it (interpreter or O1); while it is hot, it is recompiled at O3 in the background and
swapped in. When you save a change to it, Relax rechecks what changed, recompiles it and publishes the
new code; the old code stays valid, and the next call runs the new function.

**Design rules.** *Never stale:* every cached result is keyed by the hashes of its inputs. *Code only
grows:* published machine code is never freed or rewritten while it can still be on a stack, so a swap
is safe where a native hot-reload hack isn't. *Lazy by default:* Relax compiles what you call, not
everything you might. *Inspectable:* every phase reports what it's doing, so a stall can be explained
from its record.

## Repository layout

```
Cargo.toml                              the workspace
libs/relax/
  lex/ base/ session/ front/ types/     front end and type system
  codegen/ backend/                     middle end and machine code
  compiler/                             runtime, std (compiler/std), 96 end-to-end test packages
  attr/ native_macros/                  #[relax(..)] and native proc macros
  KNOWN_GAPS.md                         what isn't supported yet
libs/relax_api/                         #[relax_api] and per-thread heap routing
tools/run/runner/                       relax, the command-line runner
libs/ platform/ tools/ widgets/         the small support crates Relax links: token model,
                                        serialisation, remote inspection, profiling, and the
                                        native proc macros it checks against their source
```

The compiler is the `relax_compiler` library (`cargo build --release -p relax-compiler`); `relax`
(`tools/run/runner`) is its command-line runner. Building it needs a stable Rust toolchain and nothing
from crates.io.

## License

MIT, see [LICENSE](LICENSE). The std sources Relax compiles carry their own notices; see
`libs/relax/compiler/std/CREDITS.md` and the license files beside them.
