# Rust kernel analyzer

This wrapper runs rustc through `rustc_driver`, inspects HIR and typed MIR, and writes panic sites, explicit unsafe blocks, and calls to JSON. It only enables analysis when the Rust input is under a kernel `rust/` or `drivers/` directory.

Install compiler development libraries matching the compiler used to build the wrapper:

```sh
rustup component add rustc-dev llvm-tools
```

Build the wrapper:

```sh
RUSTC_BOOTSTRAP=1 RUSTFLAGS="-Cprefer-dynamic" \
    cargo build --manifest-path rust_kernel_analyzer/Cargo.toml --release
```

Use it as the kernel Rust compiler:

```sh
SYSROOT="$(rustc --print sysroot)"
HOST="$(rustc -vV | sed -n 's/^host: //p')"
export LD_LIBRARY_PATH="$SYSROOT/lib:$SYSROOT/lib/rustlib/$HOST/lib"
export RUST_KERNEL_ANALYSIS_OUTPUT="$PWD/rust-kernel-analysis"
export RUSTC="$PWD/rust_kernel_analyzer/target/release/rust-kernel-analyzer"
```

The wrapper performs normal compilation for non-kernel crates without running the analysis. Each analyzed kernel crate produces `<crate>.json`.

Each analyzer also writes `<module>.cfg.jsonl` with one function CFG per line. Rust MIR and LLVM use the same block and edge schema, so Python can stream records directly:

```python
import json


def read_cfgs(path):
    with open(path) as file:
        for line in file:
            if line.strip():
                yield json.loads(line)
```

The repository also provides `cfg_reader.py` with streaming, indexing, and direct lookup helpers for these files.

Function IDs are globally qualified, while blocks use function-local `bb0`, `bb1`, and similar IDs. Integer switch values are strings so values wider than JavaScript's integer range remain exact.

Rust CFG records also contain `locals`, structured block statements, `definitions`, `uses`, and projected `memory_accesses`. Assignments normalize MIR places, operands, integer widths, arithmetic, comparisons, casts, references, aggregates, calls, assertions, and switch conditions. MIR constructs that are not normalized are retained as explicit `unsupported` records instead of being silently discarded.

Build the intraprocedural def-use graph after generating the CFG:

```sh
python3 rust_kernel_analyzer/analysis/reaching_definitions.py \
    rust-kernel-analysis/rust_binder.cfg.jsonl \
    rust-kernel-analysis/rust_binder.dataflow.jsonl
```

The analysis creates argument definitions, propagates definitions through CFG joins and loops, applies strong updates to direct places and weak updates to dereferenced or indexed places, and records unresolved uses explicitly.

The wrapper must be built with a complete `rustc-dev` component from the same compiler revision used for the kernel. The bundled Android 1.97 toolchain currently has typed compiler metadata but not the compiler `.rlib` files required to link an external driver.

The `functions` array reports whether each function may panic and includes one call path to the panic target. This is computed to a fixed point over direct calls in the analyzed crate. Known external Rust panic helpers such as `assert_failed` and `unwrap_failed` are treated as roots because dependency MIR is not analyzed with the kernel crate.

## C analysis

Build the LLVM pass with the LLVM version used by Clang:

```sh
cmake -S c_kernel_analyzer -B build/c-kernel-analyzer -G Ninja
cmake --build build/c-kernel-analyzer
```

Run it while compiling a C file:

```sh
export C_KERNEL_ANALYSIS_OUTPUT="$PWD/c-kernel-analysis"
clang -g -fpass-plugin="$PWD/build/c-kernel-analyzer/CKernelAnalyzer.so" \
    -c source.c
```

Clang driver support for custom pass pipelines varies by version. The equivalent explicit LLVM invocation is:

```sh
clang -g -emit-llvm -c source.c -o source.bc
opt -load-pass-plugin build/c-kernel-analyzer/CKernelAnalyzer.so \
    -passes=kernel-failure-analysis source.bc -o /dev/null
```

Merge Rust and C results and propagate failure reachability across their direct calls:

```sh
python3 merge_kernel_analysis.py --rust rust-kernel-analysis/rust_binder.json \
    --c c-kernel-analysis/source_c.json -o kernel-analysis.json
```

Warnings remain classified separately from unconditional failures. They are fatal only under a policy such as `panic_on_warn=1`.
