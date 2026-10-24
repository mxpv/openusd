# Rust and C++ stage benchmarks

`open_bench.cpp` runs the native OpenUSD equivalent of the Rust
`open_bench` example. `compare.py` runs the executables sequentially in
fresh processes, checks prim and array counts, and retains timings, peak
RSS, and raw output in JSON. Run these tools on Linux.

## Build

Build and preserve the Rust baseline before applying optimizations:

```sh
cargo build --release --locked -p openusd --example open_bench --features mmap
cp target/release/examples/open_bench /tmp/openusd-bench-before
```

Repeat the Cargo build after applying changes. The primary comparison uses
ordinary file reads; compiling the `mmap` feature does not enable mapping.

The native benchmark can use the Linux `usd-core` wheel with headers from
an OpenUSD checkout of the same version. The build helper checks the
version and generates configuration headers under the output directory.
Python supplies the build environment; the benchmark executes C++ queries
directly. TBB headers are needed to include OpenUSD's public headers.

```sh
UV_CACHE_DIR=/tmp/openusd-uv-cache uv venv /tmp/openusd-reference
UV_CACHE_DIR=/tmp/openusd-uv-cache uv pip install \
  --python /tmp/openusd-reference/bin/python \
  usd-core==26.8 tbb-devel==2023.2.0
/tmp/openusd-reference/bin/python benchmarks/build_reference.py \
  --source /path/to/OpenUSD \
  --output /tmp/openusd-reference/open_bench
```

## Compare

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-bench-before \
  --rust target/release/examples/open_bench \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 3 --warmups 1 --check-status \
  --output /tmp/openusd-perf/island.json
```

Payloads are loaded. Traversal visits active, loaded, defined, non-abstract
prims, including every instance proxy. Metadata traversal collects prim
paths, then queries their type names. The array phase enumerates authored
attributes and reads each default-time value, counting arrays and elements.
Arrays are dropped after each read. Every instance placement is queried.

Authored enumeration keeps the property set comparable with Rust's
core-only schema registry. C++'s `GetAttributes` also enumerates geometry
schema fallbacks, including empty arrays. Fallback-only properties are
outside this comparison. An authored property can still use a schema
fallback; counts must match before interpreting timings on another scene.

The saved baseline may predate `--authored` and element counting. The
runner uses its original enumeration and checks every count it reports.
This is suitable for the Moana baseline whose array counts match authored
enumeration; a count mismatch stops the runner.

Opening is lazy in Rust and eager in C++. Compare the sum of opening,
metadata traversal, and attribute reads. Process time additionally includes
startup and stage destruction. Peak RSS is process-wide. C++ uses its
default worker count; Rust uses its existing execution model. Run without
concurrent builds or profiling during measured repetitions.

`--check-status` performs separate metadata runs and compares sorted path
and status records across all binaries. These contain active, loaded,
defined, abstract, instance, and instance-proxy bits. Both executables also
support `--retraverse` for cached-query timings and `--time` for sample
reads; invoke them directly for these workloads.

## Profile

Use a smaller Moana element for instruction profiles:

```sh
valgrind --tool=callgrind --callgrind-out-file=/tmp/openusd.callgrind \
  target/release/examples/open_bench --proxies --authored --no-heap \
  /path/to/island/usd/elements/isBayCedarA1/isBayCedarA1_bonsaiA_model.usd
callgrind_annotate --inclusive=no /tmp/openusd.callgrind
```

Allocator tracking is disabled in timing and instruction-profile runs.
Use the Rust executable without `--no-heap` for a separate heap analysis.

## Moana results

Measured on 2026-10-19 with `usd/island.usda`, including instance proxies
and authored default-time reads. Each implementation ran once to warm up,
then three times in fresh processes. Timed repetitions ran sequentially
without concurrent builds or profiling. The machine exposes 72 virtual
CPUs on an Intel Xeon E5-2699 v4; C++ uses its default worker count.

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.002 | 0.002 | 4.577 |
| Metadata, seconds | 26.762 | 25.059 | 1.184 |
| Attribute reads, seconds | 27.778 | 23.660 | 11.689 |
| Workload total, seconds | 53.618 | 48.721 | 17.369 |
| Whole process, seconds | 60.026 | 55.550 | 17.877 |
| Process peak RSS, MiB | 6685.0 | 6685.0 | 1800.7 |

Each row is independently medianed; phase medians need not sum to the
median total. Workload ranges were 53.436–56.593 seconds before,
47.758–50.610 seconds after, and 16.032–18.151 seconds for C++.

Rust's median workload time decreased by 9.1%, with 14.8% less time in
attribute reads and unchanged peak RSS. C++ remains 2.8 times faster on
this workload. Whole-process time includes startup and stage destruction;
its Rust median decreased by 7.5%.

The changes cache population reachability in the per-prim population
record, use `FxHasher` for precomputed path hashes, recognize synthetic
prototype prefixes directly, and use byte searches for ordinary property
separators. The population cache follows structural invalidation and keeps
answers provisional while layers are loading.

On the bonsai asset above, Callgrind counted 4,834,117,710 instructions
before and 3,739,037,694 after, a 22.7% reduction. Allocation, path handling,
composition, and array decoding still account for substantial work.

All builds visited 416,549 prims and read 1,425,154 arrays. Rust and C++
counted 627,170,615 array elements. All 416,549 path and status records
matched across the three builds. A nested-instancing fixture and ALab's
`book_encyclopedia01` geometry asset also matched counts and status; these
are correctness checks, not full ALab performance measurements.

Validation passed: 3,972 workspace tests, with one ignored baseline test;
strict Clippy, formatting, and documentation checks with all features.
The new regressions cover prototype-prefix syntax, property separator
boundaries, and repeated reads across parent activation changes.

[Machine-readable results](moana-results.json) retain individual timings,
counts, binary hashes, source revisions, and validation details. The Rust
baseline is commit `7ab085dc76abcbcdb66c49d8c9823d02e92d014e`, built with
Rust 1.96.1. The native benchmark uses the OpenUSD 26.8 wheel and matching
26.8 checkout headers, compiled with GCC 11.5.0 and `-O3`.
