# Rust and C++ stage benchmarks

`open_bench.cpp` runs the native OpenUSD equivalent of the Rust
`open_bench` example. `compare.py` runs the executables sequentially in
fresh processes, checks prim and array counts, and retains timings, peak
RSS, and raw output in JSON. Run these tools on Linux.

The current Moana comparison is
[property composition and borrowed spec queries](#property-composition-and-borrowed-spec-queries).

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

Pass `--before-authored` when the saved baseline supports `--authored`.
This makes both Rust builds enumerate authored attributes explicitly.

`--rust-cpu <id>` pins timed Rust processes with Linux `taskset`; C++ keeps
its default affinity. `--alternate-order` reverses the executable order on
every other measured round. The JSON records the CPU and each round's
execution order.

`--rust-mmap` enables mapped file reads in both Rust builds. Keep scene
files unchanged during mapped runs. C++ uses its default crate reader;
`USDC_USE_PREAD` selects its alternative to mapped reads.

Opening is lazy in Rust and eager in C++. Compare the sum of opening,
metadata traversal, and attribute reads. Process time additionally includes
startup and stage destruction. Each executable reports its peak RSS; C++
samples before stage destruction. C++ uses its
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

## Property path and array read follow-up

This comparison uses commit `4ce5df7` from
[PR #159](https://github.com/mxpv/openusd/pull/159) as its Rust baseline.
Property paths retain their owning prim when appended to an ordinary prim
path. Attribute resolution reuses that allocation. Aligned array reads copy
directly into a vector; unaligned reads retain the existing fallback.

Measured on the same Moana scene and machine on 2026-10-19. Both Rust builds
were pinned to CPU 0. C++ kept its default affinity and worker count. Each
executable ran once to warm up, followed by five measured rounds with
alternating executable order. Every Rust pair improved.

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.002 | 4.262 |
| Metadata, seconds | 25.007 | 25.054 | 1.102 |
| Attribute reads, seconds | 23.546 | 20.647 | 10.235 |
| Workload total, seconds | 48.554 | 45.702 | 15.870 |
| Whole process, seconds | 54.774 | 52.242 | 16.271 |
| Process peak RSS, MiB | 6684.9 | 6685.7 | 1793.4 |

Workload time decreased by 5.9%; attribute reads decreased by 12.3%.
Whole-process time decreased by 4.6%. Workload ranges were 47.078–49.784
seconds before, 43.967–48.095 seconds after, and 15.261–17.189 seconds for
C++. Rows are independently medianed. C++ remains about 2.9 times faster
on this workload and uses substantially less memory.

A separate three-run comparison with default CPU affinity and fixed
executable order measured 47.777 seconds before and 47.693 seconds after.
Those overall medians are effectively unchanged. The controlled result
does not establish the same wall-time gain under default scheduling.

On the bonsai asset, Callgrind counted 3,739,037,694 instructions before
and 3,315,311,185 after, an 11.3% reduction. These profile runs used
`--proxies --no-heap` and the core-only property registry.

Both island comparisons matched 416,549 prims, 1,425,154 arrays, and
627,170,615 elements across all builds. Separate checks matched all
416,549 traversal status records. Nested instancing and ALab's
`book_encyclopedia01` also matched counts and status. Workspace validation
passed 3,975 tests with one ignored baseline test, strict Clippy,
formatting, and documentation checks with all features. Regression tests
cover property owners, relationship targets, and aligned and unaligned
array reads.

Reproduce the controlled comparison with saved binaries:

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-followup/before --before-authored \
  --rust /tmp/openusd-followup/after-owner \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 5 --warmups 1 --rust-cpu 0 --alternate-order --check-status \
  --output /tmp/openusd-followup/pinned-island.json
```

[Follow-up results](moana-followup-results.json) retain both comparisons,
individual timings, counts, source and binary hashes, and validation
details.

## Composition and derived paths

The Rust baseline is the property-owner and aligned-array build described
above. Derived prim paths retain immutable parent links and namespace
depth. Traversal, composition graph deepening, and crate path construction
append child identifiers directly. Prim-index construction reuses its
parent and depth calculations.

The crate backend shares decoded inline values and token vectors by their
on-disk value representation. Composition borrows those values. Authored
overrides and erasures take precedence; malformed values retain their
path and field context when queried.

The full-island comparison below uses default CPU affinity for all builds.
Each executable ran once to warm up and three times in fresh processes,
with alternating executable order. Builds and profiling finished before
the measured repetitions.

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.227 |
| Metadata, seconds | 21.455 | 20.336 | 0.999 |
| Attribute reads, seconds | 18.868 | 17.336 | 9.410 |
| Workload total, seconds | 40.395 | 37.909 | 14.954 |
| Whole process, seconds | 46.002 | 43.948 | 15.446 |
| Process peak RSS, MiB | 6684.9 | 6693.8 | 1783.0 |

The combined median workload decreased by 6.2%; metadata decreased by
5.2% and attribute reads by 8.1%. Every Rust pair improved. Whole-process
time decreased by 4.5%. Peak RSS increased by 8.9 MiB (0.1%). Workload
ranges were 40.146–40.555 seconds before, 36.674–38.271 seconds after,
and 14.294–15.479 seconds for C++. Rows are independently medianed.
C++ remains about 2.5 times faster on this workload.

A separate path-only experiment pinned both Rust builds to CPU 0 and left
C++ at its default affinity. Across three alternating rounds, the median
fell from 42.754 to 39.469 seconds (7.7%). Every pair improved. That build
includes the structural path changes without the decoded-field cache.

On the bonsai asset, Callgrind counted 1,318,118,649 instructions before,
939,693,848 with the path changes, and 932,352,604 with the combined
changes. The combined reduction is 29.3%. These runs include opening,
first metadata traversal, and destruction; they skip attribute reads.

Both island experiments matched 416,549 prims, 1,425,154 arrays, and
627,170,615 elements across all builds. Separate checks matched all
416,549 traversal status records. Nested instancing and the ALab book
asset also matched counts and status. All 3,979 workspace tests passed,
with one ignored baseline test. Strict Clippy, formatting, and
documentation checks passed with all features. New regressions cover
child-path structure, deep parent-chain destruction, shared metadata,
overrides, erasures, and corrupt-value error context.

[Composition results](moana-composition-results.json) retain the two
experiments, individual timings, source and binary hashes, instruction
counts, and validation details. Paths still materialize their full text;
composition remains serial.

## Shared instance composition

This comparison uses the preceding combined composition candidate as its
Rust baseline. Registered prototype mappings are reused for settled
indices. Proxies share their prototype's status inputs; payload inclusion
uses the queried instance's load rules.

Child-name folds are cached under the index revision, population epoch,
and instance-local partition. Population masks are applied after the
cached fold. The population epoch covers namespace edits that preserve
the parent's composition index. USDA parsing, dependency discovery, and
`Prim::children` also retain structural child paths.

Both series ran on the same island scene and machine on 2026-10-19. Each
executable ran once to warm up, then three times in fresh processes with
alternating execution order. All builds used default CPU affinity and
worker settings. Builds and profiling finished before timed repetitions.

Ordinary Rust file reads:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.002 | 0.001 | 4.279 |
| Metadata, seconds | 21.226 | 18.598 | 1.009 |
| Attribute reads, seconds | 17.473 | 17.129 | 8.976 |
| Workload total, seconds | 38.701 | 35.660 | 14.263 |
| Whole process, seconds | 44.476 | 41.622 | 14.752 |
| Process peak RSS, MiB | 6693.4 | 6720.6 | 1797.3 |

The median workload decreased by 7.9%; metadata decreased by 12.4%.
Every Rust pair improved. Whole-process time decreased by 6.4%. Peak RSS
increased by 27.2 MiB (0.4%). Workload ranges were 36.886–39.149 seconds
before, 35.460–35.792 seconds after, and 14.096–14.801 seconds for C++.

Mapped Rust file reads, measured in a separate series:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.118 |
| Metadata, seconds | 17.380 | 16.679 | 1.014 |
| Attribute reads, seconds | 17.161 | 17.294 | 9.184 |
| Workload total, seconds | 34.632 | 33.974 | 14.464 |
| Whole process, seconds | 40.313 | 40.537 | 14.894 |
| Process peak RSS, MiB | 6598.9 | 6624.8 | 1800.0 |

The median workload decreased by 1.9%; metadata decreased by 4.0%.
Every Rust pair improved. Whole-process time increased by 0.6%, from
40.313 to 40.537 seconds. Peak RSS increased by 25.9 MiB (0.4%). Workload
ranges were 34.357–34.940 seconds before, 33.763–34.558 seconds after,
and 14.054–14.894 seconds for C++. These runs do not demonstrate a
whole-process speedup. Rows use independent medians in both tables.

C++ uses its default mapped crate reader in both series. `USDC_USE_PREAD`,
`USDC_ENABLE_ZERO_COPY_ARRAYS`, and `PXR_WORK_THREAD_LIMIT` were unset.
Read-mode comparisons use separate warmed series; the recorded commands
identify each mode. Reproduce mapped runs with saved binaries:

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-composition/baseline-next --before-authored \
  --rust /tmp/openusd-next/retained-after \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 3 --warmups 1 --alternate-order --rust-mmap --check-status \
  --output /tmp/openusd-next/island-mmap.json
```

Omit `--rust-mmap` for ordinary Rust reads.

An intermediate build with prototype reuse and shared status inputs ran
14.6% fewer instructions on `isBayCedarA1/element.usda`: 12,905,232,319
before and 11,024,696,421 after. It visited 136,458 prims using
`--proxies --authored --no-heap --until metadata`. This profile precedes
the USDA and child-name-cache changes.

Both island series matched 416,549 prims, 1,425,154 arrays, and
627,170,615 elements. Separate checks matched every traversal status
record. Nested instancing and the ALab book asset also matched counts
and status. All 3,981 workspace tests passed, with one ignored baseline
test. Strict Clippy, formatting, and documentation checks passed with all
features. Regressions cover child ordering after edits, new siblings,
per-instance payload unloading after cached queries, and invalid USDA
prim names.

[Instance composition results](moana-instance-results.json) retain both
series, individual timings, source and binary hashes, reference settings,
and validation details.

## Compact layer values

This comparison uses the preceding instance-composition candidate as its
Rust baseline. Large scalar payloads, dictionaries, and list operations in
`Value` now use boxes. On this x86-64 build, `Value` occupies 40 bytes,
down from 160; a `(String, Value)` field slot occupies 64 bytes, down from
184. Geometry arrays keep their contiguous `Vec` payloads.

Direct construction of the affected enum variants takes a box, and their
generated extraction helpers expose it. Typed `From` and `TryFrom`
conversions accept and return unboxed payloads. Readers, writers,
composition folds, and schema literal generation use the new storage. The
schema value snapshot was regenerated and its compiled values checked.

Massif profiles with ordinary file reads of `isBayCedarA1/element.usda`
visited 136,458 prims and built 31,258 graphs in each build. At the detailed
peak snapshots:

| Live allocation, MiB | Rust before | Rust after |
|---|---:|---:|
| Useful heap | 696.1 | 524.6 |
| Field vectors | 284.6 | 99.0 |
| Allocator overhead | 63.2 | 64.9 |

Useful heap decreased by 24.6%. The extra boxes offset part of the field
vector saving. These are instrumented, metadata-only profiles, separate
from the native island timing series. Reproduce each profile with the
corresponding preserved binary:

```sh
valgrind --tool=massif --time-unit=ms --max-snapshots=30 --threshold=1.0 \
  /tmp/openusd-memory-after --no-heap --proxies --authored \
  --until metadata /path/to/island/usd/elements/isBayCedarA1/element.usda
```

Both full-island series ran on 2026-10-19 with default CPU affinity. Each
executable ran once to warm up, then three times in fresh processes with
alternating order. Builds and profiles finished before these repetitions.
Comparisons use the preserved before/after binaries within each series;
earlier sections record separate runs.

Ordinary Rust file reads:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.578 |
| Metadata, seconds | 22.946 | 21.109 | 1.340 |
| Attribute reads, seconds | 20.672 | 18.365 | 12.483 |
| Workload total, seconds | 43.619 | 39.475 | 18.232 |
| Whole process, seconds | 50.806 | 46.303 | 18.675 |
| Process peak RSS, MiB | 6720.2 | 6114.3 | 1792.7 |

The observed median workload decreased by 9.5%; whole-process time
decreased by 8.9%. Peak RSS decreased by 605.9 MiB (9.0%). Workload ranges
were 34.827–47.526 seconds before, 34.816–43.545 seconds after, and
16.507–18.953 seconds for C++. The Rust times drifted upward across rounds
and the ranges overlap. These runs do not establish a stable 9.5% speedup.

Mapped Rust file reads, measured in a separate series:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.002 | 0.002 | 4.325 |
| Metadata, seconds | 20.708 | 20.427 | 1.252 |
| Attribute reads, seconds | 21.318 | 20.108 | 12.373 |
| Workload total, seconds | 42.028 | 40.536 | 17.849 |
| Whole process, seconds | 49.550 | 48.377 | 18.300 |
| Process peak RSS, MiB | 6624.4 | 6019.4 | 1793.8 |

The observed median workload decreased by 3.5%; whole-process time
decreased by 2.4%. Peak RSS decreased by 605.0 MiB (9.1%). Workload ranges
were 40.643–42.429 seconds before, 39.064–41.226 seconds after, and
16.327–17.967 seconds for C++. Every workload pair improved in both
series. Rows use independent medians. Mapped Rust remains 2.27 times
slower than C++ in this series.

C++ uses its default mapped crate reader in both series. `USDC_USE_PREAD`,
`USDC_ENABLE_ZERO_COPY_ARRAYS`, and `PXR_WORK_THREAD_LIMIT` were unset.
Reproduce the mapped comparison with the preserved binaries:

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-memory-before --before-authored \
  --rust /tmp/openusd-memory-after \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 3 --warmups 1 --alternate-order --rust-mmap --check-status \
  --output /tmp/openusd-memory-island-mmap.json
```

Omit `--rust-mmap` for ordinary Rust reads.

Both series matched 416,549 prims, 1,425,154 arrays, and 627,170,615
elements in every run. Separate checks matched all traversal status
records. Nested instancing and the ALab book asset also matched counts
and status. All 3,982 workspace tests passed, with one ignored baseline
test. Strict Clippy, formatting, and documentation checks passed with all
features. A regression test bounds the `Value` slot size at 40 bytes.

[Value storage results](moana-memory-results.json) retain both series,
individual timings, heap-profile totals, source and binary hashes,
reference settings, and validation details.

## Layer and prototype lookups

This comparison uses the compact-value candidate above as its Rust
baseline. `LayerGraph` stores layer nodes in a vector indexed by stable
layer IDs. Private `PathTable` storage supports borrowed text queries
through `hashbrown::Equivalent`. Prototype lookup uses the root path
component. All-inclusive population masks and empty load-rule tables use
the query path directly because their answers are namespace independent.

The direct `hashbrown` dependency has default features disabled. Version
0.17.1 was already present transitively in the baseline lockfile. Regression
tests cover stable layer handles, invalid handles, borrowed path hashing,
lookup by a text slice, and removal of a queried subtree. Existing tests
cover namespace-dependent masks and load rules for nested instances.

Callgrind metadata profiles of `isBayCedarA1/element.usda` visited 136,458
prims and built 31,258 graphs in each build. Whole-process instructions,
including teardown, decreased from 10,493,951,734 to 8,875,967,318 (15.4%).
A build with only vector layer storage took 10,256,609,102 instructions.
These profiles are separate from the native full-island timings below.

Both timing series ran on 2026-10-19 with default CPU affinity. Each
executable ran once to warm up, then three times in fresh processes with
alternating order. C++ used its default mapped crate reader and worker
count. `USDC_USE_PREAD`, `USDC_ENABLE_ZERO_COPY_ARRAYS`, and
`PXR_WORK_THREAD_LIMIT` were unset. Rows use independent medians.

Ordinary Rust file reads:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.204 |
| Metadata, seconds | 20.184 | 19.330 | 1.016 |
| Attribute reads, seconds | 17.100 | 17.232 | 9.319 |
| Workload total, seconds | 36.884 | 36.356 | 14.504 |
| Whole process, seconds | 43.135 | 42.961 | 15.000 |
| Process peak RSS, MiB | 6114.2 | 6113.7 | 1795.7 |

The median workload decreased by 1.4%; whole-process time decreased by
0.4%. Metadata time decreased by 4.2%, while attribute-read time increased
by 0.8%. Peak RSS was essentially unchanged. Workload ranges were
36.739–39.264 seconds before, 36.309–36.739 seconds after, and
14.351–16.093 seconds for C++.

Mapped Rust file reads, measured in a separate series:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.146 |
| Metadata, seconds | 16.970 | 15.196 | 0.989 |
| Attribute reads, seconds | 16.779 | 16.143 | 9.391 |
| Workload total, seconds | 34.074 | 31.460 | 14.526 |
| Whole process, seconds | 39.990 | 37.275 | 15.130 |
| Process peak RSS, MiB | 6018.9 | 6019.0 | 1775.3 |

The median workload decreased by 7.7%; whole-process time decreased by
6.8%. Metadata time decreased by 10.5%, and attribute-read time decreased
by 3.8%. Peak RSS was essentially unchanged. Every mapped workload pair
improved by 7.5–7.7%. Workload ranges were 33.439–34.134 seconds before,
30.927–31.517 seconds after, and 14.515–14.663 seconds for C++. Within
this series, the workload gap narrowed from 2.35 to 2.17 times the C++
median. Earlier sections record separate timing series.

Reproduce the mapped comparison with the preserved binaries:

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-path-next/before --before-authored \
  --rust /tmp/openusd-path-next/after \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 3 --warmups 1 --alternate-order --rust-mmap --check-status \
  --output /tmp/openusd-path-next/island-mmap.json
```

Omit `--rust-mmap` for ordinary Rust reads.

A separate mapped full-island profile collects only the first traversal
and type-name queries, including demand-loaded composition:

```sh
valgrind --tool=callgrind --collect-atstart=no \
  --toggle-collect='open_bench::traverse' \
  --callgrind-out-file=/tmp/island-metadata.callgrind \
  /tmp/openusd-path-next/after --proxies --authored --no-heap --mmap \
  --until metadata /path/to/island/usd/island.usda
```

This traversal took 53,402,895,181 instructions and built 278,816 graphs.
Identifier validation accounts for 5.4% of self instructions, path component
iteration for 5.0%, and property path construction for 3.0%. The allocator's
`_int_malloc`, `malloc`, and `_int_free` bodies together account for 15.6%.
Identifier validation comes from child and property path construction.
Property paths are constructed during USDA parsing, property type-conflict
reporting, and crate path decoding. `IndexStore::insert` accounts for
6.63 billion inclusive instructions, including its hashing and allocation
callees. These instruction counts identify remaining work; they do not
measure elapsed-time shares. Array reads and teardown are excluded.

Both timing series matched 416,549 prims, 1,425,154 arrays, and 627,170,615
elements in every run. Separate checks matched all 416,549 traversal status
records. Nested instancing and the ALab book asset also matched counts and
status. All 3,985 workspace tests passed, with one ignored baseline test.
Strict Clippy, formatting, and documentation checks passed with all
features. Dependency checks passed against a local copy of the cached
advisory database using the project's policy.

[Layer and prototype lookup results](moana-lookup-results.json) retain both
series, individual timings, profile totals, source and binary hashes,
reference settings, and validation details.

## Property composition and borrowed spec queries

This comparison uses the layer/prototype lookup candidate above as its
Rust baseline. Property-name appends borrow their input text. Common prim
classification and root-name queries avoid component iteration, and ASCII
identifiers use byte checks with a Unicode fallback.

`AbstractData::property_spec` returns a property's stored path and spec type
in one query. The text and crate backends support borrowed compound keys;
`Box` and `CowData` forward the query and respect staged removals and
replacements. The query is used for property enumeration and type-conflict
detection.

Composed property names and types are cached under their prim's composition
revision. Instance proxies reuse their canonical entry's fold. Authored-only
enumeration reads the authored property set; composed enumeration also
consults schema declarations. Conflict detection borrows the defining layer
and constructs diagnostic text and the composed property path when a kind
mismatch is found. Internal numeric dependency maps and owner sets use Fx
hashing.

Tests cover borrowed-key hashing, Unicode names, long paths, staged edits,
crate overrides, and spec removal/recreation. A regression test warms the
property-kind cache, replaces an attribute with a relationship, and replaces
it with an attribute again. Both enumeration APIs must follow each change.

A Cedar metadata Callgrind profile visited 136,458 prims and built 31,258
graphs in each build. Whole-process instructions, including teardown,
decreased from 8,875,967,318 to 8,210,606,686 (7.5%). These profiles exclude
array reads and are separate from native timing series.

Both full-island series ran on 2026-10-20 with default CPU affinity. Each
executable ran once to warm up, then three times in fresh processes with
alternating order. Builds and profiles finished before these repetitions.
C++ used its default mapped crate reader and worker count.
`USDC_USE_PREAD`, `USDC_ENABLE_ZERO_COPY_ARRAYS`, and
`PXR_WORK_THREAD_LIMIT` were unset. Rows use independent medians.

Ordinary Rust file reads:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.269 |
| Metadata, seconds | 18.436 | 17.220 | 1.053 |
| Attribute reads, seconds | 16.944 | 15.545 | 10.016 |
| Workload total, seconds | 35.581 | 33.271 | 15.054 |
| Whole process, seconds | 42.845 | 40.292 | 16.086 |
| Process peak RSS, MiB | 6113.4 | 6233.0 | 1804.9 |

The median workload decreased by 6.5%; whole-process time decreased by
6.0%. Metadata time decreased by 6.6%, and attribute-read time decreased by
8.3%. Workload ranges were 35.381–36.126 seconds before, 31.348–33.620
seconds after, and 14.732–15.786 seconds for C++. Peak RSS increased by
119.6 MiB (2.0%). The property cache retains computed names and types.

Mapped Rust file reads, measured in a separate series:

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.400 |
| Metadata, seconds | 16.417 | 14.996 | 1.145 |
| Attribute reads, seconds | 17.259 | 15.817 | 10.077 |
| Workload total, seconds | 33.652 | 30.782 | 15.456 |
| Whole process, seconds | 40.900 | 38.083 | 15.873 |
| Process peak RSS, MiB | 6018.2 | 6138.0 | 1770.8 |

The median workload decreased by 8.5%; whole-process time decreased by
6.9%. Metadata time decreased by 8.7%, and attribute-read time decreased by
8.4%. Workload ranges were 33.453–34.244 seconds before, 30.670–31.140
seconds after, and 15.177–16.425 seconds for C++. Peak RSS increased by
119.8 MiB (2.0%). Every measured workload pair improved in both series.

Within the mapped series, the workload gap narrowed from 2.18 to 1.99 times
the C++ median. The goal of finishing within 10% of default C++ time is not
met. Composition runs serially, and numeric arrays use owned vectors.

A separate composition-only diagnostic compares default C++ workers with
`PXR_WORK_THREAD_LIMIT=1`. It includes open and first traversal/type-name
queries. Arrays and teardown are excluded from these totals. Each
configuration ran once to warm up, then three times in fresh processes with
alternating order. Every run visited 416,549 prims.

| Median, seconds | Rust mapped | C++ default | C++ thread limit 1 |
|---|---:|---:|---:|
| Open | 0.001 | 4.022 | 11.526 |
| First traversal | 14.799 | 1.076 | 0.958 |
| Open + first traversal | 14.800 | 5.197 | 12.484 |

Rust takes 18.5% longer than C++ with its thread limit set to one. C++'s
default worker configuration is 2.40 times faster than its limit-one
configuration in this diagnostic. Serial composition efficiency and
parallel execution both contribute to the remaining gap. Reproduce a
limit-one C++ composition run with:

```sh
PXR_WORK_THREAD_LIMIT=1 /tmp/openusd-reference/open_bench \
  --no-heap --proxies --authored --until metadata \
  /path/to/island/usd/island.usda
```

Run Rust with the same flags plus `--mmap`, using its default environment.

Reproduce the mapped comparison with the preserved binaries:

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-path-build/before --before-authored \
  --rust /tmp/openusd-property-cache/after \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 3 --warmups 1 --alternate-order --rust-mmap --check-status \
  --output /tmp/openusd-property-cache/island-mmap.json
```

Omit `--rust-mmap` for ordinary Rust reads.

An intermediate attempt returned only a stored property path, then looked
up its type or field separately. Its median mapped workload increased by
1.3%. Native sampling found the copy-on-write wrapper using an allocating
fallback. The final property query forwards through that wrapper and
returns path and type together. The discarded timings and sampling totals
are retained in the JSON report.

Both full-island series matched 416,549 prims, 1,425,154 arrays, and
627,170,615 elements in every run. Separate checks matched all 416,549
traversal status records. Nested instancing and the ALab book asset also
matched counts and status. All 3,991 workspace tests passed, with one
ignored baseline test. Strict Clippy, formatting, and documentation checks
passed with all features. Dependency checks passed against a copied cached
advisory database using the project's policy.

[Property composition results](moana-property-results.json) retain both
series, individual timings, instruction-profile totals, the discarded
experiment, source and binary hashes, reference settings, and validation
results.

## Borrowed field queries

This comparison uses the property-composition candidate above as its Rust
baseline. `sdf::PathQuery` holds a borrowed path or a parent and suffix,
with the same hash and equality as the corresponding owned path. Compound
keys up to 256 bytes are hashed in a stack buffer; longer keys use a
temporary string.

`AbstractData::try_field_query` reads through that key. Text and crate
backends perform one spec lookup, and crate decode failures retain the
stored path in their diagnostics. `Box` forwards the query. `CowData`
forwards directly while its overlay is empty and applies staged field and
spec changes through its ordinary field reader.

The value-resolution walk reuses one borrowed key across each node's
layers. Provenance consumers materialize their property path.
Expression composition obtains its anchor lazily. Reads over the maintained
spec stack use its recorded presence; the wider clip walk checks presence
in each layer.

Tests cover direct and compound key hashes, Unicode, relative paths,
variants, nested target suffixes, long keys, crate array decoding, staged
field changes, and spec deletion/recreation. All 3,994 workspace tests
passed, with one ignored baseline test. Strict Clippy, formatting,
documentation, and diff checks passed. Dependency checks used the project's
policy and a copied cached advisory database.

The final mapped series uses default CPU affinity, one warmup per
executable, and three measured fresh processes, with alternating order.
Builds and profiles finished before these runs. C++ uses its default mapped
reader and worker count; `USDC_USE_PREAD`, `USDC_ENABLE_ZERO_COPY_ARRAYS`, and
`PXR_WORK_THREAD_LIMIT` are unset. Rows use independent medians.

The Rust builds measured in this series use owned vectors for array values.
The workload retrieves them, counts their elements, and drops them without
hashing their payloads.

Key equality compares byte ranges. A qualitative GDB profile of the
intermediate candidate captured 1,571 attribute-read stacks, with the key
comparison as the innermost frame in 147. Debugger sampling perturbs
execution and is separate from the native timing series.

| Median | Rust before | Rust after | C++ 26.8 |
|---|---:|---:|---:|
| Open, seconds | 0.001 | 0.001 | 4.183 |
| Metadata, seconds | 14.463 | 14.642 | 1.107 |
| Attribute reads, seconds | 15.002 | 14.379 | 10.655 |
| Workload total, seconds | 29.488 | 28.834 | 15.692 |
| Whole process, seconds | 36.763 | 36.277 | 16.076 |
| Process peak RSS, MiB | 6138.2 | 6135.3 | 1783.8 |

The median workload decreased by 2.2%; attribute-read
time decreased by 4.2%. Every measured workload pair improved.
Metadata time did not improve consistently. Timing ranges overlap:
29.235–29.951 seconds before, 28.558–29.915 seconds after, and
14.698–16.729 seconds for C++.

Rust remains 1.84 times the default C++ median. The goal of
finishing within 10% of C++ time is not met. Peak RSS is effectively
unchanged. The remaining composition parallelism gap is described in the
worker-count diagnostic above.

All measured runs matched 416,549 prims, 1,425,154 arrays, and 627,170,615
elements. Separate metadata runs matched all 416,549 status records. The
final binary also matched counts and status with ordinary file reads,
nested instancing, and the ALab book asset. The ordinary-reader run checks
correctness and is not a comparative timing series.

The intermediate candidate has separate complete timing series in both
read modes in the JSON report. Its median workload decreased by 1.3% with
mapped reads and 1.8% with ordinary reads. These gains are not combined
with the final series.

Reproduce the final comparison with:

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-query-equality/before --before-authored \
  --rust /tmp/openusd-query-equality/after \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 3 --warmups 1 --alternate-order --rust-mmap --check-status \
  --output /tmp/openusd-query-equality/island-mmap.json
```

[Borrowed field results](moana-field-results.json) retain the final mapped
series, intermediate series and sampling summary, discarded experiments,
source and binary hashes, reference settings, and validation results.

## Moana: shared arrays and parallel decoding

The borrowed-field candidate above is the Rust baseline for this series.
The array control adds compact composition dependency registrations,
borrowed built-in field names, and shared numeric arrays. The final
candidate also batches sibling statuses and decodes independent layer
buffers on workers.

Primitive numeric and `gf` array variants of `sdf::Value` store
`sdf::Array<T>`, with copy-on-write storage like C++ `VtArray`. Clones share
storage. Mutation detaches it;
extracting an owned `Vec<T>` copies shared elements. Aligned uncompressed
arrays of at least 2,048 bytes share mapped backing bytes on little-endian
hosts. Compressed arrays use owned storage. Arrays retain their backing
bytes independently of the layer that supplied them.

Filtered child iteration composes sibling statuses through one
layer-demand fixpoint. Multiple independent inputs totaling at least
1 MiB may decode on up to eight available CPUs. Resolution, callbacks,
layer construction, and graph updates run on the calling thread. Layer
backends implement `Send + Sync`; formats declare whether decoding needs
only the acquired bytes. Prim composition remains serial.

The final benchmark traverses with `filtered_descendants`; the two Rust
controls use the stage visitor. Both visit every matching instance
placement. The visitor supports edits between visits and keeps its lazy
loading behavior. Separate metadata runs compare sorted paths and the
active, loaded, defined, abstract, instance, and proxy status bits.

The series uses one warmup and three measured fresh processes for each of
four executables, alternating order, with default CPU affinity. Builds and
profiles finish before timing begins. C++ 26.8 uses its default mapped
reader and worker count. `USDC_USE_PREAD`, `USDC_ENABLE_ZERO_COPY_ARRAYS`,
and `PXR_WORK_THREAD_LIMIT` are unset. Rows use independent medians.

| Median | Rust before | Rust array control | Rust after | C++ 26.8 |
|---|---:|---:|---:|---:|
| Open, seconds | 0.002 | 0.001 | 0.001 | 4.519 |
| Metadata, seconds | 16.988 | 16.573 | 15.677 | 1.254 |
| Attribute reads, seconds | 16.497 | 15.051 | 14.476 | 11.428 |
| Workload total, seconds | 33.454 | 31.740 | 30.154 | 17.200 |
| Whole process, seconds | 41.882 | 39.401 | 37.760 | 17.760 |
| Process peak RSS, MiB | 6135.1 | 3849.9 | 3844.7 | 1794.0 |

The final median workload decreases by 9.9% against the starting build
and 5.0% against the array control. Peak RSS decreases by 37.3% against
the starting build.
Rust remains 1.75 times the default C++ median.
The goal of finishing within 10% of C++ time is not met.

Workload timing ranges are 33.298–33.486 seconds before, 30.740–32.226
for the array control, 28.969–31.864 after, and 15.920–19.258 for C++.
The array-control and final timing ranges overlap. Every measured pair
improves against the array control.

All runs match 416,549 prims, 1,425,154 arrays, and 627,170,615 elements.
Separate runs match all 416,549 traversal status records. The workload
retrieves array values, counts their elements, and drops them without
hashing payloads. Peak RSS savings include mapped payload pages that this
workload does not touch. Applications that read every element or extract
owned vectors have different costs. Whole-process times include setup and
teardown; workload totals sum the open, metadata, and array phases.

All 4,008 workspace tests pass, with one ignored baseline test. Tests cover
array alignment and bounds, copy-on-write mutation, backing-store lifetime,
instanced reads across edits and blocks, decode failure isolation, worker
cutoffs, and prepared sublayer reuse. Strict Clippy, documentation,
formatting, and diff checks pass. Dependency checks use the project policy
and a copied cached advisory database. Ordinary file reads, nested
instancing, and the ALab book asset match C++ counts and status records.

A separate GDB execution records 367 layer-loading barriers with the
visitor and 144 with sibling batching through the iterator. These call
counts are excluded from timing claims. The report also retains the
independent array-only series, the parallel pilot, and discarded
path-table and value/source memo experiments.

Reproduce the final comparison with:

```sh
python3 benchmarks/compare.py /path/to/island/usd/island.usda \
  --before /tmp/openusd-query-equality/after --before-authored \
  --rust-variant array=/tmp/openusd-final-array/after \
  --rust /tmp/openusd-parallel-reads/final \
  --cpp /tmp/openusd-reference/open_bench \
  --runs 3 --warmups 1 --alternate-order --rust-mmap --check-status \
  --output /tmp/openusd-parallel-reads/island.json
```

[Decoding results](moana-decoding-results.json) retain the native series,
source and binary hashes, reference settings, controls, and validation.
