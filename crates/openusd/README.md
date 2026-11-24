# openusd

[![Crates.io Version](https://img.shields.io/crates/v/openusd)](https://crates.io/crates/openusd)
[![docs.rs](https://img.shields.io/docsrs/openusd)](https://docs.rs/crate/openusd/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/mxpv/openusd/graph/badge.svg?token=LAPV2T3AI8)](https://codecov.io/gh/mxpv/openusd)
[![dependency status](https://deps.rs/repo/github/mxpv/openusd/status.svg)](https://deps.rs/repo/github/mxpv/openusd)

`openusd` is a Rust implementation of Pixar's [Universal Scene Description](https://openusd.org/release/index.html) (USD) format with no C++ dependencies.

`openusd` covers the core USD workflow: read and write `.usda`, `.usdc`, and
`.usdz` files; compose layers with references, payloads, variants, instancing,
relocates, and variable expressions; then explore or edit the result through
the `Stage` API. It supports predicate-based traversal, typed value resolution,
layer- and stage-level authoring, and transferable diffs for live sync.

For higher-level domain APIs, the companion
[`openusd-schemas`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas)
crate provides typed `Stage` views for geometry, shading, lighting, animation,
physics, rendering, and more.

## Features

- Read and write `.usda` (text), `.usdc` (binary), and `.usdz` (packages), with
  automatic format detection for `.usd` files.
- Compose sublayers, references, payloads, variants, inherits, and specializes
  with [LIVERPS strength ordering](https://github.com/mxpv/openusd/tree/main/crates/openusd/src/pcp).
  Supports [list editing](https://openusd.org/release/glossary.html#usdglossary-listediting),
  scene-graph [instancing](https://openusd.org/release/glossary.html#usdglossary-instancing),
  [relocates](https://openusd.org/release/glossary.html#usdglossary-relocates), and
  [variable expressions](https://openusd.org/dev/user_guides/variable_expressions.html).
- Query a composed [`Stage`](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/stage.rs)
  through [prim, attribute, and relationship handles](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/prim.rs).
  Composition is cached per prim, with traversal predicates, population masks,
  and payload loading controls.
- Resolve animated values with time-sample interpolation, layer offsets, and
  value clips.
- Author scenes through [layer](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/sdf/layer.rs)
  and stage APIs, with typed [spec views](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/sdf/spec.rs).
  Route edits to a chosen layer with `EditTarget`, apply API schemas, and
  rename or reparent prims with the
  [namespace editor](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/editor.rs).
- Observe stage changes, [undo edits](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/capture.rs),
  and capture replayable [diffs](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/diff.rs)
  for live sync.
- Define [collections](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/collection.rs)
  using explicit includes and excludes or path expressions, then query their
  membership.
- Integrate custom [asset resolvers](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/ar.rs)
  and [file formats](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/sdf/file_format.rs).

If you encounter a file that can't be read, please open an [issue](https://github.com/mxpv/openusd/issues) and attach the USD file for investigation.

## Compliance

The [AOUSD Core Specification 1.0](https://aousd.org/blog/foundations-of-open-3d-development-introducing-aousd-core-specification-1-0/) has been officially ratified. As part of the specification, sample implementations for compliance testing are provided as Python scripts with JSON baselines. Where JSON baselines are available, the crate parses them and verifies that its output matches.

| Area | Status | Notes |
|------|--------|-------|
| [Text format parsing](https://github.com/mxpv/openusd/tree/main/vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/text) | :white_check_mark:&nbsp;Passes | 10 tests against JSON baselines |
| [Binary format parsing](https://github.com/mxpv/openusd/tree/main/vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary) | :white_check_mark:&nbsp;Passes | 42 tests manually backported from the reference suite's `test_binary.py` in [`tests/binary_format.rs`](https://github.com/mxpv/openusd/blob/main/crates/openusd/tests/binary_format.rs) |
| [Composition](https://github.com/mxpv/openusd/tree/main/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets) | :white_check_mark:&nbsp;Passes | [`tests/composition.rs`](https://github.com/mxpv/openusd/blob/main/crates/openusd/tests/composition.rs) runs the full vendor suite (138 assets) through both the text and binary parsers, regenerating each `pcp.txt` dump to validate strength ordering, prim/property stacks, and time offsets |
| [Value resolution](https://github.com/mxpv/openusd/tree/main/vendor/core-spec-supplemental-release_dec2025/value_resolution) | :ballot_box_with_check:&nbsp;Partial | 8 tests in [`tests/value_resolution.rs`](https://github.com/mxpv/openusd/blob/main/crates/openusd/tests/value_resolution.rs) (defaults, time samples, value clips). Excludes attribute fallbacks and splines |
| [Combine chains](https://github.com/mxpv/openusd/tree/main/vendor/core-spec-supplemental-release_dec2025/data_types/tests/combine_chain) | :white_check_mark:&nbsp;Passes | [`ListOp::combined_with`](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/sdf/list_op.rs) and [`ListOp::reduced`](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/sdf/list_op.rs) against JSON baselines |

## Getting started

Add the crate to your `Cargo.toml` (or run `cargo add openusd`):

```toml
[dependencies]
openusd = "0.9"
```

If you need the latest unreleased changes, depend on the crate directly from the
git repository:

```toml
[dependencies]
openusd = { git = "https://github.com/mxpv/openusd.git" }
```

To pin a specific revision, add a `rev` field:

```toml
[dependencies]
openusd = { git = "https://github.com/mxpv/openusd.git", rev = "4c02084" }
```

### Feature flags

| Feature | Enables |
|---------|---------|
| `mmap` | Memory-mapped reads of layer files, enabled per resolver with `ar::DefaultResolver::map_files` |
| `serde` | `serde` support for serializing core types |

## Example

```rust,no_run
use openusd::{ar, usd};

// Open a stage with default settings (DefaultResolver, strict errors, all payloads loaded).
let stage = usd::Stage::open("scene.usda")?;

// Or configure via the builder:
let stage = usd::Stage::builder()
    // Use a custom asset resolver (default: DefaultResolver).
    .resolver(ar::DefaultResolver::new())
    // Leave payload arcs unloaded (default: LoadAll).
    .load(usd::InitialLoadSet::LoadNone)
    // Restrict the stage to a subtree of interest.
    .mask(usd::StagePopulationMask::new(["/World/Hero"]))
    .open("scene.usda")?;

// Recoverable composition errors discovered so far: the root layer stack at
// open, plus reference/payload diagnostics that accrue as prims are traversed.
for err in stage.composition_errors() {
    eprintln!("warning: {err}");
}

// Traverse prims filtered by a predicate. DEFAULT skips inactive/unloaded/abstract
// subtrees and stops at instances; ALL visits every composed prim.
stage.traverse(usd::PrimPredicate::DEFAULT, |path| println!("{path}"))?;
stage.traverse(usd::PrimPredicate::ALL, |path| println!("{path}"))?;

// Composed prim queries go through a `Prim` handle (mirroring C++ `UsdPrim`).
let hero = stage.prim_at("/World/Hero");
let active = hero.is_active()?;
let is_model = hero.is_model()?;
let type_name = hero.type_name()?;

// Access children and properties composed across layers, references, and payloads.
let children = hero.children()?;
let properties = hero.property_names()?;
```

To read typed schema views (a `Mesh` and its points, a `Skeleton`, a `Material`)
over the composed stage, add [`openusd-schemas`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas) alongside
this crate.

More runnable examples live in the [`examples/`](https://github.com/mxpv/openusd/tree/main/crates/openusd/examples) directory:

```bash
cargo run -p openusd --example dump_usdc -- path/to/file.usdc
cargo run -p openusd --example write_usda
cargo run -p openusd --example author_variant_and_reference
```

## License

Licensed under the
[MIT License](https://github.com/mxpv/openusd/blob/main/LICENSE), except for
`src/usd/core_schemas.rs`, which is generated from OpenUSD's own schema
definitions and covered by the Tomorrow Open Source Technology License 1.0.
`third-party/` carries that license and upstream's notice;
`vendor/OpenUSD/README.md` in the repository records where the file comes from.
