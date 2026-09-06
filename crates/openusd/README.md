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

- File formats — reads and writes `.usda` (text), `.usdc` (binary), and `.usdz` (archive).
- A fully featured [composition engine](https://github.com/mxpv/openusd/tree/main/crates/openusd/src/pcp) — [LIVRPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering over a per-prim node graph, with [list editing](https://openusd.org/release/glossary.html#usdglossary-listediting), scene-graph [instancing](https://openusd.org/release/glossary.html#usdglossary-instancing), non-destructive [relocates](https://openusd.org/release/glossary.html#usdglossary-relocates), and [variable expressions](https://openusd.org/dev/user_guides/variable_expressions.html).
- A composed [`Stage`](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/stage.rs) — lazy cached per-prim composition with typed value resolution, predicate-based traversal, and full prim/property query API over the composed scene.
- An authoring API — build scenes through [layer](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/sdf/layer.rs)- and [stage](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/stage.rs)-tier APIs, with typed [spec views](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/sdf/spec.rs), composed [prim/attribute/relationship handles](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/prim.rs) with chained fluent edits, `EditTarget` routing to a specific layer, in-memory anonymous-root stages, and applied API schema authoring.
- Live sync friendly — listen to `Stage` edit events and capture each edit as a transferable, replayable [`Diff`](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/diff.rs) for live mirroring across processes.

If you encounter a file that can't be read, please open an [issue](https://github.com/mxpv/openusd/issues) and attach the USD file for investigation.

## Getting started

Add the crate to your `Cargo.toml` (or run `cargo add openusd`):

```toml
[dependencies]
openusd = "0.7"
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

Licensed under the [MIT License](https://github.com/mxpv/openusd/blob/main/LICENSE),
except for `schemas/`, which vendors OpenUSD's core schema data under the
Tomorrow Open Source Technology License 1.0. That directory carries its own
`LICENSE`, `NOTICE.txt` and `README.md`.
