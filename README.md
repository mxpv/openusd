<p align="center">
  <img src="docs/logo.svg" alt="openusd logo" width="300px">
</p>

# openusd

[![Crates.io Version](https://img.shields.io/crates/v/openusd)](https://crates.io/crates/openusd)
[![docs.rs](https://img.shields.io/docsrs/openusd)](https://docs.rs/crate/openusd/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/mxpv/openusd/graph/badge.svg?token=LAPV2T3AI8)](https://codecov.io/gh/mxpv/openusd)
[![dependency status](https://deps.rs/repo/github/mxpv/openusd/status.svg)](https://deps.rs/repo/github/mxpv/openusd)

`openusd` is a Rust implementation of Pixar's [Universal Scene Description](https://openusd.org/release/index.html) (USD) format with no C++ dependencies.

For a detailed comparison with the C++ reference implementation and current progress, see the [Roadmap](ROADMAP.md).

## Features

- File formats — reads and writes `.usda` (text), `.usdc` (binary), and `.usdz` (archive).
- Domain schema readers (opt-in [feature flags](#feature-flags), layered on the composed stage) — [`UsdGeom`](src/schemas/geom), [`UsdLux`](src/schemas/lux), [`UsdPhysics`](src/schemas/physics), [`UsdRender`](src/schemas/render), [`UsdSkel`](src/schemas/skel), and [`UsdShade`](src/schemas/shade).
- A fully featured [composition engine](src/pcp) — [LIVRPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering over a per-prim node graph, with [list editing](https://openusd.org/release/glossary.html#usdglossary-listediting), scene-graph [instancing](https://openusd.org/release/glossary.html#usdglossary-instancing), non-destructive [relocates](https://openusd.org/release/glossary.html#usdglossary-relocates), and [variable expressions](https://openusd.org/dev/user_guides/variable_expressions.html).
- A composed [`Stage`](src/usd/stage.rs) — lazy cached per-prim composition with typed value resolution, predicate-based traversal, and full prim/property query API over the composed scene.
- An authoring API — build scenes through [layer](src/sdf/layer.rs)- and [stage](src/usd/stage.rs)-tier APIs, with typed [spec views](src/sdf/spec.rs), composed [prim/attribute/relationship handles](src/usd/prim.rs) with chained fluent edits, `EditTarget` routing to a specific layer, in-memory anonymous-root stages, and applied API schema authoring.

If you encounter a file that can't be read, please open an [issue](https://github.com/mxpv/openusd/issues) and attach the USD file for investigation.

## Compliance

The [AOUSD Core Specification 1.0](https://aousd.org/blog/foundations-of-open-3d-development-introducing-aousd-core-specification-1-0/) has been officially ratified. As part of the specification, sample implementations for compliance testing are provided as Python scripts with JSON baselines. Where JSON baselines are available, the crate parses them and verifies that its output matches.

| Area | Status | Notes |
|------|--------|-------|
| [Text format parsing](vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/text) | :white_check_mark:&nbsp;Passes | 10 tests against JSON baselines |
| [Binary format parsing](vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary) | :white_check_mark:&nbsp;Passes | 42 tests manually backported from the reference suite's `test_binary.py` in [`tests/binary_format.rs`](tests/binary_format.rs) |
| [Composition](vendor/core-spec-supplemental-release_dec2025/composition/tests/assets) | :white_check_mark:&nbsp;Passes | [`tests/composition.rs`](tests/composition.rs) runs the full vendor suite (138 assets) through both the text and binary parsers, regenerating each `pcp.txt` dump to validate strength ordering, prim/property stacks, and time offsets |
| [Value resolution](vendor/core-spec-supplemental-release_dec2025/value_resolution) | :ballot_box_with_check:&nbsp;Partial | 8 tests in [`tests/value_resolution.rs`](tests/value_resolution.rs) (defaults, time samples, value clips). Excludes attribute fallbacks and splines |
| [Combine chains](vendor/core-spec-supplemental-release_dec2025/data_types/tests/combine_chain) | :white_check_mark:&nbsp;Passes | [`ListOp::combined_with`](src/sdf/list_op.rs) and [`ListOp::reduced`](src/sdf/list_op.rs) against JSON baselines |

## Getting started

> [!WARNING]
> This crate is under active development. No API stability is guaranteed until version 1.0.

Make sure you have [`Rust`](https://www.rust-lang.org/tools/install) installed on your system, `rustup` will do the rest.

Add the crate to your `Cargo.toml` (or run `cargo add openusd`):

```toml
[dependencies]
openusd = "0.4"
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

The core library (formats, composition, and the `Stage` API) is always
available. Domain schema readers are gated behind opt-in features so you only
pay for what you use:

| Feature | Enables |
|---------|---------|
| `geom` | [`UsdGeom`](src/schemas/geom) — Imageable, Boundable, Xformable, shapes, Camera, Mesh, Curves, PointInstancer |
| `lux` | [`UsdLux`](src/schemas/lux) — light prims and Light/Shaping/Shadow APIs |
| `physics` | [`UsdPhysics`](src/schemas/physics) — scenes, joints, collisions, limit/drive APIs |
| `render` | [`UsdRender`](src/schemas/render) — RenderSettings, RenderProduct, RenderVar, RenderPass |
| `skel` | [`UsdSkel`](src/schemas/skel) — skeleton reader and skinning toolkit |
| `shade` | [`UsdShade`](src/schemas/shade) — materials, shader networks, bindings, UsdPreviewSurface |
| `serde` | `serde` support for serializing core types |

```toml
[dependencies]
openusd = { version = "0.4", features = ["geom", "lux"] }
```

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

// Inspect any recoverable composition errors collected while loading.
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

With the `geom` feature, read typed schema views over the composed stage — here a
`Mesh` and its point positions and normals:

```rust,no_run
// `PointBased` is brought in so its inherited accessors resolve on the view.
use openusd::schemas::geom::{self, PointBased};
use openusd::{gf, usd};

let stage = usd::Stage::open("scene.usda")?;

if let Some(mesh) = geom::Mesh::get(&stage, "/World/Mesh")? {
    // `points_attr` / `normals_attr` are inherited from the `PointBased` trait
    // up the chain. `point3f[]` and `normal3f[]` both decode to `Vec<gf::Vec3f>`,
    // so `get` extracts them directly.
    let points = mesh.points_attr().get::<Vec<gf::Vec3f>>()?;
    let normals = mesh.normals_attr().get::<Vec<gf::Vec3f>>()?;

    if let Some(points) = points {
        println!("{} points, normals authored: {}", points.len(), normals.is_some());
    }
}
```

More runnable examples live in the [`examples/`](examples) directory:

```bash
cargo run --example dump_usdc -- path/to/file.usdc
cargo run --example write_usda
cargo run --example author_variant_and_reference
```

## Minimum supported Rust version (MSRV)

The project targets stable Rust and aims for the latest Rust editions. The MSRV
is bumped on an as-needed basis, whenever it makes sense for the project. Please
refer to [rust-toolchain.toml](./rust-toolchain.toml) for the exact version
currently used by our CIs.

## License

Licensed under the [MIT License](LICENSE).
