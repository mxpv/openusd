<p align="center">
  <img src="docs/logo.svg" alt="openusd logo" width="300px">
</p>

# openusd

[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/mxpv/openusd/graph/badge.svg?token=LAPV2T3AI8)](https://codecov.io/gh/mxpv/openusd)
[![dependency status](https://deps.rs/repo/github/mxpv/openusd/status.svg)](https://deps.rs/repo/github/mxpv/openusd)

`openusd` is a Rust implementation of Pixar's [Universal Scene Description](https://openusd.org/release/index.html) (USD) format with no C++ dependencies.

For a detailed comparison with the C++ reference implementation and current progress, see the [Roadmap](ROADMAP.md).

## Crates

This repository contains the following crates:

| Crate | Description | |
|-------|-------------|-|
| [`openusd`](crates/openusd) | Core USD library — file formats, composition engine, and the composed `Stage` API. | [![Crates.io Version](https://img.shields.io/crates/v/openusd)](https://crates.io/crates/openusd)<br>[![docs.rs](https://img.shields.io/docsrs/openusd)](https://docs.rs/crate/openusd/latest) |
| [`openusd-schemas`](crates/openusd-schemas) | Typed views for USD's standard schemas — `UsdGeom`, `UsdShade`, `UsdSkel`, and more. | [![Crates.io Version](https://img.shields.io/crates/v/openusd-schemas)](https://crates.io/crates/openusd-schemas)<br>[![docs.rs](https://img.shields.io/docsrs/openusd-schemas)](https://docs.rs/crate/openusd-schemas/latest) |

## Features

- File formats — reads and writes `.usda` (text), `.usdc` (binary), and `.usdz` (archive).
- A fully featured [composition engine](crates/openusd/src/pcp) — [LIVRPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering over a per-prim node graph, with [list editing](https://openusd.org/release/glossary.html#usdglossary-listediting), scene-graph [instancing](https://openusd.org/release/glossary.html#usdglossary-instancing), non-destructive [relocates](https://openusd.org/release/glossary.html#usdglossary-relocates), and [variable expressions](https://openusd.org/dev/user_guides/variable_expressions.html).
- A composed [`Stage`](crates/openusd/src/usd/stage.rs) — lazy cached per-prim composition with typed value resolution, predicate-based traversal, and full prim/property query API over the composed scene.
- An authoring API — build scenes through [layer](crates/openusd/src/sdf/layer.rs)- and [stage](crates/openusd/src/usd/stage.rs)-tier APIs, with typed [spec views](crates/openusd/src/sdf/spec.rs), composed [prim/attribute/relationship handles](crates/openusd/src/usd/prim.rs) with chained fluent edits, `EditTarget` routing to a specific layer, in-memory anonymous-root stages, and applied API schema authoring.
- Live sync friendly — listen to `Stage` edit events and capture each edit as a transferable, replayable [`Diff`](crates/openusd/src/usd/diff.rs) for live mirroring across processes.
- Domain schema readers (opt-in per family, layered on the composed stage) — [`UsdGeom`](crates/openusd-schemas/src/geom), [`UsdLux`](crates/openusd-schemas/src/lux), [`UsdPhysics`](crates/openusd-schemas/src/physics), [`UsdRender`](crates/openusd-schemas/src/render), [`UsdSkel`](crates/openusd-schemas/src/skel), and [`UsdShade`](crates/openusd-schemas/src/shade).

If you encounter a file that can't be read, please open an [issue](https://github.com/mxpv/openusd/issues) and attach the USD file for investigation.

## Compliance

The [AOUSD Core Specification 1.0](https://aousd.org/blog/foundations-of-open-3d-development-introducing-aousd-core-specification-1-0/) has been officially ratified. As part of the specification, sample implementations for compliance testing are provided as Python scripts with JSON baselines. Where JSON baselines are available, the crate parses them and verifies that its output matches.

| Area | Status | Notes |
|------|--------|-------|
| [Text format parsing](vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/text) | :white_check_mark:&nbsp;Passes | 10 tests against JSON baselines |
| [Binary format parsing](vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary) | :white_check_mark:&nbsp;Passes | 42 tests manually backported from the reference suite's `test_binary.py` in [`tests/binary_format.rs`](crates/openusd/tests/binary_format.rs) |
| [Composition](vendor/core-spec-supplemental-release_dec2025/composition/tests/assets) | :white_check_mark:&nbsp;Passes | [`tests/composition.rs`](crates/openusd/tests/composition.rs) runs the full vendor suite (138 assets) through both the text and binary parsers, regenerating each `pcp.txt` dump to validate strength ordering, prim/property stacks, and time offsets |
| [Value resolution](vendor/core-spec-supplemental-release_dec2025/value_resolution) | :ballot_box_with_check:&nbsp;Partial | 8 tests in [`tests/value_resolution.rs`](crates/openusd/tests/value_resolution.rs) (defaults, time samples, value clips). Excludes attribute fallbacks and splines |
| [Combine chains](vendor/core-spec-supplemental-release_dec2025/data_types/tests/combine_chain) | :white_check_mark:&nbsp;Passes | [`ListOp::combined_with`](crates/openusd/src/sdf/list_op.rs) and [`ListOp::reduced`](crates/openusd/src/sdf/list_op.rs) against JSON baselines |

## Getting started

> [!WARNING]
> These crates are under active development. No API stability is guaranteed until version 1.0.

Make sure you have [`Rust`](https://www.rust-lang.org/tools/install) installed on your system, `rustup` will do the rest.

Add the crates you need — `openusd-schemas` is optional, with one feature per
schema family:

```toml
[dependencies]
openusd = "0.6"
openusd-schemas = { version = "0.6", features = ["geom", "shade"] }
```

Open a stage, walk its composed prims, and read a resolved attribute value:

```rust,no_run
use openusd::usd;

let stage = usd::Stage::open("scene.usda")?;

// `DEFAULT` prunes inactive, unloaded, and abstract subtrees.
stage.traverse(usd::PrimPredicate::DEFAULT, |prim_path| {
    println!("{prim_path}");
})?;

let sphere = stage.prim("/World/Sphere")?;
println!("type: {:?}", sphere.type_name()?);

// Resolved across every layer, reference, and payload that composes the prim.
let radius = stage.attribute("/World/Sphere.radius")?;
if let Some(r) = radius.get::<f64>()? {
    println!("radius = {r}");
}
```

Authoring works the same way round, with no files involved:

```rust
use openusd::usd;

let stage = usd::Stage::builder().in_memory("root.usda")?;

stage.define_prim("/World")?.set_type_name("Xform")?;
stage.define_prim("/World/Sphere")?.set_type_name("Sphere")?;
stage.set_default_prim("World")?;

stage.create_attribute("/World/Sphere.radius", "double")?.set(2.5_f64)?;
```

Typed schema views layer on top of that stage — here a mesh's points and the
shader driving a material's surface:

```rust,no_run
use openusd::{gf, usd};
use openusd_schemas::geom::{self, PointBased};
use openusd_schemas::shade;

let stage = usd::Stage::open("scene.usda")?;

// `PointBased` is in scope so `Mesh` inherits its accessors.
if let Some(mesh) = geom::Mesh::get(&stage, "/World/Mesh")? {
    if let Some(points) = mesh.points_attr().get::<Vec<gf::Vec3f>>()? {
        println!("{} points", points.len());
    }
}

// Follow the material's surface terminal to the shader driving it.
if let Some(material) = shade::Material::get(&stage, "/World/Material")? {
    if let Some(terminal) = material.compute_surface_source(&[])? {
        for source in terminal.sources() {
            if let Some(shader) = source.shader() {
                println!("surface shader: {:?}", shader.id()?);
            }
        }
    }
}
```

See each crate's own README for the full API and more examples: [`openusd`](crates/openusd/README.md) for the core library, [`openusd-schemas`](crates/openusd-schemas/README.md) for the domain schemas.

## Minimum supported Rust version (MSRV)

The project targets stable Rust and aims for the latest Rust editions. The MSRV
is bumped on an as-needed basis, whenever it makes sense for the project. Please
refer to [rust-toolchain.toml](./rust-toolchain.toml) for the exact version
currently used by our CIs.

## License

Licensed under the [MIT License](LICENSE).
