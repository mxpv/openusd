<p align="center">
  <img src="docs/logo.svg" alt="openusd logo" width="300px">
</p>

# openusd

[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/mxpv/openusd/graph/badge.svg?token=LAPV2T3AI8)](https://codecov.io/gh/mxpv/openusd)
[![dependency status](https://deps.rs/repo/github/mxpv/openusd/status.svg)](https://deps.rs/repo/github/mxpv/openusd)

`openusd` is a Rust implementation of Pixar's
[Universal Scene Description](https://openusd.org/release/index.html) (USD),
with no C++ dependencies. Read and write USD files, compose layers into scenes,
and query or edit them through a typed Rust API.

This repository contains the following crates:

| Crate | Description | Release / docs |
|-------|-------------|-|
| [`openusd`](crates/openusd) | The core USD library: implements the file formats, scene composition, and the `Stage` API. | [![Crates.io Version](https://img.shields.io/crates/v/openusd)](https://crates.io/crates/openusd)<br>[![docs.rs](https://img.shields.io/docsrs/openusd)](https://docs.rs/crate/openusd/latest) |
| [`openusd‑schemas`](crates/openusd-schemas) | Typed views for reading and authoring standard schemas, including `UsdGeom`, `UsdShade`, and `UsdSkel`. | [![Crates.io Version](https://img.shields.io/crates/v/openusd-schemas)](https://crates.io/crates/openusd-schemas)<br>[![docs.rs](https://img.shields.io/docsrs/openusd-schemas)](https://docs.rs/crate/openusd-schemas/latest) |
| [`openusd‑build`](crates/openusd-build) | Build-time Rust code generation from OpenUSD `schema.usda` files. | [![Crates.io Version](https://img.shields.io/crates/v/openusd-build)](https://crates.io/crates/openusd-build)<br>[![docs.rs](https://img.shields.io/docsrs/openusd-build)](https://docs.rs/crate/openusd-build/latest) |
| [`openusd‑mtlx`](crates/openusd-mtlx) | Read-only MaterialX `.mtlx` file format: documents open as `UsdShade` layers. | [![Crates.io Version](https://img.shields.io/crates/v/openusd-mtlx)](https://crates.io/crates/openusd-mtlx)<br>[![docs.rs](https://img.shields.io/docsrs/openusd-mtlx)](https://docs.rs/crate/openusd-mtlx/latest) |

If a file fails to load, please open an
[issue](https://github.com/mxpv/openusd/issues) with the USD file and the error.

## Compliance

The test suite checks text and binary parsing, composition, value resolution,
and list-operation combining against reference tests and baselines from the
[AOUSD Core Specification](docs/aousd_core_spec_1.0.1.pdf) supplemental material.
CI runs the workspace tests on Linux, macOS, and Windows.

Refer to the [compliance table](COMPLIANCE.md) for what is currently covered.

## Getting started

> [!WARNING]
> These crates are under active development. APIs may change before version 1.0.

Add the crates you need to `Cargo.toml`. `openusd-schemas` is optional, with
one feature per schema family:

```toml
[dependencies]
openusd = { version = "0.9", features = ["mmap"] }
openusd-schemas = { version = "0.9", features = ["geom", "shade"] }
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

Create an in-memory stage and author a sphere:

```rust
use openusd::usd;

let stage = usd::Stage::builder().in_memory("root.usda")?;

stage.define_prim("/World")?.set_type_name("Xform")?;
stage.define_prim("/World/Sphere")?.set_type_name("Sphere")?;
stage.set_default_prim("World")?;

stage.create_attribute("/World/Sphere.radius", "double")?.set(2.5_f64)?;
```

For typed schema access, register the enabled schema families when opening the
stage. This example reads a mesh's points and finds a material's surface shader:

```rust,no_run
use openusd::{gf, usd};
use openusd_schemas::geom::{self, PointBasedSchema};
use openusd_schemas::shade;

// Register schema types, inheritance, and property fallback values.
let stage = usd::Stage::builder()
    .schema_registry(openusd_schemas::schema_registry())
    .open("scene.usda")?;

// Import `PointBasedSchema` to use its accessors on `Mesh`.
if let Some(mesh) = geom::Mesh::get(&stage, "/World/Mesh")? {
    if let Some(points) = mesh.points_attr().get::<Vec<gf::Vec3f>>()? {
        println!("{} points", points.len());
    }
}

// Follow the material's surface terminal to the shader driving it.
if let Some(material) = shade::Material::get(&stage, "/World/Material")? {
    if let Some(terminal) = material.surface_source(&[])? {
        for source in terminal.sources() {
            if let Some(shader) = source.shader() {
                println!("surface shader: {:?}", shader.node_def().shader_id()?);
            }
        }
    }
}
```

More runnable examples, including file conversion and variant authoring, are
available in [`crates/openusd/examples`](crates/openusd/examples):

```sh
cargo run -p openusd --example dump_usdc -- path/to/file.usdc
cargo run -p openusd --example author_variant_and_reference
```

## Minimum supported Rust version (MSRV)

The MSRV is declared in the workspace's [Cargo.toml](Cargo.toml) as
`rust-version` and may increase as the project develops.
[rust-toolchain.toml](rust-toolchain.toml) pins the toolchain used for
development and CI.

## License

Licensed under the [MIT License](LICENSE), with exceptions for vendored OpenUSD
schemas and generated code covered by the Tomorrow Open Source Technology
License 1.0. See the [OpenUSD notices](vendor/OpenUSD/README.md) for details.
