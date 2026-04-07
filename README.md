# openusd

[![Crates.io Version](https://img.shields.io/crates/v/openusd)](https://crates.io/crates/openusd)
[![docs.rs](https://img.shields.io/docsrs/openusd)](https://docs.rs/crate/openusd/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/mxpv/openusd/graph/badge.svg?token=LAPV2T3AI8)](https://codecov.io/gh/mxpv/openusd)
[![dependency status](https://deps.rs/repo/github/mxpv/openusd/status.svg)](https://deps.rs/repo/github/mxpv/openusd)

`openusd` is a Rust implementation of Pixar's [Universal Scene Description](https://openusd.org/release/index.html) (USD) format with no C++ dependencies.

## Documentation

The following list of docs was used during crate development:

- [User documentation](https://openusd.org/release/index.html)
- [Book of USD](https://remedy-entertainment.github.io/USDBook/)
- [API Documentation](https://openusd.org/release/api/index.html)
- [USD Cookbook](https://github.com/ColinKennedy/USD-Cookbook)

For a detailed comparison with the C++ reference implementation and current progress, see the [Roadmap](ROADMAP.md).

## Features

- Reads all major USD formats: `.usda` (text), `.usdc` (binary), and `.usdz` (archive).
- Composed [`Stage`](src/stage.rs) with full [LIVERPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering (sublayers, inherits, variants, references, payloads, specializes).
- Recursive [layer collection](src/compose) with cycle detection, format auto-detection, and expression evaluation.
- List-edit composition (`prepend`, `append`, `add`, `delete`, `explicit`) across layers.
- Generic typed field access via `Stage::field<T>` with `TryFrom<Value>` conversion.
- [Variable expression](src/expr.rs) evaluator for USD's [expression syntax](https://openusd.org/dev/user_guides/variable_expressions.html).
- [Asset resolution](src/ar.rs) with pluggable `Resolver` trait, filesystem `DefaultResolver`, and search paths.

If you encounter a file that can't be read, please open an [issue](https://github.com/mxpv/openusd/issues) and attach the USD file for investigation.

## Example

```rust,no_run
use openusd::{sdf::FieldKey, Stage};

let stage = Stage::open("scene.usda")?;

// Traverse all prims in the composed scene graph.
stage.traverse(|path| {
    println!("{path}");
})?;

// Read a typed field value (generic over TryFrom<Value>).
let active: Option<bool> = stage.field("/World/Cube", FieldKey::Active)?;

// Access children composed across layers, references, and payloads.
let children = stage.prim_children("/World/Cube")?;
let properties = stage.prim_properties("/World/Cube")?;
```

## Getting started

To begin, simply clone the repository including its submodules.
Make sure you have [`Rust`](https://www.rust-lang.org/tools/install) installed on your system, `rustup` will do the rest.

```bash
# Clone the project
git clone --recurse-submodules https://github.com/mxpv/openusd.git
cd openusd

# Use cargo to build, test, lint, etc.
cargo build
cargo clippy

# Run examples
cargo run --example dump_usdc -- ~/caldera/layers/cameras.usd
```

## Minimum supported Rust version (MSRV)

The project typically targets the latest stable Rust version. Please refer to [rust-toolchain.toml](./rust-toolchain.toml) for exact version currently used by our CIs.

> [!NOTE]
> This crate is under active development. No API stability is guaranteed until version 1.0.
