# openusd-build

[![Crates.io Version](https://img.shields.io/crates/v/openusd-build)](https://crates.io/crates/openusd-build)
[![docs.rs](https://img.shields.io/docsrs/openusd-build)](https://docs.rs/crate/openusd-build/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)

`openusd-build` generates Rust code from OpenUSD `schema.usda` files. It serves
the same purpose as `usdGenSchema` for C++: generating typed schema views,
property accessors, and the schema definitions used by a stage's registry.

The generator uses
[`openusd`](https://github.com/mxpv/openusd/tree/main/crates/openusd)
to open schema libraries as stages and resolve their sublayers and inheritance.
It is written in Rust and requires no C++ or Python dependencies.

Add it as a build dependency, configure your schema libraries in `build.rs`,
and include the generated code with `openusd::include_schema!`.
[`openusd-schemas`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas)
uses this workflow to build its ten standard schema families.

Each library produces a single Rust file containing:

- A `tokens` module with constants for schema names, property names, and token
  values.
- A `SCHEMAS` constant with schema declarations, including property fallbacks,
  allowed tokens, and inheritance. The registry accepts these declarations
  directly, without parsing schema files at runtime.
- Typed schema views with accessors for declared and inherited properties.
- Optional Rust enums generated from token properties' `allowedTokens`.

## Usage

```toml
[dependencies]
openusd = "0.7"

[build-dependencies]
openusd-build = "0.7"
```

```rust
// build.rs
fn main() -> Result<(), openusd_build::Error> {
    openusd_build::configure()
        .search_path("schemas")
        .schema("schemas/usdGeom/schema.usda")
        .generate()
}
```

Use the `libraryName` declared in `schema.usda` to include the generated code:

```rust
// src/lib.rs
pub mod geom {
    openusd::include_schema!("usdGeom");
}
```

Register the generated schema definitions so the stage can recognize schema
types and supply fallback values for properties without authored values:

```rust
use openusd::{gf, usd};

let registry = usd::SchemaRegistry::builder().register(geom::SCHEMAS).build()?;
let stage = usd::Stage::builder().schema_registry(registry).open("scene.usda")?;

let mesh = geom::Mesh::get(&stage, "/World/Mesh")?.expect("a Mesh");
let points = mesh.points_attr().get::<Vec<gf::Vec3f>>()?;
```

To generate several libraries, call `.schema(..)` once for each library. If a
schema inherits from a library generated elsewhere, use `.extern_library(..)`
to specify the Rust module containing that library's views.

## The generated output

[`fixtures/tiny/expected.rs`](https://github.com/mxpv/openusd/blob/main/crates/openusd-build/fixtures/tiny/expected.rs)
shows the complete output for a small test library. For a larger example, see
the generated core `usd` schemas in
[`core_schemas.rs`](https://github.com/mxpv/openusd/blob/main/crates/openusd/src/usd/core_schemas.rs).

Generated property methods use names and documentation from the source schema.
For example, an attribute accessor includes the declared type, fallback value,
and Rust type used to read it:

```rust
/// The bounds, in the shape's own space.
///
/// Declared `double3 extent = (1.0, 1.0, 1.0)`. Read it with
/// `get::<::openusd::gf::Vec3d>()`.
fn extent_attr(&self) -> ::openusd::usd::Attribute {
    self.prim().attribute(tokens::EXTENT)
}
```

## License

Licensed under the [MIT License](https://github.com/mxpv/openusd/blob/main/LICENSE).
