# openusd-build

Generates Rust schema views from OpenUSD `schema.usda` files, the way
`usdGenSchema` generates C++ ones. It is a build dependency: a crate describes
its schema libraries in `build.rs`, and the generated views are included into
its own modules.

```rust
// build.rs
fn main() -> Result<(), openusd_build::Error> {
    openusd_build::configure()
        .search_path("schemas")
        .schema("schemas/usdGeom/schema.usda")
        .generate()
}
```

```rust
// src/lib.rs
pub mod geom {
    openusd::include_schema!("usdGeom");
}
```

A library is named by the `libraryName` its `schema.usda` declares, which is
what `include_schema!` asks for. Generating from several schemas in one run is
one `.schema(..)` call each; a class that inherits from a library this run does
not generate needs that library declared with `.extern_library(..)` so the
generated code can name its types.

## Status

The configuration surface above is complete. Reading a `schema.usda` and
emitting from it is not implemented yet, so `generate` writes no files, and the
crate is not published until it does.

## License

Licensed under the [MIT License](https://github.com/mxpv/openusd/blob/main/LICENSE).
