# Vendored OpenUSD schema data

`usd/generatedSchema.usda` is copied verbatim, with no modifications, from
[OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD) v26.05 (commit
`2095fafafd033fa23386d7ec6d58c7cc33974518`), where it lives at
`pxr/usd/usd/generatedSchema.usda`. It is the flattened schema data C++ loads
for the core `usd` library.

`usd/manifest.usda` is not an upstream file. It carries what a flattened layer
drops — each schema's kind, its bases, and a multiple-apply schema's property
namespace prefix — which C++ keeps in `pxr/usd/usd/plugInfo.json`. Its contents
are derived from that file and from the `customData` of
`pxr/usd/usd/schema.usda`. See `SchemaRegistryBuilder::family` for the format.

It therefore declares one schema the schematics does not: `SchemaBase`, the
root `plugInfo.json` puts above both `Typed` and `APISchemaBase`. An abstract
schema needs no class prim, since nothing is ever defined as one.

## Regenerating

The `.usdc` beside each `.usda` holds the same scene description in the binary
crate format, and is what `SchemaRegistry::builder` embeds. The text
is what to review and edit; the binary is a build artifact that happens to be
committed. After changing either `.usda`, or after vendoring a
newer OpenUSD, regenerate both from the workspace root:

```bash
cargo run -p openusd --example convert -- \
    crates/openusd/schemas/usd/generatedSchema.usda \
    crates/openusd/schemas/usd/generatedSchema.usdc
cargo run -p openusd --example convert -- \
    crates/openusd/schemas/usd/manifest.usda \
    crates/openusd/schemas/usd/manifest.usdc
```

The `vendored_usdc_matches_usda` test in `usd::schema_registry` fails when the
two encodings disagree, so a forgotten regeneration does not reach a release.

## License

OpenUSD is licensed under the Tomorrow Open Source Technology License 1.0,
reproduced here in `LICENSE` along with the upstream `NOTICE.txt`. That license
governs this directory; the rest of the crate is MIT.
