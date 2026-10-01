# Vendored OpenUSD schema definitions

Each `<library>/schema.usda` is copied from
[OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD) v26.05 (commit
`2095fafafd033fa23386d7ec6d58c7cc33974518`), where it lives at
`pxr/usd/<library>/schema.usda`. These are the definitions upstream's own
`usdGenSchema` reads, and this crate's `build.rs` generates its views from
them through `openusd-build`.

Beside the families that register metadata fields, `<library>/plugInfo.json`
is copied from the same commit, where it lives at
`pxr/usd/<library>/plugInfo.json`. `build.rs` reads the `SdfMetadata` block of
each, which is where upstream declares those fields.

`usdShaders/shaderDefs.usda` is copied from the same commit, where it lives at
`pxr/usd/plugin/usdShaders/shaders/shaderDefs.usda`. It defines the shader
nodes `UsdPreviewSurface`, `UsdUVTexture` and their companions, which `build.rs`
generates the `shade::nodes` views of.

`usd/schema.usda` is here because every other file sublayers it: it declares
`Typed`, `APISchemaBase` and the core API schemas the domain families inherit
from. This crate generates nothing from it: the core crate carries the `usd`
family itself, its views included, in a file generated once and committed.

Every file is verbatim but that one, which adds a `SchemaBase` class upstream
registers through `plugInfo.json` instead. The addition is marked in the file
itself; `vendor/OpenUSD/README.md` in the repository says why it is needed and
what to re-apply after vendoring a newer OpenUSD.

## License

This subtree is licensed under the Tomorrow Open Source Technology License
1.0, not this crate's MIT license. `LICENSE` and `NOTICE.txt` are upstream's
own, copied beside the definitions as §4 of that license requires.
