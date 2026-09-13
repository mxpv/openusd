# Vendored OpenUSD schema definitions

Each `<library>/schema.usda` is copied from
[OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD) v26.05 (commit
`2095fafafd033fa23386d7ec6d58c7cc33974518`), where it lives at
`pxr/usd/<library>/schema.usda`. These are the definitions upstream's own
`usdGenSchema` reads, and this crate's `build.rs` generates its views from
them through `openusd-build`.

`usd/schema.usda` is here because every other file sublayers it: it declares
`Typed`, `APISchemaBase` and the core API schemas the domain families inherit
from. No views are generated for it — the core crate carries the `usd` family
itself, and `openusd::usd` holds its hand-written views.

Every file is verbatim but that one, which adds a `SchemaBase` class upstream
registers through `plugInfo.json` instead. The addition is marked in the file
itself; `vendor/OpenUSD/README.md` in the repository says why it is needed and
what to re-apply after vendoring a newer OpenUSD.

## License

This subtree is licensed under the Tomorrow Open Source Technology License
1.0, not this crate's MIT license. `LICENSE` and `NOTICE.txt` are upstream's
own, copied beside the definitions as §4 of that license requires.
