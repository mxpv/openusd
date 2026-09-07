# Vendored OpenUSD test schemas

`testUsdGenSchema/` holds the schema files upstream's own `usdGenSchema` test
uses, copied verbatim and unmodified from
[OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD) v26.05 (commit
`2095fafafd033fa23386d7ec6d58c7cc33974518`), where they live at
`pxr/usd/usd/testenv/testUsdGenSchema/`.

Two kinds of file are here:

- the schema sources: `schema.usda`, the sublayer beside it and the codeless
  and literal-identifier variants, plus `schemaFail.usda` and `schemaFail2.usda`
  through `schemaFail24.usda`, each of which upstream expects to be rejected.
- `baseline/<case>/generatedSchema.usda`, the flattened schema data upstream
  generates from those sources. The generated C++ beside them upstream is not
  copied, since nothing here compares against it.

They are test input, so they ship with the repository and not with the crate:
`Cargo.toml` excludes `fixtures/` from the package. A published
`openusd-build` therefore never looks for them.

## What we do and do not take from them

The baselines are compared for what they *mean* — the same specs carrying the
same fields — rather than byte for byte, since the schematics is the
contractual output and its formatting is not.

The failure files are used selectively. Each is a test only where it exercises
a rule this crate keeps; the rest are listed, with the reason their schema is
accepted, in the test module that reads them. A rule upstream enforces to
protect a C++ build is not a rule here.

## License

This subtree is licensed under the Tomorrow Open Source Technology License 1.0
(`LICENSE`), with attribution in `NOTICE.txt`. The rest of the crate is MIT.
