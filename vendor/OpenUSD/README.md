# OpenUSD

The licence and notice for everything this workspace takes from
[OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD), at v26.05 (commit
`2095fafafd033fa23386d7ec6d58c7cc33974518`). The content itself lives with the
crate that reads it; this records where it came from and what governs it.

| Path | What it is |
|---|---|
| `crates/openusd-schemas/schemas/<library>/schema.usda` | The schema definitions, copied from `pxr/usd/<library>/schema.usda`. That crate's `build.rs` generates its views from them, so they are vendored inside it: Cargo cannot package a path outside a crate. |
| `crates/openusd-build/fixtures/testUsdGenSchema/` | Upstream's own `usdGenSchema` test corpus — the schemas it generates from, the failure cases it rejects, and the baselines it produces. |
| `crates/openusd-build/fixtures/upstream/<library>/generatedSchema.usda` | The flattened schema data upstream generates for each domain library, and the only oracle here that this project did not produce. |
| `crates/openusd/src/usd/core_schemas.rs` | Generated from the vendored `usd/schema.usda`, and so a derivative work of it. It is committed rather than built because `openusd-build` depends on `openusd` and could not run in its build script; that crate's `core_family` test regenerates it and fails when it drifts. |

Only the first and last of those ship: the fixtures are test data, and
`openusd-build` excludes `fixtures/` from its package.

## Modifications

Every vendored file is verbatim but one. `usd/schema.usda` adds a `SchemaBase`
class, which upstream registers through `pxr/usd/usd/plugInfo.json` instead and
which `openusd` reads no plugInfo to find; without it
`UsdSchemaRegistry::IsA` would stop one level short of where C++ stops. The
addition is marked in the file's own documentation and carries nothing else
with it — `SchemaBase` declares no property, so no schema's fallbacks change,
and a class that inherits nothing already derives from it, so no other class
names it.

After vendoring a newer OpenUSD, re-apply that class and run `openusd-build`'s
`core_family` test with `UPDATE_EXPECTED=1` to rewrite `core_schemas.rs`.

## Licence

OpenUSD is licensed under the Tomorrow Open Source Technology License 1.0,
reproduced in `LICENSE`, with upstream's `NOTICE.txt` beside it. That licence
governs the paths above; the rest of the workspace is MIT.

`openusd` and `openusd-schemas` each publish some of that content, and §4(a)
and §4(d) ask for the licence and the notices to travel with it, so both carry
their own copy under `third-party/`. Those are copies of the two files here:
change one and change all three.
