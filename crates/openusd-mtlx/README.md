# openusd-mtlx

A read-only `.mtlx` file format for [openusd](../openusd): a MaterialX
document opens as a USD layer laid out the way C++ OpenUSD's `usdMtlx`
plugin lays it out, so a reference, payload or sublayer naming a `.mtlx`
composes into ordinary `UsdShade` prims.

```rust,no_run
use openusd::usd;

let stage = usd::Stage::builder()
    .format(&openusd_mtlx::MTLX)
    .open("shot.usda")?;
# Ok::<(), openusd::Error>(())
```

Each `surfacematerial` becomes a `Material` at
`/MaterialX/Materials/<name>`, each node a `Shader` whose `info:id` names its
MaterialX nodedef. The nodedefs come from MaterialX 1.39's `stdlib`, `pbrlib`
and `bxdf` libraries, embedded under `libraries/` (Apache-2.0, see
`libraries/LICENSE`), and from those the document declares itself.

Shading the result is a renderer's work, as it is in C++: this crate
translates the document and evaluates nothing.
