# openusd-schemas

[![Crates.io Version](https://img.shields.io/crates/v/openusd-schemas)](https://crates.io/crates/openusd-schemas)
[![docs.rs](https://img.shields.io/docsrs/openusd-schemas)](https://docs.rs/crate/openusd-schemas/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)

Typed Rust APIs for USD's standard schemas, built on [`openusd`](https://github.com/mxpv/openusd/tree/main/crates/openusd).

A USD stage is, underneath, prims carrying loosely typed attributes. This crate
puts the schemas back on top of it: ask a `Mesh` for its points and face counts,
a `Camera` for its focal length, a `Material` for the shader bound to its surface
output, a `Skeleton` for its joints and skinning weights — as ordinary Rust types,
instead of spelling out attribute names and decoding values by hand. Every view
authors as well as reads.

```rust,ignore
let mesh = geom::Mesh::get(&stage, "/World/Mesh")?.unwrap();
let points = mesh.points_attr().get::<Vec<gf::Vec3f>>()?;
```

## Usage

Add both crates — a schema view is a handle on a stage the core opens — and
enable the families you need:

```toml
[dependencies]
openusd = "0.7"
openusd-schemas = { version = "0.7", features = ["geom", "lux"] }
```

Nothing is enabled by default. A family that builds on another's views enables
it, so `lux`, `media`, `physics`, `proc`, `skel` and `vol` each pull in `geom`.

Hand `schema_registry()` to the stage you open. It is what makes a prim a
`Mesh`, what resolves the fallback a schema declares for a property nothing
authored, and what answers `is_a` along a schema's inheritance; a stage opened
without it knows only the core `usd` family, and the typed `get` constructors
answer `None`.

### Feature flags

| Feature | Enables |
|---------|---------|
| `geom` | [`UsdGeom`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/geom) — Imageable, Boundable, Xformable, shapes, Camera, Mesh, Curves, PointInstancer |
| `lux` | [`UsdLux`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/lux) — light prims and Light/Shaping/Shadow APIs |
| `media` | [`UsdMedia`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/media) — SpatialAudio and AssetPreviewsAPI |
| `physics` | [`UsdPhysics`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/physics) — scenes, joints, collisions, limit/drive APIs |
| `proc` | [`UsdProc`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/proc) — GenerativeProcedural |
| `render` | [`UsdRender`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/render) — RenderSettings, RenderProduct, RenderVar, RenderPass |
| `shade` | [`UsdShade`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/shade) — materials, shader networks, bindings, UsdPreviewSurface |
| `skel` | [`UsdSkel`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/skel) — skeleton reader and skinning toolkit |
| `ui` | [`UsdUI`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/ui) — Backdrop, SceneGraphPrimAPI, NodeGraphNodeAPI |
| `vol` | [`UsdVol`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/vol) — Volume, OpenVDBAsset, Field3DAsset |

## Example

Open a stage with the core crate, then read a `Mesh` and its point positions and
normals through the `geom` views:

```rust,no_run
// `PointBasedSchema` is brought in so its inherited accessors resolve.
use openusd_schemas::geom::{self, PointBasedSchema};
use openusd::{gf, usd};

let stage = usd::Stage::builder()
    .schema_registry(openusd_schemas::schema_registry())
    .open("scene.usda")?;

if let Some(mesh) = geom::Mesh::get(&stage, "/World/Mesh")? {
    // `points_attr` / `normals_attr` are inherited from `PointBasedSchema` up
    // the chain. `point3f[]` and `normal3f[]` both decode to `Vec<gf::Vec3f>`,
    // so `get` extracts them directly.
    let points = mesh.points_attr().get::<Vec<gf::Vec3f>>()?;
    let normals = mesh.normals_attr().get::<Vec<gf::Vec3f>>()?;

    if let Some(points) = points {
        println!("{} points, normals authored: {}", points.len(), normals.is_some());
    }
}
```

Values a prim does not author fall back to what the schema declares, resolved
through the registry handed to the builder above.

## Vendored schemas

Every view is generated at build time from the schema definitions under
`schemas/<library>/schema.usda`, copied from OpenUSD v26.05 — the same files
upstream's own `usdGenSchema` reads. `build.rs` runs
[`openusd-build`](https://github.com/mxpv/openusd/tree/main/crates/openusd-build)
over them to emit a family's views, its tokens, and the schema data the
registry reads fallbacks and inheritance from. What is hand-written beside
them is what a property cannot express: a transform stack, a skinning
topology, a computed render spec.

`schemas/README.md` records where each file came from and the one place this
copy departs from upstream.

## License

Licensed under the
[MIT License](https://github.com/mxpv/openusd/blob/main/LICENSE), except for
the schema definitions under `schemas/`, which are copied from OpenUSD and
covered by the Tomorrow Open Source Technology License 1.0. `third-party/`
carries that license and upstream's notice; `vendor/OpenUSD/README.md` in the
repository records which files they are and the one modification made to them.
