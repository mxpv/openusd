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

Ten schema families ship here, each behind its own feature flag, so a build
compiles only the domains it touches:

`UsdGeom` · `UsdLux` · `UsdMedia` · `UsdPhysics` · `UsdProc` · `UsdRender` ·
`UsdShade` · `UsdSkel` · `UsdUI` · `UsdVol`

The two crates share a version and release together.

## Usage

Add both crates — a schema view is a handle on a stage the core opens — and
enable the families you need:

```toml
[dependencies]
openusd = "0.7"
openusd-schemas = { version = "0.7", features = ["geom", "lux"] }
```

Nothing is enabled by default.

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

`lux`, `media`, `proc`, `skel`, and `vol` build on the `geom` trait chain and
enable it transitively.

## Example

Open a stage with the core crate, then read a `Mesh` and its point positions and
normals through the `geom` views:

```rust,no_run
// `PointBased` is brought in so its inherited accessors resolve on the view.
use openusd_schemas::geom::{self, PointBased};
use openusd::{gf, usd};

let stage = usd::Stage::open("scene.usda")?;

if let Some(mesh) = geom::Mesh::get(&stage, "/World/Mesh")? {
    // `points_attr` / `normals_attr` are inherited from the `PointBased` trait
    // up the chain. `point3f[]` and `normal3f[]` both decode to `Vec<gf::Vec3f>`,
    // so `get` extracts them directly.
    let points = mesh.points_attr().get::<Vec<gf::Vec3f>>()?;
    let normals = mesh.normals_attr().get::<Vec<gf::Vec3f>>()?;

    if let Some(points) = points {
        println!("{} points, normals authored: {}", points.len(), normals.is_some());
    }
}
```

Values a prim does not author fall back to what the schema declares, resolved
through the core's `usd::SchemaRegistry`.

## License

Licensed under the [MIT License](https://github.com/mxpv/openusd/blob/main/LICENSE).
