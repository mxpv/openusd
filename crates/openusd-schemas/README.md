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
openusd = "0.9"
openusd-schemas = { version = "0.9", features = ["geom", "lux"] }
```

Nothing is enabled by default. A family that builds on another's views enables
it, so `lux`, `media`, `physics`, `proc`, `render`, `shade`, `skel` and `vol`
each pull in `geom`, and `lux`, `physics` and `render` pull in `shade`.
[Schema families](#schema-families) lists each feature and what it covers.

Hand `schema_registry()` to the stage you open. It is what makes a prim a
`Mesh`, what resolves the fallback a schema declares for a property nothing
authored, and what answers `is_a` along a schema's inheritance; a stage opened
without it knows only the core `usd` family, and the typed `get` constructors
answer `None`.

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

## Schema families

One feature per family. Each generates a typed view for every class of its
schema library; the notes list what is implemented beside those views and
what remains.

| Feature | Schema | Status | Notes |
|---|---|---|---|
| [`geom`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/geom) | [UsdGeom](https://openusd.org/release/api/usd_geom_page_front.html) | :white_check_mark: | Every schema class: meshes, curves, points, shapes, cameras. Primvars, transform stacks and `XformCache`, bounds and `BBoxCache`, point instancers, subsets, motion, model draw mode, and stage metrics |
| [`lux`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/lux) | [UsdLux](https://openusd.org/release/api/usd_lux_page_front.html) | :white_check_mark: | Light and light-filter prims with the light, shaping and shadow APIs. Light linking, light lists, blackbody color, and lights as shading nodes |
| [`media`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/media) | [UsdMedia](https://openusd.org/release/api/usd_media_page_front.html) | :white_check_mark: | `SpatialAudio`, and `AssetPreviewsAPI` with its thumbnails |
| [`physics`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/physics) | [UsdPhysics](https://openusd.org/release/api/usd_physics_page_front.html) | :white_check_mark: | Scenes, rigid bodies, colliders and collision groups, joints with the limit and drive APIs. Mass properties and scene parsing (`physics::parse`) |
| [`proc`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/proc) | [UsdProc](https://openusd.org/release/api/usd_proc_page_front.html) | :white_check_mark: | `GenerativeProcedural` |
| [`render`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/render) | [UsdRender](https://openusd.org/release/api/usd_render_page_front.html) | :white_check_mark: | Render settings, products, vars and passes. The computed render spec (`render::render_spec`) |
| [`semantics`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/semantics) | [UsdSemantics](https://openusd.org/release/api/class_usd_semantics_labels_a_p_i.html) | :white_check_mark: | `LabelsAPI`, with direct and inherited taxonomies and `LabelsQuery` |
| [`shade`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/shade) | [UsdShade](https://openusd.org/release/api/usd_shade_page_front.html) | :white_check_mark: | Materials, shaders and node graphs. Connections and connectable behaviors, material binding (direct, collection-based and per subset), coordinate systems, node definitions, UDIM textures, and a `UsdPreviewSurface` reader<br>Remaining:<br>- the Sdr shader registry<br>- renderer shader dialects (MDL; MaterialX documents are read by [`openusd-mtlx`](https://github.com/mxpv/openusd/tree/main/crates/openusd-mtlx)) |
| [`skel`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/skel) | [UsdSkel](https://openusd.org/release/api/usd_skel_page_front.html) | :white_check_mark: | Skeletons, animations and blend shapes. Skeleton, animation and skinning queries, joint remapping, and baked skinning |
| [`ui`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/ui) | [UsdUI](https://openusd.org/release/api/usd_u_i_page_front.html) | :white_check_mark: | `Backdrop`, `SceneGraphPrimAPI`, `NodeGraphNodeAPI` and `AccessibilityAPI`. The `uiHints` dictionary |
| [`vol`](https://github.com/mxpv/openusd/tree/main/crates/openusd-schemas/src/vol) | [UsdVol](https://openusd.org/release/api/usd_vol_page_front.html) | :white_check_mark: | `Volume` with its OpenVDB and Field3D field assets. The `ParticleField` Gaussian-splat schemas |

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
