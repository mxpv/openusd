# openusd

[![Crates.io Version](https://img.shields.io/crates/v/openusd)](https://crates.io/crates/openusd)
[![docs.rs](https://img.shields.io/docsrs/openusd)](https://docs.rs/crate/openusd/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/mxpv/openusd/graph/badge.svg?token=LAPV2T3AI8)](https://codecov.io/gh/mxpv/openusd)
[![dependency status](https://deps.rs/repo/github/mxpv/openusd/status.svg)](https://deps.rs/repo/github/mxpv/openusd)

`openusd` is a Rust implementation of Pixar's [Universal Scene Description](https://openusd.org/release/index.html) (USD) format with no C++ dependencies.

For a detailed comparison with the C++ reference implementation and current progress, see the [Roadmap](ROADMAP.md).

## Features

- File formats — reads and writes `.usda` (text), `.usdc` (binary), and `.usdz` (archive).
- Fully featured [composition engine](src/pcp)
  - [LIVRPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering with sublayers, inherits, variants, references, payloads, and specializes.
  - [List-edit composition](https://openusd.org/release/glossary.html#usdglossary-listediting) across layers.
  - Per-prim node graph with namespace mapping across composition arcs.
  - Non-destructive namespace remapping via [relocates](https://openusd.org/release/glossary.html#usdglossary-relocates).
  - Permission restrictions — a direct arc to a `permission = private` prim is reported and its opinions are dropped from value resolution.
  - [Variable expressions](https://openusd.org/dev/user_guides/variable_expressions.html) with string interpolation and built-in functions.
- Composed [`Stage`](src/usd/stage.rs)
  - Recursive layer collection with cycle detection and pluggable asset resolution.
  - Lazy per-prim composition with caching, depth-first traversal, and typed field access.
  - Prim status, schema, and model-hierarchy queries on composed prims.
  - Predicate-based traversal that prunes inactive, unloaded, or abstract subtrees.
  - Working-set control via population masks and initial payload-loading rules.
  - [Session layer](https://openusd.org/release/glossary.html#usdglossary-sessionlayer) and [variant fallback](https://openusd.org/release/glossary.html#usdglossary-variantset) selections via `StageBuilder`.
  - Recoverable error handling via `StageBuilder::on_error` callback.
- Authoring API
  - Build USD scenes through [layer](src/sdf/layer.rs)- and [stage](src/usd/stage.rs)-tier APIs.
  - Typed [spec views](src/sdf/spec.rs) for compile-time-checked per-kind editing.
  - Composed [prim, attribute, and relationship handles](src/usd/prim.rs) with chained fluent edits.
  - `EditTarget` routing of opinions to a specific layer; in-memory stages for anonymous-root authoring.
  - Applied API schema authoring.
- Domain schema readers (opt-in [feature flags](#feature-flags), layered on the composed stage)
  - [`UsdGeom`](src/schemas/geom) — Imageable / Boundable / Xformable, intrinsic shapes, Camera, Mesh, Curves, PointInstancer.
  - [`UsdLux`](src/schemas/lux) — concrete light prims plus LightAPI / ShapingAPI / ShadowAPI and friends.
  - [`UsdPhysics`](src/schemas/physics) — scene, joints, collisions, and per-DOF limit / drive APIs.
  - [`UsdRender`](src/schemas/render) — RenderSettings / RenderProduct / RenderVar / RenderPass plus render-product/var conformance helpers.
  - [`UsdSkel`](src/schemas/skel) — schema reader plus a pure-math skinning toolkit (topology, anim mapping, LBS, blend shapes).
  - [`UsdShade`](src/schemas/shade) — Material / NodeGraph / Shader, connectable inputs / outputs, MaterialBindingAPI, and UsdPreviewSurface.

If you encounter a file that can't be read, please open an [issue](https://github.com/mxpv/openusd/issues) and attach the USD file for investigation.

## Compliance

The [AOUSD Core Specification 1.0](https://aousd.org/blog/foundations-of-open-3d-development-introducing-aousd-core-specification-1-0/) has been officially ratified. As part of the specification, sample implementations for compliance testing are provided as Python scripts with JSON baselines. Where JSON baselines are available, the crate parses them and verifies that its output matches.

| Area | Status | Notes |
|------|--------|-------|
| [Text format parsing](vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/text) | :white_check_mark:&nbsp;Passes | 10 tests against JSON baselines |
| [Binary format parsing](vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary) | :white_check_mark:&nbsp;Passes | 42 tests manually backported from the reference suite's `test_binary.py` in [`tests/binary_format.rs`](tests/binary_format.rs) |
| [Composition](vendor/core-spec-supplemental-release_dec2025/composition/tests/assets) | :white_check_mark:&nbsp;Passes | [`tests/composition.rs`](tests/composition.rs) verifies composed prim/property/child existence (text + binary). Exact `pcp.txt` result diffing (strength order, stacks) is not yet covered |
| [Value resolution](vendor/core-spec-supplemental-release_dec2025/value_resolution) | :ballot_box_with_check:&nbsp;Partial | 8 tests in [`tests/value_resolution.rs`](tests/value_resolution.rs) (defaults, time samples, value clips). Excludes attribute fallbacks and splines |
| [Combine chains](vendor/core-spec-supplemental-release_dec2025/data_types/tests/combine_chain) | :white_check_mark:&nbsp;Passes | [`ListOp::combined_with`](src/sdf/list_op.rs) and [`ListOp::reduced`](src/sdf/list_op.rs) against JSON baselines |

## Getting started

> [!WARNING]
> This crate is under active development. No API stability is guaranteed until version 1.0.

Make sure you have [`Rust`](https://www.rust-lang.org/tools/install) installed on your system, `rustup` will do the rest.

Add the crate to your `Cargo.toml` (or run `cargo add openusd`):

```toml
[dependencies]
openusd = "0.4"
```

If you need the latest unreleased changes, depend on the crate directly from the
git repository:

```toml
[dependencies]
openusd = { git = "https://github.com/mxpv/openusd.git" }
```

To pin a specific revision, add a `rev` field:

```toml
[dependencies]
openusd = { git = "https://github.com/mxpv/openusd.git", rev = "4c02084" }
```

### Feature flags

The core library (formats, composition, and the `Stage` API) is always
available. Domain schema readers are gated behind opt-in features so you only
pay for what you use:

| Feature | Enables |
|---------|---------|
| `geom` | [`UsdGeom`](src/schemas/geom) — Imageable, Boundable, Xformable, shapes, Camera, Mesh, Curves, PointInstancer |
| `lux` | [`UsdLux`](src/schemas/lux) — light prims and Light/Shaping/Shadow APIs |
| `physics` | [`UsdPhysics`](src/schemas/physics) — scenes, joints, collisions, limit/drive APIs |
| `render` | [`UsdRender`](src/schemas/render) — RenderSettings, RenderProduct, RenderVar, RenderPass |
| `skel` | [`UsdSkel`](src/schemas/skel) — skeleton reader and skinning toolkit |
| `shade` | [`UsdShade`](src/schemas/shade) — materials, shader networks, bindings, UsdPreviewSurface |
| `serde` | `serde` support for serializing core types |

```toml
[dependencies]
openusd = { version = "0.4", features = ["geom", "lux"] }
```

## Example

```rust,no_run
use openusd::{ar, sdf, usd};

// Open a stage with default settings (DefaultResolver, strict errors, all payloads loaded).
let stage = usd::Stage::open("scene.usda")?;

// Or configure via the builder:
let stage = usd::Stage::builder()
    // Use a custom asset resolver (default: DefaultResolver).
    .resolver(ar::DefaultResolver::new())
    // Handle composition errors instead of failing (default: hard error).
    .on_error(|err| {
        eprintln!("warning: {err}");
        Ok(()) // skip missing dependency and continue
    })
    // Leave payload arcs unloaded (default: LoadAll).
    .initial_load_set(usd::InitialLoadSet::LoadNone)
    // Restrict the stage to a subtree of interest.
    .population_mask(usd::StagePopulationMask::new(["/World/Hero"]))
    .open("scene.usda")?;

// Traverse prims filtered by a predicate. DEFAULT skips inactive/unloaded/abstract
// subtrees and stops at instances; ALL visits every composed prim.
stage.traverse(usd::PrimPredicate::DEFAULT, |path| println!("{path}"))?;
stage.traverse(usd::PrimPredicate::ALL, |path| println!("{path}"))?;

// Composed prim queries.
let active = stage.is_active("/World/Hero")?;
let is_model = stage.is_model("/World/Hero")?;
let type_name = stage.type_name("/World/Hero")?;

// Read a typed field value.
let visible: Option<bool> = stage.field("/World/Hero", sdf::FieldKey::Active)?;

// Access children composed across layers, references, and payloads.
let children = stage.prim_children("/World/Hero")?;
let properties = stage.prim_properties("/World/Hero")?;

// Author into an in-memory stage.
let stage = usd::Stage::builder().in_memory("anon.usda")?;
let mesh = stage
    .define_prim("/World/Mesh")?
    .set_type_name("Mesh")?
    .set_kind("component")?;
let radius = mesh
    .create_attribute("radius", "double")?
    .set_variability(sdf::Variability::Uniform)?
    .set(sdf::Value::Double(1.0))?;
let binding = mesh
    .create_relationship("material:binding")?
    .add_target(sdf::Path::new("/World/Material")?)?;
```

More runnable examples live in the [`examples/`](examples) directory:

```bash
cargo run --example dump_usdc -- path/to/file.usdc
cargo run --example write_usda
cargo run --example author_variant_and_reference
```

## Minimum supported Rust version (MSRV)

The project targets stable Rust and aims for the latest Rust editions. The MSRV
is bumped on an as-needed basis, whenever it makes sense for the project. Please
refer to [rust-toolchain.toml](./rust-toolchain.toml) for the exact version
currently used by our CIs.

## License

Licensed under the [MIT License](LICENSE).
