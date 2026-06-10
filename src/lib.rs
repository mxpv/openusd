//! Native Rust implementation of [Universal Scene Description](https://openusd.org) (USD).
//!
//! The crate aims for full feature parity with the C++ reference
//! implementation, and is structured to mirror its layout, so developers
//! familiar with the C++ codebase will find roughly the same modules, types, and
//! primitives ([`sdf`], [`pcp`], [`usd`], …).
//!
//! All major file formats are supported — text (`.usda`), binary (`.usdc`),
//! and archives (`.usdz`) — with no C++ dependencies.
//!
//! # Modules
//!
//! | Module | Purpose |
//! |--------|---------|
//! | [`sdf`] | Core data model — [`Value`](sdf::Value), [`Path`](sdf::Path), [`Spec`](sdf::Spec), [`AbstractData`](sdf::AbstractData) trait, mutable [`Data`](sdf::Data), and schema field keys. |
//! | [`usda`] | Text format. [`usda::parse`] / [`usda::read_file`] parse and [`TextWriter`](usda::TextWriter) emits `.usda` files. |
//! | [`usdc`] | Binary format. [`CrateData`](usdc::CrateData) parses and [`CrateWriter`](usdc::CrateWriter) emits `.usdc` files. |
//! | [`usdz`] | Archive format. [`Archive`](usdz::Archive) reads and [`ArchiveWriter`](usdz::ArchiveWriter) emits `.usdz` packages. |
//! | [`ar`] | Asset resolution. [`Resolver`](ar::Resolver) trait maps asset paths (`@...@`) to physical locations; [`DefaultResolver`](ar::DefaultResolver) searches the filesystem. |
//! | [`layer`] | Layer collection. [`Collector`](layer::Collector) recursively loads all layers from a root file. |
//! | [`pcp`] | Prim Cache Population — the composition engine. Implements LIVRPS strength ordering, per-prim index caching, and namespace mapping via [`MapFunction`](pcp::MapFunction). |
//! | [`usd`] | Composed stage API. [`Stage`](usd::Stage) merges opinions across layers using [LIVERPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering. |
//! | [`gf`] | Graphics foundations — linear algebra types (`Vec3f`, `Matrix4d`, …). |
//! | [`tf`] | Tools foundation — [`Token`](tf::Token), the interned-identifier string. |
//! | [`schemas`] | Domain-schema readers (UsdPhysics, UsdSkel, …) — non-core extensions, feature-gated. |
//!
//! # Quick start
//!
//! Open a stage and walk its composed prims (`DEFAULT` prunes inactive,
//! unloaded, and abstract subtrees):
//!
//! ```no_run
//! use openusd::usd;
//!
//! let stage = usd::Stage::open("scene.usda")?;
//! stage.traverse(usd::PrimPredicate::DEFAULT, |prim_path| {
//!     println!("{prim_path}");
//! })?;
//! # Ok::<(), anyhow::Error>(())
//! ```
//!
//! Query the composed scene through `UsdPrim` / `UsdAttribute`-style handles
//! and resolve an attribute's value across all composition arcs:
//!
//! ```no_run
//! use openusd::usd;
//!
//! let stage = usd::Stage::open("scene.usda")?;
//!
//! let sphere = stage.prim_at("/World/Sphere");
//! println!("type: {:?}", sphere.type_name()?);
//!
//! let radius = stage.attribute_at("/World/Sphere.radius");
//! if let Some(r) = radius.get::<f64>()? {
//!     println!("radius = {r}");
//! }
//! # Ok::<(), anyhow::Error>(())
//! ```
//!
//! Author a scene in memory, then read a value back — no files involved:
//!
//! ```
//! use openusd::usd;
//!
//! let stage = usd::Stage::builder().in_memory("root.usda")?;
//!
//! stage.define_prim("/World")?.set_type_name("Xform")?;
//! stage.define_prim("/World/Sphere")?.set_type_name("Sphere")?;
//! stage.set_default_prim("World")?;
//!
//! stage.create_attribute("/World/Sphere.radius", "double")?.set(2.5_f64)?;
//! let radius = stage.attribute_at("/World/Sphere.radius").get::<f64>()?;
//! assert_eq!(radius, Some(2.5));
//!
//! # Ok::<(), anyhow::Error>(())
//! ```
//!
//! Configure how a stage is opened through [`StageBuilder`](usd::StageBuilder) —
//! restrict population to a subtree, leave payloads unloaded, and inspect any
//! recoverable composition errors collected while loading:
//!
//! ```no_run
//! use openusd::usd;
//!
//! let stage = usd::Stage::builder()
//!     .mask(usd::StagePopulationMask::new(["/World/Hero"]))
//!     .load(usd::InitialLoadSet::LoadNone)
//!     .open("scene.usda")?;
//!
//! for err in stage.composition_errors() {
//!     eprintln!("warning: {err}");
//! }
//! # Ok::<(), anyhow::Error>(())
//! ```

pub mod ar;
pub mod gf;
pub mod layer;
pub mod pcp;
pub mod schemas;
pub mod sdf;
pub mod tf;
pub mod usd;
pub mod usda;
pub mod usdc;
pub mod usdz;

pub use layer::{Collector, DependencyKind};
