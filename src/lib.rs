//! Native Rust implementation of [Universal Scene Description](https://openusd.org) (USD).
//!
//! Reads and writes `.usda` (text), `.usdc` (binary), and `.usdz` (packaged)
//! files without any C++ dependencies.
//!
//! # Modules
//!
//! | Module | Purpose |
//! |--------|---------|
//! | [`sdf`] | Core data model — [`Value`](sdf::Value), [`Path`](sdf::Path), [`Spec`](sdf::Spec), [`AbstractData`](sdf::AbstractData) trait, mutable [`Data`](sdf::Data), and schema field keys. |
//! | [`usda`] | Text format. [`TextReader`](usda::TextReader) parses and [`TextWriter`](usda::TextWriter) emits `.usda` files. |
//! | [`usdc`] | Binary format. [`CrateData`](usdc::CrateData) parses and [`CrateWriter`](usdc::CrateWriter) emits `.usdc` files. |
//! | [`usdz`] | Archive format. [`Archive`](usdz::Archive) reads and [`ArchiveWriter`](usdz::ArchiveWriter) emits `.usdz` packages. |
//! | [`ar`] | Asset resolution. [`Resolver`](ar::Resolver) trait maps asset paths (`@...@`) to physical locations; [`DefaultResolver`](ar::DefaultResolver) searches the filesystem. |
//! | [`layer`] | Layer collection. [`Collector`](layer::Collector) recursively loads all layers from a root file. |
//! | [`pcp`] | Prim Cache Population — the composition engine. Implements LIVRPS strength ordering, per-prim index caching, and namespace mapping via [`MapFunction`](pcp::MapFunction). |
//! | [`usd`] | Composed stage API. [`Stage`](usd::Stage) merges opinions across layers using [LIVERPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering. |
//! | [`expr`] | Variable expression parser and evaluator for USD's `\`...\`` expression syntax. |
//! | [`math`] | Shared 4×4 row-major matrix helpers used by the schema layer. |
//! | [`schemas`] | Domain-schema readers (UsdPhysics, UsdSkel, …) — non-core extensions, feature-gated. |
//!
//! # Quick start
//!
//! ```no_run
//! use openusd::usd::{self, PrimPredicate};
//!
//! let stage = usd::Stage::open("scene.usda").unwrap();
//!
//! stage.traverse(PrimPredicate::DEFAULT, |prim_path| {
//!     println!("{prim_path}");
//! }).unwrap();
//! ```

pub mod ar;
pub mod expr;
pub mod layer;
pub mod math;
pub mod pcp;
pub mod schemas;
pub mod sdf;
pub mod usd;
pub mod usda;
pub mod usdc;
pub mod usdz;

pub use half::f16;
pub use layer::{Collector, DependencyKind};
