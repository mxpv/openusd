//! Native Rust implementation of [Universal Scene Description](https://openusd.org) (USD).
//!
//! Reads `.usda` (text), `.usdc` (binary), and `.usdz` (packaged) files without
//! any C++ dependencies.
//!
//! # Modules
//!
//! | Module | Purpose |
//! |--------|---------|
//! | [`sdf`] | Core data model — [`Value`](sdf::Value), [`Path`](sdf::Path), [`Spec`](sdf::Spec), [`AbstractData`](sdf::AbstractData) trait, and schema field keys. |
//! | [`usda`] | Text format reader. [`TextReader`](usda::TextReader) parses `.usda` files into [`AbstractData`](sdf::AbstractData). |
//! | [`usdc`] | Binary format reader. [`CrateData`](usdc::CrateData) parses `.usdc` files into [`AbstractData`](sdf::AbstractData). |
//! | [`usdz`] | Archive format reader. [`Archive`](usdz::Archive) extracts layers from `.usdz` packages. |
//! | [`ar`] | Asset resolution. [`Resolver`](ar::Resolver) trait maps asset paths (`@...@`) to physical locations; [`DefaultResolver`](ar::DefaultResolver) searches the filesystem. |
//! | [`layer`] | Layer collection. [`collect_layers`](layer::collect_layers) recursively loads all layers from a root file. |
//! | [`pcp`] | Prim Cache Population — the composition engine. Implements LIVRPS strength ordering, per-prim index caching, and namespace mapping via [`MapFunction`](pcp::MapFunction). |
//! | [`stage`] | Composed stage. [`Stage`](stage::Stage) merges opinions across layers using [LIVERPS](https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html) strength ordering. |
//! | [`expr`] | Variable expression parser and evaluator for USD's `\`...\`` expression syntax. |
//!
//! # Quick start
//!
//! ```no_run
//! use openusd::Stage;
//!
//! let stage = Stage::open("scene.usda").unwrap();
//!
//! stage.traverse(|prim_path| {
//!     println!("{prim_path}");
//! }).unwrap();
//! ```

pub mod ar;
pub mod expr;
pub mod layer;
pub mod pcp;
pub mod sdf;
pub mod stage;
pub mod usda;
pub mod usdc;
pub mod usdz;

pub use half::f16;
pub use layer::DependencyKind;
pub use stage::{Stage, StageBuilder};

/// A recoverable error encountered during stage composition.
///
/// Wraps errors from both layer collection ([`layer::Error`]) and prim
/// composition ([`pcp::Error`]). The error handler provided via
/// [`StageBuilder::on_error`] decides whether to skip and continue or abort.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CompositionError {
    /// Error during layer collection (e.g. unresolved asset path).
    #[error(transparent)]
    Layer(#[from] layer::Error),
    /// Error during prim composition (e.g. missing defaultPrim, arc cycle).
    #[error(transparent)]
    Pcp(#[from] pcp::Error),
}
