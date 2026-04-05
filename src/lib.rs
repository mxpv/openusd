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
//! | [`compose`] | Layer collection. [`collect_layers`](compose::collect_layers) recursively resolves and loads the full layer stack from a root file. |
//! | [`expr`] | Variable expression parser and evaluator for USD's `\`...\`` expression syntax. |
//!
//! # Quick start
//!
//! ```no_run
//! use openusd::ar::{DefaultResolver, Resolver};
//! use openusd::compose;
//!
//! let resolver = DefaultResolver::new();
//! let stack = compose::collect_layers(&resolver, "scene.usda").unwrap();
//!
//! println!("loaded {} layers", stack.len());
//! for layer in stack.iter() {
//!     println!("  {}", layer.identifier);
//! }
//! ```

pub mod ar;
pub mod compose;
pub mod expr;
pub mod sdf;
pub mod usda;
pub mod usdc;
pub mod usdz;

pub use half::f16;
