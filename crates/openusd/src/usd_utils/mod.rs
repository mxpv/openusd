//! Utilities over layers and stages, the counterpart of C++ `UsdUtils`.
//!
//! [`compute_all_dependencies`] walks the layers and assets a layer reaches
//! (C++ `UsdUtilsComputeAllDependencies`).

mod dependencies;

pub use dependencies::{Dependencies, compute_all_dependencies};

/// An asset path the dependency walk cannot follow.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DependencyError {
    /// An asset path C++ expands before following it: a variable expression,
    /// a UDIM or UV-tile pattern, or a clip template.
    #[error("{kind} {path:?} in {layer} is not supported yet")]
    Unsupported {
        /// What the path needs expanded.
        kind: &'static str,
        /// The authored path.
        path: String,
        /// The layer authoring it.
        layer: String,
    },
}
