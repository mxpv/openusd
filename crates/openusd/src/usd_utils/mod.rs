//! Utilities over layers and stages, the counterpart of C++ `UsdUtils`.
//!
//! [`compute_all_dependencies`] walks the layers and assets a layer reaches
//! (C++ `UsdUtilsComputeAllDependencies`), [`create_new_usdz_package`]
//! writes them into a USDZ package (C++ `UsdUtilsCreateNewUsdzPackage`), and
//! [`modify_asset_paths`] rewrites the asset paths a layer authors (C++
//! `UsdUtilsModifyAssetPaths`).

mod dependencies;
mod package;

pub use dependencies::{Dependencies, compute_all_dependencies, modify_asset_paths};
pub use package::create_new_usdz_package;

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
