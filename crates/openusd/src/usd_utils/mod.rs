//! Utilities over layers and stages, the counterpart of C++ `UsdUtils`.
//!
//! [`compute_all_dependencies`] walks the layers and assets a layer reaches
//! (C++ `UsdUtilsComputeAllDependencies`), [`create_new_usdz_package`]
//! writes them into a USDZ package (C++ `UsdUtilsCreateNewUsdzPackage`), and
//! [`modify_asset_paths`] rewrites the asset paths a layer authors (C++
//! `UsdUtilsModifyAssetPaths`).

mod discover;
mod package;
mod walk;

pub use discover::{Dependencies, compute_all_dependencies};
pub use package::create_new_usdz_package;
pub use walk::modify_asset_paths;

/// An asset path the dependency walk cannot follow.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum DependencyError {
    /// An asset path that needs expanding or evaluating before it can be
    /// followed: a UDIM pattern or clip template, which C++ expands by listing
    /// the filesystem, or a variable expression.
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
