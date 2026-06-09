//! The `inputs:` / `outputs:` namespacing shared by the connectable views.
//!
//! A UsdShadeInput is an `inputs:<name>` attribute; a UsdShadeOutput is an
//! `outputs:<name>` attribute. These helpers centralise the namespacing so the
//! [`Connectable`](super::Connectable) trait and the connection-following
//! readers build property names / paths the same way. The attribute authoring
//! itself lives on [`Connectable`].

use anyhow::Result;

use crate::sdf::Path;

use super::tokens::{NS_INPUTS, NS_OUTPUTS};

/// The full property name for an input: `inputs:<base>`.
pub fn input_name(base: &str) -> String {
    format!("{NS_INPUTS}{base}")
}

/// The full property name for an output: `outputs:<base>`.
pub fn output_name(base: &str) -> String {
    format!("{NS_OUTPUTS}{base}")
}

/// The base name of a connectable property — strips the leading `inputs:` or
/// `outputs:` namespace (C++ `UsdShadeInput` / `UsdShadeOutput::GetBaseName`).
/// A name in neither namespace is returned unchanged.
pub fn base_name(full_name: &str) -> &str {
    full_name
        .strip_prefix(NS_INPUTS)
        .or_else(|| full_name.strip_prefix(NS_OUTPUTS))
        .unwrap_or(full_name)
}

/// Full property path of an input on `prim`, e.g.
/// `/Mat/Surface.inputs:diffuseColor`. Useful as a connection source / target
/// without materialising the attribute first.
pub fn input_path(prim: &Path, base: &str) -> Result<Path> {
    prim.append_property(input_name(base))
}
