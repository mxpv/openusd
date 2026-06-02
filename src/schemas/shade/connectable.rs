//! Connectable inputs / outputs — the shared vocabulary behind
//! `UsdShadeShader`, `UsdShadeNodeGraph`, and `UsdShadeMaterial`.
//!
//! A UsdShadeInput is a `inputs:<name>` attribute; a UsdShadeOutput is
//! an `outputs:<name>` attribute. Both are plain attributes — the only
//! thing that makes them "connectable" is that a `.connect`
//! (`connectionPaths`) may wire one to another. This module centralises
//! the namespacing + connection authoring so the typed prim authors
//! (`shader`, `material`) stay thin.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Attribute, Prim};

use super::tokens::{NS_INPUTS, NS_OUTPUTS};

/// The full property name for an input: `inputs:<base>`.
pub fn input_name(base: &str) -> String {
    format!("{NS_INPUTS}{base}")
}

/// The full property name for an output: `outputs:<base>`.
pub fn output_name(base: &str) -> String {
    format!("{NS_OUTPUTS}{base}")
}

/// Create a `inputs:<base>` attribute of `type_name` on `prim`
/// (`custom = false`). Returns the [`Attribute`] handle so the caller
/// can `.set(...)` a default value or `.set_connections(...)` it.
pub fn create_input(prim: &Prim, base: &str, type_name: &str) -> Result<Attribute> {
    Ok(prim.create_attribute(&input_name(base), type_name)?.set_custom(false)?)
}

/// Create an `outputs:<base>` attribute of `type_name` on `prim`
/// (`custom = false`). Outputs typically carry no value — they're the
/// source endpoint a downstream input connects to.
pub fn create_output(prim: &Prim, base: &str, type_name: &str) -> Result<Attribute> {
    Ok(prim
        .create_attribute(&output_name(base), type_name)?
        .set_custom(false)?)
}

/// Full property path of an input on `prim`, e.g.
/// `/Mat/Surface.inputs:diffuseColor`. Useful as a connection source /
/// target without materialising the attribute first.
pub fn input_path(prim: &Path, base: &str) -> Result<Path> {
    prim.append_property(&input_name(base))
}

/// Full property path of an output on `prim`, e.g.
/// `/Mat/Tex.outputs:rgb`.
pub fn output_path(prim: &Path, base: &str) -> Result<Path> {
    prim.append_property(&output_name(base))
}
