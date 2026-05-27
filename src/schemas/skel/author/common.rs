//! Shared low-level authoring helpers used across the per-prim
//! modules under [`super`].
//!
//! These wrap [`crate::usd::Stage`]'s public authoring entry points
//! (`create_attribute` + `Attribute` fluent setters) with default
//! choices that match Pixar's per-attribute schema declarations
//! (variability, type name, custom flag). Keeping the wrapping local
//! to one file means each schema-specific module reads as pure spec
//! plumbing rather than repeated boilerplate.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::Stage;

/// Author a `uniform token[]` attribute on `prim` with name `name` and
/// the given default value.
pub(super) fn author_uniform_token_array(stage: &Stage, prim: &Path, name: &str, tokens: Vec<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token[]")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::TokenVec(tokens))?;
    Ok(())
}

/// Author a `uniform matrix4d[]` attribute on `prim` with the given default.
/// Matrices are USD's row-major flattened `[f64; 16]` representation.
pub(super) fn author_uniform_matrix4d_array(
    stage: &Stage,
    prim: &Path,
    name: &str,
    matrices: Vec<[f64; 16]>,
) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "matrix4d[]")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Matrix4dVec(matrices))?;
    Ok(())
}
