//! Low-level authoring building blocks shared across the schema families.
//!
//! Each helper wraps [`crate::usd::Stage`]'s public authoring entry points
//! (`create_attribute` / `create_relationship` + the `Attribute` /
//! `Relationship` fluent setters) with default choices that recur across
//! `usdGeom`, `usdLux`, `usdPhysics`, and `usdSkel` (`custom = false`,
//! `variability = Varying` unless overridden).
//!
//! Family-specific authoring (typed-value helpers, primvar metadata,
//! applied-API tokens) stays in each family's `author/common.rs`; this
//! module only holds the helpers that would otherwise be duplicated
//! verbatim across all four.

// Each helper is used by at least one schema feature, but typically not
// all four — silence the dead-code warning on per-feature builds.
#![allow(dead_code)]

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value, Variability};
use crate::usd::{Attribute, Prim, Stage};

/// Author a `varying float` attribute on `prim` with the given default value.
pub(crate) fn author_float(stage: &Stage, prim: &Path, name: &str, value: f32) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float")?
        .set_custom(false)?
        .set(Value::Float(value))?;
    Ok(())
}

/// Author a `varying bool` attribute on `prim` with the given default value.
pub(crate) fn author_bool(stage: &Stage, prim: &Path, name: &str, value: bool) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "bool")?
        .set_custom(false)?
        .set(Value::Bool(value))?;
    Ok(())
}

/// Author a `varying token` attribute on `prim` with the given default value.
pub(crate) fn author_token(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token")?
        .set_custom(false)?
        .set(Value::Token(value.into()))?;
    Ok(())
}

/// Author a `varying asset` attribute on `prim` with the given default value.
pub(crate) fn author_asset(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "asset")?
        .set_custom(false)?
        .set(Value::AssetPath(value.into()))?;
    Ok(())
}

/// Author a `varying int` attribute on `prim` with the given default value.
pub(crate) fn author_int(stage: &Stage, prim: &Path, name: &str, value: i32) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "int")?
        .set_custom(false)?
        .set(Value::Int(value))?;
    Ok(())
}

/// Author a `uniform token` attribute on `prim` with the given default value.
pub(crate) fn author_uniform_token(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Token(value.into()))?;
    Ok(())
}

/// Author a `uniform asset` attribute on `prim` with the given default value.
pub(crate) fn author_uniform_asset(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "asset")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::AssetPath(value.into()))?;
    Ok(())
}

/// Author a `uniform token[]` attribute on `prim` with the given default value.
pub(crate) fn author_uniform_token_vec(stage: &Stage, prim: &Path, name: &str, tokens: Vec<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token[]")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::TokenVec(tokens))?;
    Ok(())
}

/// Author a relationship on `prim` with the given target paths. Thin path-based
/// wrapper around [`Prim::author_relationship_targets`] for schema modules that
/// still pass `(stage, prim_path)` rather than a [`Prim`] handle.
pub(crate) fn author_rel_targets<I, P>(stage: &Stage, prim: &Path, name: &str, targets: I) -> Result<()>
where
    I: IntoIterator<Item = P>,
    P: Into<Path>,
{
    Prim::new(stage, prim.clone()).author_relationship_targets(name, targets)?;
    Ok(())
}

/// Get-or-create a varying attribute of the given `type_name` on `prim`, with
/// `custom = false`. Callers write the value via the returned [`Attribute`]
/// fluent setters.
pub(crate) fn varying_attribute<'s>(
    stage: &'s Stage,
    prim: &Path,
    name: &str,
    type_name: &str,
) -> Result<Attribute<'s>> {
    Ok(Prim::new(stage, prim.clone())
        .create_attribute(name, type_name)?
        .set_custom(false)?)
}

/// Resolve the `default` field of the attribute `name` on `prim` as a raw
/// [`Value`]. The building block the typed `read_*` helpers below share.
pub(crate) fn attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    stage.field::<Value>(prim.append_property(name)?, FieldKey::Default)
}

/// Read a `token` (or `string`) attribute as a `String`.
pub(crate) fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

/// Read an `asset` (or `string` / `token`) attribute as its path `String`.
pub(crate) fn read_asset(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

/// Read an `int` attribute. An `int64` opinion is accepted via a checked
/// narrow so an out-of-range value yields `None` rather than silently wrapping.
pub(crate) fn read_int(stage: &Stage, prim: &Path, name: &str) -> Result<Option<i32>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Int(i)) => Some(i),
        Some(Value::Int64(i)) => i32::try_from(i).ok(),
        _ => None,
    })
}
