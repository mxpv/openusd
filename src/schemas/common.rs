//! Low-level building blocks shared across the schema families.
//!
//! The authoring helpers wrap [`crate::usd::Stage`]'s public authoring
//! entry points (`create_attribute` / `create_relationship` + the
//! `Attribute` / `Relationship` fluent setters) with the default choices
//! that recur across families (`custom = false`, `variability = Varying`
//! unless overridden). The view-gate helpers ([`get_typed`],
//! [`get_typed_any`], [`get_with_api`]) back the typed-view `get` lookups
//! the migrated families (`geom`, `lux`, `media`, `proc`) share.
//!
//! Family-specific authoring (typed-value helpers, primvar metadata,
//! applied-API tokens) stays in each family's module; this module only
//! holds the helpers that would otherwise be duplicated verbatim.

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
pub(crate) fn varying_attribute(stage: &Stage, prim: &Path, name: &str, type_name: &str) -> Result<Attribute> {
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

/// Coerce an `asset` (or `string` / `token`) value to its path string.
pub(crate) fn value_as_asset_str(value: &Value) -> Option<&str> {
    match value {
        Value::AssetPath(s) | Value::String(s) | Value::Token(s) => Some(s),
        _ => None,
    }
}

/// Read an `asset` (or `string` / `token`) attribute as its path `String`.
pub(crate) fn read_asset(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(attr_value(stage, prim, name)?
        .as_ref()
        .and_then(value_as_asset_str)
        .map(str::to_owned))
}

/// Read a `double` (or `timecode`) attribute as an `f64`, coercing the
/// narrower numeric opinions (`float`, `half`, `int`, `int64`) a weaker
/// layer might have authored for the same field.
pub(crate) fn read_f64(stage: &Stage, prim: &Path, name: &str) -> Result<Option<f64>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::TimeCode(d) | Value::Double(d)) => Some(d),
        Some(Value::Float(f)) => Some(f as f64),
        Some(Value::Half(h)) => Some(h.to_f32() as f64),
        Some(Value::Int64(i)) => Some(i as f64),
        Some(Value::Int(i)) => Some(i as f64),
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

/// Wrap `path` as a concrete view's `Prim` if its composed `typeName` equals
/// `type_name` — the type-gate every typed view's `get` performs.
pub(crate) fn get_typed(stage: &Stage, path: impl Into<Path>, type_name: &str) -> Result<Option<Prim>> {
    let path = path.into();
    if stage.type_name(&path)?.as_deref() != Some(type_name) {
        return Ok(None);
    }
    Ok(Some(stage.prim_at_path(path)))
}

/// Like [`get_typed`], but matches any of `type_names` — for views that share
/// one Rust type across several concrete schemas.
pub(crate) fn get_typed_any(stage: &Stage, path: impl Into<Path>, type_names: &[&str]) -> Result<Option<Prim>> {
    let path = path.into();
    match stage.type_name(&path)? {
        Some(t) if type_names.contains(&t.as_str()) => Ok(Some(stage.prim_at_path(path))),
        _ => Ok(None),
    }
}

/// Wrap `path` as an applied-API view's `Prim` if any of `apis` appears in the
/// prim's composed `apiSchemas` — the gate every single-apply API view's `get`
/// performs.
pub(crate) fn get_with_api(stage: &Stage, path: impl Into<Path>, apis: &[&str]) -> Result<Option<Prim>> {
    let path = path.into();
    let applied = stage.api_schemas(&path)?;
    if apis.iter().any(|a| applied.iter().any(|s| s == a)) {
        Ok(Some(stage.prim_at_path(path)))
    } else {
        Ok(None)
    }
}
