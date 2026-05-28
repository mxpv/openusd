//! Shared low-level authoring helpers used across the per-prim modules.
//!
//! Wraps [`crate::usd::Stage::create_attribute`] +
//! [`crate::usd::Stage::create_relationship`] with default choices that
//! match the per-attribute schema declarations in
//! `usdPhysics/schema.usda` (variability, type name, custom flag).

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::Stage;

pub(super) use crate::schemas::common::{author_bool, author_float, author_rel_targets, author_uniform_token};

/// Author a `uniform bool` attribute with the given default. Used for
/// `startsAsleep` and `excludeFromArticulation`.
pub(super) fn author_uniform_bool(stage: &Stage, prim: &Path, name: &str, value: bool) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "bool")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Bool(value))?;
    Ok(())
}

/// Author a `varying vector3f` attribute with the given default.
pub(super) fn author_vector3f(stage: &Stage, prim: &Path, name: &str, value: [f32; 3]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "vector3f")?
        .set_custom(false)?
        .set(Value::Vec3f(value))?;
    Ok(())
}

/// Author a `varying point3f` attribute with the given default.
pub(super) fn author_point3f(stage: &Stage, prim: &Path, name: &str, value: [f32; 3]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "point3f")?
        .set_custom(false)?
        .set(Value::Vec3f(value))?;
    Ok(())
}

/// Author a `varying float3` attribute with the given default. Used
/// for `diagonalInertia`.
pub(super) fn author_float3(stage: &Stage, prim: &Path, name: &str, value: [f32; 3]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float3")?
        .set_custom(false)?
        .set(Value::Vec3f(value))?;
    Ok(())
}

/// Author a `varying quatf` attribute with the given default. Used for
/// MassAPI's `principalAxes` and joint `localRot0` / `localRot1`.
pub(super) fn author_quatf(stage: &Stage, prim: &Path, name: &str, value: [f32; 4]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "quatf")?
        .set_custom(false)?
        .set(Value::Quatf(value))?;
    Ok(())
}

/// Author a `varying string` attribute with the given default. Used
/// for `CollisionGroup.mergeGroup`.
pub(super) fn author_string(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "string")?
        .set_custom(false)?
        .set(Value::String(value.into()))?;
    Ok(())
}
