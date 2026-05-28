//! Shared low-level authoring helpers for the per-prim modules under
//! [`super`].
//!
//! Mirrors `schemas::skel::author::common`: each helper wraps a
//! [`crate::usd::Stage::create_attribute`] call with default choices that
//! match the per-attribute schema declarations in
//! `usdLux/schema.usda` (variability, type name, custom flag).

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::Stage;

use crate::schemas::lux::tokens::{A_TREAT_AS_LINE, A_TREAT_AS_POINT};

pub(super) use crate::schemas::common::{author_rel_targets, varying_attribute};

/// Author a `varying float` input on `prim` with the given default value.
pub(super) fn author_input_float(stage: &Stage, prim: &Path, name: &str, value: f32) -> Result<()> {
    varying_attribute(stage, prim, name, "float")?.set(Value::Float(value))?;
    Ok(())
}

/// Author a `varying bool` input on `prim` with the given default value.
pub(super) fn author_input_bool(stage: &Stage, prim: &Path, name: &str, value: bool) -> Result<()> {
    varying_attribute(stage, prim, name, "bool")?.set(Value::Bool(value))?;
    Ok(())
}

/// Author a `varying color3f` input on `prim` with the given default value.
pub(super) fn author_input_color3f(stage: &Stage, prim: &Path, name: &str, value: [f32; 3]) -> Result<()> {
    varying_attribute(stage, prim, name, "color3f")?.set(Value::Vec3f(value))?;
    Ok(())
}

/// Author a `varying asset` input on `prim` with the given default value.
pub(super) fn author_input_asset(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    varying_attribute(stage, prim, name, "asset")?.set(Value::AssetPath(value.into()))?;
    Ok(())
}

/// Author the `treatAsPoint` bool flag on a SphereLight prim. Sits at
/// the bare attribute name (not `inputs:`-prefixed) per
/// `usdLux/schema.usda`.
pub(super) fn author_treat_as_point(stage: &Stage, prim: &Path, value: bool) -> Result<()> {
    let attr_path = prim.append_property(A_TREAT_AS_POINT)?;
    stage
        .create_attribute(attr_path, "bool")?
        .set_custom(false)?
        .set(Value::Bool(value))?;
    Ok(())
}

/// Author the `treatAsLine` bool flag on a CylinderLight prim.
pub(super) fn author_treat_as_line(stage: &Stage, prim: &Path, value: bool) -> Result<()> {
    let attr_path = prim.append_property(A_TREAT_AS_LINE)?;
    stage
        .create_attribute(attr_path, "bool")?
        .set_custom(false)?
        .set(Value::Bool(value))?;
    Ok(())
}
