//! Shared low-level authoring helpers for the per-prim modules under
//! [`super`].
//!
//! Mirrors `schemas::skel::author::common`: each helper wraps a
//! [`crate::usd::Stage::create_attribute`] call with default choices that
//! match the per-attribute schema declarations in
//! `usdLux/schema.usda` (variability, type name, custom flag).

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::{Attribute, Stage};

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

/// Author a relationship at `prim.name` with a single target.
pub(super) fn author_rel_targets<I, P>(stage: &Stage, prim: &Path, name: &str, targets: I) -> Result<()>
where
    I: IntoIterator<Item = P>,
    P: Into<Path>,
{
    let rel_path = prim.append_property(name)?;
    let paths: Vec<Path> = targets.into_iter().map(Into::into).collect();
    stage
        .create_relationship(rel_path)?
        .set_custom(false)?
        .set_targets(paths)?;
    Ok(())
}

/// Get-or-create a varying attribute with the given type. Returned
/// handle defaults to `custom = false` and `variability = Varying`.
fn varying_attribute<'s>(stage: &'s Stage, prim: &Path, name: &str, type_name: &str) -> Result<Attribute<'s>> {
    let attr_path = prim.append_property(name)?;
    Ok(stage.create_attribute(attr_path, type_name)?.set_custom(false)?)
}
