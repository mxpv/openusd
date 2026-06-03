//! Helpers shared by the concrete UsdGeom view types: the `get` type-gate and
//! the attribute-authoring shorthands their `create_*_attr` methods build on.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, Stage};

/// Resolve `path` to a [`Prim`] handle only when its `typeName` matches
/// `type_name` — the shared gate behind every concrete view's `get`.
pub(super) fn get_typed(stage: &Stage, path: impl Into<sdf::Path>, type_name: &str) -> Result<Option<Prim>> {
    let path = path.into();
    if stage.type_name(&path)?.as_deref() != Some(type_name) {
        return Ok(None);
    }
    Ok(Some(stage.prim_at_path(path)))
}

/// Author a varying attribute named `name` of `type_name` with
/// `custom = false`, returning its handle.
pub(super) fn create(prim: &Prim, name: &str, type_name: &str) -> Result<Attribute> {
    Ok(prim.create_attribute(name, type_name)?.set_custom(false)?)
}

/// Author a `uniform token` attribute named `name` with `custom = false`.
pub(super) fn create_uniform_token(prim: &Prim, name: &str) -> Result<Attribute> {
    Ok(create(prim, name, "token")?.set_variability(sdf::Variability::Uniform)?)
}
