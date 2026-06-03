//! Grouping prims — `Xform` and `Scope`.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Prim, SchemaBase, SchemaKind, Stage};

use super::internal::get_typed;
use super::tokens as tok;
use super::{impl_geom_schema, Imageable, Xformable};

/// A transformable grouping prim (C++ `UsdGeomXform`) — an [`Xformable`] with
/// no geometry of its own. Compose a transform with the `set_*` setters
/// inherited from [`Xformable`].
#[derive(Clone, derive_more::Deref)]
pub struct Xform(Prim);

impl Xform {
    /// Author a `def Xform` prim at `path` (C++ `UsdGeomXform::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_XFORM)?))
    }

    /// Wrap `path` as an `Xform` if it is typed `Xform`
    /// (C++ `UsdGeomXform::Get`); returns `None` otherwise.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_XFORM).map(|o| o.map(Self))
    }
}

impl_geom_schema!(xformable Xform);

/// A pure grouping prim (C++ `UsdGeomScope`) — [`Imageable`] but not
/// transformable.
#[derive(Clone, derive_more::Deref)]
pub struct Scope(Prim);

impl Scope {
    /// Author a `def Scope` prim at `path` (C++ `UsdGeomScope::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SCOPE)?))
    }

    /// Wrap `path` as a `Scope` if it is typed `Scope`
    /// (C++ `UsdGeomScope::Get`); returns `None` otherwise.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SCOPE).map(|o| o.map(Self))
    }
}

impl_geom_schema!(imageable Scope);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xform_and_scope_are_pure_typed_prims() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Xform::define(&stage, "/Group")?;
        Scope::define(&stage, "/Stage")?;

        assert_eq!(stage.type_name(&sdf::path("/Group")?)?.as_deref(), Some("Xform"));
        assert_eq!(stage.type_name(&sdf::path("/Stage")?)?.as_deref(), Some("Scope"));
        assert!(Xform::get(&stage, "/Group")?.is_some());
        assert!(Scope::get(&stage, "/Stage")?.is_some());
        assert!(Xform::get(&stage, "/Stage")?.is_none());
        Ok(())
    }
}
