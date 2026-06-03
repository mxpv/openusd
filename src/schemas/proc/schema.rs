//! `UsdProcGenerativeProcedural` — runtime-generated procedural geometry.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, Stage};

use super::impl_proc_schema;
use super::tokens as tok;
use crate::schemas::common::get_typed;

/// A generative procedural prim (C++ `UsdProcGenerativeProcedural`) — a
/// [`geom::Boundable`](crate::schemas::geom::Boundable) prim whose children are
/// generated at runtime by the named `proceduralSystem`. Its input parameters
/// live in the `primvars:` namespace; transform / extent / visibility come
/// from the UsdGeom layer (the inherited `extent_attr` / `xform_op_order` /
/// `visibility_attr` accessors).
#[derive(Clone, derive_more::Deref)]
pub struct GenerativeProcedural(Prim);

impl GenerativeProcedural {
    /// Author a `def GenerativeProcedural` prim at `path`
    /// (C++ `UsdProcGenerativeProcedural::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.define_prim(path)?.set_type_name(tok::T_GENERATIVE_PROCEDURAL)?,
        ))
    }

    /// Wrap `path` as a `GenerativeProcedural` if it is typed
    /// `GenerativeProcedural` (C++ `UsdProcGenerativeProcedural::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_GENERATIVE_PROCEDURAL).map(|o| o.map(Self))
    }

    /// Name or convention of the system responsible for evaluating this
    /// procedural, routing it to the right runtime engine (e.g. Houdini Engine or
    /// a RenderMan convention). C++ `UsdProcGenerativeProcedural::GetProceduralSystemAttr`.
    ///
    /// Type `token`. Fetch with `get::<String>()?`.
    pub fn procedural_system_attr(&self) -> Attribute {
        self.attribute(tok::A_PROCEDURAL_SYSTEM)
    }

    /// Author `proceduralSystem` (`uniform token`)
    /// (C++ `CreateProceduralSystemAttr`).
    pub fn create_procedural_system_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_PROCEDURAL_SYSTEM, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_proc_schema!(boundable GenerativeProcedural);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::geom::Boundable;

    #[test]
    fn generative_procedural_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let p = GenerativeProcedural::define(&stage, "/World/Proc")?;
        p.create_procedural_system_attr()?
            .set(sdf::Value::Token("Houdini".into()))?;

        let p = GenerativeProcedural::get(&stage, "/World/Proc")?.expect("GenerativeProcedural");
        assert_eq!(
            p.procedural_system_attr().get::<sdf::Value>()?,
            Some(sdf::Value::Token("Houdini".into()))
        );
        // Inherited Boundable accessor is available on the handle.
        assert_eq!(p.extent_attr().get::<sdf::Value>()?, None);
        assert!(GenerativeProcedural::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    #[test]
    fn get_rejects_non_procedural() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/NotProc")?.set_type_name("Scope")?;
        assert!(GenerativeProcedural::get(&stage, "/NotProc")?.is_none());
        Ok(())
    }
}
