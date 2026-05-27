//! `SkelRoot` prim authoring.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::skel::tokens::T_SKEL_ROOT;

/// Author a `def SkelRoot` prim at `path` on the stage's edit target. Returns
/// a [`Prim`] handle so callers can chain further attribute / API authoring
/// (e.g. `apply_skel_binding` later in this module).
///
/// `SkelRoot` inherits from `Boundable` per Pixar's
/// `usdSkel/schema.usda` and itself has no Skel-specific attributes —
/// `extent` / `xformOpOrder` come from the UsdGeom side and are
/// authored separately. The prim only carries the typed `SkelRoot`
/// `typeName` so downstream traversals (`find_skel_roots`,
/// `discover_bindings`) recognise the subtree.
pub fn define_skel_root<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<Prim<'s>> {
    Ok(stage.define_prim(path)?.set_type_name(T_SKEL_ROOT)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;
    use crate::usd::Stage;

    #[test]
    fn define_skel_root_authors_typed_prim() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_skel_root(&stage, sdf::path("/World/Character")?)?;

        let path = sdf::path("/World/Character")?;
        assert_eq!(stage.spec_type(&path)?, Some(sdf::SpecType::Prim));
        assert_eq!(stage.type_name(&path)?.as_deref(), Some(T_SKEL_ROOT));
        assert_eq!(
            stage.field::<sdf::Value>(&path, sdf::FieldKey::Specifier)?,
            Some(sdf::Value::Specifier(sdf::Specifier::Def)),
        );
        Ok(())
    }

    #[test]
    fn define_skel_root_creates_ancestor_overs() -> Result<()> {
        // Ancestor prim chain auto-creates as `over`; only the leaf is the
        // typed `def SkelRoot`.
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_skel_root(&stage, sdf::path("/World/Character")?)?;

        assert_eq!(
            stage.field::<sdf::Value>("/World", sdf::FieldKey::Specifier)?,
            Some(sdf::Value::Specifier(sdf::Specifier::Over)),
        );
        Ok(())
    }
}
