//! `UsdGeomImageable` — the base of the UsdGeom prim hierarchy.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Relationship, SchemaBase, Stage};

use super::tokens as tok;
use super::{Purpose, Visibility};

/// A prim that can be visualized — the base for every UsdGeom prim
/// (C++ `UsdGeomImageable`). Carries `visibility` / `purpose` (both
/// inherited down namespace) and the `proxyPrim` relationship.
///
/// Implemented by every concrete UsdGeom schema through the
/// `Imageable → Xformable → Boundable → Gprim` chain, so its accessors are
/// available on each shape.
pub trait Imageable: SchemaBase {
    /// `visibility` attribute handle (C++ `GetVisibilityAttr`).
    fn visibility_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_VISIBILITY)
    }

    /// Author the `visibility` attribute (`token`, varying), returning its
    /// handle (C++ `CreateVisibilityAttr`).
    fn create_visibility_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_VISIBILITY, "token")?
            .set_custom(false)?)
    }

    /// `purpose` attribute handle (C++ `GetPurposeAttr`).
    fn purpose_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_PURPOSE)
    }

    /// Author the `purpose` attribute (`uniform token`), returning its
    /// handle (C++ `CreatePurposeAttr`).
    fn create_purpose_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_PURPOSE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `proxyPrim` relationship handle (C++ `GetProxyPrimRel`).
    fn proxy_prim_rel(&self) -> Relationship {
        self.prim().relationship(tok::REL_PROXY_PRIM)
    }

    /// Resolve the effective composed `visibility`, walking ancestors
    /// (C++ `ComputeVisibility`): an `invisible` opinion on this prim or any
    /// ancestor prunes the subtree, so the result is
    /// [`Visibility::Invisible`]; otherwise [`Visibility::Inherited`].
    fn compute_visibility(&self) -> Result<Visibility> {
        let stage = self.stage();
        let mut cur = self.path().clone();
        loop {
            if direct_token(stage, &cur, tok::A_VISIBILITY)?
                .as_deref()
                .and_then(Visibility::from_token)
                .unwrap_or_default()
                == Visibility::Invisible
            {
                return Ok(Visibility::Invisible);
            }
            match cur.parent() {
                Some(p) => cur = p,
                None => return Ok(Visibility::Inherited),
            }
        }
    }

    /// Resolve the effective composed `purpose` (C++ `ComputePurpose`):
    /// inherited from the closest ancestor with an authored opinion, falling
    /// back to [`Purpose::Default`]. An authored-but-unrecognized token stops
    /// the walk and resolves to [`Purpose::Default`].
    fn compute_purpose(&self) -> Result<Purpose> {
        let stage = self.stage();
        let mut cur = self.path().clone();
        loop {
            if let Some(token) = direct_token(stage, &cur, tok::A_PURPOSE)? {
                return Ok(Purpose::from_token(&token).unwrap_or_default());
            }
            match cur.parent() {
                Some(p) => cur = p,
                None => return Ok(Purpose::Default),
            }
        }
    }
}

/// Read a token (or string) attribute's authored default at `prim`,
/// regardless of variability, used by the inheritance walks above to inspect
/// ancestor opinions directly.
fn direct_token(stage: &Stage, prim: &sdf::Path, name: &str) -> Result<Option<String>> {
    let attr = prim.append_property(name)?;
    Ok(match stage.field::<sdf::Value>(attr, sdf::FieldKey::Default)? {
        Some(sdf::Value::Token(s)) | Some(sdf::Value::String(s)) => Some(s),
        _ => None,
    })
}
