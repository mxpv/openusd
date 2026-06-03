//! `UsdGeomBoundable` — prims with a computable bounding extent.

use anyhow::Result;

use crate::usd::Attribute;

use super::tokens as tok;
use super::Xformable;

/// A prim with a bounding extent (C++ `UsdGeomBoundable`). Inherits
/// [`Xformable`].
pub trait Boundable: Xformable {
    /// `extent` attribute handle — local-space `[min, max]` corners stored as
    /// `float3[2]` (C++ `GetExtentAttr`).
    fn extent_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_EXTENT)
    }

    /// Author the `extent` attribute (`float3[]`), returning its handle
    /// (C++ `CreateExtentAttr`).
    fn create_extent_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_EXTENT, "float3[]")?
            .set_custom(false)?)
    }
}
