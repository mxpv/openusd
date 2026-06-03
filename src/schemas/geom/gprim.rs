//! `UsdGeomGprim` — the base for geometric primitives.

use anyhow::Result;

use crate::sdf;
use crate::usd::Attribute;

use super::tokens as tok;
use super::Boundable;

/// A geometric primitive — the base for the intrinsic shapes, meshes, and
/// curves (C++ `UsdGeomGprim`). Inherits [`Boundable`] and adds the
/// orientation/sidedness attributes shared by all gprims.
pub trait Gprim: Boundable {
    /// `doubleSided` attribute handle (C++ `GetDoubleSidedAttr`).
    fn double_sided_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_DOUBLE_SIDED)
    }

    /// Author `doubleSided` (`uniform bool`), returning its handle
    /// (C++ `CreateDoubleSidedAttr`).
    fn create_double_sided_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_DOUBLE_SIDED, "bool")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `orientation` attribute handle — `rightHanded` / `leftHanded`
    /// (C++ `GetOrientationAttr`).
    fn orientation_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_ORIENTATION)
    }

    /// Author `orientation` (`uniform token`), returning its handle
    /// (C++ `CreateOrientationAttr`).
    fn create_orientation_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_ORIENTATION, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `primvars:displayColor` attribute handle — the fallback display color
    /// primvar every gprim carries (C++ `GetDisplayColorAttr`).
    fn display_color_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_DISPLAY_COLOR)
    }

    /// Author `primvars:displayColor` (`color3f[]`), returning its handle
    /// (C++ `CreateDisplayColorAttr`). Set its `interpolation` metadata to
    /// describe per-prim vs. per-element values.
    fn create_display_color_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_DISPLAY_COLOR, "color3f[]")?
            .set_custom(false)?)
    }

    /// `primvars:displayOpacity` attribute handle (C++ `GetDisplayOpacityAttr`).
    fn display_opacity_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_DISPLAY_OPACITY)
    }

    /// Author `primvars:displayOpacity` (`float[]`), returning its handle
    /// (C++ `CreateDisplayOpacityAttr`).
    fn create_display_opacity_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_DISPLAY_OPACITY, "float[]")?
            .set_custom(false)?)
    }
}
