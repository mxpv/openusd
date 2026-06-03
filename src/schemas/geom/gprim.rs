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
    /// Whether the gprim's surfaces should be shaded and rendered from both
    /// sides rather than back-face culled to its [`orientation`](Self::orientation_attr).
    /// C++ `UsdGeomGprim::GetDoubleSidedAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
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

    /// The winding order that decides which side of each face is the front:
    /// `rightHanded` (counter-clockwise) or `leftHanded` (clockwise).
    /// C++ `UsdGeomGprim::GetOrientationAttr`.
    ///
    /// Type `token`. Fetch with `get::<Orientation>()?`.
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

    /// The fallback per-vertex/per-element color primvar used to display the
    /// gprim when no bound material provides one (RGB in linear space).
    /// C++ `UsdGeomGprim::GetDisplayColorAttr`.
    ///
    /// Type `color3f[]`. Fetch with `get::<Vec<[f32; 3]>>()?`.
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

    /// The fallback display opacity primvar paired with
    /// [`displayColor`](Self::display_color_attr): 1.0 is fully opaque, 0.0
    /// fully transparent. C++ `UsdGeomGprim::GetDisplayOpacityAttr`.
    ///
    /// Type `float[]`. Fetch with `get::<Vec<f32>>()?`.
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
