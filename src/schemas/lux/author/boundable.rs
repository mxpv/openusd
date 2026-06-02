//! Authoring helpers for the boundable concrete light prims:
//! `DiskLight`, `RectLight`, `SphereLight`, `CylinderLight`,
//! `PortalLight`.
//!
//! All five inherit `BoundableLightBase` in `usdLux/schema.usda` and
//! auto-apply `LightAPI`, so each `*LightAuthor` exposes the shared
//! LightAPI setters via the [`super::LightApiSetters`] trait plus the
//! per-light geometry attributes the schema defines.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::lux::tokens::{
    A_HEIGHT, A_LENGTH, A_RADIUS, A_TEXTURE_FILE, A_WIDTH, T_CYLINDER_LIGHT, T_DISK_LIGHT, T_PORTAL_LIGHT,
    T_RECT_LIGHT, T_SPHERE_LIGHT,
};

use super::common::{author_input_asset, author_input_float, author_treat_as_line, author_treat_as_point};
use super::light_api::LightApiSetters;

/// Author a `def DiskLight` prim at `path`. Returns a chainable
/// [`DiskLightAuthor`] exposing LightAPI setters via
/// [`LightApiSetters`] plus the disk-specific `inputs:radius`.
pub fn define_disk_light(stage: &Stage, path: impl Into<Path>) -> Result<DiskLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_DISK_LIGHT)?;
    Ok(DiskLightAuthor { prim })
}

pub struct DiskLightAuthor {
    prim: Prim,
}

impl DiskLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:radius` (spec default 0.5).
    pub fn set_radius(self, radius: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_RADIUS, radius)?;
        Ok(self)
    }
}

impl LightApiSetters for DiskLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── RectLight ───────────────────────────────────────────────────────

/// Author a `def RectLight` prim at `path`. Per spec, the rectangle is
/// centered in the XY plane (1 unit in each axis by default) and emits
/// light along the -Z axis.
pub fn define_rect_light(stage: &Stage, path: impl Into<Path>) -> Result<RectLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_RECT_LIGHT)?;
    Ok(RectLightAuthor { prim })
}

pub struct RectLightAuthor {
    prim: Prim,
}

impl RectLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:width` along the local X axis (spec default 1).
    pub fn set_width(self, width: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_WIDTH, width)?;
        Ok(self)
    }

    /// Set `inputs:height` along the local Y axis (spec default 1).
    pub fn set_height(self, height: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_HEIGHT, height)?;
        Ok(self)
    }

    /// Set `inputs:texture:file` — a color texture mapped onto the rectangle.
    pub fn set_texture_file(self, path: impl Into<String>) -> Result<Self> {
        author_input_asset(self.prim.stage(), self.prim.path(), A_TEXTURE_FILE, path)?;
        Ok(self)
    }
}

impl LightApiSetters for RectLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── SphereLight ─────────────────────────────────────────────────────

/// Author a `def SphereLight` prim at `path`.
pub fn define_sphere_light(stage: &Stage, path: impl Into<Path>) -> Result<SphereLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_SPHERE_LIGHT)?;
    Ok(SphereLightAuthor { prim })
}

pub struct SphereLightAuthor {
    prim: Prim,
}

impl SphereLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:radius` (spec default 0.5).
    pub fn set_radius(self, radius: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_RADIUS, radius)?;
        Ok(self)
    }

    /// Set `treatAsPoint` (spec default false). Note: per spec this is
    /// authored at the bare attribute name (not `inputs:`-prefixed).
    pub fn set_treat_as_point(self, treat_as_point: bool) -> Result<Self> {
        author_treat_as_point(self.prim.stage(), self.prim.path(), treat_as_point)?;
        Ok(self)
    }
}

impl LightApiSetters for SphereLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── CylinderLight ───────────────────────────────────────────────────

/// Author a `def CylinderLight` prim at `path`. The cylinder is
/// centered at the origin with its major axis along X per spec.
pub fn define_cylinder_light(stage: &Stage, path: impl Into<Path>) -> Result<CylinderLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_CYLINDER_LIGHT)?;
    Ok(CylinderLightAuthor { prim })
}

pub struct CylinderLightAuthor {
    prim: Prim,
}

impl CylinderLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:length` along the local X axis (spec default 1).
    pub fn set_length(self, length: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_LENGTH, length)?;
        Ok(self)
    }

    /// Set `inputs:radius` (spec default 0.5).
    pub fn set_radius(self, radius: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_RADIUS, radius)?;
        Ok(self)
    }

    /// Set `treatAsLine` (spec default false). Authored at the bare
    /// attribute name, mirroring `treatAsPoint` on SphereLight.
    pub fn set_treat_as_line(self, treat_as_line: bool) -> Result<Self> {
        author_treat_as_line(self.prim.stage(), self.prim.path(), treat_as_line)?;
        Ok(self)
    }
}

impl LightApiSetters for CylinderLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── PortalLight ─────────────────────────────────────────────────────

/// Author a `def PortalLight` prim at `path`. A portal is a rectangle
/// in the local XY plane used to guide sampling of an enclosing
/// DomeLight (spec default size 1×1).
pub fn define_portal_light(stage: &Stage, path: impl Into<Path>) -> Result<PortalLightAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PORTAL_LIGHT)?;
    Ok(PortalLightAuthor { prim })
}

pub struct PortalLightAuthor {
    prim: Prim,
}

impl PortalLightAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `inputs:width` along the local X axis (spec default 1).
    pub fn set_width(self, width: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_WIDTH, width)?;
        Ok(self)
    }

    /// Set `inputs:height` along the local Y axis (spec default 1).
    pub fn set_height(self, height: f32) -> Result<Self> {
        author_input_float(self.prim.stage(), self.prim.path(), A_HEIGHT, height)?;
        Ok(self)
    }
}

impl LightApiSetters for PortalLightAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn disk_light_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_disk_light(&stage, sdf::path("/Disk")?)?
            .set_radius(0.75)?
            .set_intensity(600.0)?
            .set_color([1.0, 0.5, 0.5])?;

        let light = crate::schemas::lux::read_disk_light(&stage, &sdf::path("/Disk")?)?.expect("DiskLight");
        assert!((light.radius - 0.75).abs() < 1e-3);
        assert!((light.common.intensity - 600.0).abs() < 1e-3);
        assert_eq!(light.common.color, [1.0, 0.5, 0.5]);
        Ok(())
    }

    #[test]
    fn rect_light_roundtrip_with_texture() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_rect_light(&stage, sdf::path("/Rect")?)?
            .set_width(2.0)?
            .set_height(1.0)?
            .set_texture_file("./softbox.exr")?
            .set_intensity(1500.0)?;

        let light = crate::schemas::lux::read_rect_light(&stage, &sdf::path("/Rect")?)?.expect("RectLight");
        assert!((light.width - 2.0).abs() < 1e-3);
        assert!((light.height - 1.0).abs() < 1e-3);
        assert_eq!(light.texture_file.as_deref(), Some("./softbox.exr"));
        assert!((light.common.intensity - 1500.0).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn sphere_light_treat_as_point_flag() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_sphere_light(&stage, sdf::path("/Bulb")?)?
            .set_radius(0.1)?
            .set_treat_as_point(true)?
            .set_intensity(800.0)?;

        let light = crate::schemas::lux::read_sphere_light(&stage, &sdf::path("/Bulb")?)?.expect("SphereLight");
        assert!((light.radius - 0.1).abs() < 1e-3);
        assert!(light.treat_as_point);
        Ok(())
    }

    #[test]
    fn cylinder_light_treat_as_line_flag() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_cylinder_light(&stage, sdf::path("/Tube")?)?
            .set_length(3.0)?
            .set_radius(0.05)?
            .set_treat_as_line(true)?;

        let light = crate::schemas::lux::read_cylinder_light(&stage, &sdf::path("/Tube")?)?.expect("CylinderLight");
        assert!((light.length - 3.0).abs() < 1e-3);
        assert!((light.radius - 0.05).abs() < 1e-3);
        assert!(light.treat_as_line);
        Ok(())
    }

    #[test]
    fn portal_light_dimensions() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_portal_light(&stage, sdf::path("/Portal")?)?
            .set_width(1.2)?
            .set_height(2.4)?;

        let portal = crate::schemas::lux::read_portal_light(&stage, &sdf::path("/Portal")?)?.expect("PortalLight");
        assert!((portal.width - 1.2).abs() < 1e-3);
        assert!((portal.height - 2.4).abs() < 1e-3);
        Ok(())
    }
}
