//! Reader functions for the [UsdLux](super) schema family.
//!
//! Each `read_*_light` helper returns the populated struct (or `None`
//! when the prim isn't typed as the expected light kind). Unauthored
//! attributes fall back to Pixar's documented defaults via the
//! `Default` impls in [`super::types`].
//!
//! `read_light_api` returns the common LightAPI inputs for *any* light
//! prim — the per-light readers call it internally and then layer their
//! own kind-specific attributes on top.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::tokens::*;
use super::types::*;

/// Read the common `LightAPI` inputs from any light prim.
///
/// Returns the populated [`ReadLight`] with Pixar defaults applied for
/// every unauthored attribute. The `path` field is filled in from the
/// prim passed in.
pub fn read_light_api(stage: &Stage, prim: &Path) -> Result<ReadLight> {
    let defaults = ReadLight::default();
    Ok(ReadLight {
        path: prim.as_str().to_string(),
        intensity: read_f32(stage, prim, A_INTENSITY)?.unwrap_or(defaults.intensity),
        exposure: read_f32(stage, prim, A_EXPOSURE)?.unwrap_or(defaults.exposure),
        diffuse: read_f32(stage, prim, A_DIFFUSE)?.unwrap_or(defaults.diffuse),
        specular: read_f32(stage, prim, A_SPECULAR)?.unwrap_or(defaults.specular),
        normalize: read_bool(stage, prim, A_NORMALIZE)?.unwrap_or(defaults.normalize),
        color: read_color3f(stage, prim, A_COLOR)?.unwrap_or(defaults.color),
        enable_color_temperature: read_bool(stage, prim, A_ENABLE_COLOR_TEMPERATURE)?
            .unwrap_or(defaults.enable_color_temperature),
        color_temperature: read_f32(stage, prim, A_COLOR_TEMPERATURE)?.unwrap_or(defaults.color_temperature),
        filters: read_rel_targets(stage, prim, REL_FILTERS)?,
    })
}

/// Read a `DistantLight` prim. Returns `None` when the prim isn't
/// typed `DistantLight`.
pub fn read_distant_light(stage: &Stage, prim: &Path) -> Result<Option<ReadDistantLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_DISTANT_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadDistantLight::default();
    // DistantLight overrides LightAPI's `intensity = 1.0` default to 50000;
    // pull common attrs but re-apply the DistantLight-specific intensity
    // default when unauthored.
    let mut common = read_light_api(stage, prim)?;
    if read_f32(stage, prim, A_INTENSITY)?.is_none() {
        common.intensity = defaults.common.intensity;
    }
    Ok(Some(ReadDistantLight {
        common,
        angle_deg: read_f32(stage, prim, A_ANGLE)?.unwrap_or(defaults.angle_deg),
    }))
}

/// Read a `SphereLight` prim. Returns `None` when the prim isn't
/// typed `SphereLight`.
pub fn read_sphere_light(stage: &Stage, prim: &Path) -> Result<Option<ReadSphereLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_SPHERE_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadSphereLight::default();
    Ok(Some(ReadSphereLight {
        common: read_light_api(stage, prim)?,
        radius: read_f32(stage, prim, A_RADIUS)?.unwrap_or(defaults.radius),
        treat_as_point: read_bool(stage, prim, A_TREAT_AS_POINT)?.unwrap_or(defaults.treat_as_point),
    }))
}

/// Read a `RectLight` prim. Returns `None` when the prim isn't typed
/// `RectLight`.
pub fn read_rect_light(stage: &Stage, prim: &Path) -> Result<Option<ReadRectLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_RECT_LIGHT) {
        return Ok(None);
    }
    Ok(Some(ReadRectLight {
        common: read_light_api(stage, prim)?,
        width: read_f32(stage, prim, A_WIDTH)?.unwrap_or(1.0),
        height: read_f32(stage, prim, A_HEIGHT)?.unwrap_or(1.0),
        texture_file: read_asset_path(stage, prim, A_TEXTURE_FILE)?,
    }))
}

/// Read a `DiskLight` prim. Returns `None` when the prim isn't typed
/// `DiskLight`.
pub fn read_disk_light(stage: &Stage, prim: &Path) -> Result<Option<ReadDiskLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_DISK_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadDiskLight::default();
    Ok(Some(ReadDiskLight {
        common: read_light_api(stage, prim)?,
        radius: read_f32(stage, prim, A_RADIUS)?.unwrap_or(defaults.radius),
    }))
}

/// Read a `CylinderLight` prim. Returns `None` when the prim isn't
/// typed `CylinderLight`.
pub fn read_cylinder_light(stage: &Stage, prim: &Path) -> Result<Option<ReadCylinderLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_CYLINDER_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadCylinderLight::default();
    Ok(Some(ReadCylinderLight {
        common: read_light_api(stage, prim)?,
        length: read_f32(stage, prim, A_LENGTH)?.unwrap_or(defaults.length),
        radius: read_f32(stage, prim, A_RADIUS)?.unwrap_or(defaults.radius),
        treat_as_line: read_bool(stage, prim, A_TREAT_AS_LINE)?.unwrap_or(defaults.treat_as_line),
    }))
}

/// Read a `DomeLight` or `DomeLight_1` prim. Both surface the same
/// reader struct; the type-name distinction is a Pixar versioning
/// artefact and the attribute set is functionally identical for
/// consumers.
pub fn read_dome_light(stage: &Stage, prim: &Path) -> Result<Option<ReadDomeLight>> {
    let type_name = stage.type_name(prim)?;
    if !matches!(type_name.as_deref(), Some(T_DOME_LIGHT) | Some(T_DOME_LIGHT_1)) {
        return Ok(None);
    }
    let defaults = ReadDomeLight::default();
    Ok(Some(ReadDomeLight {
        common: read_light_api(stage, prim)?,
        texture_file: read_asset_path(stage, prim, A_TEXTURE_FILE)?,
        texture_format: read_token(stage, prim, A_TEXTURE_FORMAT)?
            .as_deref()
            .and_then(TextureFormat::from_token)
            .unwrap_or_default(),
        portals: read_rel_targets(stage, prim, REL_PORTALS)?,
        guide_radius: read_f32(stage, prim, A_GUIDE_RADIUS)?.unwrap_or(defaults.guide_radius),
    }))
}

/// Read a `GeometryLight` prim. Returns `None` when the prim isn't
/// typed `GeometryLight`.
pub fn read_geometry_light(stage: &Stage, prim: &Path) -> Result<Option<ReadGeometryLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_GEOMETRY_LIGHT) {
        return Ok(None);
    }
    Ok(Some(ReadGeometryLight {
        common: read_light_api(stage, prim)?,
        geometry: read_rel_first_target(stage, prim, REL_GEOMETRY)?,
    }))
}

/// Read a `PortalLight` prim. Returns `None` when the prim isn't
/// typed `PortalLight`.
pub fn read_portal_light(stage: &Stage, prim: &Path) -> Result<Option<ReadPortalLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_PORTAL_LIGHT) {
        return Ok(None);
    }
    Ok(Some(ReadPortalLight {
        common: read_light_api(stage, prim)?,
        width: read_f32(stage, prim, A_WIDTH)?.unwrap_or(1.0),
        height: read_f32(stage, prim, A_HEIGHT)?.unwrap_or(1.0),
    }))
}

/// Dispatch on the prim's `typeName` and return the matching
/// concrete light variant. Returns `None` when the prim isn't a
/// recognised UsdLux light type.
pub fn read_light(stage: &Stage, prim: &Path) -> Result<Option<ReadAnyLight>> {
    let Some(type_name) = stage.type_name(prim)? else {
        return Ok(None);
    };
    Ok(match type_name.as_str() {
        T_DISTANT_LIGHT => read_distant_light(stage, prim)?.map(ReadAnyLight::Distant),
        T_SPHERE_LIGHT => read_sphere_light(stage, prim)?.map(ReadAnyLight::Sphere),
        T_RECT_LIGHT => read_rect_light(stage, prim)?.map(ReadAnyLight::Rect),
        T_DISK_LIGHT => read_disk_light(stage, prim)?.map(ReadAnyLight::Disk),
        T_CYLINDER_LIGHT => read_cylinder_light(stage, prim)?.map(ReadAnyLight::Cylinder),
        T_DOME_LIGHT | T_DOME_LIGHT_1 => read_dome_light(stage, prim)?.map(ReadAnyLight::Dome),
        T_GEOMETRY_LIGHT => read_geometry_light(stage, prim)?.map(ReadAnyLight::Geometry),
        T_PORTAL_LIGHT => read_portal_light(stage, prim)?.map(ReadAnyLight::Portal),
        _ => None,
    })
}

/// Returns `true` when `type_name` is a recognised UsdLux light
/// prim. Useful for stage walks that want to filter to light prims
/// without dispatching the full reader.
pub fn is_light_type(type_name: &str) -> bool {
    matches!(
        type_name,
        T_DISTANT_LIGHT
            | T_SPHERE_LIGHT
            | T_RECT_LIGHT
            | T_DISK_LIGHT
            | T_CYLINDER_LIGHT
            | T_DOME_LIGHT
            | T_DOME_LIGHT_1
            | T_GEOMETRY_LIGHT
            | T_PORTAL_LIGHT
    )
}

// ── Applied API schemas ─────────────────────────────────────────────

/// Read `ShapingAPI` on a light prim. Returns `None` when the API
/// isn't applied.
pub fn read_shaping(stage: &Stage, prim: &Path) -> Result<Option<ReadShaping>> {
    if !stage.has_api_schema(prim, API_SHAPING)? {
        return Ok(None);
    }
    let defaults = ReadShaping::default();
    Ok(Some(ReadShaping {
        focus: read_f32(stage, prim, A_SHAPING_FOCUS)?.unwrap_or(defaults.focus),
        focus_tint: read_color3f(stage, prim, A_SHAPING_FOCUS_TINT)?.unwrap_or(defaults.focus_tint),
        cone_angle_deg: read_f32(stage, prim, A_SHAPING_CONE_ANGLE)?.unwrap_or(defaults.cone_angle_deg),
        cone_softness: read_f32(stage, prim, A_SHAPING_CONE_SOFTNESS)?.unwrap_or(defaults.cone_softness),
        ies_file: read_asset_path(stage, prim, A_SHAPING_IES_FILE)?,
        ies_angle_scale: read_f32(stage, prim, A_SHAPING_IES_ANGLE_SCALE)?.unwrap_or(defaults.ies_angle_scale),
        ies_normalize: read_bool(stage, prim, A_SHAPING_IES_NORMALIZE)?.unwrap_or(defaults.ies_normalize),
    }))
}

/// Read `ShadowAPI` on a light prim. Returns `None` when the API
/// isn't applied.
pub fn read_shadow(stage: &Stage, prim: &Path) -> Result<Option<ReadShadow>> {
    if !stage.has_api_schema(prim, API_SHADOW)? {
        return Ok(None);
    }
    let defaults = ReadShadow::default();
    Ok(Some(ReadShadow {
        enable: read_bool(stage, prim, A_SHADOW_ENABLE)?.unwrap_or(defaults.enable),
        color: read_color3f(stage, prim, A_SHADOW_COLOR)?.unwrap_or(defaults.color),
        distance: read_f32(stage, prim, A_SHADOW_DISTANCE)?.unwrap_or(defaults.distance),
        falloff: read_f32(stage, prim, A_SHADOW_FALLOFF)?.unwrap_or(defaults.falloff),
        falloff_gamma: read_f32(stage, prim, A_SHADOW_FALLOFF_GAMMA)?.unwrap_or(defaults.falloff_gamma),
    }))
}

/// Read `LightListAPI` on a prim. Returns `None` when the API isn't
/// applied.
pub fn read_light_list(stage: &Stage, prim: &Path) -> Result<Option<ReadLightList>> {
    if !stage.has_api_schema(prim, API_LIGHT_LIST)? {
        return Ok(None);
    }
    Ok(Some(ReadLightList {
        lights: read_rel_targets(stage, prim, REL_LIGHT_LIST)?,
        cache_behavior: read_token(stage, prim, A_LIGHT_LIST_CACHE_BEHAVIOR)?
            .as_deref()
            .and_then(LightListCacheBehavior::from_token)
            .unwrap_or_default(),
    }))
}

/// Walk the stage once and return categorised path lists for every
/// recognised UsdLux prim type plus prims carrying any of the
/// UsdLux applied APIs.
pub fn find_lux_prims(stage: &Stage) -> Result<LuxPrims> {
    let mut out = LuxPrims::default();
    stage.traverse(|path| {
        let p = path.as_str().to_string();
        if let Ok(Some(type_name)) = stage.type_name(path) {
            match type_name.as_str() {
                T_DISTANT_LIGHT => out.distant.push(p.clone()),
                T_SPHERE_LIGHT => out.sphere.push(p.clone()),
                T_RECT_LIGHT => out.rect.push(p.clone()),
                T_DISK_LIGHT => out.disk.push(p.clone()),
                T_CYLINDER_LIGHT => out.cylinder.push(p.clone()),
                T_DOME_LIGHT | T_DOME_LIGHT_1 => out.dome.push(p.clone()),
                T_GEOMETRY_LIGHT => out.geometry.push(p.clone()),
                T_PORTAL_LIGHT => out.portal.push(p.clone()),
                T_LIGHT_FILTER => out.light_filters.push(p.clone()),
                _ => {}
            }
        }
        if let Ok(api) = stage.api_schemas(path) {
            if api.iter().any(|s| s == API_SHAPING) {
                out.shaping.push(p.clone());
            }
            if api.iter().any(|s| s == API_SHADOW) {
                out.shadow.push(p.clone());
            }
            if api.iter().any(|s| s == API_LIGHT_LIST) {
                out.light_list.push(p);
            }
        }
    })?;
    Ok(out)
}

// ────────────────────────────────────────────────────────────────────────
// internal value helpers
// ────────────────────────────────────────────────────────────────────────

fn attr_default(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    let attr = prim.append_property(name)?;
    stage.field::<Value>(attr, "default")
}

fn read_f32(stage: &Stage, prim: &Path, name: &str) -> Result<Option<f32>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Float(f)) => Some(f),
        Some(Value::Double(d)) => Some(d as f32),
        Some(Value::Half(h)) => Some(h.to_f32()),
        Some(Value::Int(i)) => Some(i as f32),
        _ => None,
    })
}

fn read_bool(stage: &Stage, prim: &Path, name: &str) -> Result<Option<bool>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    })
}

fn read_color3f(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f32; 3]>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Vec3f(v)) => Some(v),
        Some(Value::Vec3d(v)) => Some([v[0] as f32, v[1] as f32, v[2] as f32]),
        Some(Value::Vec3h(v)) => Some([v[0].to_f32(), v[1].to_f32(), v[2].to_f32()]),
        _ => None,
    })
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_asset_path(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_default(stage, prim, name)? {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

fn read_rel_first_target(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    Ok(read_rel_targets(stage, prim, rel_name)?.into_iter().next())
}

fn read_rel_targets(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Vec<String>> {
    let rel_path = prim.append_property(rel_name)?;
    let raw = stage.field::<Value>(rel_path, "targetPaths")?;
    let paths = match raw {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    };
    Ok(paths.into_iter().map(|p| p.as_str().to_string()).collect())
}
