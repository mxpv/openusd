//! Reader functions for the [UsdLux](super) schema family.
//!
//! Each `read_*_light` helper returns the populated struct (or `None`
//! when the prim isn't typed as the expected light kind). Unauthored
//! attributes fall back to Pixar's documented defaults via the
//! `Default` impls in [`super::types`].
//!
//! `read_light_api` returns the common LightAPI inputs from a prim
//! that's either typed as a concrete UsdLux light or carries
//! `LightAPI`, `MeshLightAPI`, or `VolumeLightAPI` as an applied
//! schema; per-light readers call the internal `read_light_inputs`
//! helper directly since they've already verified the prim's typeName.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read the common `LightAPI` inputs from a light prim.
///
/// Returns the attribute's `default` field for every `inputs:*` —
/// matches Pixar's `UsdAttribute::Get(value)` no-time-arg semantic, so
/// authored `timeSamples` are NOT evaluated. Use
/// [`read_light_api_at`] when you need an animated value resolved at
/// a specific stage time.
///
/// Returns `None` when the prim isn't a concrete UsdLux light type and
/// doesn't carry `LightAPI`, `MeshLightAPI`, or `VolumeLightAPI` as an
/// applied schema — that way callers can't accidentally produce a
/// fully-defaulted "light" out of an arbitrary prim.
pub fn read_light_api(stage: &Stage, prim: &Path) -> Result<Option<ReadLight>> {
    read_light_api_inner(stage, prim, None)
}

/// [`read_light_api`] resolved at stage time `time`. Authored
/// `timeSamples` interpolate against the stage's
/// [`crate::usd::InterpolationType`].
pub fn read_light_api_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadLight>> {
    read_light_api_inner(stage, prim, Some(time))
}

fn read_light_api_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadLight>> {
    let type_name = stage.type_name(prim)?;
    if type_name.as_deref() == Some(T_DISTANT_LIGHT) {
        let intensity_fallback = ReadDistantLight::default().common.intensity;
        return Ok(Some(read_light_inputs_with_intensity(
            stage,
            prim,
            time,
            intensity_fallback,
        )?));
    }
    if type_name.as_deref().is_some_and(is_light_type) || has_light_api_schema(stage, prim)? {
        return Ok(Some(read_light_inputs(stage, prim, time)?));
    }
    Ok(None)
}

fn has_light_api_schema(stage: &Stage, prim: &Path) -> Result<bool> {
    Ok(stage.api_schemas(prim)?.iter().any(|s| is_light_api_schema(s)))
}

fn is_light_api_schema(name: &str) -> bool {
    matches!(name, API_LIGHT | API_MESH_LIGHT | API_VOLUME_LIGHT)
}

/// Inner helper used by both the gated [`read_light_api`] and the
/// per-light readers (which have already validated the typeName).
/// Falls back to LightAPI's documented `inputs:intensity = 1.0`
/// default.
fn read_light_inputs(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<ReadLight> {
    read_light_inputs_with_intensity(stage, prim, time, ReadLight::default().intensity)
}

/// Variant of [`read_light_inputs`] that lets `DistantLight` (whose
/// schema overrides LightAPI's intensity default to 50000) substitute
/// its own fallback without querying `inputs:intensity` twice.
fn read_light_inputs_with_intensity(
    stage: &Stage,
    prim: &Path,
    time: Option<f64>,
    intensity_fallback: f32,
) -> Result<ReadLight> {
    let defaults = ReadLight::default();
    Ok(ReadLight {
        path: prim.as_str().to_string(),
        intensity: read_f32(stage, prim, A_INTENSITY, time)?.unwrap_or(intensity_fallback),
        exposure: read_f32(stage, prim, A_EXPOSURE, time)?.unwrap_or(defaults.exposure),
        diffuse: read_f32(stage, prim, A_DIFFUSE, time)?.unwrap_or(defaults.diffuse),
        specular: read_f32(stage, prim, A_SPECULAR, time)?.unwrap_or(defaults.specular),
        normalize: read_bool(stage, prim, A_NORMALIZE, time)?.unwrap_or(defaults.normalize),
        color: read_color3f(stage, prim, A_COLOR, time)?.unwrap_or(defaults.color),
        enable_color_temperature: read_bool(stage, prim, A_ENABLE_COLOR_TEMPERATURE, time)?
            .unwrap_or(defaults.enable_color_temperature),
        color_temperature: read_f32(stage, prim, A_COLOR_TEMPERATURE, time)?.unwrap_or(defaults.color_temperature),
        filters: read_rel_targets(stage, prim, REL_FILTERS)?,
    })
}

/// Read a `DistantLight` prim. Returns `None` when the prim isn't
/// typed `DistantLight`.
pub fn read_distant_light(stage: &Stage, prim: &Path) -> Result<Option<ReadDistantLight>> {
    read_distant_light_inner(stage, prim, None)
}

/// [`read_distant_light`] resolved at stage time `time`. Animated
/// `inputs:*` interpolate per the stage's
/// [`crate::usd::InterpolationType`].
pub fn read_distant_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadDistantLight>> {
    read_distant_light_inner(stage, prim, Some(time))
}

fn read_distant_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadDistantLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_DISTANT_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadDistantLight::default();
    Ok(Some(ReadDistantLight {
        common: read_light_inputs_with_intensity(stage, prim, time, defaults.common.intensity)?,
        angle_deg: read_f32(stage, prim, A_ANGLE, time)?.unwrap_or(defaults.angle_deg),
    }))
}

/// Read a `SphereLight` prim. Returns `None` when the prim isn't
/// typed `SphereLight`.
pub fn read_sphere_light(stage: &Stage, prim: &Path) -> Result<Option<ReadSphereLight>> {
    read_sphere_light_inner(stage, prim, None)
}

/// [`read_sphere_light`] resolved at stage time `time`.
pub fn read_sphere_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadSphereLight>> {
    read_sphere_light_inner(stage, prim, Some(time))
}

fn read_sphere_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadSphereLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_SPHERE_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadSphereLight::default();
    Ok(Some(ReadSphereLight {
        common: read_light_inputs(stage, prim, time)?,
        radius: read_f32(stage, prim, A_RADIUS, time)?.unwrap_or(defaults.radius),
        treat_as_point: read_bool(stage, prim, A_TREAT_AS_POINT, time)?.unwrap_or(defaults.treat_as_point),
    }))
}

/// Read a `RectLight` prim. Returns `None` when the prim isn't typed
/// `RectLight`.
pub fn read_rect_light(stage: &Stage, prim: &Path) -> Result<Option<ReadRectLight>> {
    read_rect_light_inner(stage, prim, None)
}

/// [`read_rect_light`] resolved at stage time `time`.
pub fn read_rect_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadRectLight>> {
    read_rect_light_inner(stage, prim, Some(time))
}

fn read_rect_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadRectLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_RECT_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadRectLight::default();
    Ok(Some(ReadRectLight {
        common: read_light_inputs(stage, prim, time)?,
        width: read_f32(stage, prim, A_WIDTH, time)?.unwrap_or(defaults.width),
        height: read_f32(stage, prim, A_HEIGHT, time)?.unwrap_or(defaults.height),
        texture_file: read_asset_path(stage, prim, A_TEXTURE_FILE, time)?,
    }))
}

/// Read a `DiskLight` prim. Returns `None` when the prim isn't typed
/// `DiskLight`.
pub fn read_disk_light(stage: &Stage, prim: &Path) -> Result<Option<ReadDiskLight>> {
    read_disk_light_inner(stage, prim, None)
}

/// [`read_disk_light`] resolved at stage time `time`.
pub fn read_disk_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadDiskLight>> {
    read_disk_light_inner(stage, prim, Some(time))
}

fn read_disk_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadDiskLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_DISK_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadDiskLight::default();
    Ok(Some(ReadDiskLight {
        common: read_light_inputs(stage, prim, time)?,
        radius: read_f32(stage, prim, A_RADIUS, time)?.unwrap_or(defaults.radius),
    }))
}

/// Read a `CylinderLight` prim. Returns `None` when the prim isn't
/// typed `CylinderLight`.
pub fn read_cylinder_light(stage: &Stage, prim: &Path) -> Result<Option<ReadCylinderLight>> {
    read_cylinder_light_inner(stage, prim, None)
}

/// [`read_cylinder_light`] resolved at stage time `time`.
pub fn read_cylinder_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadCylinderLight>> {
    read_cylinder_light_inner(stage, prim, Some(time))
}

fn read_cylinder_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadCylinderLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_CYLINDER_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadCylinderLight::default();
    Ok(Some(ReadCylinderLight {
        common: read_light_inputs(stage, prim, time)?,
        length: read_f32(stage, prim, A_LENGTH, time)?.unwrap_or(defaults.length),
        radius: read_f32(stage, prim, A_RADIUS, time)?.unwrap_or(defaults.radius),
        treat_as_line: read_bool(stage, prim, A_TREAT_AS_LINE, time)?.unwrap_or(defaults.treat_as_line),
    }))
}

/// Read a `DomeLight` or `DomeLight_1` prim. Both surface the same
/// reader struct; the type-name distinction is a Pixar versioning
/// artefact and the attribute set is functionally identical for
/// consumers.
pub fn read_dome_light(stage: &Stage, prim: &Path) -> Result<Option<ReadDomeLight>> {
    read_dome_light_inner(stage, prim, None)
}

/// [`read_dome_light`] resolved at stage time `time`.
pub fn read_dome_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadDomeLight>> {
    read_dome_light_inner(stage, prim, Some(time))
}

fn read_dome_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadDomeLight>> {
    let type_name = stage.type_name(prim)?;
    if !matches!(type_name.as_deref(), Some(T_DOME_LIGHT) | Some(T_DOME_LIGHT_1)) {
        return Ok(None);
    }
    let is_v1_1 = type_name.as_deref() == Some(T_DOME_LIGHT_1);
    let defaults = ReadDomeLight::default();
    Ok(Some(ReadDomeLight {
        common: read_light_inputs(stage, prim, time)?,
        texture_file: read_asset_path(stage, prim, A_TEXTURE_FILE, time)?,
        texture_format: read_token(stage, prim, A_TEXTURE_FORMAT, time)?
            .as_deref()
            .and_then(TextureFormat::from_token)
            .unwrap_or_default(),
        portals: read_rel_targets(stage, prim, REL_PORTALS)?,
        guide_radius: read_f32(stage, prim, A_GUIDE_RADIUS, time)?.unwrap_or(defaults.guide_radius),
        // poleAxis is a DomeLight_1-only addition; surface it as `None`
        // for legacy DomeLight even if a stray opinion is authored.
        pole_axis: if is_v1_1 {
            read_token(stage, prim, A_POLE_AXIS, time)?
                .as_deref()
                .and_then(PoleAxis::from_token)
        } else {
            None
        },
    }))
}

/// Read a `GeometryLight` prim. Returns `None` when the prim isn't
/// typed `GeometryLight`.
pub fn read_geometry_light(stage: &Stage, prim: &Path) -> Result<Option<ReadGeometryLight>> {
    read_geometry_light_inner(stage, prim, None)
}

/// [`read_geometry_light`] resolved at stage time `time`.
pub fn read_geometry_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadGeometryLight>> {
    read_geometry_light_inner(stage, prim, Some(time))
}

fn read_geometry_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadGeometryLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_GEOMETRY_LIGHT) {
        return Ok(None);
    }
    Ok(Some(ReadGeometryLight {
        common: read_light_inputs(stage, prim, time)?,
        geometry: read_rel_first_target(stage, prim, REL_GEOMETRY)?,
    }))
}

/// Read a `PortalLight` prim. Returns `None` when the prim isn't
/// typed `PortalLight`.
pub fn read_portal_light(stage: &Stage, prim: &Path) -> Result<Option<ReadPortalLight>> {
    read_portal_light_inner(stage, prim, None)
}

/// [`read_portal_light`] resolved at stage time `time`.
pub fn read_portal_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadPortalLight>> {
    read_portal_light_inner(stage, prim, Some(time))
}

fn read_portal_light_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadPortalLight>> {
    if stage.type_name(prim)?.as_deref() != Some(T_PORTAL_LIGHT) {
        return Ok(None);
    }
    let defaults = ReadPortalLight::default();
    Ok(Some(ReadPortalLight {
        common: read_light_inputs(stage, prim, time)?,
        width: read_f32(stage, prim, A_WIDTH, time)?.unwrap_or(defaults.width),
        height: read_f32(stage, prim, A_HEIGHT, time)?.unwrap_or(defaults.height),
    }))
}

/// Dispatch on the prim's `typeName` and return the matching
/// concrete light variant. Returns `None` when the prim isn't a
/// recognised UsdLux light type.
pub fn read_light(stage: &Stage, prim: &Path) -> Result<Option<ReadAnyLight>> {
    read_light_dispatch(stage, prim, None)
}

/// [`read_light`] resolved at stage time `time`.
pub fn read_light_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadAnyLight>> {
    read_light_dispatch(stage, prim, Some(time))
}

fn read_light_dispatch(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadAnyLight>> {
    let Some(type_name) = stage.type_name(prim)? else {
        return Ok(None);
    };
    Ok(match type_name.as_str() {
        T_DISTANT_LIGHT => read_distant_light_inner(stage, prim, time)?.map(ReadAnyLight::Distant),
        T_SPHERE_LIGHT => read_sphere_light_inner(stage, prim, time)?.map(ReadAnyLight::Sphere),
        T_RECT_LIGHT => read_rect_light_inner(stage, prim, time)?.map(ReadAnyLight::Rect),
        T_DISK_LIGHT => read_disk_light_inner(stage, prim, time)?.map(ReadAnyLight::Disk),
        T_CYLINDER_LIGHT => read_cylinder_light_inner(stage, prim, time)?.map(ReadAnyLight::Cylinder),
        T_DOME_LIGHT | T_DOME_LIGHT_1 => read_dome_light_inner(stage, prim, time)?.map(ReadAnyLight::Dome),
        T_GEOMETRY_LIGHT => read_geometry_light_inner(stage, prim, time)?.map(ReadAnyLight::Geometry),
        T_PORTAL_LIGHT => read_portal_light_inner(stage, prim, time)?.map(ReadAnyLight::Portal),
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
    read_shaping_inner(stage, prim, None)
}

/// [`read_shaping`] resolved at stage time `time`.
pub fn read_shaping_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadShaping>> {
    read_shaping_inner(stage, prim, Some(time))
}

fn read_shaping_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadShaping>> {
    if !stage.has_api_schema(prim, API_SHAPING)? {
        return Ok(None);
    }
    let defaults = ReadShaping::default();
    Ok(Some(ReadShaping {
        focus: read_f32(stage, prim, A_SHAPING_FOCUS, time)?.unwrap_or(defaults.focus),
        focus_tint: read_color3f(stage, prim, A_SHAPING_FOCUS_TINT, time)?.unwrap_or(defaults.focus_tint),
        cone_angle_deg: read_f32(stage, prim, A_SHAPING_CONE_ANGLE, time)?.unwrap_or(defaults.cone_angle_deg),
        cone_softness: read_f32(stage, prim, A_SHAPING_CONE_SOFTNESS, time)?.unwrap_or(defaults.cone_softness),
        ies_file: read_asset_path(stage, prim, A_SHAPING_IES_FILE, time)?,
        ies_angle_scale: read_f32(stage, prim, A_SHAPING_IES_ANGLE_SCALE, time)?.unwrap_or(defaults.ies_angle_scale),
        ies_normalize: read_bool(stage, prim, A_SHAPING_IES_NORMALIZE, time)?.unwrap_or(defaults.ies_normalize),
    }))
}

/// Read `ShadowAPI` on a light prim. Returns `None` when the API
/// isn't applied.
pub fn read_shadow(stage: &Stage, prim: &Path) -> Result<Option<ReadShadow>> {
    read_shadow_inner(stage, prim, None)
}

/// [`read_shadow`] resolved at stage time `time`.
pub fn read_shadow_at(stage: &Stage, prim: &Path, time: f64) -> Result<Option<ReadShadow>> {
    read_shadow_inner(stage, prim, Some(time))
}

fn read_shadow_inner(stage: &Stage, prim: &Path, time: Option<f64>) -> Result<Option<ReadShadow>> {
    if !stage.has_api_schema(prim, API_SHADOW)? {
        return Ok(None);
    }
    let defaults = ReadShadow::default();
    Ok(Some(ReadShadow {
        enable: read_bool(stage, prim, A_SHADOW_ENABLE, time)?.unwrap_or(defaults.enable),
        color: read_color3f(stage, prim, A_SHADOW_COLOR, time)?.unwrap_or(defaults.color),
        distance: read_f32(stage, prim, A_SHADOW_DISTANCE, time)?.unwrap_or(defaults.distance),
        falloff: read_f32(stage, prim, A_SHADOW_FALLOFF, time)?.unwrap_or(defaults.falloff),
        falloff_gamma: read_f32(stage, prim, A_SHADOW_FALLOFF_GAMMA, time)?.unwrap_or(defaults.falloff_gamma),
    }))
}

/// Read `LightListAPI` on a prim. Returns `None` when the API isn't
/// applied.
///
/// `lightList:cacheBehavior` is `uniform token` per Pixar's schema —
/// not animatable — so there is no `_at(time)` sibling.
pub fn read_light_list(stage: &Stage, prim: &Path) -> Result<Option<ReadLightList>> {
    if !stage.has_api_schema(prim, API_LIGHT_LIST)? {
        return Ok(None);
    }
    Ok(Some(ReadLightList {
        lights: read_rel_targets(stage, prim, REL_LIGHT_LIST)?,
        cache_behavior: read_token(stage, prim, A_LIGHT_LIST_CACHE_BEHAVIOR, None)?
            .as_deref()
            .and_then(LightListCacheBehavior::from_token)
            .unwrap_or_default(),
    }))
}

/// Walk the stage once and return categorised path lists for every
/// recognised UsdLux prim type plus prims carrying any of the
/// UsdLux applied APIs.
///
/// Uses the default traversal predicate (active + defined + loaded +
/// non-abstract), matching the convention shared with `find_geom_prims`
/// and `find_physics_prims`. Consumers that need to see inactive or
/// class prims should iterate over `stage.traverse_all` themselves and
/// dispatch via [`read_light`] / [`read_shaping`] / etc.
pub fn find_lux_prims(stage: &Stage) -> Result<LuxPrims> {
    let mut out = LuxPrims::default();
    // Stage::traverse's visitor returns `()`, so we capture the first
    // error in this slot and short-circuit the rest of the walk.
    // Without this, type_name / api_schemas failures would be
    // silently dropped via `if let Ok(...)`.
    let mut err: Result<()> = Ok(());
    stage.traverse(|path| {
        if err.is_err() {
            return;
        }
        err = bucket_lux_prim(stage, path, &mut out);
    })?;
    err?;
    Ok(out)
}

/// Inspect `path`'s typeName and apiSchemas and push it into the
/// matching [`LuxPrims`] buckets. Returns early with an error if any
/// stage query fails.
fn bucket_lux_prim(stage: &Stage, path: &Path, out: &mut LuxPrims) -> Result<()> {
    let p = path.as_str().to_string();
    let mut concrete_typed = true;
    if let Some(type_name) = stage.type_name(path)? {
        match type_name.as_str() {
            T_DISTANT_LIGHT => out.distant.push(p.clone()),
            T_SPHERE_LIGHT => out.sphere.push(p.clone()),
            T_RECT_LIGHT => out.rect.push(p.clone()),
            T_DISK_LIGHT => out.disk.push(p.clone()),
            T_CYLINDER_LIGHT => out.cylinder.push(p.clone()),
            T_DOME_LIGHT | T_DOME_LIGHT_1 => out.dome.push(p.clone()),
            T_GEOMETRY_LIGHT => out.geometry.push(p.clone()),
            T_PORTAL_LIGHT => out.portal.push(p.clone()),
            T_LIGHT_FILTER => {
                out.light_filters.push(p.clone());
                concrete_typed = false;
            }
            _ => concrete_typed = false,
        }
    } else {
        concrete_typed = false;
    }
    let api = stage.api_schemas(path)?;
    if api.iter().any(|s| s == API_SHAPING) {
        out.shaping.push(p.clone());
    }
    if api.iter().any(|s| s == API_SHADOW) {
        out.shadow.push(p.clone());
    }
    if api.iter().any(|s| s == API_LIGHT_LIST) {
        out.light_list.push(p.clone());
    }
    // Bucket prims that carry LightAPI / MeshLightAPI /
    // VolumeLightAPI without being one of the concrete light
    // typeNames — the canonical way to make an arbitrary mesh or
    // volume emissive.
    if !concrete_typed && api.iter().any(|s| is_light_api_schema(s)) {
        out.light_api.push(p);
    }
    Ok(())
}

// ────────────────────────────────────────────────────────────────────────
// internal value helpers
// ────────────────────────────────────────────────────────────────────────

/// Read an attribute's value. `time = None` returns the attribute's
/// `default` field only — matching Pixar's `UsdAttribute::Get(value)`
/// no-time-arg semantic. `time = Some(t)` routes through
/// [`Stage::value_at`] so authored `timeSamples` interpolate against
/// the stage's [`crate::usd::InterpolationType`].
fn attr_value(stage: &Stage, prim: &Path, name: &str, time: Option<f64>) -> Result<Option<Value>> {
    let attr = prim.append_property(name)?;
    match time {
        None => stage.field::<Value>(attr, "default"),
        Some(t) => stage.value_at(attr, t),
    }
}

fn read_f32(stage: &Stage, prim: &Path, name: &str, time: Option<f64>) -> Result<Option<f32>> {
    Ok(match attr_value(stage, prim, name, time)? {
        Some(Value::Float(f)) => Some(f),
        // Double values that exceed f32's finite range saturate to
        // ±infinity via `as`, which can flip sentinel-driven branches
        // (e.g. shadow:distance treats -1.0 / -inf as "unbounded").
        // Clamp to f32::MIN / f32::MAX instead so consumers see a
        // finite-but-huge value rather than an unintended unbounded one.
        Some(Value::Double(d)) => Some(d.clamp(f32::MIN as f64, f32::MAX as f64) as f32),
        Some(Value::Half(h)) => Some(h.to_f32()),
        _ => None,
    })
}

fn read_bool(stage: &Stage, prim: &Path, name: &str, time: Option<f64>) -> Result<Option<bool>> {
    Ok(match attr_value(stage, prim, name, time)? {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    })
}

fn read_color3f(stage: &Stage, prim: &Path, name: &str, time: Option<f64>) -> Result<Option<[f32; 3]>> {
    Ok(match attr_value(stage, prim, name, time)? {
        Some(Value::Vec3f(v)) => Some(v),
        Some(Value::Vec3d(v)) => Some([v[0] as f32, v[1] as f32, v[2] as f32]),
        Some(Value::Vec3h(v)) => Some([v[0].to_f32(), v[1].to_f32(), v[2].to_f32()]),
        _ => None,
    })
}

fn read_token(stage: &Stage, prim: &Path, name: &str, time: Option<f64>) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name, time)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_asset_path(stage: &Stage, prim: &Path, name: &str, time: Option<f64>) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name, time)? {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

fn read_rel_first_target(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    Ok(read_rel_targets(stage, prim, rel_name)?.into_iter().next())
}

// TODO: this only flattens the strongest layer's PathListOp.
// Cross-layer relationship composition — e.g. `append rel lightList`
// in a stronger layer over a base `rel lightList` — needs a Stage-level
// composed-relationship helper that doesn't exist yet (analogous to how
// `Stage::api_schemas` composes apiSchemas listOps). Until that lands,
// multi-layer `lightList` / `light:filters` / `portals` / `geometry`
// opinions may surface only the strongest layer's targets.
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
