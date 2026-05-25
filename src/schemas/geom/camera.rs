//! `UsdGeomCamera` reader.
//!
//! Pulls every authored attribute on a Camera prim into a
//! [`ReadCamera`], falling back to Pixar's documented defaults
//! (50 mm lens, perspective projection, etc.) for anything unauthored.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `Camera` prim. Returns `None` when the prim isn't typed
/// `Camera`.
pub fn read_camera(stage: &Stage, prim: &Path) -> Result<Option<ReadCamera>> {
    if stage.type_name(prim)?.as_deref() != Some(T_CAMERA) {
        return Ok(None);
    }
    let defaults = ReadCamera::default();
    Ok(Some(ReadCamera {
        focal_length: read_f32(stage, prim, A_FOCAL_LENGTH)?.unwrap_or(defaults.focal_length),
        horizontal_aperture: read_f32(stage, prim, A_HORIZONTAL_APERTURE)?.unwrap_or(defaults.horizontal_aperture),
        vertical_aperture: read_f32(stage, prim, A_VERTICAL_APERTURE)?.unwrap_or(defaults.vertical_aperture),
        horizontal_aperture_offset: read_f32(stage, prim, A_HORIZONTAL_APERTURE_OFFSET)?
            .unwrap_or(defaults.horizontal_aperture_offset),
        vertical_aperture_offset: read_f32(stage, prim, A_VERTICAL_APERTURE_OFFSET)?
            .unwrap_or(defaults.vertical_aperture_offset),
        f_stop: read_f32(stage, prim, A_F_STOP)?.unwrap_or(defaults.f_stop),
        focus_distance: read_f32(stage, prim, A_FOCUS_DISTANCE)?.unwrap_or(defaults.focus_distance),
        projection: read_projection(stage, prim)?,
        clipping_range: read_clipping_range(stage, prim)?.unwrap_or(defaults.clipping_range),
        clipping_planes: read_clipping_planes(stage, prim)?,
        shutter_open: read_f32(stage, prim, A_SHUTTER_OPEN)?.unwrap_or(defaults.shutter_open),
        shutter_close: read_f32(stage, prim, A_SHUTTER_CLOSE)?.unwrap_or(defaults.shutter_close),
        exposure: read_f32(stage, prim, A_EXPOSURE)?.unwrap_or(defaults.exposure),
        exposure_iso: read_f32(stage, prim, A_EXPOSURE_ISO)?.unwrap_or(defaults.exposure_iso),
        exposure_time: read_f32(stage, prim, A_EXPOSURE_TIME)?.unwrap_or(defaults.exposure_time),
        exposure_f_stop: read_f32(stage, prim, A_EXPOSURE_F_STOP)?.unwrap_or(defaults.exposure_f_stop),
        exposure_responsivity: read_f32(stage, prim, A_EXPOSURE_RESPONSIVITY)?
            .unwrap_or(defaults.exposure_responsivity),
        stereo_role: read_stereo_role(stage, prim)?,
    }))
}

// ────────────────────────────────────────────────────────────────────────
// internal helpers
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

fn read_projection(stage: &Stage, prim: &Path) -> Result<Projection> {
    Ok(match attr_default(stage, prim, A_PROJECTION)? {
        Some(Value::Token(s) | Value::String(s)) => Projection::from_token(&s).unwrap_or_default(),
        _ => Projection::default(),
    })
}

fn read_stereo_role(stage: &Stage, prim: &Path) -> Result<StereoRole> {
    Ok(match attr_default(stage, prim, A_STEREO_ROLE)? {
        Some(Value::Token(s) | Value::String(s)) => StereoRole::from_token(&s).unwrap_or_default(),
        _ => StereoRole::default(),
    })
}

fn read_clipping_range(stage: &Stage, prim: &Path) -> Result<Option<[f32; 2]>> {
    Ok(match attr_default(stage, prim, A_CLIPPING_RANGE)? {
        Some(Value::Vec2f(v)) => Some(v),
        Some(Value::Vec2d(v)) => Some([v[0] as f32, v[1] as f32]),
        _ => None,
    })
}

fn read_clipping_planes(stage: &Stage, prim: &Path) -> Result<Vec<[f32; 4]>> {
    Ok(match attr_default(stage, prim, A_CLIPPING_PLANES)? {
        Some(Value::Vec4fVec(v)) => v,
        Some(Value::Vec4dVec(v)) => v
            .into_iter()
            .map(|p| [p[0] as f32, p[1] as f32, p[2] as f32, p[3] as f32])
            .collect(),
        _ => Vec::new(),
    })
}
