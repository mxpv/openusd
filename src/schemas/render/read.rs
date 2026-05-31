//! Reader functions for the [UsdRender](super) schema family.
//!
//! UsdRender attributes are `uniform` (not time-sampled), so the readers
//! take no `time` argument — each returns the attribute's `default`
//! field, matching Pixar's `UsdAttribute::Get(value)` no-time semantic.
//! Unauthored attributes fall back to the documented defaults via the
//! `Default` impls in [`super::types`].

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read the attributes shared by `RenderSettings` / `RenderProduct` via
/// their abstract base `RenderSettingsBase`. Per-field fallback to the
/// spec default ([`ReadSettingsBase::default`]) for any unauthored attr.
///
/// Not type-gated — both concrete schemas carry these attributes, and the
/// computed render spec reads the base off each prim regardless of which.
pub fn read_settings_base(stage: &Stage, prim: &Path) -> Result<ReadSettingsBase> {
    let d = ReadSettingsBase::default();
    Ok(ReadSettingsBase {
        resolution: read_int2(stage, prim, A_RESOLUTION)?.unwrap_or(d.resolution),
        pixel_aspect_ratio: read_f32(stage, prim, A_PIXEL_ASPECT_RATIO)?.unwrap_or(d.pixel_aspect_ratio),
        aspect_ratio_conform_policy: read_token(stage, prim, A_ASPECT_RATIO_CONFORM_POLICY)?
            .and_then(|t| AspectRatioConformPolicy::from_token(&t))
            .unwrap_or(d.aspect_ratio_conform_policy),
        data_window_ndc: read_float4(stage, prim, A_DATA_WINDOW_NDC)?.unwrap_or(d.data_window_ndc),
        instantaneous_shutter: read_bool(stage, prim, A_INSTANTANEOUS_SHUTTER)?.unwrap_or(d.instantaneous_shutter),
        disable_motion_blur: read_bool(stage, prim, A_DISABLE_MOTION_BLUR)?.unwrap_or(d.disable_motion_blur),
        disable_depth_of_field: read_bool(stage, prim, A_DISABLE_DEPTH_OF_FIELD)?.unwrap_or(d.disable_depth_of_field),
        camera: read_rel_first_target(stage, prim, REL_CAMERA)?,
    })
}

// ── value-read helpers ──────────────────────────────────────────────

fn attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    stage.field::<Value>(prim.append_property(name)?, "default")
}

fn read_f32(stage: &Stage, prim: &Path, name: &str) -> Result<Option<f32>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Float(f)) => Some(f),
        Some(Value::Double(d)) => Some(d.clamp(f32::MIN as f64, f32::MAX as f64) as f32),
        Some(Value::Half(h)) => Some(h.to_f32()),
        _ => None,
    })
}

fn read_bool(stage: &Stage, prim: &Path, name: &str) -> Result<Option<bool>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    })
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_int2(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[i32; 2]>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Vec2i(v)) => Some(v),
        _ => None,
    })
}

fn read_float4(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f32; 4]>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Vec4f(v)) => Some(v),
        Some(Value::Vec4d(v)) => Some([v[0] as f32, v[1] as f32, v[2] as f32, v[3] as f32]),
        _ => None,
    })
}

fn read_rel_first_target(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    let rel_path = prim.append_property(rel_name)?;
    let paths = match stage.field::<Value>(rel_path, "targetPaths")? {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    };
    Ok(paths.into_iter().next().map(|p| p.as_str().to_string()))
}
