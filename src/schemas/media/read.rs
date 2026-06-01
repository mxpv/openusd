//! Reader for the [UsdMedia](super) schema family.

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `SpatialAudio` prim's media attributes. Returns `None` when the
/// prim is not typed `SpatialAudio`, so a caller can't fabricate a
/// defaulted struct from an arbitrary prim. Unauthored attributes fall
/// back to the spec defaults.
pub fn read_spatial_audio(stage: &Stage, prim: &Path) -> Result<Option<ReadSpatialAudio>> {
    if stage.type_name(prim)?.as_deref() != Some(T_SPATIAL_AUDIO) {
        return Ok(None);
    }
    let d = ReadSpatialAudio::default();
    Ok(Some(ReadSpatialAudio {
        file_path: read_asset(stage, prim, A_FILE_PATH)?,
        aural_mode: read_token(stage, prim, A_AURAL_MODE)?
            .and_then(|t| AuralMode::from_token(&t))
            .unwrap_or(d.aural_mode),
        playback_mode: read_token(stage, prim, A_PLAYBACK_MODE)?
            .and_then(|t| PlaybackMode::from_token(&t))
            .unwrap_or(d.playback_mode),
        start_time: read_f64(stage, prim, A_START_TIME)?.unwrap_or(d.start_time),
        end_time: read_f64(stage, prim, A_END_TIME)?.unwrap_or(d.end_time),
        media_offset: read_f64(stage, prim, A_MEDIA_OFFSET)?.unwrap_or(d.media_offset),
        gain: read_f64(stage, prim, A_GAIN)?.unwrap_or(d.gain),
    }))
}

fn attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    stage.field::<Value>(prim.append_property(name)?, FieldKey::Default)
}

fn read_asset(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_f64(stage: &Stage, prim: &Path, name: &str) -> Result<Option<f64>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::TimeCode(d) | Value::Double(d)) => Some(d),
        Some(Value::Float(f)) => Some(f as f64),
        Some(Value::Half(h)) => Some(h.to_f32() as f64),
        Some(Value::Int64(i)) => Some(i as f64),
        Some(Value::Int(i)) => Some(i as f64),
        _ => None,
    })
}
