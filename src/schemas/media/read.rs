//! Reader for the [UsdMedia](super) schema family.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::Stage;

use crate::schemas::common::{read_asset, read_f64, read_token};

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
