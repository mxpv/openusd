//! `SpatialAudio` authoring.
//!
//! Authors the media-specific attributes. The prim is also
//! `Imageable` / `Xformable`; its transform / visibility / purpose are
//! authored through the UsdGeom layer on the same prim.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::common::{
    author_double, author_uniform_asset, author_uniform_double, author_uniform_timecode, author_uniform_token,
};
use crate::schemas::media::tokens::*;
use crate::schemas::media::types::{AuralMode, PlaybackMode};

/// Author a `def SpatialAudio` prim at `path`. Returns a chainable
/// [`SpatialAudioAuthor`].
pub fn define_spatial_audio<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<SpatialAudioAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_SPATIAL_AUDIO)?;
    Ok(SpatialAudioAuthor { prim })
}

pub struct SpatialAudioAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> SpatialAudioAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `filePath` (`uniform asset`).
    pub fn set_file_path(self, path: impl Into<String>) -> Result<Self> {
        author_uniform_asset(self.prim.stage(), self.prim.path(), A_FILE_PATH, path)?;
        Ok(self)
    }

    /// Set `auralMode` (`uniform token`).
    pub fn set_aural_mode(self, mode: AuralMode) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_AURAL_MODE, mode.as_token())?;
        Ok(self)
    }

    /// Set `playbackMode` (`uniform token`).
    pub fn set_playback_mode(self, mode: PlaybackMode) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_PLAYBACK_MODE, mode.as_token())?;
        Ok(self)
    }

    /// Set `startTime` (`uniform timecode`).
    pub fn set_start_time(self, value: f64) -> Result<Self> {
        author_uniform_timecode(self.prim.stage(), self.prim.path(), A_START_TIME, value)?;
        Ok(self)
    }

    /// Set `endTime` (`uniform timecode`).
    pub fn set_end_time(self, value: f64) -> Result<Self> {
        author_uniform_timecode(self.prim.stage(), self.prim.path(), A_END_TIME, value)?;
        Ok(self)
    }

    /// Set `mediaOffset` (`uniform double`).
    pub fn set_media_offset(self, value: f64) -> Result<Self> {
        author_uniform_double(self.prim.stage(), self.prim.path(), A_MEDIA_OFFSET, value)?;
        Ok(self)
    }

    /// Set `gain` (`double`, varying).
    pub fn set_gain(self, value: f64) -> Result<Self> {
        author_double(self.prim.stage(), self.prim.path(), A_GAIN, value)?;
        Ok(self)
    }
}
