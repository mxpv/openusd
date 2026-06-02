//! Decoded enums + read struct for the [UsdMedia](super) schema family.

use super::tokens::*;

/// `auralMode` — whether the audio is positioned in 3D or plays flat.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AuralMode {
    /// Positioned in 3D relative to the listener (the spec default).
    #[default]
    Spatial,
    /// Played without spatialization (e.g. background music).
    NonSpatial,
}

impl AuralMode {
    pub fn as_token(self) -> &'static str {
        match self {
            AuralMode::Spatial => AURAL_SPATIAL,
            AuralMode::NonSpatial => AURAL_NON_SPATIAL,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            AURAL_SPATIAL => AuralMode::Spatial,
            AURAL_NON_SPATIAL => AuralMode::NonSpatial,
            _ => return None,
        })
    }
}

/// `playbackMode` — how/when the audio plays relative to the stage's
/// `startTimeCode` / `endTimeCode` (spec `UsdMediaSpatialAudio`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PlaybackMode {
    /// Play once, starting at `startTime` (the spec default).
    #[default]
    OnceFromStart,
    /// Play once, from `startTime` to `endTime`.
    OnceFromStartToEnd,
    /// Loop, starting at `startTime`.
    LoopFromStart,
    /// Loop, between `startTime` and `endTime`.
    LoopFromStartToEnd,
    /// Loop over the whole stage playback range.
    LoopFromStage,
}

impl PlaybackMode {
    pub fn as_token(self) -> &'static str {
        match self {
            PlaybackMode::OnceFromStart => PLAYBACK_ONCE_FROM_START,
            PlaybackMode::OnceFromStartToEnd => PLAYBACK_ONCE_FROM_START_TO_END,
            PlaybackMode::LoopFromStart => PLAYBACK_LOOP_FROM_START,
            PlaybackMode::LoopFromStartToEnd => PLAYBACK_LOOP_FROM_START_TO_END,
            PlaybackMode::LoopFromStage => PLAYBACK_LOOP_FROM_STAGE,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            PLAYBACK_ONCE_FROM_START => PlaybackMode::OnceFromStart,
            PLAYBACK_ONCE_FROM_START_TO_END => PlaybackMode::OnceFromStartToEnd,
            PLAYBACK_LOOP_FROM_START => PlaybackMode::LoopFromStart,
            PLAYBACK_LOOP_FROM_START_TO_END => PlaybackMode::LoopFromStartToEnd,
            PLAYBACK_LOOP_FROM_STAGE => PlaybackMode::LoopFromStage,
            _ => return None,
        })
    }
}

/// A `SpatialAudio` prim's media attributes.
///
/// `Default` matches Pixar's `usdMedia/schema.usda` fallbacks. The prim
/// is also `Imageable` / `Xformable`; its transform, visibility, and
/// purpose are read/authored through the UsdGeom layer.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadSpatialAudio {
    /// `filePath` - the audio asset, if authored.
    pub file_path: Option<String>,
    /// `auralMode` (default `spatial`).
    pub aural_mode: AuralMode,
    /// `playbackMode` (default `onceFromStart`).
    pub playback_mode: PlaybackMode,
    /// `startTime` - media start in stage time (default `0`).
    pub start_time: f64,
    /// `endTime` - media end in stage time (default `0`).
    pub end_time: f64,
    /// `mediaOffset` - offset into the media file (default `0.0`).
    pub media_offset: f64,
    /// `gain` - volume multiplier (default `1.0`).
    pub gain: f64,
}

impl Default for ReadSpatialAudio {
    fn default() -> Self {
        Self {
            file_path: None,
            aural_mode: AuralMode::default(),
            playback_mode: PlaybackMode::default(),
            start_time: 0.0,
            end_time: 0.0,
            media_offset: 0.0,
            gain: 1.0,
        }
    }
}
