//! UsdMedia schema reader + authoring.
//!
//! Decodes and authors Pixar's `UsdMedia` family. The one concrete schema
//! is [`tokens::T_SPATIAL_AUDIO`] - a sound source that is also
//! `Imageable` / `Xformable` (its transform / visibility / purpose come
//! from the UsdGeom layer; this module covers the media-specific
//! attributes).
//!
//! # Defaults
//!
//! [`ReadSpatialAudio`]'s `Default` matches Pixar's `usdMedia/schema.usda`
//! fallbacks (`auralMode = spatial`, `playbackMode = onceImageVisible`,
//! `gain = 1.0`), so callers can `unwrap_or_default()` for a spec-correct
//! fallback.

pub mod tokens;

mod author;
mod read;
mod types;

pub use author::{define_spatial_audio, SpatialAudioAuthor};
pub use read::read_spatial_audio;
pub use types::{AuralMode, PlaybackMode, ReadSpatialAudio};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;
    use crate::usd::Stage;
    use anyhow::Result;

    #[test]
    fn spatial_audio_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_spatial_audio(&stage, sdf::path("/World/Audio")?)?
            .set_file_path("./ambient.wav")?
            .set_aural_mode(AuralMode::NonSpatial)?
            .set_playback_mode(PlaybackMode::LoopFromStartToEnd)?
            .set_start_time(24.0)?
            .set_end_time(48.0)?
            .set_media_offset(2.5)?
            .set_gain(0.5)?;

        let a = read_spatial_audio(&stage, &sdf::path("/World/Audio")?)?.expect("SpatialAudio");
        assert_eq!(a.file_path.as_deref(), Some("./ambient.wav"));
        assert_eq!(a.aural_mode, AuralMode::NonSpatial);
        assert_eq!(a.playback_mode, PlaybackMode::LoopFromStartToEnd);
        assert_eq!(a.start_time, 24.0);
        assert_eq!(a.end_time, 48.0);
        assert_eq!(a.media_offset, 2.5);
        assert_eq!(a.gain, 0.5);
        Ok(())
    }

    #[test]
    fn spatial_audio_defaults_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_spatial_audio(&stage, sdf::path("/Audio")?)?;

        let a = read_spatial_audio(&stage, &sdf::path("/Audio")?)?.expect("SpatialAudio");
        assert_eq!(a, ReadSpatialAudio::default());
        assert_eq!(a.aural_mode, AuralMode::Spatial);
        assert_eq!(a.playback_mode, PlaybackMode::OnceFromStart);
        assert_eq!(a.gain, 1.0);

        // A non-SpatialAudio prim reads back as None.
        stage.define_prim(sdf::path("/NotAudio")?)?.set_type_name("Scope")?;
        assert!(read_spatial_audio(&stage, &sdf::path("/NotAudio")?)?.is_none());
        Ok(())
    }
}
