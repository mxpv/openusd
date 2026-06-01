//! Integration test for the `UsdMedia` schema reader against a fixture.

use anyhow::Result;

use openusd::schemas::media::{read_default_thumbnail, read_spatial_audio, AuralMode, PlaybackMode};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdMedia_scene.usda";

#[test]
fn reads_spatial_audio_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    let a = read_spatial_audio(&stage, &sdf::path("/World/Ambient")?)?.expect("SpatialAudio");
    assert_eq!(a.file_path.as_deref(), Some("./ambient.wav"));
    assert_eq!(a.aural_mode, AuralMode::NonSpatial);
    assert_eq!(a.playback_mode, PlaybackMode::LoopFromStart);
    assert_eq!(a.start_time, 24.0);
    assert_eq!(a.end_time, 48.0);
    assert_eq!(a.media_offset, 2.5);
    assert_eq!(a.gain, 0.5);

    // A non-SpatialAudio prim reads back as None.
    assert!(read_spatial_audio(&stage, &sdf::path("/World")?)?.is_none());
    Ok(())
}

#[test]
fn reads_asset_preview_thumbnail_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    assert_eq!(
        read_default_thumbnail(&stage, &sdf::path("/World/Chair")?)?.as_deref(),
        Some("./chair_thumb.jpg"),
    );
    Ok(())
}
