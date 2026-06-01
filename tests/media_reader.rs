//! Integration test for the `UsdMedia` schema reader against a fixture.

use anyhow::Result;

use openusd::schemas::media::{read_spatial_audio, AuralMode, PlaybackMode};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdMedia_scene.usda";

#[test]
fn reads_spatial_audio_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    let a = read_spatial_audio(&stage, &sdf::path("/World/Ambient")?)?.expect("SpatialAudio");
    assert_eq!(a.file_path.as_deref(), Some("./ambient.wav"));
    assert_eq!(a.aural_mode, AuralMode::NonSpatial);
    assert_eq!(a.playback_mode, PlaybackMode::OnStart);
    assert_eq!(a.media_offset, 2.5);
    assert_eq!(a.gain, 0.5);
    // Unauthored timecode fields fall back to the spec default.
    assert_eq!(a.start_time, 0.0);
    assert_eq!(a.end_time, 0.0);

    // A non-SpatialAudio prim reads back as None.
    assert!(read_spatial_audio(&stage, &sdf::path("/World")?)?.is_none());
    Ok(())
}
