//! Integration tests for the UsdMedia schema views against a fixture.

use anyhow::Result;

use openusd::schemas::media::{AssetPreviewsAPI, AuralMode, PlaybackMode, SpatialAudio};
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdMedia_scene.usda";

#[test]
fn spatial_audio_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    let a = SpatialAudio::get(&stage, sdf::path("/World/Ambient")?)?.expect("SpatialAudio");

    assert_eq!(
        a.file_path_attr().get::<sdf::Value>()?,
        Some(sdf::Value::AssetPath("./ambient.wav".into()))
    );
    assert_eq!(
        a.aural_mode_attr()
            .get::<Token>()?
            .as_deref()
            .and_then(AuralMode::from_token),
        Some(AuralMode::NonSpatial)
    );
    assert_eq!(
        a.playback_mode_attr()
            .get::<Token>()?
            .as_deref()
            .and_then(PlaybackMode::from_token),
        Some(PlaybackMode::LoopFromStart)
    );
    // startTime / endTime are `timecode`-valued.
    assert_eq!(a.start_time_attr().get::<sdf::TimeCode>()?, Some(sdf::TimeCode(24.0)));
    assert_eq!(a.end_time_attr().get::<sdf::TimeCode>()?, Some(sdf::TimeCode(48.0)));
    assert_eq!(a.media_offset_attr().get::<f64>()?, Some(2.5));
    assert_eq!(a.gain_attr().get::<f64>()?, Some(0.5));

    // A non-SpatialAudio prim reads back as None.
    assert!(SpatialAudio::get(&stage, sdf::path("/World")?)?.is_none());
    Ok(())
}

#[test]
fn asset_preview_thumbnail_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    let previews = AssetPreviewsAPI::get(&stage, sdf::path("/World/Chair")?)?.expect("AssetPreviewsAPI");
    assert_eq!(previews.default_thumbnail()?.as_deref(), Some("./chair_thumb.jpg"));

    // A prim without the API applied is not wrapped.
    assert!(AssetPreviewsAPI::get(&stage, sdf::path("/World/Ambient")?)?.is_none());
    Ok(())
}

#[test]
fn token_round_trips() {
    assert_eq!(AuralMode::default(), AuralMode::Spatial);
    assert_eq!(AuralMode::NonSpatial.as_token(), "nonSpatial");
    assert_eq!(AuralMode::from_token("spatial"), Some(AuralMode::Spatial));
    assert_eq!(AuralMode::from_token("bogus"), None);

    assert_eq!(PlaybackMode::default(), PlaybackMode::OnceFromStart);
    assert_eq!(
        PlaybackMode::from_token("loopFromStage"),
        Some(PlaybackMode::LoopFromStage)
    );
    assert_eq!(PlaybackMode::LoopFromStartToEnd.as_token(), "loopFromStartToEnd");
}
