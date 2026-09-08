//! UsdMedia schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdMedia` family:
//!
//! - [`SpatialAudio`] (C++ `UsdMediaSpatialAudio`) — a sound source. It is a
//!   [`geom::Xformable`](crate::geom::Xformable) prim (its transform
//!   / visibility / purpose come from the UsdGeom layer); this module adds the
//!   media-specific attributes (`filePath`, `auralMode`, `playbackMode`,
//!   `startTime` / `endTime`, `mediaOffset`, `gain`).
//! - [`AssetPreviewsAPI`] (C++ `UsdMediaAssetPreviewsAPI`) — a single-apply API
//!   schema encoding pre-rendered previews (thumbnails) under a prim's
//!   `assetInfo` metadata.
//!
//! # Conventions
//!
//! Property accessors mirror the C++ `Get*Attr` / `Create*Attr` pair: a
//! `foo_attr()` returns an [`openusd::usd::Attribute`] handle whose `get()`
//! yields the authored value, or the fallback the schema declares when
//! nothing is authored (see [`openusd::usd::SchemaRegistry`]), and `create_foo_attr()` authors
//! the attribute with its schema-declared type / variability. The `startTime`
//! / `endTime` attributes are `timecode`, so they read / write as
//! [`openusd::sdf::TimeCode`].
//!
//! `auralMode` / `playbackMode` decode through the [`AuralMode`] /
//! [`PlaybackMode`] enums via `from_token` / `as_token`.
//!
//! # Example
//!
//! ```
//! use openusd_schemas::media::{AuralMode, SpatialAudio, SpatialAudioSchema};
//! use openusd::sdf;
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda").unwrap();
//!
//! // Author a non-spatial ambient track that loops from frame 24 to 48.
//! let audio = SpatialAudio::define(&stage, "/World/Ambient").unwrap();
//! audio.create_file_path_attr().unwrap().set(sdf::Value::AssetPath("./ambient.wav".into())).unwrap();
//! audio.create_aural_mode_attr().unwrap().set(sdf::Value::Token(AuralMode::NonSpatial.as_token().into())).unwrap();
//! audio.create_start_time_attr().unwrap().set(sdf::TimeCode(24.0)).unwrap();
//! audio.create_end_time_attr().unwrap().set(sdf::TimeCode(48.0)).unwrap();
//! audio.create_gain_attr().unwrap().set(0.5_f64).unwrap();
//!
//! // Read it back through a typed view.
//! let audio = SpatialAudio::get(&stage, "/World/Ambient").unwrap().expect("SpatialAudio");
//! assert_eq!(audio.start_time_attr().get::<sdf::TimeCode>().unwrap(), Some(sdf::TimeCode(24.0)));
//! let mode = audio
//!     .aural_mode_attr()
//!     .get::<sdf::Value>().unwrap()
//!     .and_then(|v| v.try_as_token())
//!     .and_then(AuralMode::from_token);
//! assert_eq!(mode, Some(AuralMode::NonSpatial));
//! ```

openusd::include_schema!("usdMedia");

mod previews;

use openusd::tf;
use tokens::*;

// Token-valued attribute enums. Each decodes one `allowedTokens` attribute via
// `from_token` / `as_token`, with the Pixar default as its `Default`.

/// `UsdMediaSpatialAudio.auralMode` token values. The spec default is
/// [`AuralMode::Spatial`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AuralMode {
    #[default]
    Spatial,
    NonSpatial,
}

impl AuralMode {
    pub fn as_token(self) -> &'static str {
        match self {
            AuralMode::Spatial => SPATIAL,
            AuralMode::NonSpatial => NON_SPATIAL,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            SPATIAL => AuralMode::Spatial,
            NON_SPATIAL => AuralMode::NonSpatial,
            _ => return None,
        })
    }
}

/// `UsdMediaSpatialAudio.playbackMode` token values. The spec default is
/// [`PlaybackMode::OnceFromStart`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PlaybackMode {
    #[default]
    OnceFromStart,
    OnceFromStartToEnd,
    LoopFromStart,
    LoopFromStartToEnd,
    LoopFromStage,
}

impl PlaybackMode {
    pub fn as_token(self) -> &'static str {
        match self {
            PlaybackMode::OnceFromStart => ONCE_FROM_START,
            PlaybackMode::OnceFromStartToEnd => ONCE_FROM_START_TO_END,
            PlaybackMode::LoopFromStart => LOOP_FROM_START,
            PlaybackMode::LoopFromStartToEnd => LOOP_FROM_START_TO_END,
            PlaybackMode::LoopFromStage => LOOP_FROM_STAGE,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            ONCE_FROM_START => PlaybackMode::OnceFromStart,
            ONCE_FROM_START_TO_END => PlaybackMode::OnceFromStartToEnd,
            LOOP_FROM_START => PlaybackMode::LoopFromStart,
            LOOP_FROM_START_TO_END => PlaybackMode::LoopFromStartToEnd,
            LOOP_FROM_STAGE => PlaybackMode::LoopFromStage,
            _ => return None,
        })
    }
}
