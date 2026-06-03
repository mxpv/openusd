//! UsdMedia schema views.
//!
//! Typed value-views over a composed [`crate::usd::Stage`], mirroring Pixar's
//! `UsdMedia` family:
//!
//! - [`SpatialAudio`] (C++ `UsdMediaSpatialAudio`) — a sound source. It is a
//!   [`geom::Xformable`](crate::schemas::geom::Xformable) prim (its transform
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
//! `foo_attr()` returns an [`crate::usd::Attribute`] handle whose `get()`
//! yields the authored value (or `None` — there is no schema registry yet to
//! supply fallbacks), and `create_foo_attr()` authors the attribute with its
//! schema-declared type / variability. The `startTime` / `endTime` attributes
//! are `timecode`, so they read / write as [`sdf::TimeCode`].
//!
//! `auralMode` / `playbackMode` decode through the [`AuralMode`] /
//! [`PlaybackMode`] enums via `from_token` / `as_token`.
//!
//! # Example
//!
//! ```
//! use openusd::schemas::media::{AuralMode, SpatialAudio};
//! use openusd::sdf;
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder().in_memory("scene.usda")?;
//!
//! // Author a non-spatial ambient track that loops from frame 24 to 48.
//! let audio = SpatialAudio::define(&stage, "/World/Ambient")?;
//! audio.create_file_path_attr()?.set(sdf::Value::AssetPath("./ambient.wav".into()))?;
//! audio.create_aural_mode_attr()?.set(sdf::Value::Token(AuralMode::NonSpatial.as_token().into()))?;
//! audio.create_start_time_attr()?.set(sdf::TimeCode(24.0))?;
//! audio.create_end_time_attr()?.set(sdf::TimeCode(48.0))?;
//! audio.create_gain_attr()?.set(0.5_f64)?;
//!
//! // Read it back through a typed view.
//! let audio = SpatialAudio::get(&stage, "/World/Ambient")?.expect("SpatialAudio");
//! assert_eq!(audio.start_time_attr().get::<sdf::TimeCode>()?, Some(sdf::TimeCode(24.0)));
//! let mode = audio
//!     .aural_mode_attr()
//!     .get::<sdf::Value>()?
//!     .and_then(|v| v.try_as_token())
//!     .and_then(|t| AuralMode::from_token(&t));
//! assert_eq!(mode, Some(AuralMode::NonSpatial));
//! # Ok::<(), Box<dyn std::error::Error + Send + Sync>>(())
//! ```

pub mod tokens;

mod schema;

pub use schema::{AssetPreviewsAPI, SpatialAudio};

use tokens::*;

/// Implement the schema-trait chain for a concrete `struct $ty(Prim)` media
/// newtype. All trait paths are fully qualified, so the call site only needs
/// the macro in scope.
///
/// - `xformable` is a typed [`geom::Xformable`](crate::schemas::geom::Xformable)
///   prim (`SpatialAudio`).
/// - `applied_api` is a single-apply API-schema view (`AssetPreviewsAPI`).
macro_rules! impl_media_schema {
    (xformable $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
        impl $crate::schemas::geom::Imageable for $ty {}
        impl $crate::schemas::geom::Xformable for $ty {}
    };
    (applied_api $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::SingleApplyApi;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
}

pub(crate) use impl_media_schema;

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
