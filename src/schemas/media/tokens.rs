//! Token constants for the [UsdMedia](super) schema family.
//!
//! Mirrors the grouping in Pixar's `pxr/usd/usdMedia/tokens.h`.

// ── Concrete prim type names ────────────────────────────────────────
pub const T_SPATIAL_AUDIO: &str = "SpatialAudio";

// ── SpatialAudio attribute names ────────────────────────────────────
pub const A_FILE_PATH: &str = "filePath";
pub const A_AURAL_MODE: &str = "auralMode";
pub const A_PLAYBACK_MODE: &str = "playbackMode";
pub const A_START_TIME: &str = "startTime";
pub const A_END_TIME: &str = "endTime";
pub const A_MEDIA_OFFSET: &str = "mediaOffset";
pub const A_GAIN: &str = "gain";

// ── `auralMode` token values ────────────────────────────────────────
pub const AURAL_SPATIAL: &str = "spatial";
pub const AURAL_NON_SPATIAL: &str = "nonSpatial";

// ── `playbackMode` token values ─────────────────────────────────────
pub const PLAYBACK_ONCE_IMAGE_VISIBLE: &str = "onceImageVisible";
pub const PLAYBACK_ONCE_IMAGE_INACTIVE: &str = "onceImageInactive";
pub const PLAYBACK_ON_START: &str = "onStart";
pub const PLAYBACK_NONE: &str = "none";
