//! The UsdMedia schema views: [`SpatialAudio`] and [`AssetPreviewsAPI`].

use std::collections::HashMap;

use anyhow::Result;

use crate::schemas::common::{get_typed, get_with_api, value_as_asset_str};
use crate::sdf::{self, FieldKey, Value};
use crate::usd::{Attribute, Prim, Stage};

use super::impl_media_schema;
use super::tokens as tok;

/// An audio source prim (C++ `UsdMediaSpatialAudio`) — a
/// [`geom::Xformable`](crate::schemas::geom::Xformable) prim placing audio in
/// the scene. `auralMode` selects spatial vs. non-spatial playback; the
/// `startTime` / `endTime` cues are `timecode`-valued.
#[derive(Clone, derive_more::Deref)]
pub struct SpatialAudio(Prim);

impl SpatialAudio {
    /// Author a `def SpatialAudio` prim at `path`
    /// (C++ `UsdMediaSpatialAudio::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SPATIAL_AUDIO)?))
    }

    /// Wrap `path` as a `SpatialAudio` if it is typed `SpatialAudio`
    /// (C++ `UsdMediaSpatialAudio::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SPATIAL_AUDIO).map(|o| o.map(Self))
    }

    /// `filePath` attribute handle — the audio asset (C++ `GetFilePathAttr`).
    ///
    /// `uniform asset`: `get::<sdf::Value>()?` yields a [`sdf::Value::AssetPath`].
    pub fn file_path_attr(&self) -> Attribute {
        self.attribute(tok::A_FILE_PATH)
    }

    /// Author `filePath` (`uniform asset`) (C++ `CreateFilePathAttr`).
    pub fn create_file_path_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FILE_PATH, "asset")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `auralMode` attribute handle (C++ `GetAuralModeAttr`).
    ///
    /// `uniform token`: `get::<sdf::Value>()?` yields the token (`spatial` /
    /// `nonSpatial`); decode it with
    /// [`AuralMode::from_token`](super::AuralMode::from_token).
    pub fn aural_mode_attr(&self) -> Attribute {
        self.attribute(tok::A_AURAL_MODE)
    }

    /// Author `auralMode` (`uniform token`) (C++ `CreateAuralModeAttr`).
    pub fn create_aural_mode_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_AURAL_MODE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `playbackMode` attribute handle (C++ `GetPlaybackModeAttr`).
    ///
    /// `uniform token`: `get::<sdf::Value>()?` yields the token (`onceFromStart`
    /// / `loopFromStage` / …); decode it with
    /// [`PlaybackMode::from_token`](super::PlaybackMode::from_token).
    pub fn playback_mode_attr(&self) -> Attribute {
        self.attribute(tok::A_PLAYBACK_MODE)
    }

    /// Author `playbackMode` (`uniform token`) (C++ `CreatePlaybackModeAttr`).
    pub fn create_playback_mode_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_PLAYBACK_MODE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `startTime` attribute handle — playback start cue
    /// (C++ `GetStartTimeAttr`).
    ///
    /// `uniform timecode`: read with `get::<sdf::TimeCode>()?`.
    pub fn start_time_attr(&self) -> Attribute {
        self.attribute(tok::A_START_TIME)
    }

    /// Author `startTime` (`uniform timecode`) (C++ `CreateStartTimeAttr`).
    /// Set its value as an [`sdf::TimeCode`].
    pub fn create_start_time_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_START_TIME, "timecode")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `endTime` attribute handle — playback end cue (C++ `GetEndTimeAttr`).
    ///
    /// `uniform timecode`: read with `get::<sdf::TimeCode>()?`.
    pub fn end_time_attr(&self) -> Attribute {
        self.attribute(tok::A_END_TIME)
    }

    /// Author `endTime` (`uniform timecode`) (C++ `CreateEndTimeAttr`).
    pub fn create_end_time_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_END_TIME, "timecode")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `mediaOffset` attribute handle — offset into the asset, in seconds
    /// (C++ `GetMediaOffsetAttr`).
    ///
    /// `uniform double`: read with `get::<f64>()?`.
    pub fn media_offset_attr(&self) -> Attribute {
        self.attribute(tok::A_MEDIA_OFFSET)
    }

    /// Author `mediaOffset` (`uniform double`) (C++ `CreateMediaOffsetAttr`).
    pub fn create_media_offset_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_MEDIA_OFFSET, "double")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// `gain` attribute handle — linear amplitude multiplier
    /// (C++ `GetGainAttr`).
    ///
    /// `double`: read with `get::<f64>()?`.
    pub fn gain_attr(&self) -> Attribute {
        self.attribute(tok::A_GAIN)
    }

    /// Author `gain` (`double`) (C++ `CreateGainAttr`).
    pub fn create_gain_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_GAIN, "double")?.set_custom(false)?)
    }
}

impl_media_schema!(xformable SpatialAudio);

/// Pre-rendered previews of an asset (C++ `UsdMediaAssetPreviewsAPI`). Apply
/// it to a prim, then author / read its default thumbnail; the data lives in
/// the prim's `assetInfo` metadata rather than as schema attributes:
///
/// ```text
/// assetInfo = {
///     dictionary previews = {
///         dictionary thumbnails = {
///             dictionary default = { asset defaultImage = @chair_thumb.jpg@ }
///         }
///     }
/// }
/// ```
#[derive(Clone, derive_more::Deref)]
pub struct AssetPreviewsAPI(Prim);

impl AssetPreviewsAPI {
    /// Apply `AssetPreviewsAPI` to the prim at `path`
    /// (C++ `UsdMediaAssetPreviewsAPI::Apply`). The prim is opened as `over`.
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.override_prim(path)?.add_applied_schema(tok::API_ASSET_PREVIEWS)?,
        ))
    }

    /// Wrap `path` as an `AssetPreviewsAPI` if it carries `AssetPreviewsAPI` in
    /// its `apiSchemas` (C++ `UsdMediaAssetPreviewsAPI::Get`); returns `None`
    /// otherwise.
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_ASSET_PREVIEWS]).map(|o| o.map(Self))
    }

    /// The default thumbnail image path
    /// (`assetInfo.previews.thumbnails.default.defaultImage`), or `None` when
    /// no preview is authored (C++ `GetDefaultThumbnails`).
    pub fn default_thumbnail(&self) -> Result<Option<String>> {
        let Some(Value::Dictionary(asset_info)) =
            self.stage().field::<Value>(self.path().clone(), FieldKey::AssetInfo)?
        else {
            return Ok(None);
        };
        let leaf = nested_dict(&asset_info, tok::PREVIEWS)
            .and_then(|d| nested_dict(d, tok::THUMBNAILS))
            .and_then(|d| nested_dict(d, tok::PREVIEW_DEFAULT))
            .and_then(|d| d.get(tok::DEFAULT_IMAGE));
        Ok(leaf.and_then(value_as_asset_str).map(str::to_owned))
    }

    /// Author the default thumbnail image path under the prim's `assetInfo`
    /// (`previews.thumbnails.default.defaultImage`) (C++ `SetDefaultThumbnails`).
    ///
    /// Only the `previews` sub-tree is merged into the edit target's own
    /// `assetInfo` opinion; other `assetInfo` keys (whether authored locally or
    /// on weaker layers) are left to compose, so the thumbnail does not flatten
    /// them into the edit target.
    pub fn set_default_thumbnail(self, image: impl Into<String>) -> Result<Self> {
        let image = image.into();
        let prim = self.stage().override_prim(self.path().clone())?.update_metadata(
            FieldKey::AssetInfo.as_str(),
            |local| {
                let mut asset_info = match local {
                    Some(Value::Dictionary(d)) => d,
                    _ => HashMap::new(),
                };
                let previews = nested_dict_mut(&mut asset_info, tok::PREVIEWS);
                let thumbnails = nested_dict_mut(previews, tok::THUMBNAILS);
                let default = nested_dict_mut(thumbnails, tok::PREVIEW_DEFAULT);
                default.insert(tok::DEFAULT_IMAGE.to_string(), Value::AssetPath(image));
                Value::Dictionary(asset_info)
            },
        )?;
        Ok(Self(prim))
    }
}

impl_media_schema!(applied_api AssetPreviewsAPI);

/// Borrow a nested dictionary by `key`, if present and dictionary-valued.
fn nested_dict<'a>(d: &'a HashMap<String, Value>, key: &str) -> Option<&'a HashMap<String, Value>> {
    match d.get(key) {
        Some(Value::Dictionary(inner)) => Some(inner),
        _ => None,
    }
}

/// Get-or-create a nested dictionary at `key`, replacing a non-dictionary
/// value if one is somehow there.
fn nested_dict_mut<'a>(d: &'a mut HashMap<String, Value>, key: &str) -> &'a mut HashMap<String, Value> {
    let entry = d
        .entry(key.to_string())
        .or_insert_with(|| Value::Dictionary(HashMap::new()));
    if !matches!(entry, Value::Dictionary(_)) {
        *entry = Value::Dictionary(HashMap::new());
    }
    let Value::Dictionary(inner) = entry else {
        unreachable!("entry was just ensured to be a dictionary")
    };
    inner
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::media::{AuralMode, PlaybackMode};

    #[test]
    fn spatial_audio_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let a = SpatialAudio::define(&stage, "/World/Audio")?;
        a.create_file_path_attr()?
            .set(sdf::Value::AssetPath("./ambient.wav".into()))?;
        a.create_aural_mode_attr()?
            .set(sdf::Value::Token(AuralMode::NonSpatial.as_token().into()))?;
        a.create_playback_mode_attr()?
            .set(sdf::Value::Token(PlaybackMode::LoopFromStartToEnd.as_token().into()))?;
        a.create_start_time_attr()?.set(sdf::TimeCode(24.0))?;
        a.create_end_time_attr()?.set(sdf::TimeCode(48.0))?;
        a.create_media_offset_attr()?.set(2.5_f64)?;
        a.create_gain_attr()?.set(0.5_f64)?;

        let a = SpatialAudio::get(&stage, "/World/Audio")?.expect("SpatialAudio");
        assert_eq!(
            a.file_path_attr().get::<sdf::Value>()?,
            Some(sdf::Value::AssetPath("./ambient.wav".into()))
        );
        assert_eq!(a.start_time_attr().get::<sdf::TimeCode>()?, Some(sdf::TimeCode(24.0)));
        assert_eq!(a.media_offset_attr().get::<f64>()?, Some(2.5));
        assert_eq!(a.gain_attr().get::<f64>()?, Some(0.5));
        assert!(SpatialAudio::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    #[test]
    fn get_rejects_non_spatial_audio() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/NotAudio")?.set_type_name("Scope")?;
        assert!(SpatialAudio::get(&stage, "/NotAudio")?.is_none());
        Ok(())
    }

    #[test]
    fn asset_previews_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Chair")?.set_type_name("Xform")?;
        AssetPreviewsAPI::apply(&stage, "/Chair")?.set_default_thumbnail("./chair_thumb.jpg")?;

        assert!(stage.has_api_schema(&sdf::path("/Chair")?, tok::API_ASSET_PREVIEWS)?);
        let previews = AssetPreviewsAPI::get(&stage, "/Chair")?.expect("AssetPreviewsAPI");
        assert_eq!(previews.default_thumbnail()?.as_deref(), Some("./chair_thumb.jpg"));
        Ok(())
    }

    #[test]
    fn get_rejects_unapplied() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Bare")?.set_type_name("Xform")?;
        assert!(AssetPreviewsAPI::get(&stage, "/Bare")?.is_none());
        Ok(())
    }

    #[test]
    fn set_thumbnail_preserves_other_asset_info() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let mut info = HashMap::new();
        info.insert("name".to_string(), Value::String("Chair".to_string()));
        stage
            .define_prim("/Chair")?
            .set_type_name("Xform")?
            .set_metadata("assetInfo", Value::Dictionary(info))?;
        AssetPreviewsAPI::apply(&stage, "/Chair")?.set_default_thumbnail("./t.jpg")?;

        // The pre-existing `name` entry survives alongside the new previews.
        let Some(Value::Dictionary(info)) = stage.field::<Value>(sdf::path("/Chair")?, FieldKey::AssetInfo)? else {
            panic!("assetInfo");
        };
        assert_eq!(info.get("name"), Some(&Value::String("Chair".to_string())));
        assert!(info.contains_key(tok::PREVIEWS));
        Ok(())
    }
}
