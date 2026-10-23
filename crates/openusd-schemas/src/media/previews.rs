//! What `UsdMediaAssetPreviewsAPI` keeps in `assetInfo` rather than in
//! properties of its own.

use openusd::Result;
use openusd::sdf::Value;
use openusd::usd::{Object, SchemaBase};

use super::AssetPreviewsAPI;
use super::tokens;

/// The one key in this dictionary that upstream declares no token for: the
/// thumbnail every asset has unless a caller asks for a named one.
const DEFAULT: &str = "default";

impl AssetPreviewsAPI {
    /// The asset's default preview thumbnail image path, read from
    /// `assetInfo.previews.thumbnails.default.defaultImage`, or `None` when no
    /// preview is authored. C++ `UsdMediaAssetPreviewsAPI::GetDefaultThumbnails`.
    pub fn default_thumbnail(&self) -> Result<Option<String>> {
        let image = self.prim().asset_info_by_key(&default_image_path())?;
        Ok(image.as_ref().and_then(Value::as_str).map(str::to_owned))
    }

    /// Author the default thumbnail image path under the prim's `assetInfo`
    /// (`previews.thumbnails.default.defaultImage`) (C++ `SetDefaultThumbnails`).
    ///
    /// Only the `previews` sub-tree is merged into the edit target's own
    /// `assetInfo` opinion; other `assetInfo` keys (whether authored locally or
    /// on weaker layers) are left to compose, so the thumbnail does not flatten
    /// them into the edit target.
    pub fn set_default_thumbnail(self, image: impl Into<String>) -> Result<Self> {
        let image = Value::AssetPath(image.into().into());
        let prim = self
            .stage()
            .override_prim(self.path().clone())?
            .set_asset_info_by_key(&default_image_path(), image)?;
        Ok(Self(prim))
    }
}

/// The `assetInfo` key path of the default thumbnail's image.
fn default_image_path() -> String {
    format!(
        "{}:{}:{DEFAULT}:{}",
        tokens::PREVIEWS,
        tokens::THUMBNAILS,
        tokens::DEFAULT_IMAGE
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    use openusd::sdf::FieldKey;

    use crate::media::{AuralMode, PlaybackMode, SpatialAudio, SpatialAudioSchema};
    use openusd::Result;
    use openusd::sdf;

    #[test]
    fn spatial_audio_roundtrip() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
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
        assert_eq!(a.start_time()?, Some(sdf::TimeCode(24.0)));
        assert_eq!(a.media_offset()?, Some(2.5));
        assert_eq!(a.gain()?, Some(0.5));
        assert!(SpatialAudio::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    #[test]
    fn get_rejects_non_spatial_audio() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/NotAudio")?.set_type_name("Scope")?;
        assert!(SpatialAudio::get(&stage, "/NotAudio")?.is_none());
        Ok(())
    }

    #[test]
    fn asset_previews_roundtrip() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let chair = stage.define_prim("/Chair")?;
        chair.clone().set_type_name("Xform")?;
        AssetPreviewsAPI::apply(&chair)?.set_default_thumbnail("./chair_thumb.jpg")?;

        assert!(stage.prim("/Chair")?.has_api_schema(tokens::ASSET_PREVIEWS_API)?);
        let previews = AssetPreviewsAPI::get(&stage, "/Chair")?.expect("AssetPreviewsAPI");
        assert_eq!(previews.default_thumbnail()?.as_deref(), Some("./chair_thumb.jpg"));
        Ok(())
    }

    #[test]
    fn get_rejects_unapplied() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Bare")?.set_type_name("Xform")?;
        assert!(AssetPreviewsAPI::get(&stage, "/Bare")?.is_none());
        Ok(())
    }

    #[test]
    fn set_thumbnail_preserves_other_asset_info() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let mut info = HashMap::new();
        info.insert("name".to_string(), Value::String("Chair".to_string()));
        let chair = stage
            .define_prim("/Chair")?
            .set_type_name("Xform")?
            .set_metadata("assetInfo", Value::Dictionary(info.into()))?;
        AssetPreviewsAPI::apply(&chair)?.set_default_thumbnail("./t.jpg")?;

        // The pre-existing `name` entry survives alongside the new previews.
        let Some(Value::Dictionary(info)) = stage.field::<Value>("/Chair", FieldKey::AssetInfo)? else {
            panic!("assetInfo");
        };
        assert_eq!(info.get("name"), Some(&Value::String("Chair".to_string())));
        assert!(info.contains_key(tokens::PREVIEWS));
        Ok(())
    }
}
