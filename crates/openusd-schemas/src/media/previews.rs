//! What `UsdMediaAssetPreviewsAPI` keeps in `assetInfo` rather than in
//! properties of its own.

use std::collections::HashMap;

use openusd::Result;
use openusd::sdf::{FieldKey, Value};
use openusd::usd::SchemaBase;

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
        let Some(Value::Dictionary(asset_info)) =
            self.stage().field::<Value>(self.path().clone(), FieldKey::AssetInfo)?
        else {
            return Ok(None);
        };
        let leaf = asset_info
            .get(tokens::PREVIEWS)
            .and_then(Value::try_as_dictionary_ref)
            .and_then(|d| d.get(tokens::THUMBNAILS).and_then(Value::try_as_dictionary_ref))
            .and_then(|d| d.get(DEFAULT).and_then(Value::try_as_dictionary_ref))
            .and_then(|d| d.get(tokens::DEFAULT_IMAGE));
        Ok(leaf.and_then(Value::as_str).map(str::to_owned))
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
                let previews = nested_dict_mut(&mut asset_info, tokens::PREVIEWS);
                let thumbnails = nested_dict_mut(previews, tokens::THUMBNAILS);
                let default = nested_dict_mut(thumbnails, DEFAULT);
                default.insert(tokens::DEFAULT_IMAGE.to_string(), Value::AssetPath(image.into()));
                Some(Value::Dictionary(asset_info))
            },
        )?;
        Ok(Self(prim))
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
        assert_eq!(a.start_time_attr().get::<sdf::TimeCode>()?, Some(sdf::TimeCode(24.0)));
        assert_eq!(a.media_offset_attr().get::<f64>()?, Some(2.5));
        assert_eq!(a.gain_attr().get::<f64>()?, Some(0.5));
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
            .set_metadata("assetInfo", Value::Dictionary(info))?;
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
