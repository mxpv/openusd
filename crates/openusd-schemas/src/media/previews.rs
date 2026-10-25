//! What `UsdMediaAssetPreviewsAPI` keeps in `assetInfo` rather than in
//! properties of its own.

use openusd::Result;
use openusd::ar;
use openusd::sdf::{self, Value};
use openusd::usd::{self, Object, SchemaBase};

use super::AssetPreviewsAPI;
use super::tokens;

/// The default thumbnail images of an asset, the dictionary at
/// `assetInfo["previews:thumbnails:default"]` (C++
/// `UsdMediaAssetPreviewsAPI::Thumbnails`).
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Thumbnails {
    /// `defaultImage`: the image that stands for the asset.
    pub default_image: sdf::AssetPath,
}

impl AssetPreviewsAPI {
    /// The prim's default thumbnails (C++ `GetDefaultThumbnails`). `None`
    /// unless the prim has the API applied, the value at
    /// `previews:thumbnails:default` is a dictionary, and its `defaultImage`
    /// is an asset path.
    pub fn default_thumbnails(&self) -> Result<Option<Thumbnails>> {
        if !self.prim().has_api_schema(tokens::ASSET_PREVIEWS_API)? {
            return Ok(None);
        }
        let thumbnails = self.prim().asset_info_by_key(tokens::PREVIEW_THUMBNAILS_DEFAULT)?;
        Ok(thumbnails
            .and_then(Value::try_as_dictionary)
            .and_then(|mut thumbnails| thumbnails.remove(tokens::DEFAULT_IMAGE))
            .and_then(Value::try_as_asset_path)
            .map(|default_image| Thumbnails { default_image }))
    }

    /// Author `thumbnails` as the prim's default thumbnails (C++
    /// `SetDefaultThumbnails`). The dictionary at `previews:thumbnails:default`
    /// in the edit target is replaced whole, keys beside `defaultImage`
    /// included. The prim need not have the API applied, as in C++.
    pub fn set_default_thumbnails(self, thumbnails: &Thumbnails) -> Result<Self> {
        let dictionary = sdf::Dictionary::from([(
            tokens::DEFAULT_IMAGE.to_string(),
            Value::AssetPath(thumbnails.default_image.clone()),
        )]);
        let prim = self
            .0
            .set_asset_info_by_key(tokens::PREVIEW_THUMBNAILS_DEFAULT, Value::Dictionary(dictionary))?;
        Ok(Self(prim))
    }

    /// Drop the edit target's default thumbnails (C++
    /// `ClearDefaultThumbnails`).
    pub fn clear_default_thumbnails(self) -> Result<Self> {
        let prim = self.0.clear_asset_info_by_key(tokens::PREVIEW_THUMBNAILS_DEFAULT)?;
        Ok(Self(prim))
    }

    /// The previews of the asset at `layer_path`, the
    /// [`layer_default_previews`](Self::layer_default_previews) of the layer
    /// read from it (C++ `GetAssetDefaultPreviews(layerPath)`). A layer that
    /// fails to open is an error, where C++ answers no previews.
    // TODO: C++ reuses a layer already open at `layer_path`, which needs
    // layers shared between stages (C++ `SdfLayer::FindOrOpen`).
    pub fn asset_default_previews(layer_path: &str) -> Result<Option<Self>> {
        // One cache scope spans the read and the stage open, so a package is
        // opened once.
        let _scope = ar::CacheScope::begin();
        Self::layer_default_previews(sdf::Layer::open(layer_path)?)
    }

    /// The previews of the asset `layer` holds: the API on its default prim
    /// (C++ `GetAssetDefaultPreviews(layer)`). `None` where the layer names no
    /// default prim, or the default prim does not have the API applied. A
    /// stage that fails to open is an error, where C++ answers no previews.
    ///
    /// The view is on a stage of its own, masked to the default prim and its
    /// ancestors, which the view keeps open. `layer` moves into that stage, and
    /// an edit through the view changes it there.
    pub fn layer_default_previews(layer: sdf::Layer) -> Result<Option<Self>> {
        let Some(default_prim) = layer
            .pseudo_root()
            .and_then(|root| root.default_prim())
            .and_then(|name| sdf::default_prim_path(&name))
        else {
            return Ok(None);
        };
        // A child that no prim has keeps the mask to the default prim and its
        // ancestors, without the prims beneath it.
        let mask = usd::StagePopulationMask::new([default_prim.append_path(NO_SUCH_PRIM)?])?;
        let stage = usd::Stage::builder()
            .schema_registry(crate::schema_registry())
            .mask(mask)
            .open_layer(layer)?;
        Self::from_prim(stage.prim(default_prim)?)
    }
}

/// A child name no prim has (C++ `__No_Such_Prim__`).
const NO_SUCH_PRIM: &str = "__No_Such_Prim__";

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
    fn get_rejects_unapplied() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Bare")?.set_type_name("Xform")?;
        assert!(AssetPreviewsAPI::get(&stage, "/Bare")?.is_none());
        Ok(())
    }

    /// An `Xform` at `/Chair` on a stage of its own.
    fn chair() -> Result<usd::Prim> {
        Ok(crate::tests::stage("anon.usda")?
            .define_prim("/Chair")?
            .set_type_name("Xform")?)
    }

    /// Thumbnails with `image` as their default image.
    fn thumbnails(image: &str) -> Thumbnails {
        Thumbnails {
            default_image: image.into(),
        }
    }

    /// The thumbnails read before the API is applied are none, even once
    /// authored; after it is applied they read back (C++
    /// `testUsdMediaAssetPreviewsAPI.py`'s `test_DefaultThumbnails`).
    #[test]
    fn thumbnails_need_api() -> Result<()> {
        let chair = chair()?;
        let previews = AssetPreviewsAPI::from_prim_unchecked(chair.clone());
        assert_eq!(previews.default_thumbnails()?, None);

        let previews = previews.set_default_thumbnails(&thumbnails("./chair_thumb.jpg"))?;
        assert_eq!(previews.default_thumbnails()?, None);

        let previews = AssetPreviewsAPI::apply(&chair)?;
        assert_eq!(previews.default_thumbnails()?, Some(thumbnails("./chair_thumb.jpg")));
        Ok(())
    }

    /// A `defaultImage` that is a string, not an asset path, reads as none.
    #[test]
    fn thumbnails_asset_only() -> Result<()> {
        let chair = chair()?;
        AssetPreviewsAPI::apply(&chair)?;
        let key = format!("{}:{}", tokens::PREVIEW_THUMBNAILS_DEFAULT, tokens::DEFAULT_IMAGE);
        let chair = chair.set_asset_info_by_key(&key, Value::String("./chair_thumb.jpg".into()))?;
        assert_eq!(AssetPreviewsAPI::from_prim_unchecked(chair).default_thumbnails()?, None);
        Ok(())
    }

    /// A set replaces the whole `default` dictionary.
    #[test]
    fn set_replaces_dictionary() -> Result<()> {
        let chair = chair()?;
        let sibling = format!("{}:sibling", tokens::PREVIEW_THUMBNAILS_DEFAULT);
        let chair = chair.set_asset_info_by_key(&sibling, Value::Int(1))?;
        let previews = AssetPreviewsAPI::apply(&chair)?.set_default_thumbnails(&thumbnails("./t.jpg"))?;
        assert_eq!(previews.prim().asset_info_by_key(&sibling)?, None);
        assert_eq!(previews.default_thumbnails()?, Some(thumbnails("./t.jpg")));
        Ok(())
    }

    /// The thumbnails leave the other `assetInfo` keys alone.
    #[test]
    fn set_keeps_other_asset_info() -> Result<()> {
        let chair = chair()?.set_asset_info_by_key("name", Value::String("Chair".to_string()))?;
        let previews = AssetPreviewsAPI::apply(&chair)?.set_default_thumbnails(&thumbnails("./t.jpg"))?;
        assert_eq!(
            previews.prim().asset_info_by_key("name")?,
            Some(Value::String("Chair".to_string()))
        );
        Ok(())
    }

    #[test]
    fn clear_default_thumbnails() -> Result<()> {
        let chair = chair()?;
        let previews = AssetPreviewsAPI::apply(&chair)?.set_default_thumbnails(&thumbnails("./t.jpg"))?;
        let previews = previews.clear_default_thumbnails()?;
        assert_eq!(previews.default_thumbnails()?, None);
        assert_eq!(
            previews.prim().asset_info_by_key(tokens::PREVIEW_THUMBNAILS_DEFAULT)?,
            None
        );
        Ok(())
    }

    /// An asset holding `/Chair`, with the API and thumbnails applied and a
    /// child prim beneath it, and `/Bare`, without the API, whose default
    /// prim is `default_prim`. It is exported to `asset.usda` in a directory
    /// kept alive beside its path.
    fn asset(default_prim: Option<&str>) -> Result<(tempfile::TempDir, String)> {
        let chair = chair()?;
        let stage = chair.stage().clone();
        stage.define_prim("/Chair/Seat")?;
        stage.define_prim("/Bare")?;
        AssetPreviewsAPI::apply(&chair)?.set_default_thumbnails(&thumbnails("./chair_thumb.jpg"))?;
        if let Some(name) = default_prim {
            stage.set_default_prim(name)?;
        }
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("asset.usda").to_str().expect("utf-8").to_string();
        stage.root_layer().export(&path)?;
        Ok((dir, path))
    }

    #[test]
    fn asset_default_previews() -> Result<()> {
        let (_dir, path) = asset(Some("Chair"))?;
        let previews = AssetPreviewsAPI::asset_default_previews(&path)?.expect("default previews");
        assert_eq!(previews.path().as_str(), "/Chair");
        let thumbnails = previews.default_thumbnails()?.expect("thumbnails");
        assert_eq!(thumbnails.default_image.asset_path(), "./chair_thumb.jpg");
        Ok(())
    }

    #[test]
    fn previews_no_default_prim() -> Result<()> {
        let (_dir, path) = asset(None)?;
        assert!(AssetPreviewsAPI::asset_default_previews(&path)?.is_none());
        Ok(())
    }

    /// A layer already read answers through its unsaved default prim.
    #[test]
    fn layer_default_previews() -> Result<()> {
        let (_dir, path) = asset(None)?;
        let mut layer = sdf::Layer::open(&path)?;
        layer.edit(|e| e.set_default_prim("Chair"))?;
        let previews = AssetPreviewsAPI::layer_default_previews(layer)?.expect("default previews");
        assert_eq!(previews.path().as_str(), "/Chair");
        Ok(())
    }

    /// A default prim without the API has no previews, as C++'s view of it
    /// tests false.
    #[test]
    fn previews_without_api() -> Result<()> {
        let (_dir, path) = asset(Some("Bare"))?;
        assert!(AssetPreviewsAPI::asset_default_previews(&path)?.is_none());
        Ok(())
    }

    /// A default prim the layer does not author has no previews.
    #[test]
    fn previews_missing_default_prim() -> Result<()> {
        let (_dir, path) = asset(Some("Missing"))?;
        assert!(AssetPreviewsAPI::asset_default_previews(&path)?.is_none());
        Ok(())
    }

    /// The view's stage holds the default prim, and not the prims beneath it.
    #[test]
    fn previews_masked_children() -> Result<()> {
        let (_dir, path) = asset(Some("Chair"))?;
        let previews = AssetPreviewsAPI::asset_default_previews(&path)?.expect("default previews");
        assert!(previews.prim().is_valid()?);
        assert!(!previews.stage().prim("/Chair/Seat")?.is_valid()?);
        Ok(())
    }
}
