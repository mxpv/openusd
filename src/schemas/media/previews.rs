//! `AssetPreviewsAPI` - precomputed lightweight asset previews.
//!
//! An applied API (no direct properties) that reads/writes a thumbnail
//! under the prim's `assetInfo` metadata dictionary (spec
//! `UsdMediaAssetPreviewsAPI`):
//!
//! ```text
//! assetInfo = {
//!     dictionary previews = {
//!         dictionary thumbnails = {
//!             dictionary default = { asset defaultImage = @chair_thumb.jpg@ }
//!         }
//!     }
//! }
//! ```

use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use crate::schemas::common::value_as_asset_str;

use super::tokens::*;

/// Apply `AssetPreviewsAPI` to `prim` (adds it to `apiSchemas`). The
/// thumbnail data itself is authored with [`set_default_thumbnail`].
pub fn apply_asset_previews(stage: &Stage, prim: impl Into<Path>) -> Result<()> {
    stage.override_prim(prim)?.add_applied_schema(API_ASSET_PREVIEWS)?;
    Ok(())
}

/// Author the default thumbnail image path under the prim's `assetInfo`
/// (`previews.thumbnails.default.defaultImage`), creating an `over` if the
/// prim has no spec on the edit-target layer.
///
/// Only the `previews` sub-tree is merged into the edit target's own
/// `assetInfo` opinion; other `assetInfo` keys (whether authored locally or
/// on weaker layers) are left to compose, so the thumbnail does not flatten
/// them into the edit target.
pub fn set_default_thumbnail(stage: &Stage, prim: &Path, image: impl Into<String>) -> Result<()> {
    let image = image.into();
    stage
        .override_prim(prim.clone())?
        .update_metadata(FieldKey::AssetInfo.as_str(), |local| {
            let mut asset_info = match local {
                Some(Value::Dictionary(d)) => d,
                _ => HashMap::new(),
            };
            let previews = nested_dict_mut(&mut asset_info, PREVIEWS);
            let thumbnails = nested_dict_mut(previews, THUMBNAILS);
            let default = nested_dict_mut(thumbnails, PREVIEW_DEFAULT);
            default.insert(DEFAULT_IMAGE.to_string(), Value::AssetPath(image));
            Value::Dictionary(asset_info)
        })?;
    Ok(())
}

/// Read the default thumbnail image path
/// (`assetInfo.previews.thumbnails.default.defaultImage`), or `None` when
/// no preview is authored.
pub fn read_default_thumbnail(stage: &Stage, prim: &Path) -> Result<Option<String>> {
    let Some(Value::Dictionary(asset_info)) = stage.field::<Value>(prim.clone(), FieldKey::AssetInfo)? else {
        return Ok(None);
    };
    let leaf = nested_dict(&asset_info, PREVIEWS)
        .and_then(|d| nested_dict(d, THUMBNAILS))
        .and_then(|d| nested_dict(d, PREVIEW_DEFAULT))
        .and_then(|d| d.get(DEFAULT_IMAGE));
    Ok(leaf.and_then(value_as_asset_str).map(str::to_owned))
}

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
    use crate::sdf;

    #[test]
    fn asset_previews_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/Chair")?)?.set_type_name("Xform")?;
        apply_asset_previews(&stage, sdf::path("/Chair")?)?;
        set_default_thumbnail(&stage, &sdf::path("/Chair")?, "./chair_thumb.jpg")?;

        assert!(stage.has_api_schema(&sdf::path("/Chair")?, API_ASSET_PREVIEWS)?);
        assert_eq!(
            read_default_thumbnail(&stage, &sdf::path("/Chair")?)?.as_deref(),
            Some("./chair_thumb.jpg"),
        );
        Ok(())
    }

    #[test]
    fn no_thumbnail_reads_none() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/Bare")?)?.set_type_name("Xform")?;
        assert!(read_default_thumbnail(&stage, &sdf::path("/Bare")?)?.is_none());
        Ok(())
    }

    #[test]
    fn set_thumbnail_preserves_other_asset_info() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let mut info = HashMap::new();
        info.insert("name".to_string(), Value::String("Chair".to_string()));
        stage
            .define_prim(sdf::path("/Chair")?)?
            .set_type_name("Xform")?
            .set_metadata("assetInfo", Value::Dictionary(info))?;
        set_default_thumbnail(&stage, &sdf::path("/Chair")?, "./t.jpg")?;

        // The pre-existing `name` entry survives alongside the new previews.
        let Some(Value::Dictionary(info)) = stage.field::<Value>(sdf::path("/Chair")?, FieldKey::AssetInfo)? else {
            panic!("assetInfo");
        };
        assert_eq!(info.get("name"), Some(&Value::String("Chair".to_string())));
        assert!(info.contains_key(PREVIEWS));
        Ok(())
    }
}
