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
use crate::usd::{Prim, Stage};

use super::tokens::*;

/// Apply `AssetPreviewsAPI` to `prim` (adds it to `apiSchemas`). The
/// thumbnail data itself is authored with [`set_default_thumbnail`].
pub fn apply_asset_previews(stage: &Stage, prim: impl Into<Path>) -> Result<()> {
    let prim = prim.into();
    stage.override_prim(prim.clone())?;
    Prim::new(stage, prim).add_applied_schema(API_ASSET_PREVIEWS)?;
    Ok(())
}

/// Author the default thumbnail image path under the prim's `assetInfo`
/// (`previews.thumbnails.default.defaultImage`). Preserves any other
/// `assetInfo` entries.
pub fn set_default_thumbnail(stage: &Stage, prim: &Path, image: impl Into<String>) -> Result<()> {
    let mut asset_info = match stage.field::<Value>(prim.clone(), FieldKey::AssetInfo)? {
        Some(Value::Dictionary(d)) => d,
        _ => HashMap::new(),
    };
    let previews = nested_dict_mut(&mut asset_info, PREVIEWS);
    let thumbnails = nested_dict_mut(previews, THUMBNAILS);
    let default = nested_dict_mut(thumbnails, PREVIEW_DEFAULT);
    default.insert(DEFAULT_IMAGE.to_string(), Value::AssetPath(image.into()));

    Prim::new(stage, prim.clone()).set_metadata("assetInfo", Value::Dictionary(asset_info))?;
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
    Ok(match leaf {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s.clone()),
        _ => None,
    })
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
    match entry {
        Value::Dictionary(inner) => inner,
        _ => unreachable!("just ensured a dictionary"),
    }
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
