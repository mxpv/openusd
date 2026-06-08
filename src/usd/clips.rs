//! Value-clip introspection — a read-only view mirroring C++ `UsdClipsAPI`.
//!
//! Reads the authored `clips` dictionary metadata (spec 12.3.4) on a prim:
//! per-clip-set asset paths, the `active` / `times` curves, the manifest, the
//! per-set prim path, the interpolate-missing flag, and the template-clip
//! fields. This is raw *authored* introspection — resolved clip values come
//! through [`Attribute::get_at`](crate::usd::Attribute::get_at), which is where
//! the clip schedule is actually applied.
//!
//! Getters take a clip-set name (the key in the `clips` dictionary); the
//! conventional default set is named `"default"`. Names are discovered via
//! [`ClipsAPI::clip_sets`].

use crate::pcp::clip::keys;
use crate::sdf::{self, Value};

use super::Prim;

/// Read-only view of the value-clip metadata on a prim (C++ `UsdClipsAPI`).
///
/// ```no_run
/// # use openusd::usd::{Stage, ClipsAPI};
/// # fn demo(stage: &Stage) -> anyhow::Result<()> {
/// let prim = stage.prim_at(openusd::sdf::path("/World/Anim")?);
/// let clips = ClipsAPI::new(&prim);
/// for set in clips.clip_sets()? {
///     let assets = clips.clip_asset_paths(&set)?;
///     let active = clips.clip_active(&set)?;
///     // ...
/// }
/// # Ok(())
/// # }
/// ```
pub struct ClipsAPI {
    prim: Prim,
}

impl ClipsAPI {
    /// Wrap `prim` for clip-metadata introspection.
    pub fn new(prim: &Prim) -> Self {
        Self { prim: prim.clone() }
    }

    /// Names of the authored clip sets (the keys of the `clips` dictionary),
    /// sorted. Empty when none are authored.
    pub fn clip_sets(&self) -> anyhow::Result<Vec<String>> {
        self.prim.clip_sets()
    }

    /// Ordered clip asset paths for `clip_set` (`assetPaths`).
    pub fn clip_asset_paths(&self, clip_set: &str) -> anyhow::Result<Vec<String>> {
        Ok(self
            .field(clip_set, keys::ASSET_PATHS)?
            .as_ref()
            .and_then(as_string_vec)
            .unwrap_or_default())
    }

    /// `(stageTime, clipIndex)` activation pairs for `clip_set` (`active`).
    pub fn clip_active(&self, clip_set: &str) -> anyhow::Result<Vec<(f64, f64)>> {
        Ok(self.field(clip_set, keys::ACTIVE)?.as_ref().map(as_pairs).unwrap_or_default())
    }

    /// `(stageTime, clipTime)` timing pairs for `clip_set` (`times`).
    pub fn clip_times(&self, clip_set: &str) -> anyhow::Result<Vec<(f64, f64)>> {
        Ok(self.field(clip_set, keys::TIMES)?.as_ref().map(as_pairs).unwrap_or_default())
    }

    /// Prim path queried within each clip for `clip_set` (`primPath`), if authored.
    pub fn clip_prim_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        Ok(self.field(clip_set, keys::PRIM_PATH)?.as_ref().and_then(as_string))
    }

    /// Manifest layer asset path for `clip_set` (`manifestAssetPath`), if authored.
    pub fn clip_manifest_asset_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        Ok(self.field(clip_set, keys::MANIFEST_ASSET_PATH)?.as_ref().and_then(as_asset))
    }

    /// Whether gaps in `clip_set` interpolate across surrounding clips rather
    /// than falling back to the manifest default (`interpolateMissingClipValues`).
    pub fn interpolate_missing_clip_values(&self, clip_set: &str) -> anyhow::Result<Option<bool>> {
        Ok(self.field(clip_set, keys::INTERPOLATE_MISSING)?.as_ref().and_then(as_bool))
    }

    /// Template asset-path pattern for `clip_set` (`templateAssetPath`), if
    /// authored. Authored as `asset`, so read through the asset extractor.
    pub fn clip_template_asset_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        Ok(self.field(clip_set, keys::TEMPLATE_ASSET_PATH)?.as_ref().and_then(as_asset))
    }

    /// Template stride for `clip_set` (`templateStride`), if authored.
    pub fn clip_template_stride(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self.field(clip_set, keys::TEMPLATE_STRIDE)?.as_ref().and_then(as_f64))
    }

    /// Template start time for `clip_set` (`templateStartTime`), if authored.
    pub fn clip_template_start_time(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self.field(clip_set, keys::TEMPLATE_START_TIME)?.as_ref().and_then(as_f64))
    }

    /// Template end time for `clip_set` (`templateEndTime`), if authored.
    pub fn clip_template_end_time(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self.field(clip_set, keys::TEMPLATE_END_TIME)?.as_ref().and_then(as_f64))
    }

    /// Template active offset for `clip_set` (`templateActiveOffset`), if authored.
    pub fn clip_template_active_offset(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self.field(clip_set, keys::TEMPLATE_ACTIVE_OFFSET)?.as_ref().and_then(as_f64))
    }

    /// Read a single field from `clip_set`'s entry in the composed `clips`
    /// dictionary, or `None` when the set (or field) is not authored.
    fn field(&self, clip_set: &str, key: &str) -> anyhow::Result<Option<Value>> {
        let Some(Value::Dictionary(sets)) = self.prim.stage().field::<Value>(self.prim.path(), sdf::FieldKey::Clips)?
        else {
            return Ok(None);
        };
        Ok(match sets.get(clip_set) {
            Some(Value::Dictionary(set)) => set.get(key).cloned(),
            _ => None,
        })
    }
}

fn as_string(value: &Value) -> Option<String> {
    match value {
        Value::String(s) | Value::Token(s) => Some(s.clone()),
        _ => None,
    }
}

fn as_asset(value: &Value) -> Option<String> {
    match value {
        Value::AssetPath(s) | Value::String(s) | Value::Token(s) => Some(s.clone()),
        _ => None,
    }
}

fn as_string_vec(value: &Value) -> Option<Vec<String>> {
    match value {
        Value::StringVec(v) | Value::TokenVec(v) => Some(v.clone()),
        _ => None,
    }
}

fn as_pairs(value: &Value) -> Vec<(f64, f64)> {
    match value {
        Value::Vec2dVec(pairs) => pairs.iter().map(|p| (p.x, p.y)).collect(),
        _ => Vec::new(),
    }
}

fn as_bool(value: &Value) -> Option<bool> {
    match value {
        Value::Bool(b) => Some(*b),
        _ => None,
    }
}

fn as_f64(value: &Value) -> Option<f64> {
    match value {
        Value::Double(d) => Some(*d),
        Value::Float(f) => Some(*f as f64),
        Value::Int(i) => Some(*i as f64),
        Value::Int64(i) => Some(*i as f64),
        Value::Half(h) => Some(h.to_f32() as f64),
        _ => None,
    }
}
