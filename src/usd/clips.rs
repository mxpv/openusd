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

use std::collections::HashMap;

use crate::gf;
use crate::pcp::clip::keys;
use crate::sdf::{self, Value};

use super::{Prim, StageAuthoringError};

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
        Ok(self
            .field(clip_set, keys::ACTIVE)?
            .as_ref()
            .map(as_pairs)
            .unwrap_or_default())
    }

    /// `(stageTime, clipTime)` timing pairs for `clip_set` (`times`).
    pub fn clip_times(&self, clip_set: &str) -> anyhow::Result<Vec<(f64, f64)>> {
        Ok(self
            .field(clip_set, keys::TIMES)?
            .as_ref()
            .map(as_pairs)
            .unwrap_or_default())
    }

    /// Prim path queried within each clip for `clip_set` (`primPath`), if authored.
    pub fn clip_prim_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        Ok(self.field(clip_set, keys::PRIM_PATH)?.as_ref().and_then(as_string))
    }

    /// Manifest layer asset path for `clip_set` (`manifestAssetPath`), if authored.
    pub fn clip_manifest_asset_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        Ok(self
            .field(clip_set, keys::MANIFEST_ASSET_PATH)?
            .as_ref()
            .and_then(as_asset))
    }

    /// Whether gaps in `clip_set` interpolate across surrounding clips rather
    /// than falling back to the manifest default (`interpolateMissingClipValues`).
    pub fn interpolate_missing_clip_values(&self, clip_set: &str) -> anyhow::Result<Option<bool>> {
        Ok(self
            .field(clip_set, keys::INTERPOLATE_MISSING)?
            .as_ref()
            .and_then(as_bool))
    }

    /// Template asset-path pattern for `clip_set` (`templateAssetPath`), if
    /// authored. Authored as `asset`, so read through the asset extractor.
    pub fn clip_template_asset_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        Ok(self
            .field(clip_set, keys::TEMPLATE_ASSET_PATH)?
            .as_ref()
            .and_then(as_asset))
    }

    /// Template stride for `clip_set` (`templateStride`), if authored.
    pub fn clip_template_stride(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self.field(clip_set, keys::TEMPLATE_STRIDE)?.as_ref().and_then(as_f64))
    }

    /// Template start time for `clip_set` (`templateStartTime`), if authored.
    pub fn clip_template_start_time(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self
            .field(clip_set, keys::TEMPLATE_START_TIME)?
            .as_ref()
            .and_then(as_f64))
    }

    /// Template end time for `clip_set` (`templateEndTime`), if authored.
    pub fn clip_template_end_time(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self.field(clip_set, keys::TEMPLATE_END_TIME)?.as_ref().and_then(as_f64))
    }

    /// Template active offset for `clip_set` (`templateActiveOffset`), if authored.
    pub fn clip_template_active_offset(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        Ok(self
            .field(clip_set, keys::TEMPLATE_ACTIVE_OFFSET)?
            .as_ref()
            .and_then(as_f64))
    }

    /// Author the clip asset paths for `clip_set` (`assetPaths`).
    ///
    /// openusd has no `asset[]` value, so these are stored as a string array
    /// (they read back through [`clip_asset_paths`](Self::clip_asset_paths)
    /// either way); scalar asset fields below author as `asset`.
    pub fn set_clip_asset_paths(&self, clip_set: &str, paths: Vec<String>) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::ASSET_PATHS, Value::StringVec(paths))
    }

    /// Author the `(stageTime, clipIndex)` activation pairs for `clip_set` (`active`).
    pub fn set_clip_active(&self, clip_set: &str, active: Vec<(f64, f64)>) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::ACTIVE, pairs_value(active))
    }

    /// Author the `(stageTime, clipTime)` timing pairs for `clip_set` (`times`).
    pub fn set_clip_times(&self, clip_set: &str, times: Vec<(f64, f64)>) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::TIMES, pairs_value(times))
    }

    /// Author the per-clip prim path for `clip_set` (`primPath`).
    pub fn set_clip_prim_path(&self, clip_set: &str, prim_path: impl Into<String>) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::PRIM_PATH, Value::String(prim_path.into()))
    }

    /// Author the manifest asset path for `clip_set` (`manifestAssetPath`).
    pub fn set_clip_manifest_asset_path(
        &self,
        clip_set: &str,
        asset_path: impl Into<String>,
    ) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::MANIFEST_ASSET_PATH, Value::AssetPath(asset_path.into()))
    }

    /// Author the interpolate-missing flag for `clip_set` (`interpolateMissingClipValues`).
    pub fn set_interpolate_missing_clip_values(
        &self,
        clip_set: &str,
        interpolate: bool,
    ) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::INTERPOLATE_MISSING, Value::Bool(interpolate))
    }

    /// Author the template asset-path pattern for `clip_set` (`templateAssetPath`).
    pub fn set_clip_template_asset_path(
        &self,
        clip_set: &str,
        asset_path: impl Into<String>,
    ) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::TEMPLATE_ASSET_PATH, Value::AssetPath(asset_path.into()))
    }

    /// Author the template stride for `clip_set` (`templateStride`).
    pub fn set_clip_template_stride(&self, clip_set: &str, stride: f64) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::TEMPLATE_STRIDE, Value::Double(stride))
    }

    /// Author the template start time for `clip_set` (`templateStartTime`).
    pub fn set_clip_template_start_time(&self, clip_set: &str, start: f64) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::TEMPLATE_START_TIME, Value::Double(start))
    }

    /// Author the template end time for `clip_set` (`templateEndTime`).
    pub fn set_clip_template_end_time(&self, clip_set: &str, end: f64) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::TEMPLATE_END_TIME, Value::Double(end))
    }

    /// Author the template active offset for `clip_set` (`templateActiveOffset`).
    pub fn set_clip_template_active_offset(&self, clip_set: &str, offset: f64) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::TEMPLATE_ACTIVE_OFFSET, Value::Double(offset))
    }

    /// Read a single field from `clip_set`'s entry in the composed `clips`
    /// dictionary, or `None` when the set (or field) is not authored.
    fn field(&self, clip_set: &str, key: &str) -> anyhow::Result<Option<Value>> {
        let Some(Value::Dictionary(sets)) = self
            .prim
            .stage()
            .field::<Value>(self.prim.path(), sdf::FieldKey::Clips)?
        else {
            return Ok(None);
        };
        Ok(match sets.get(clip_set) {
            Some(Value::Dictionary(set)) => set.get(key).cloned(),
            _ => None,
        })
    }

    /// Read-modify-write a single field into `clip_set`'s entry of the `clips`
    /// dictionary on the edit-target layer, preserving the other sets and
    /// fields already authored there.
    fn set_field(&self, clip_set: &str, key: &str, value: Value) -> Result<(), StageAuthoringError> {
        let clip_set = clip_set.to_string();
        let key = key.to_string();
        self.prim
            .clone()
            .update_metadata(sdf::FieldKey::Clips.as_str(), move |current| {
                let mut sets = match current {
                    Some(Value::Dictionary(d)) => d,
                    _ => HashMap::new(),
                };
                match sets
                    .entry(clip_set)
                    .or_insert_with(|| Value::Dictionary(HashMap::new()))
                {
                    Value::Dictionary(set) => {
                        set.insert(key, value);
                    }
                    other => *other = Value::Dictionary(HashMap::from([(key, value)])),
                }
                Value::Dictionary(sets)
            })?;
        Ok(())
    }
}

fn pairs_value(pairs: Vec<(f64, f64)>) -> Value {
    Value::Vec2dVec(pairs.into_iter().map(|(x, y)| gf::vec2d(x, y)).collect())
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf;
    use crate::usd::Stage;
    use std::collections::HashMap;

    fn fixture(name: &str) -> String {
        format!(
            "{}/fixtures/{name}/root.usda",
            std::env::var("CARGO_MANIFEST_DIR").unwrap()
        )
    }

    /// `clip_asset_anchor` authors the explicit form on `/Model`:
    /// `asset[] assetPaths`, `double2[] active`, `string primPath`.
    #[test]
    fn reads_explicit_clip_set_from_fixture() -> anyhow::Result<()> {
        let stage = Stage::open(&fixture("clip_asset_anchor"))?;
        let clips = ClipsAPI::new(&stage.prim_at(sdf::path("/Model")?));

        assert_eq!(clips.clip_sets()?, vec!["default".to_string()]);
        assert_eq!(clips.clip_asset_paths("default")?, vec!["./clip.usda".to_string()]);
        assert_eq!(clips.clip_active("default")?, vec![(0.0, 0.0)]);
        assert_eq!(clips.clip_prim_path("default")?.as_deref(), Some("/Model"));
        Ok(())
    }

    /// `clip_template` authors the template form on `/Model`:
    /// `asset templateAssetPath`, `double templateStart/End/Stride`. The
    /// `asset`-typed template path is the case a `String`-only extractor
    /// would silently miss.
    #[test]
    fn reads_template_clip_set_from_fixture() -> anyhow::Result<()> {
        let stage = Stage::open(&fixture("clip_template"))?;
        let clips = ClipsAPI::new(&stage.prim_at(sdf::path("/Model")?));

        assert_eq!(
            clips.clip_template_asset_path("default")?.as_deref(),
            Some("./clip.#.usda")
        );
        assert_eq!(clips.clip_template_start_time("default")?, Some(1.0));
        assert_eq!(clips.clip_template_end_time("default")?, Some(2.0));
        assert_eq!(clips.clip_template_stride("default")?, Some(1.0));
        // No explicit asset paths authored in the template form.
        assert!(clips.clip_asset_paths("default")?.is_empty());
        Ok(())
    }

    /// Fields the bundled fixtures don't exercise (`times`,
    /// `manifestAssetPath`, `interpolateMissingClipValues`,
    /// `templateActiveOffset`) plus the missing-set / missing-field edges,
    /// authored in-memory with the value types the parser produces.
    #[test]
    fn reads_remaining_fields_and_missing_edges() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let set = Value::Dictionary(
            [
                (
                    keys::TIMES.to_string(),
                    Value::Vec2dVec(vec![gf::vec2d(0.0, 0.0), gf::vec2d(10.0, 5.0)]),
                ),
                (
                    keys::MANIFEST_ASSET_PATH.to_string(),
                    Value::AssetPath("manifest.usda".into()),
                ),
                (keys::INTERPOLATE_MISSING.to_string(), Value::Bool(true)),
                (keys::TEMPLATE_ACTIVE_OFFSET.to_string(), Value::Double(0.5)),
            ]
            .into_iter()
            .collect::<HashMap<_, _>>(),
        );
        stage.define_prim(sdf::path("/Anim")?)?.set_metadata(
            "clips",
            Value::Dictionary([("default".to_string(), set)].into_iter().collect()),
        )?;
        let clips = ClipsAPI::new(&stage.prim_at(sdf::path("/Anim")?));

        assert_eq!(clips.clip_times("default")?, vec![(0.0, 0.0), (10.0, 5.0)]);
        assert_eq!(
            clips.clip_manifest_asset_path("default")?.as_deref(),
            Some("manifest.usda")
        );
        assert_eq!(clips.interpolate_missing_clip_values("default")?, Some(true));
        assert_eq!(clips.clip_template_active_offset("default")?, Some(0.5));

        // Missing set, missing field, and a prim with no clips at all.
        assert!(clips.clip_asset_paths("nope")?.is_empty());
        assert!(clips.clip_prim_path("default")?.is_none());
        assert!(ClipsAPI::new(&stage.prim_at(sdf::path("/Absent")?))
            .clip_sets()?
            .is_empty());
        Ok(())
    }

    /// Author every field across two sets via the setters and read it all
    /// back — also covers that the per-field read-modify-write preserves the
    /// other sets and fields already authored.
    #[test]
    fn set_get_round_trip() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/Anim")?)?;
        let clips = ClipsAPI::new(&stage.prim_at(sdf::path("/Anim")?));

        clips.set_clip_asset_paths("default", vec!["a.usda".into(), "b.usda".into()])?;
        clips.set_clip_active("default", vec![(0.0, 0.0), (10.0, 1.0)])?;
        clips.set_clip_times("default", vec![(0.0, 0.0), (10.0, 5.0)])?;
        clips.set_clip_prim_path("default", "/Anim")?;
        clips.set_clip_manifest_asset_path("default", "manifest.usda")?;
        clips.set_interpolate_missing_clip_values("default", true)?;
        clips.set_clip_template_asset_path("tmpl", "clip.#.usda")?;
        clips.set_clip_template_stride("tmpl", 1.0)?;
        clips.set_clip_template_start_time("tmpl", 0.0)?;
        clips.set_clip_template_end_time("tmpl", 10.0)?;
        clips.set_clip_template_active_offset("tmpl", 0.5)?;

        assert_eq!(clips.clip_sets()?, vec!["default".to_string(), "tmpl".to_string()]);
        assert_eq!(
            clips.clip_asset_paths("default")?,
            vec!["a.usda".to_string(), "b.usda".to_string()]
        );
        assert_eq!(clips.clip_active("default")?, vec![(0.0, 0.0), (10.0, 1.0)]);
        assert_eq!(clips.clip_times("default")?, vec![(0.0, 0.0), (10.0, 5.0)]);
        assert_eq!(clips.clip_prim_path("default")?.as_deref(), Some("/Anim"));
        assert_eq!(
            clips.clip_manifest_asset_path("default")?.as_deref(),
            Some("manifest.usda")
        );
        assert_eq!(clips.interpolate_missing_clip_values("default")?, Some(true));
        assert_eq!(clips.clip_template_asset_path("tmpl")?.as_deref(), Some("clip.#.usda"));
        assert_eq!(clips.clip_template_stride("tmpl")?, Some(1.0));
        assert_eq!(clips.clip_template_start_time("tmpl")?, Some(0.0));
        assert_eq!(clips.clip_template_end_time("tmpl")?, Some(10.0));
        assert_eq!(clips.clip_template_active_offset("tmpl")?, Some(0.5));
        Ok(())
    }
}
