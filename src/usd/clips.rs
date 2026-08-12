//! Value-clip authoring and introspection — a view mirroring C++ `UsdClipsAPI`.
//!
//! Reads and writes the `clips` dictionary metadata (spec 12.3.4) on a prim:
//! per-clip-set asset paths, the `active` / `times` curves, the manifest, the
//! per-set prim path, the interpolate-missing flag, and the template-clip
//! fields, plus the `clipSets` strength-ordering list-op. This is raw
//! *authored* metadata — resolved clip values come through
//! [`Attribute::get_at`](crate::usd::Attribute::get_at), which is where the
//! clip schedule is actually applied.
//!
//! Per-set getters/setters take a clip-set name (the key in the `clips`
//! dictionary); the conventional default set is named `"default"`. Authored
//! names are discovered via [`ClipsAPI::clip_set_names`].

use std::collections::HashMap;

use crate::gf;
use crate::pcp::clip::keys;
use crate::pcp::clip_manifest;
use crate::sdf::{self, AssetPath, Value};

use super::{Prim, StageAuthoringError};

/// Read/write view of the value-clip metadata on a prim (C++ `UsdClipsAPI`).
///
/// ```no_run
/// # use openusd::usd::{Stage, ClipsAPI};
/// # fn demo(stage: &Stage) -> anyhow::Result<()> {
/// let prim = stage.prim("/World/Anim")?;
/// let clips = ClipsAPI::new(&prim);
/// for set in clips.clip_set_names()? {
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
    /// Wrap `prim` for clip-metadata introspection and authoring.
    pub fn new(prim: &Prim) -> Self {
        Self { prim: prim.clone() }
    }

    /// Names of the authored clip sets (the keys of the `clips` dictionary),
    /// sorted, empty when none are authored. This enumerates every authored set
    /// regardless of `clipSets`; a set listed here may still resolve no clip
    /// values (e.g. a template set with invalid metadata, or a name excluded by
    /// `clipSets`). Use [`clip_sets`](Self::clip_sets) for the strength order.
    pub fn clip_set_names(&self) -> anyhow::Result<Vec<String>> {
        self.prim.clip_sets()
    }

    /// The composed `clipSets` strength-ordering list-op (C++
    /// `UsdClipsAPI::GetClipSets`), folding the list-op edits across layers and
    /// preserving the prepend/append/delete structure. `None` when `clipSets`
    /// is unauthored — clip sets then fall back to name order (spec 12.3.4.1).
    pub fn clip_sets(&self) -> anyhow::Result<Option<sdf::StringListOp>> {
        let path = self.prim.path().clone();
        self.prim
            .stage()
            .masked(&path, |g, cache| cache.clip_sets_list_op(g, &path))
    }

    /// Author the `clipSets` strength-ordering list-op (C++
    /// `UsdClipsAPI::SetClipSets`). Build the op with
    /// [`sdf::StringListOp::explicit`] for a plain ordered list, or with the
    /// prepend/append/delete operators to edit a composed order.
    pub fn set_clip_sets(&self, clip_sets: sdf::StringListOp) -> Result<(), StageAuthoringError> {
        self.prim
            .clone()
            .set_metadata(sdf::FieldKey::ClipSets.as_str(), Value::StringListOp(clip_sets))?;
        Ok(())
    }

    /// The whole composed `clips` dictionary (C++ `UsdClipsAPI::GetClips`),
    /// resolved once. Prefer this over the per-field getters when reading many
    /// fields, since each per-field getter re-resolves the entire dictionary.
    pub fn clips(&self) -> anyhow::Result<Option<sdf::Dictionary>> {
        Ok(self
            .prim
            .stage()
            .field::<Value>(self.prim.path(), sdf::FieldKey::Clips)?
            .and_then(Value::try_as_dictionary))
    }

    /// Replace the entire `clips` dictionary (C++ `UsdClipsAPI::SetClips`).
    /// Authors all sets in one write, unlike the per-field setters which each
    /// read-modify-write the dictionary.
    pub fn set_clips(&self, clips: sdf::Dictionary) -> Result<(), StageAuthoringError> {
        self.prim
            .clone()
            .set_metadata(sdf::FieldKey::Clips.as_str(), Value::Dictionary(clips))?;
        Ok(())
    }

    /// Ordered clip asset paths for `clip_set` (`assetPaths`), an `asset[]` (C++
    /// `VtArray<SdfAssetPath>`). Empty when unauthored.
    pub fn clip_asset_paths(&self, clip_set: &str) -> anyhow::Result<Vec<AssetPath>> {
        Ok(self
            .field(clip_set, keys::ASSET_PATHS)?
            .and_then(Value::try_as_asset_path_vec)
            .unwrap_or_default())
    }

    /// `(stageTime, clipIndex)` activation pairs for `clip_set` (`active`),
    /// each a `gf::Vec2d`. Empty when unauthored.
    pub fn clip_active(&self, clip_set: &str) -> anyhow::Result<Vec<gf::Vec2d>> {
        Ok(self
            .field(clip_set, keys::ACTIVE)?
            .and_then(Value::try_as_vec_2d_vec)
            .unwrap_or_default())
    }

    /// `(stageTime, clipTime)` timing pairs for `clip_set` (`times`), each a
    /// `gf::Vec2d`. Empty when unauthored.
    pub fn clip_times(&self, clip_set: &str) -> anyhow::Result<Vec<gf::Vec2d>> {
        Ok(self
            .field(clip_set, keys::TIMES)?
            .and_then(Value::try_as_vec_2d_vec)
            .unwrap_or_default())
    }

    /// Prim path queried within each clip for `clip_set` (`primPath`), if authored.
    pub fn clip_prim_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        self.cast_field(clip_set, keys::PRIM_PATH)
    }

    /// Manifest layer asset path for `clip_set` (`manifestAssetPath`), an
    /// `asset` (C++ `SdfAssetPath`), if authored.
    pub fn clip_manifest_asset_path(&self, clip_set: &str) -> anyhow::Result<Option<AssetPath>> {
        Ok(self
            .field(clip_set, keys::MANIFEST_ASSET_PATH)?
            .and_then(Value::try_as_asset_path))
    }

    /// Whether gaps in `clip_set` interpolate across surrounding clips rather
    /// than falling back to the manifest default (`interpolateMissingClipValues`).
    pub fn interpolate_missing_clip_values(&self, clip_set: &str) -> anyhow::Result<Option<bool>> {
        self.cast_field(clip_set, keys::INTERPOLATE_MISSING)
    }

    /// Template asset-path pattern for `clip_set` (`templateAssetPath`), if authored.
    pub fn clip_template_asset_path(&self, clip_set: &str) -> anyhow::Result<Option<String>> {
        self.cast_field(clip_set, keys::TEMPLATE_ASSET_PATH)
    }

    /// Template stride for `clip_set` (`templateStride`), if authored.
    pub fn clip_template_stride(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        self.cast_field(clip_set, keys::TEMPLATE_STRIDE)
    }

    /// Template start time for `clip_set` (`templateStartTime`), if authored.
    pub fn clip_template_start_time(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        self.cast_field(clip_set, keys::TEMPLATE_START_TIME)
    }

    /// Template end time for `clip_set` (`templateEndTime`), if authored.
    pub fn clip_template_end_time(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        self.cast_field(clip_set, keys::TEMPLATE_END_TIME)
    }

    /// Template active offset for `clip_set` (`templateActiveOffset`), if authored.
    pub fn clip_template_active_offset(&self, clip_set: &str) -> anyhow::Result<Option<f64>> {
        self.cast_field(clip_set, keys::TEMPLATE_ACTIVE_OFFSET)
    }

    /// Author the clip asset paths for `clip_set` (`assetPaths`), as an `asset[]`.
    ///
    /// Explicit `assetPaths` take precedence over the template-clip fields: a
    /// set that authors both resolves through the explicit form, leaving the
    /// `templateAssetPath` / `templateStartTime` / … opinions inert.
    pub fn set_clip_asset_paths(
        &self,
        clip_set: &str,
        paths: impl IntoIterator<Item = impl Into<AssetPath>>,
    ) -> Result<(), StageAuthoringError> {
        let paths = paths.into_iter().map(Into::into).collect();
        self.set_field(clip_set, keys::ASSET_PATHS, Value::AssetPathVec(paths))
    }

    /// Author the `(stageTime, clipIndex)` activation pairs for `clip_set` (`active`).
    pub fn set_clip_active(&self, clip_set: &str, active: Vec<gf::Vec2d>) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::ACTIVE, Value::Vec2dVec(active))
    }

    /// Author the `(stageTime, clipTime)` timing pairs for `clip_set` (`times`).
    pub fn set_clip_times(&self, clip_set: &str, times: Vec<gf::Vec2d>) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::TIMES, Value::Vec2dVec(times))
    }

    /// Author the per-clip prim path for `clip_set` (`primPath`).
    pub fn set_clip_prim_path(&self, clip_set: &str, prim_path: impl Into<String>) -> Result<(), StageAuthoringError> {
        self.set_field(clip_set, keys::PRIM_PATH, Value::String(prim_path.into()))
    }

    /// Author the manifest asset path for `clip_set` (`manifestAssetPath`).
    pub fn set_clip_manifest_asset_path(
        &self,
        clip_set: &str,
        asset_path: impl Into<AssetPath>,
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
        self.set_field(
            clip_set,
            keys::TEMPLATE_ASSET_PATH,
            Value::AssetPath(AssetPath::new(asset_path)),
        )
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

    /// Generate a manifest layer for `clip_set` (C++
    /// `UsdClipsAPI::GenerateClipManifest`), declaring every attribute the set's
    /// clips carry time samples for. Opens each clip the set's `active` schedule
    /// names.
    ///
    /// Errors when a clip cannot be read, rather than returning a manifest that
    /// omits what it carried: naming such a manifest from `manifestAssetPath`
    /// would stop value resolution sourcing those attributes from the clips at
    /// all. Synthesis during value resolution makes the opposite trade and
    /// degrades to the clips it can read.
    ///
    /// `None` when the prim is the pseudo-root, when no set of that name
    /// resolves here, or when the prim lies outside the stage's population mask
    /// — a masked-out prim is not composed, so no manifest can be derived for
    /// it.
    ///
    /// With `write_blocks_for_missing`, the manifest also carries a value block
    /// at each clip's activation time for the attributes that clip has no
    /// samples for. Value resolution reads those blocks when filling a gap under
    /// `interpolateMissingClipValues`, skipping a clip it can tell is empty
    /// without opening it.
    ///
    /// The manifest is returned, not installed: export it and name it from
    /// `manifestAssetPath` to put it to use.
    ///
    /// ```no_run
    /// # use openusd::{sdf, usd::{Stage, ClipsAPI}};
    /// # fn demo(stage: &Stage) -> anyhow::Result<()> {
    /// let clips = ClipsAPI::new(&stage.prim("/World/Anim")?);
    /// if let Some(manifest) = clips.generate_clip_manifest("default", false)? {
    ///     manifest.export("manifest.usda")?;
    ///     clips.set_clip_manifest_asset_path("default", "./manifest.usda")?;
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn generate_clip_manifest(
        &self,
        clip_set: &str,
        write_blocks_for_missing: bool,
    ) -> anyhow::Result<Option<sdf::Layer>> {
        let path = self.prim.path().clone();
        self.prim.stage().masked(&path, |g, cache| {
            cache.generate_clip_manifest(g, &path, clip_set, write_blocks_for_missing)
        })
    }

    /// Generate a manifest layer for `clip_layers`, queried under
    /// `clip_prim_path` (C++ `UsdClipsAPI::GenerateClipManifestFromLayers`).
    ///
    /// The clip-set form, [`generate_clip_manifest`](Self::generate_clip_manifest),
    /// resolves and opens the clips itself and can write value blocks; this one
    /// takes layers the caller already holds and only declares.
    pub fn generate_clip_manifest_from_layers(
        clip_layers: &[&sdf::Layer],
        clip_prim_path: &sdf::Path,
    ) -> anyhow::Result<sdf::Layer> {
        // Without an activation schedule there are no times to block at, so
        // every clip is passed for declaration only.
        let clips: Vec<(&sdf::Layer, Option<f64>)> = clip_layers.iter().map(|layer| (*layer, None)).collect();
        clip_manifest::generate_manifest(&clips, clip_prim_path, clip_manifest::CLIP_MANIFEST_TAG)
    }

    /// Read a single field from `clip_set`'s entry in the composed `clips`
    /// dictionary and coerce it to `T` via [`Value::cast`]. Returns `None` when
    /// the set (or field) is unauthored, or its value can't cast to `T`.
    fn cast_field<T: sdf::FromValueCast>(&self, clip_set: &str, key: &str) -> anyhow::Result<Option<T>> {
        Ok(self.field(clip_set, key)?.and_then(|v| v.cast().ok()))
    }

    /// Read the raw `Value` of a single field in `clip_set`'s entry of the
    /// composed `clips` dictionary, or `None` when the set or field is unauthored.
    fn field(&self, clip_set: &str, key: &str) -> anyhow::Result<Option<Value>> {
        let Some(mut sets) = self.clips()? else {
            return Ok(None);
        };
        Ok(match sets.get_mut(clip_set) {
            Some(Value::Dictionary(set)) => set.remove(key),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf;
    use crate::usd::{Stage, TimeCode};
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
        let clips = ClipsAPI::new(&stage.prim("/Model")?);

        assert_eq!(clips.clip_set_names()?, vec!["default".to_string()]);
        assert_eq!(clips.clip_asset_paths("default")?, vec![AssetPath::new("./clip.usda")]);
        assert_eq!(clips.clip_active("default")?, vec![gf::vec2d(0.0, 0.0)]);
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
        let clips = ClipsAPI::new(&stage.prim("/Model")?);

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
        stage.define_prim("/Anim")?.set_metadata(
            "clips",
            Value::Dictionary([("default".to_string(), set)].into_iter().collect()),
        )?;
        let clips = ClipsAPI::new(&stage.prim("/Anim")?);

        assert_eq!(
            clips.clip_times("default")?,
            vec![gf::vec2d(0.0, 0.0), gf::vec2d(10.0, 5.0)]
        );
        assert_eq!(
            clips.clip_manifest_asset_path("default")?,
            Some(AssetPath::new("manifest.usda"))
        );
        assert_eq!(clips.interpolate_missing_clip_values("default")?, Some(true));
        assert_eq!(clips.clip_template_active_offset("default")?, Some(0.5));

        // Missing set, missing field, and a prim with no clips at all.
        assert!(clips.clip_asset_paths("nope")?.is_empty());
        assert!(clips.clip_prim_path("default")?.is_none());
        assert!(ClipsAPI::new(&stage.prim("/Absent")?).clip_set_names()?.is_empty());
        Ok(())
    }

    /// Author every field across two sets via the setters and read it all
    /// back — also covers that the per-field read-modify-write preserves the
    /// other sets and fields already authored.
    #[test]
    fn set_get_round_trip() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Anim")?;
        let clips = ClipsAPI::new(&stage.prim("/Anim")?);

        clips.set_clip_asset_paths("default", ["a.usda", "b.usda"])?;
        clips.set_clip_active("default", vec![gf::vec2d(0.0, 0.0), gf::vec2d(10.0, 1.0)])?;
        clips.set_clip_times("default", vec![gf::vec2d(0.0, 0.0), gf::vec2d(10.0, 5.0)])?;
        clips.set_clip_prim_path("default", "/Anim")?;
        clips.set_clip_manifest_asset_path("default", "manifest.usda")?;
        clips.set_interpolate_missing_clip_values("default", true)?;
        clips.set_clip_template_asset_path("tmpl", "clip.#.usda")?;
        clips.set_clip_template_stride("tmpl", 1.0)?;
        clips.set_clip_template_start_time("tmpl", 0.0)?;
        clips.set_clip_template_end_time("tmpl", 10.0)?;
        clips.set_clip_template_active_offset("tmpl", 0.5)?;

        assert_eq!(clips.clip_set_names()?, vec!["default".to_string(), "tmpl".to_string()]);
        assert_eq!(
            clips.clip_asset_paths("default")?,
            vec![AssetPath::new("a.usda"), AssetPath::new("b.usda")]
        );
        assert_eq!(
            clips.clip_active("default")?,
            vec![gf::vec2d(0.0, 0.0), gf::vec2d(10.0, 1.0)]
        );
        assert_eq!(
            clips.clip_times("default")?,
            vec![gf::vec2d(0.0, 0.0), gf::vec2d(10.0, 5.0)]
        );
        assert_eq!(clips.clip_prim_path("default")?.as_deref(), Some("/Anim"));
        assert_eq!(
            clips.clip_manifest_asset_path("default")?,
            Some(AssetPath::new("manifest.usda"))
        );
        assert_eq!(clips.interpolate_missing_clip_values("default")?, Some(true));
        assert_eq!(clips.clip_template_asset_path("tmpl")?.as_deref(), Some("clip.#.usda"));
        assert_eq!(clips.clip_template_stride("tmpl")?, Some(1.0));
        assert_eq!(clips.clip_template_start_time("tmpl")?, Some(0.0));
        assert_eq!(clips.clip_template_end_time("tmpl")?, Some(10.0));
        assert_eq!(clips.clip_template_active_offset("tmpl")?, Some(0.5));
        Ok(())
    }

    /// `clipSets` round-trips through the list-op setter/getter, and a prepend
    /// composes over a weaker explicit opinion.
    #[test]
    fn clip_sets_list_op_round_trip() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Anim")?;
        let clips = ClipsAPI::new(&stage.prim("/Anim")?);

        assert!(clips.clip_sets()?.is_none());
        clips.set_clip_sets(sdf::StringListOp::explicit(vec!["b".into(), "a".into()]))?;
        let order = clips.clip_sets()?.expect("authored");
        assert_eq!(order.flatten(), vec!["b".to_string(), "a".to_string()]);
        Ok(())
    }

    /// `set_clips` authors the whole dictionary in one write and `clips` reads
    /// it back composed.
    #[test]
    fn clips_dict_round_trip() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Anim")?;
        let clips = ClipsAPI::new(&stage.prim("/Anim")?);
        assert!(clips.clips()?.is_none());

        let set = Value::Dictionary([(keys::PRIM_PATH.to_string(), Value::String("/Geo".into()))].into());
        clips.set_clips(sdf::Dictionary::from([("default".to_string(), set)]))?;

        assert_eq!(clips.clip_set_names()?, vec!["default".to_string()]);
        assert_eq!(clips.clip_prim_path("default")?.as_deref(), Some("/Geo"));
        assert!(clips.clips()?.is_some());
        Ok(())
    }

    /// Every attribute path `manifest` declares, in its sorted order.
    fn declared(manifest: &sdf::Layer) -> Vec<String> {
        manifest
            .data()
            .spec_paths()
            .into_iter()
            .filter(|path| path.is_property_path())
            .map(|path| path.as_str().to_owned())
            .collect()
    }

    /// The generated manifest declares the attributes the clips carry samples
    /// for under `primPath`, including one inside a variant, and leaves out an
    /// attribute with no samples (`d`) and everything outside `primPath`
    /// (`/Clip/B`). Ported from the C++ `testUsdValueClips` manifest-generation
    /// assets.
    #[test]
    fn generate_manifest_declares_sampled() -> anyhow::Result<()> {
        let stage = Stage::open(&fixture("clip_manifest_gen"))?;
        let clips = ClipsAPI::new(&stage.prim("/Model")?);

        let manifest = clips.generate_clip_manifest("default", false)?.expect("set resolves");
        assert_eq!(
            declared(&manifest),
            ["/Clip/A.a", "/Clip/A.b", "/Clip/A.z", "/Clip/A{v=a}.c"]
        );
        // Declarations only — the clips' sample values are not copied.
        let a = manifest.attribute("/Clip/A.a")?.expect("declared");
        assert_eq!(a.type_name().as_deref(), Some("double"));
        assert!(a.time_samples().is_none());
        assert!(a.default().is_none());
        Ok(())
    }

    /// With blocks requested, each attribute is blocked at the activation time
    /// of every clip that carries no samples for it. `clip_1` is activated at 0
    /// and again at 8, so `z` — which only `clip_2` carries — is blocked twice.
    #[test]
    fn generate_manifest_blocks_missing() -> anyhow::Result<()> {
        let stage = Stage::open(&fixture("clip_manifest_gen"))?;
        let clips = ClipsAPI::new(&stage.prim("/Model")?);

        let manifest = clips.generate_clip_manifest("default", true)?.expect("set resolves");
        let blocked = |path: &str| -> anyhow::Result<Vec<f64>> {
            Ok(manifest
                .attribute(sdf::path(path)?)?
                .expect("declared")
                .time_samples()
                .unwrap_or_default()
                .into_iter()
                .map(|(time, value)| {
                    assert_eq!(value, Value::ValueBlock);
                    time
                })
                .collect())
        };
        assert_eq!(blocked("/Clip/A.a")?, vec![4.0]);
        assert_eq!(blocked("/Clip/A{v=a}.c")?, vec![4.0]);
        assert_eq!(blocked("/Clip/A.z")?, vec![0.0, 8.0]);
        Ok(())
    }

    /// A generated manifest is consumable: exported and named from
    /// `manifestAssetPath`, it gates value resolution exactly as the synthesized
    /// one it replaces did. An unknown clip-set name generates nothing.
    #[test]
    fn generate_manifest_round_trip() -> anyhow::Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = Stage::open(&fixture("clip_manifest_gen"))?;
        let clips = ClipsAPI::new(&stage.prim("/Model")?);
        assert!(clips.generate_clip_manifest("nope", false)?.is_none());

        // `a` is declared by the clips, `d` is authored without samples.
        let value = |name: &str| stage.attribute(name)?.get_at(TimeCode::from(0.0));
        assert_eq!(value("/Model.a")?, Some(1.0f64));
        assert_eq!(value("/Model.d")?, None::<f64>);

        let path = dir.path().join("manifest.usda");
        clips
            .generate_clip_manifest("default", false)?
            .expect("set resolves")
            .export(path.to_string_lossy())?;
        clips.set_clip_manifest_asset_path("default", path.to_string_lossy().as_ref())?;

        assert_eq!(
            clips.clip_manifest_asset_path("default")?,
            Some(AssetPath::new(path.to_string_lossy()))
        );
        assert_eq!(value("/Model.a")?, Some(1.0f64));
        assert_eq!(value("/Model.d")?, None::<f64>);
        Ok(())
    }

    /// A clip the schedule names but cannot be read fails generation, so a
    /// manifest that would silently de-source that clip's attributes is never
    /// handed back for export.
    #[test]
    fn generate_manifest_unreadable_clip_errors() -> anyhow::Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("clip.usda"),
            "#usda 1.0\ndef \"Model\"\n{\n    double a.timeSamples = { 0: 1.0 }\n}\n",
        )?;
        std::fs::write(
            dir.path().join("root.usda"),
            r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@, @./absent.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0), (4, 1)]
        }
    }
)
{
    double a
}
"#,
        )?;

        let stage = Stage::open(&dir.path().join("root.usda").to_string_lossy())?;
        let clips = ClipsAPI::new(&stage.prim("/Model")?);
        let error = clips
            .generate_clip_manifest("default", false)
            .expect_err("clip missing");
        assert!(format!("{error:#}").contains("absent.usda"), "{error:#}");
        Ok(())
    }

    /// The from-layers form declares over layers the caller already holds,
    /// without an activation schedule, so it never writes blocks.
    #[test]
    fn generate_manifest_from_layers() -> anyhow::Result<()> {
        let mut clip = sdf::Layer::new_anonymous("clip.usda");
        clip.edit(|l| {
            sdf::AttributeSpec::new(l.data_mut(), "/A.sampled", "double", sdf::Variability::Varying, false)?
                .set_time_sample(0.0, Value::Double(1.0));
            sdf::AttributeSpec::new(l.data_mut(), "/A.bare", "double", sdf::Variability::Varying, false)?;
            Ok(())
        })?;

        let manifest = ClipsAPI::generate_clip_manifest_from_layers(&[&clip], &sdf::path("/A")?)?;
        assert_eq!(declared(&manifest), ["/A.sampled"]);
        assert!(
            manifest
                .attribute("/A.sampled")?
                .expect("declared")
                .time_samples()
                .is_none()
        );
        Ok(())
    }

    /// Authoring clips on a prim that has no local spec on the edit-target
    /// layer creates an `over` (C++ `SetMetadata` behavior) rather than erroring.
    #[test]
    fn set_creates_over_without_local_spec() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let clips = ClipsAPI::new(&stage.prim("/NoSpec")?);
        clips.set_clip_prim_path("default", "/Geo")?;
        assert_eq!(clips.clip_prim_path("default")?.as_deref(), Some("/Geo"));
        Ok(())
    }
}
