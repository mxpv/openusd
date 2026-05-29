//! Value clips (spec 12.3.4): the explicit clip-set metadata model and the
//! stage-to-clip time mapping used during attribute value resolution.
//!
//! A clip set is a named group of value clips that partition an attribute's
//! time samples across external clip layers. The set is described by a
//! dictionary-valued `clips` metadata field; the `clipSets` field orders the
//! sets by strength. Only the explicit form is modelled here — template clips
//! (spec 12.3.4.1.3) are resolved to explicit metadata elsewhere and are not
//! parsed by [`ClipSet::parse_all`].

use crate::sdf::{Path, Value};
use std::collections::HashMap;

/// Dictionary keys inside a single clip set's metadata (spec 12.3.4.1).
pub(crate) mod keys {
    /// Ordered asset paths to the clips holding time-varying data (explicit).
    pub const ASSET_PATHS: &str = "assetPaths";
    /// Asset path of the layer indexing the attributes carried by the clips.
    pub const MANIFEST_ASSET_PATH: &str = "manifestAssetPath";
    /// Prim path substituted for the stage prim's path when querying clips.
    pub const PRIM_PATH: &str = "primPath";
    /// `(stageTime, assetIndex)` pairs selecting the active clip over time.
    pub const ACTIVE: &str = "active";
    /// `(stageTime, clipTime)` pairs forming the stage-to-clip timing curve.
    pub const TIMES: &str = "times";
}

/// A single explicit clip set: a named group of value clips with sequencing
/// and timing metadata (spec 12.3.4.1).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ClipSet {
    /// Clip set name — the key in the `clips` dictionary.
    pub name: String,
    /// Prim path substituted for the stage prim's path when querying clip
    /// layers (spec 12.3.4.1.1.1). `None` means use the stage prim's own path.
    pub prim_path: Option<Path>,
    /// Asset path of the manifest layer (spec 12.3.4.1.1.2), if authored.
    pub manifest_asset: Option<String>,
    /// Ordered clip asset paths holding time-varying data.
    pub asset_paths: Vec<String>,
    /// `(stageTime, assetIndex)` pairs, sorted by stage time. Each entry marks
    /// the clip active from its stage time up to the next entry (spec 12.3.4.3).
    pub active: Vec<(f64, usize)>,
    /// `(stageTime, clipTime)` pairs, sorted by stage time, forming the
    /// timing curve (spec 12.3.4.4). Duplicate stage times encode jump
    /// discontinuities (spec 12.3.4.8).
    pub times: Vec<(f64, f64)>,
}

impl ClipSet {
    /// Parses every explicit clip set from a composed `clips` dictionary value.
    ///
    /// `clip_sets_order` is the resolved `clipSets` field, when authored: it
    /// orders the returned sets strongest-first. Without it, sets are returned
    /// sorted by name for determinism. Sets lacking explicit `assetPaths`
    /// (e.g. template-only sets) are skipped.
    pub(crate) fn parse_all(clips: &Value, clip_sets_order: Option<&[String]>) -> Vec<ClipSet> {
        let Value::Dictionary(sets) = clips else {
            return Vec::new();
        };

        let ordered_names: Vec<&String> = match clip_sets_order {
            Some(order) => order.iter().filter(|name| sets.contains_key(*name)).collect(),
            None => {
                let mut names: Vec<&String> = sets.keys().collect();
                names.sort();
                names
            }
        };

        ordered_names
            .into_iter()
            .filter_map(|name| match sets.get(name) {
                Some(Value::Dictionary(set)) => Self::parse_one(name, set),
                _ => None,
            })
            .collect()
    }

    /// Parses a single clip set from its metadata dictionary. Returns `None`
    /// when the set has no explicit `assetPaths` (template form is deferred).
    fn parse_one(name: &str, set: &HashMap<String, Value>) -> Option<ClipSet> {
        // TODO: handle template clips (spec 12.3.4.1.3). When a set authors
        // `templateAssetPath` instead of `assetPaths`, derive the explicit
        // `assetPaths`/`active`/`times` from the template metadata here rather
        // than skipping the set.
        let asset_paths = set.get(keys::ASSET_PATHS).and_then(as_string_vec)?;

        let prim_path = set
            .get(keys::PRIM_PATH)
            .and_then(as_string)
            .and_then(|s| Path::new(&s).ok());
        let manifest_asset = set.get(keys::MANIFEST_ASSET_PATH).and_then(as_asset);

        let mut active: Vec<(f64, usize)> = set
            .get(keys::ACTIVE)
            .map(as_pairs)
            .unwrap_or_default()
            .into_iter()
            .map(|(stage, index)| (stage, index as usize))
            .collect();
        active.sort_by(|a, b| a.0.total_cmp(&b.0));

        let mut times = set.get(keys::TIMES).map(as_pairs).unwrap_or_default();
        times.sort_by(|a, b| a.0.total_cmp(&b.0));

        Some(ClipSet {
            name: name.to_string(),
            prim_path,
            manifest_asset,
            asset_paths,
            active,
            times,
        })
    }

    /// Returns the index into [`Self::asset_paths`] of the clip active at
    /// `stage_time` (spec 12.3.4.3). The first entry is active for all earlier
    /// times and the last entry for all later times. Returns `None` when no
    /// `active` entries are authored.
    pub(crate) fn active_clip(&self, stage_time: f64) -> Option<usize> {
        let mut chosen = self.active.first()?.1;
        for &(stage, index) in &self.active {
            if stage <= stage_time {
                chosen = index;
            } else {
                break;
            }
        }
        Some(chosen)
    }

    /// Maps `stage_time` to clip time through the `times` timing curve
    /// (spec 12.3.4.4). With no `times` authored, the stage time is returned
    /// unchanged.
    pub(crate) fn map_stage_to_clip(&self, stage_time: f64) -> f64 {
        map_stage_to_clip(&self.times, stage_time)
    }
}

/// Maps `stage_time` to clip time through a sorted `(stageTime, clipTime)`
/// timing curve made of linear segments (spec 12.3.4.4). Duplicate stage times
/// encode a jump discontinuity (spec 12.3.4.8): the earlier entry's clip time
/// applies up to that stage time, the later entry's at and after it. Out-of-
/// range stage times clamp to the first or last clip time.
fn map_stage_to_clip(times: &[(f64, f64)], stage_time: f64) -> f64 {
    let (Some(&(first_stage, first_clip)), Some(&(last_stage, last_clip))) = (times.first(), times.last()) else {
        return stage_time;
    };
    if stage_time <= first_stage {
        return first_clip;
    }
    if stage_time >= last_stage {
        return last_clip;
    }

    // Index of the last entry whose stage time does not exceed `stage_time`.
    // For a duplicated stage time this lands on the right-hand entry, so a
    // query exactly at the jump uses the "at and after" clip time.
    let lo = times.iter().rposition(|&(stage, _)| stage <= stage_time).unwrap_or(0);
    let (stage0, clip0) = times[lo];
    let (stage1, clip1) = times[lo + 1];

    if stage0 == stage1 {
        return clip1;
    }
    if stage_time == stage0 {
        return clip0;
    }
    let ratio = (stage_time - stage0) / (stage1 - stage0);
    clip0 + ratio * (clip1 - clip0)
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

/// Extracts a string list from an `asset[]`/`string[]`/`token[]` value. The
/// USDA parser stores `asset[]` arrays as [`Value::StringVec`].
fn as_string_vec(value: &Value) -> Option<Vec<String>> {
    match value {
        Value::StringVec(v) | Value::TokenVec(v) => Some(v.clone()),
        _ => None,
    }
}

/// Extracts `(f64, f64)` pairs from a `double2[]` value (`active`, `times`).
fn as_pairs(value: &Value) -> Vec<(f64, f64)> {
    match value {
        Value::Vec2dVec(pairs) => pairs.iter().map(|p| (p[0], p[1])).collect(),
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clip_set(active: Vec<(f64, usize)>, times: Vec<(f64, f64)>) -> ClipSet {
        ClipSet {
            name: "default".into(),
            prim_path: None,
            manifest_asset: None,
            asset_paths: Vec::new(),
            active,
            times,
        }
    }

    #[test]
    fn active_clip_ranges() {
        // active = [(0,0),(1,1),(2,2)] (spec 12.3.4.3 example).
        let cs = clip_set(vec![(0.0, 0), (1.0, 1), (2.0, 2)], vec![]);
        assert_eq!(cs.active_clip(-5.0), Some(0)); // before first → first
        assert_eq!(cs.active_clip(0.0), Some(0));
        assert_eq!(cs.active_clip(1.5), Some(1));
        assert_eq!(cs.active_clip(2.0), Some(2));
        assert_eq!(cs.active_clip(100.0), Some(2)); // after last → last
    }

    #[test]
    fn active_clip_empty() {
        assert_eq!(clip_set(vec![], vec![]).active_clip(0.0), None);
    }

    #[test]
    fn map_times_linear() {
        // times = [(0,1),(1,2),(2,3)] (spec 12.3.4.4 example).
        let cs = clip_set(vec![], vec![(0.0, 1.0), (1.0, 2.0), (2.0, 3.0)]);
        assert_eq!(cs.map_stage_to_clip(0.0), 1.0);
        assert_eq!(cs.map_stage_to_clip(1.0), 2.0);
        assert_eq!(cs.map_stage_to_clip(1.5), 2.5); // interpolated
        assert_eq!(cs.map_stage_to_clip(-3.0), 1.0); // clamp low
        assert_eq!(cs.map_stage_to_clip(9.0), 3.0); // clamp high
    }

    #[test]
    fn map_times_identity() {
        // No times authored → stage time passes through.
        assert_eq!(clip_set(vec![], vec![]).map_stage_to_clip(7.5), 7.5);
    }

    #[test]
    fn map_times_jump_discontinuity() {
        // times = [(0,0),(10,10),(10,25),(20,35)] (spec 12.3.4.8).
        // [0,10): first clip [0,10); [10,20]: second clip [25,35].
        let cs = clip_set(vec![], vec![(0.0, 0.0), (10.0, 10.0), (10.0, 25.0), (20.0, 35.0)]);
        assert_eq!(cs.map_stage_to_clip(5.0), 5.0);
        assert!((cs.map_stage_to_clip(9.999) - 9.999).abs() < 1e-6); // left of jump
        assert_eq!(cs.map_stage_to_clip(10.0), 25.0); // at jump → "at and after"
        assert_eq!(cs.map_stage_to_clip(15.0), 30.0); // second segment
        assert_eq!(cs.map_stage_to_clip(20.0), 35.0);
    }

    #[test]
    fn map_times_looping() {
        // times = [(0,0),(25,25),(25,0),(50,25)] — 25 frames looped twice.
        let cs = clip_set(vec![], vec![(0.0, 0.0), (25.0, 25.0), (25.0, 0.0), (50.0, 25.0)]);
        assert_eq!(cs.map_stage_to_clip(20.0), 20.0);
        assert_eq!(cs.map_stage_to_clip(45.0), 20.0); // one loop later → same clip time
    }

    /// Parses a clip set from a real USDA `clips` metadata opinion, mirroring
    /// the spec 12.3.4.1.2.4 example.
    #[test]
    fn parse_explicit_from_usda() {
        use crate::sdf::AbstractData;

        let parsed = crate::usda::parser::Parser::new(
            r#"#usda 1.0
def Xform "Geo" (
    clips = {
        dictionary default = {
            double2[] active = [(0, 0), (1, 1), (2, 2)]
            asset[] assetPaths = [@./quad_1.usda@, @./quad_2.usda@, @./quad_3.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Geo"
            double2[] times = [(0, 1), (1, 2), (2, 3)]
        }
    }
)
{
}
"#,
        )
        .parse()
        .expect("parse usda");
        let data = crate::usda::TextReader::from_data(parsed);

        let clips = data
            .try_get(&Path::new("/Geo").unwrap(), "clips")
            .expect("try_get")
            .expect("clips authored")
            .into_owned();

        let sets = ClipSet::parse_all(&clips, None);
        assert_eq!(sets.len(), 1);
        let cs = &sets[0];
        assert_eq!(cs.name, "default");
        assert_eq!(cs.prim_path, Some(Path::new("/Geo").unwrap()));
        assert_eq!(cs.manifest_asset.as_deref(), Some("./manifest.usda"));
        assert_eq!(cs.asset_paths, vec!["./quad_1.usda", "./quad_2.usda", "./quad_3.usda"]);
        assert_eq!(cs.active, vec![(0.0, 0), (1.0, 1), (2.0, 2)]);
        assert_eq!(cs.times, vec![(0.0, 1.0), (1.0, 2.0), (2.0, 3.0)]);
    }
}
