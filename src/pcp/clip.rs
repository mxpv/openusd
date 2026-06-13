//! Value clips (spec 12.3.4): the explicit clip-set metadata model and the
//! stage-to-clip time mapping used during attribute value resolution.
//!
//! A clip set is a named group of value clips that partition an attribute's
//! time samples across external clip layers. The set is described by a
//! dictionary-valued `clips` metadata field; the `clipSets` field orders the
//! sets by strength. Only the explicit form is modelled here — template clips
//! (spec 12.3.4.1.3) are resolved to explicit metadata elsewhere and are not
//! parsed by [`ClipSet::parse`].

use std::collections::HashMap;

use crate::gf;
use crate::sdf::{AssetPath, LayerOffset, Path, Value};

use super::LayerId;

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
    /// `bool` — interpolate across surrounding clips for an attribute whose
    /// active clip has a gap, instead of falling to the manifest default
    /// (spec 12.3.4.6-7).
    pub const INTERPOLATE_MISSING: &str = "interpolateMissingClipValues";

    // ── Template clip keys (spec 12.3.4.1.3) ──────────────────────────────
    /// `#`-pattern asset path expanded into explicit `assetPaths`.
    pub const TEMPLATE_ASSET_PATH: &str = "templateAssetPath";
    /// Inclusive start of the time range searched for template clips.
    pub const TEMPLATE_START_TIME: &str = "templateStartTime";
    /// Inclusive end of the time range searched for template clips.
    pub const TEMPLATE_END_TIME: &str = "templateEndTime";
    /// Step between successive template clip times.
    pub const TEMPLATE_STRIDE: &str = "templateStride";
    /// Offset applied to each clip's active stage time.
    pub const TEMPLATE_ACTIVE_OFFSET: &str = "templateActiveOffset";
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
    /// Ordered clip asset paths holding time-varying data (an `asset[]`,
    /// C++ `VtArray<SdfAssetPath>`).
    pub asset_paths: Vec<AssetPath>,
    /// `(stageTime, assetIndex)` pairs, sorted by stage time. Each entry marks
    /// the clip active from its stage time up to the next entry (spec 12.3.4.3).
    pub active: Vec<(f64, usize)>,
    /// `(stageTime, clipTime)` knots (`gf::Vec2d`), sorted by stage time,
    /// forming the timing curve (spec 12.3.4.4). Duplicate stage times encode
    /// jump discontinuities (spec 12.3.4.8).
    pub times: Vec<gf::Vec2d>,
    /// When `true`, a gap in the active clip is filled by interpolating across
    /// the nearest surrounding clips rather than by the manifest default
    /// (spec 12.3.4.6-7).
    pub interpolate_missing: bool,
}

/// A parsed clip set plus the layer provenance needed for asset resolution.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct ResolvedClipSet {
    pub set: ClipSet,
    pub asset_layer: LayerId,
    pub manifest_layer: Option<LayerId>,
}

impl ClipSet {
    /// Parses every explicit clip set from a composed `clips` dictionary value.
    ///
    /// `clip_sets_order` is the resolved `clipSets` field, when authored: it
    /// orders the returned sets strongest-first. Without it, sets are returned
    /// sorted by name for determinism. Sets lacking explicit `assetPaths`
    /// (e.g. template-only sets) are skipped.
    pub(crate) fn parse(clips: &Value, clip_sets_order: Option<&[String]>) -> Vec<ClipSet> {
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
                Some(Value::Dictionary(set)) => Self::parse_set(name, set),
                _ => None,
            })
            .collect()
    }

    /// Parses a single clip set from its metadata dictionary. Returns `None`
    /// when the set declares neither explicit `assetPaths` nor a usable
    /// `templateAssetPath`.
    ///
    /// Template sets (spec 12.3.4.1.3) authoring `templateAssetPath` +
    /// `templateStartTime` / `templateEndTime` / `templateStride` (and
    /// optionally `templateActiveOffset`) are expanded here into the explicit
    /// `assetPaths` / `active` / `times` form before resolution, so the rest
    /// of the pipeline only ever sees explicit clip sets. Explicit
    /// `assetPaths`, when authored, take precedence over the template form.
    fn parse_set(name: &str, set: &HashMap<String, Value>) -> Option<ClipSet> {
        let prim_path = set
            .get(keys::PRIM_PATH)
            .and_then(Value::as_str)
            .and_then(|s| Path::new(s).ok());
        let manifest_asset = set
            .get(keys::MANIFEST_ASSET_PATH)
            .and_then(Value::as_str)
            .map(str::to_owned);

        // Explicit form wins; otherwise expand a template set. `assetPaths` is
        // a strict `asset[]`, and `active` / `times` a strict `double2[]`, so
        // each extracts through `get` (exact `TryFrom`) rather than `cast`.
        let (asset_paths, active, times) = match get::<Vec<AssetPath>>(set, keys::ASSET_PATHS) {
            Some(asset_paths) => {
                let mut active: Vec<(f64, usize)> = get::<Vec<gf::Vec2d>>(set, keys::ACTIVE)
                    .unwrap_or_default()
                    .into_iter()
                    .map(|p| (p.x, p.y as usize))
                    .collect();
                active.sort_by(|a, b| a.0.total_cmp(&b.0));

                let mut times = get::<Vec<gf::Vec2d>>(set, keys::TIMES).unwrap_or_default();
                times.sort_by(|a, b| a.x.total_cmp(&b.x));
                (asset_paths, active, times)
            }
            None => expand_template(set)?,
        };

        let interpolate_missing = get::<bool>(set, keys::INTERPOLATE_MISSING).unwrap_or(false);

        Some(ClipSet {
            name: name.to_string(),
            prim_path,
            manifest_asset,
            asset_paths,
            active,
            times,
            interpolate_missing,
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

    /// Retimes the schedule through `offset`, shifting the stage component of
    /// every `active` and `times` entry while leaving the clip-time targets and
    /// asset paths untouched. A template-derived schedule is produced in clip
    /// time and brought into stage time here; explicit `active`/`times` are
    /// retimed as they compose.
    pub(crate) fn retime_stage_times(&mut self, offset: LayerOffset) {
        if offset.is_identity() {
            return;
        }
        for (stage, _) in &mut self.active {
            *stage = offset.apply(*stage);
        }
        for knot in &mut self.times {
            knot.x = offset.apply(knot.x);
        }
        // A positive scale preserves the existing stage ordering; only a
        // negative scale (time reversal) needs a re-sort.
        if offset.scale < 0.0 {
            self.active.sort_by(|a, b| a.0.total_cmp(&b.0));
            self.times.sort_by(|a, b| a.x.total_cmp(&b.x));
        }
    }

    /// The stage times at which a clipped attribute's value changes under this
    /// set (the clip half of `UsdAttribute::GetTimeSamples`). `per_clip[i]` is
    /// the in-clip sample times the clip at `asset_paths[i]` authors for the
    /// attribute; an active entry referencing an index past `per_clip` is
    /// treated as authoring none.
    ///
    /// For each clip active over a stage interval, the result gathers the
    /// timing-curve knots in the interval and the clip's in-clip sample times
    /// mapped to stage time through [`Self::stage_times_for_clip_time`] and
    /// clamped to the interval, plus the clip-switch boundary. The first active
    /// entry is active from negative infinity (spec 12.3.4.3, matching
    /// [`Self::active_clip`]), so its interval has no lower bound and its stage
    /// time is not a switch; each later entry's stage time bounds its interval
    /// and is itself a switch boundary (the value can jump as the active clip
    /// changes). Returns the union sorted ascending; empty when no clip is active.
    ///
    /// Every active interval contributes its switch boundary, mirroring C++
    /// `Usd_ClipSet` with `interpolateMissingClipValues` off: a clip authoring
    /// no in-interval sample still reports the boundary where it becomes active,
    /// since the active clip changes there. Whether the set sources the
    /// attribute at all is decided by the caller's participation check before
    /// this routine runs.
    pub(crate) fn stage_sample_times(&self, per_clip: &[Vec<f64>]) -> Vec<f64> {
        let mut out: Vec<f64> = Vec::new();
        for (k, &(start, clip_index)) in self.active.iter().enumerate() {
            let samples = per_clip.get(clip_index).map_or(&[][..], Vec::as_slice);
            let end = self.active.get(k + 1).map(|next| next.0);
            // The first entry is active from negative infinity; later entries
            // start at `start`, which is also a clip-switch sample time.
            let lower = (k > 0).then_some(start);
            let in_interval = |t: f64| lower.is_none_or(|l| t >= l) && end.is_none_or(|e| t < e);

            if let Some(boundary) = lower {
                out.push(boundary);
            }
            out.extend(self.times.iter().map(|knot| knot.x).filter(|&x| in_interval(x)));
            for &clip_time in samples {
                out.extend(
                    self.stage_times_for_clip_time(clip_time)
                        .into_iter()
                        .filter(|&t| in_interval(t)),
                );
            }
        }
        // Drop non-finite times before dedup: a clip may author a NaN time-
        // sample key, and `dedup` (PartialEq) would not collapse repeated NaNs.
        out.retain(|t| t.is_finite());
        out.sort_by(f64::total_cmp);
        out.dedup();
        out
    }

    /// Whether this set's active-clip schedule alone can make the value vary
    /// over time, the clip-schedule half of
    /// [`UsdAttribute::ValueMightBeTimeVarying`]. True when more than one clip
    /// window is active, since switching the active clip can change the value.
    /// A conservative over-approximation: it does not check whether the windows
    /// resolve to distinct values (matching the "might" in the C++ name), and
    /// time variation within a single window is reported through the sample-time
    /// count instead.
    ///
    /// [`UsdAttribute::ValueMightBeTimeVarying`]: crate::usd::Attribute::value_might_be_time_varying
    pub(crate) fn may_be_time_varying(&self) -> bool {
        self.active.len() > 1
    }

    /// The stage times mapping to clip time `clip_time` — the inverse of
    /// [`Self::map_stage_to_clip`] over the timing curve. With no `times`
    /// authored the mapping is identity (the clip time is its own stage time).
    /// Each linear segment that crosses `clip_time` contributes one stage time;
    /// a constant segment (no clip-time change) contributes none, since the
    /// value is held there and only the activation boundary marks a change.
    fn stage_times_for_clip_time(&self, clip_time: f64) -> Vec<f64> {
        if self.times.is_empty() {
            return vec![clip_time];
        }
        self.times
            .windows(2)
            .filter_map(|seg| {
                let (sa, ca) = (seg[0].x, seg[0].y);
                let (sb, cb) = (seg[1].x, seg[1].y);
                let (lo, hi) = if ca <= cb { (ca, cb) } else { (cb, ca) };
                if ca == cb || clip_time < lo || clip_time > hi {
                    return None;
                }
                Some(sa + (clip_time - ca) / (cb - ca) * (sb - sa))
            })
            .collect()
    }
}

/// Maps `stage_time` to clip time through a sorted `(stageTime, clipTime)`
/// timing curve made of linear segments (spec 12.3.4.4). Duplicate stage times
/// encode a jump discontinuity (spec 12.3.4.8): the earlier entry's clip time
/// applies up to that stage time, the later entry's at and after it. Out-of-
/// range stage times clamp to the first or last clip time.
fn map_stage_to_clip(times: &[gf::Vec2d], stage_time: f64) -> f64 {
    let (Some(first), Some(last)) = (times.first(), times.last()) else {
        return stage_time;
    };
    if stage_time < first.x {
        return first.y;
    }
    if stage_time >= last.x {
        return last.y;
    }

    // Index of the last entry whose stage time does not exceed `stage_time`.
    // For a duplicated stage time this lands on the right-hand entry, so a
    // query exactly at the jump uses the "at and after" clip time.
    let lo = times.iter().rposition(|knot| knot.x <= stage_time).unwrap_or(0);
    let (lo_knot, hi_knot) = (times[lo], times[lo + 1]);
    let (stage0, clip0) = (lo_knot.x, lo_knot.y);
    let (stage1, clip1) = (hi_knot.x, hi_knot.y);

    if stage0 == stage1 {
        return clip1;
    }
    if stage_time == stage0 {
        return clip0;
    }
    let ratio = (stage_time - stage0) / (stage1 - stage0);
    gf::lerp(clip0, clip1, ratio)
}

/// Derived `(assetPaths, active, times)` from a template clip set.
type TemplateExpansion = (Vec<AssetPath>, Vec<(f64, usize)>, Vec<gf::Vec2d>);

/// Expand a template clip set (spec 12.3.4.1.3) into explicit
/// `(assetPaths, active, times)`.
///
/// Iterates clip times from `templateStartTime` to `templateEndTime`
/// (inclusive) by `templateStride`, substituting each time into the
/// `#`-pattern `templateAssetPath`. Each generated clip `i` contributes
/// `assetPaths[i]`, an `active` entry `(stageTime, i)`, and a `times`
/// entry `(clipTime, clipTime)`. `templateActiveOffset`, when authored,
/// shifts each clip's active stage time to `clipTime + offset` and adds
/// boundary knots to `times` at `start - |offset|` and `end + |offset|`.
///
/// Returns `None` when the required template fields are missing or
/// invalid (non-positive stride, `end < start`, `|activeOffset| > stride`,
/// or an unparseable pattern).
///
/// Times are scaled by a fixed promotion factor during iteration so a
/// fractional `stride` accumulates without binary-float drift, matching
/// C++ `Usd_ClipSetDefinition` template derivation.
fn expand_template(set: &HashMap<String, Value>) -> Option<TemplateExpansion> {
    let template = set
        .get(keys::TEMPLATE_ASSET_PATH)
        .and_then(Value::as_str)
        .map(str::to_owned)?;
    // Template timing is `double`, read strictly like C++ `IsHolding<double>`.
    let start = get::<f64>(set, keys::TEMPLATE_START_TIME)?;
    let end = get::<f64>(set, keys::TEMPLATE_END_TIME)?;
    let stride = get::<f64>(set, keys::TEMPLATE_STRIDE)?;
    let active_offset = get::<f64>(set, keys::TEMPLATE_ACTIVE_OFFSET);

    if stride.is_nan() || stride <= 0.0 || end < start {
        return None;
    }
    // Spec 12.3.4.1.3: the active offset magnitude may not exceed the stride.
    if active_offset.is_some_and(|off| off.abs() > stride) {
        return None;
    }

    let pattern = HashPattern::parse(&template)?;

    // Promote to integers so a fractional stride doesn't accumulate float
    // drift across the loop (C++ uses the same trick).
    const PROMOTION: f64 = 10000.0;
    let end_p = end * PROMOTION;
    let stride_p = stride * PROMOTION;

    let mut asset_paths = Vec::new();
    let mut active = Vec::new();
    let mut times = Vec::new();

    // An active offset lets a query reach `|offset|` before the first clip and
    // after the last. Author timing knots at those expanded boundaries so the
    // lead/trail range maps linearly to clip time instead of clamping to the
    // first or last clip time (spec 12.3.4.1.3, matching C++ derivation).
    if let Some(off) = active_offset {
        let front = start - off.abs();
        times.push(gf::vec2d(front, front));
    }

    let mut t = start * PROMOTION;
    let mut index = 0usize;
    // `+ 0.5` keeps the inclusive endpoint despite residual rounding.
    while t <= end_p + 0.5 {
        let clip_time = t / PROMOTION;
        asset_paths.push(pattern.format(clip_time).into());
        times.push(gf::vec2d(clip_time, clip_time));
        let stage_time = match active_offset {
            Some(off) => (t + off * PROMOTION) / PROMOTION,
            None => clip_time,
        };
        active.push((stage_time, index));
        index += 1;
        t += stride_p;
    }

    if let Some(off) = active_offset {
        let back = end + off.abs();
        times.push(gf::vec2d(back, back));
    }

    if asset_paths.is_empty() {
        return None;
    }
    active.sort_by(|a, b| a.0.total_cmp(&b.0));
    times.sort_by(|a, b| a.x.total_cmp(&b.x));
    Some((asset_paths, active, times))
}

/// A parsed `templateAssetPath` pattern: a prefix, one or two adjacent
/// `#`-groups (integer, optionally followed by a subinteger group), and
/// a suffix. Per spec the groups must be adjacent and number one or two.
struct HashPattern {
    prefix: String,
    int_width: usize,
    /// Width of the subinteger group, when the pattern has two groups.
    frac_width: Option<usize>,
    suffix: String,
}

impl HashPattern {
    /// Parse `path/basename.###.usd` or `path/basename.##.##.usd`.
    /// Returns `None` when there is no `#`-group, more than two groups,
    /// or stray `#` outside the (adjacent) groups.
    fn parse(template: &str) -> Option<HashPattern> {
        let first = template.find('#')?;
        let prefix = template[..first].to_string();
        let rest = &template[first..];

        // First (integer) group.
        let int_width = rest.chars().take_while(|&c| c == '#').count();
        let after_int = &rest[int_width..];

        // Optional `.<##...>` subinteger group immediately following.
        let (frac_width, suffix) = if let Some(dot_rest) = after_int.strip_prefix('.') {
            if dot_rest.starts_with('#') {
                let frac_width = dot_rest.chars().take_while(|&c| c == '#').count();
                (Some(frac_width), dot_rest[frac_width..].to_string())
            } else {
                (None, after_int.to_string())
            }
        } else {
            (None, after_int.to_string())
        };

        // Spec: hash groups must be adjacent and number one or two — any
        // further `#` in the suffix means a malformed (3+ group) pattern.
        if suffix.contains('#') {
            return None;
        }

        Some(HashPattern {
            prefix,
            int_width,
            frac_width,
            suffix,
        })
    }

    /// Substitute `time` into the pattern. Integer group zero-pads to the
    /// hash count (widening when the value needs more digits); the
    /// subinteger group is fixed-width fractional precision.
    fn format(&self, time: f64) -> String {
        let body = match self.frac_width {
            // Two groups: `<int>.<frac>` at the given widths (spec example
            // `foo.#.###.usd` @ 1.15 -> `foo.1.150.usd`).
            Some(frac_width) => {
                let rendered = format!("{:.*}", frac_width, time);
                let (int_part, frac_part) = rendered.split_once('.').unwrap_or((rendered.as_str(), ""));
                let neg = int_part.starts_with('-');
                let digits = int_part.trim_start_matches('-');
                let padded = format!("{:0>width$}", digits, width = self.int_width);
                let sign = if neg { "-" } else { "" };
                format!("{sign}{padded}.{frac_part}")
            }
            // One group: zero-padded integer, truncating the clip time toward
            // zero like the C++ `int(time)` cast (spec example `foo.###.usd`
            // @ 12 -> `foo.012.usd`).
            None => format!("{:0width$}", time as i64, width = self.int_width),
        };
        format!("{}{}{}", self.prefix, body, self.suffix)
    }
}

/// Reads `key` from a clip-set dictionary and extracts it strictly as `T` — the
/// exact-variant [`TryFrom`] tier — yielding `None` when the key is absent or
/// the authored type does not match. Mirrors C++ `Usd_ClipSetDefinition`'s
/// `IsHolding<T>` reads, which likewise treat a type mismatch as unauthored.
fn get<T: TryFrom<Value>>(set: &HashMap<String, Value>, key: &str) -> Option<T> {
    set.get(key).cloned().and_then(|v| T::try_from(v).ok())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    /// Builds a `double2[]` knot list (`active` / `times`) from `(x, y)` pairs.
    fn knots(pairs: &[(f64, f64)]) -> Vec<gf::Vec2d> {
        pairs.iter().map(|&(x, y)| gf::vec2d(x, y)).collect()
    }

    // Template hash substitution (clipsAPI.h doc examples).

    #[test]
    fn hash_substitution_integer() {
        // foo.##.usd  @ 12  => foo.12.usd
        assert_eq!(HashPattern::parse("foo.##.usd").unwrap().format(12.0), "foo.12.usd");
        // foo.###.usd @ 12  => foo.012.usd
        assert_eq!(HashPattern::parse("foo.###.usd").unwrap().format(12.0), "foo.012.usd");
        // foo.#.usd   @ 333 => foo.333.usd
        assert_eq!(HashPattern::parse("foo.#.usd").unwrap().format(333.0), "foo.333.usd");
        // Fractional clip times truncate toward zero, not round:
        // foo.#.usd @ 1.6 => foo.1.usd.
        assert_eq!(HashPattern::parse("foo.#.usd").unwrap().format(1.6), "foo.1.usd");
    }

    #[test]
    fn hash_substitution_subinteger() {
        // foo.#.###.usd @ 1.15 => foo.1.150.usd
        assert_eq!(
            HashPattern::parse("foo.#.###.usd").unwrap().format(1.15),
            "foo.1.150.usd"
        );
        // foo.#.##.usd  @ 1.1  => foo.1.10.usd
        assert_eq!(HashPattern::parse("foo.#.##.usd").unwrap().format(1.1), "foo.1.10.usd");
    }

    #[test]
    fn hash_pattern_rejects_three_groups() {
        assert!(HashPattern::parse("foo.#.#.#.usd").is_none());
        assert!(HashPattern::parse("foo.usd").is_none());
    }

    #[test]
    fn template_expands_to_explicit_clip_set() {
        use std::collections::HashMap;
        let mut set = HashMap::new();
        set.insert(
            keys::TEMPLATE_ASSET_PATH.to_string(),
            Value::AssetPath("clip.##.usd".into()),
        );
        set.insert(keys::TEMPLATE_START_TIME.to_string(), Value::Double(101.0));
        set.insert(keys::TEMPLATE_END_TIME.to_string(), Value::Double(103.0));
        set.insert(keys::TEMPLATE_STRIDE.to_string(), Value::Double(1.0));

        let parsed = ClipSet::parse_set("default", &set).expect("template set");
        assert_eq!(
            parsed.asset_paths,
            vec![
                "clip.101.usd".to_string(),
                "clip.102.usd".to_string(),
                "clip.103.usd".to_string()
            ],
        );
        assert_eq!(parsed.active, vec![(101.0, 0), (102.0, 1), (103.0, 2)]);
        assert_eq!(parsed.times, knots(&[(101.0, 101.0), (102.0, 102.0), (103.0, 103.0)]));
    }

    #[test]
    fn template_active_offset_shifts_active_times() {
        use std::collections::HashMap;
        let mut set = HashMap::new();
        set.insert(
            keys::TEMPLATE_ASSET_PATH.to_string(),
            Value::AssetPath("c.#.usd".into()),
        );
        set.insert(keys::TEMPLATE_START_TIME.to_string(), Value::Double(0.0));
        set.insert(keys::TEMPLATE_END_TIME.to_string(), Value::Double(2.0));
        set.insert(keys::TEMPLATE_STRIDE.to_string(), Value::Double(1.0));
        set.insert(keys::TEMPLATE_ACTIVE_OFFSET.to_string(), Value::Double(-0.5));

        let parsed = ClipSet::parse_set("default", &set).expect("template set");
        // Active stage times shift by the offset; `times` keeps the clip-time
        // knots plus boundary knots expanded by |offset| at each end.
        assert_eq!(parsed.active, vec![(-0.5, 0), (0.5, 1), (1.5, 2)]);
        assert_eq!(
            parsed.times,
            knots(&[(-0.5, -0.5), (0.0, 0.0), (1.0, 1.0), (2.0, 2.0), (2.5, 2.5)])
        );
    }

    #[test]
    fn template_rejects_invalid_metadata() {
        use std::collections::HashMap;
        let base = |off: f64, stride: f64| {
            let mut set = HashMap::new();
            set.insert(
                keys::TEMPLATE_ASSET_PATH.to_string(),
                Value::AssetPath("c.#.usd".into()),
            );
            set.insert(keys::TEMPLATE_START_TIME.to_string(), Value::Double(0.0));
            set.insert(keys::TEMPLATE_END_TIME.to_string(), Value::Double(2.0));
            set.insert(keys::TEMPLATE_STRIDE.to_string(), Value::Double(stride));
            set.insert(keys::TEMPLATE_ACTIVE_OFFSET.to_string(), Value::Double(off));
            set
        };
        // |activeOffset| > stride is rejected (spec 12.3.4.1.3).
        assert!(ClipSet::parse_set("default", &base(2.0, 1.0)).is_none());
        // Non-positive stride is rejected.
        assert!(ClipSet::parse_set("default", &base(0.0, 0.0)).is_none());
    }

    #[test]
    fn explicit_asset_paths_win_over_template() {
        use std::collections::HashMap;
        let mut set = HashMap::new();
        set.insert(
            keys::ASSET_PATHS.to_string(),
            Value::AssetPathVec(vec!["explicit.usd".into()]),
        );
        set.insert(
            keys::TEMPLATE_ASSET_PATH.to_string(),
            Value::AssetPath("c.#.usd".into()),
        );
        set.insert(keys::TEMPLATE_START_TIME.to_string(), Value::Double(0.0));
        set.insert(keys::TEMPLATE_END_TIME.to_string(), Value::Double(2.0));
        set.insert(keys::TEMPLATE_STRIDE.to_string(), Value::Double(1.0));

        let parsed = ClipSet::parse_set("default", &set).expect("explicit set");
        assert_eq!(parsed.asset_paths, vec!["explicit.usd".to_string()]);
    }

    fn clip_set(active: Vec<(f64, usize)>, times: Vec<gf::Vec2d>) -> ClipSet {
        ClipSet {
            name: "default".into(),
            prim_path: None,
            manifest_asset: None,
            asset_paths: Vec::new(),
            active,
            times,
            interpolate_missing: false,
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
        let cs = clip_set(vec![], knots(&[(0.0, 1.0), (1.0, 2.0), (2.0, 3.0)]));
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
    fn stage_times_identity() {
        // Two clips, identity timing: each clip's in-clip samples are stage
        // times, clamped to that clip's active interval, plus the boundaries.
        let cs = clip_set(vec![(0.0, 0), (10.0, 1)], vec![]);
        // clip 0 authors {0,5,12} (12 is outside its [0,10) interval); clip 1 {10,15}.
        let times = cs.stage_sample_times(&[vec![0.0, 5.0, 12.0], vec![10.0, 15.0]]);
        assert_eq!(times, vec![0.0, 5.0, 10.0, 15.0]);
    }

    #[test]
    fn stage_times_empty_window_boundary() {
        // An active clip authoring no samples still reports the boundary where it
        // becomes active: clip 1's window opens at stage 10, a value-change point
        // (the active clip switches there), so 10 is reported alongside clip 0's
        // samples.
        let cs = clip_set(vec![(0.0, 0), (10.0, 1)], vec![]);
        let times = cs.stage_sample_times(&[vec![0.0, 5.0], vec![]]);
        assert_eq!(times, vec![0.0, 5.0, 10.0]);
    }

    #[test]
    fn stage_times_linear_timing() {
        // times maps stage→clip as clip = stage/2, so a clip time maps back to
        // stage 2*clip. Boundary 0 and timing knots {0,10} join the mapped
        // sample stage times {0,5,10}.
        let cs = clip_set(vec![(0.0, 0)], knots(&[(0.0, 0.0), (10.0, 5.0)]));
        let times = cs.stage_sample_times(&[vec![0.0, 2.5, 5.0]]);
        assert_eq!(times, vec![0.0, 5.0, 10.0]);
    }

    #[test]
    fn stage_times_before_first_active() {
        // The first clip is active from -∞ (matches active_clip): a sample
        // mapping before the first active entry's stage time is still reported,
        // and that stage time is not a spurious switch boundary.
        let cs = clip_set(vec![(10.0, 0)], vec![]);
        let times = cs.stage_sample_times(&[vec![5.0, 15.0]]);
        assert_eq!(times, vec![5.0, 15.0]);
    }

    #[test]
    fn stage_times_no_active() {
        // No active entries → no clip is scheduled → no sample times.
        assert!(clip_set(vec![], vec![])
            .stage_sample_times(&[vec![0.0, 1.0]])
            .is_empty());
    }

    #[test]
    fn map_times_jump_discontinuity() {
        // times = [(0,0),(10,10),(10,25),(20,35)] (spec 12.3.4.8).
        // [0,10): first clip [0,10); [10,20]: second clip [25,35].
        let cs = clip_set(vec![], knots(&[(0.0, 0.0), (10.0, 10.0), (10.0, 25.0), (20.0, 35.0)]));
        assert_eq!(cs.map_stage_to_clip(5.0), 5.0);
        assert!((cs.map_stage_to_clip(9.999) - 9.999).abs() < 1e-6); // left of jump
        assert_eq!(cs.map_stage_to_clip(10.0), 25.0); // at jump → "at and after"
        assert_eq!(cs.map_stage_to_clip(15.0), 30.0); // second segment
        assert_eq!(cs.map_stage_to_clip(20.0), 35.0);
    }

    #[test]
    fn map_times_initial_jump() {
        // At a duplicated first stage time, the right-hand entry applies
        // exactly at the jump.
        let cs = clip_set(vec![], knots(&[(0.0, 0.0), (0.0, 25.0), (10.0, 35.0)]));
        assert_eq!(cs.map_stage_to_clip(-1.0), 0.0);
        assert_eq!(cs.map_stage_to_clip(0.0), 25.0);
        assert_eq!(cs.map_stage_to_clip(5.0), 30.0);
    }

    #[test]
    fn map_times_looping() {
        // times = [(0,0),(25,25),(25,0),(50,25)] — 25 frames looped twice.
        let cs = clip_set(vec![], knots(&[(0.0, 0.0), (25.0, 25.0), (25.0, 0.0), (50.0, 25.0)]));
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
        let data = sdf::Data::from_specs(parsed);

        let clips = data
            .try_field(&Path::new("/Geo").unwrap(), "clips")
            .expect("try_field")
            .expect("clips authored")
            .into_owned();

        let sets = ClipSet::parse(&clips, None);
        assert_eq!(sets.len(), 1);
        let cs = &sets[0];
        assert_eq!(cs.name, "default");
        assert_eq!(cs.prim_path, Some(Path::new("/Geo").unwrap()));
        assert_eq!(cs.manifest_asset.as_deref(), Some("./manifest.usda"));
        assert_eq!(cs.asset_paths, vec!["./quad_1.usda", "./quad_2.usda", "./quad_3.usda"]);
        assert_eq!(cs.active, vec![(0.0, 0), (1.0, 1), (2.0, 2)]);
        assert_eq!(cs.times, knots(&[(0.0, 1.0), (1.0, 2.0), (2.0, 3.0)]));
    }
}
