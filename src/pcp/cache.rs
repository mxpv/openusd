//! Composition graph: lazily-built cache of per-prim composition indices.
//!
//! The [`Cache`] is the primary interface between [`Stage`](crate::usd::Stage)
//! and the composition engine. It caches [`PrimIndex`] results alongside the
//! [`CompositionContext`] that flows from parent prims to children, so ancestor
//! composition is never recomputed.
//!
//! Relocates (`layerRelocates`) are handled at the cache level: source paths
//! are resolved, full composition indices are built for them, and the results
//! are merged as `ArcType::Relocate` nodes. The child name lists are
//! adjusted to hide relocated sources and expose targets.

use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{AbstractData, Path, SpecType, Value};

use super::clip::ResolvedClipSet;
use super::deps::Dependencies;
use super::index::{AncestorArc, ArcType, CompositionContext, Node, PrimIndex};
use super::rel::Relocates;
use super::{LayerStack, VariantFallbackMap};

/// Lazily-built composition graph.
///
/// Caches per-prim composition indices and contexts. When a prim is queried
/// for the first time, its index is built using the parent's cached context
/// (if available). During depth-first traversal, parents are always composed
/// before children, so the context chain is always populated.
///
/// An optional [`VariantFallbackMap`] provides fallback selections for variant
/// sets that have no authored opinion. Authored selections always take priority;
/// fallbacks are tried in order before the default (first variant in the set).
///
/// All public methods return `Result` — a [`pcp::Error`](super::Error) is
/// returned when composition fails. The caller ([`Stage`](crate::usd::Stage))
/// decides whether to skip or abort via its error handler.
pub struct Cache {
    stack: LayerStack,
    /// Per-prim composition indices, keyed by composed path.
    indices: HashMap<Path, PrimIndex>,
    /// Per-prim composition contexts for child propagation.
    contexts: HashMap<Path, CompositionContext>,
    /// Reverse `(layer, site) → prim_index_paths` map for surgical invalidation.
    deps: Dependencies,
    /// Relocate namespace remapping state.
    relocates: Relocates,
    /// Variant fallback selections tried when no authored selection exists.
    variant_fallbacks: VariantFallbackMap,
    /// Lazily-loaded value-clip and manifest layers, keyed by resolved
    /// identifier. Clip layers do not participate in composition (spec
    /// 12.3.4), so they are held here rather than in the [`LayerStack`].
    clip_layers: HashMap<String, sdf::Layer>,
    /// Shared prototypes for scene-graph instancing (spec 11.3.3), keyed by
    /// their `/__Prototype_N` root path. Instances with the same instancing key
    /// reuse one prototype, so its subtree is composed only once. Cleared by
    /// [`Self::invalidate_prototypes`] on any composition change. Path-keyed so
    /// the common query direction (path to prototype) is a single lookup.
    prototypes: HashMap<Path, Prototype>,
    /// Maps an instancing key to its prototype root, the lookup direction used
    /// only when registering an instance to dedup against an existing key.
    prototype_keys: HashMap<InstanceKey, Path>,
    /// Counter for minting `/__Prototype_N` identities in registration order.
    prototype_count: usize,
}

/// A shared prototype for a set of instances with the same [`InstanceKey`]
/// (spec 11.3.3). Its composition is backed by the canonical instance's
/// already arc-only subtree, exposed under a synthetic `/__Prototype_N` path.
///
/// TODO: the prototype is alias-backed by the canonical instance rather than
/// composed as its own root, so prototype-root attribute queries reflect the
/// canonical instance's composition (which keeps its own local opinions).
/// Materializing `/__Prototype_N` as an independently composed namespace is
/// future work.
struct Prototype {
    /// Registration order (the `N` in `/__Prototype_N`). Kept so prototypes can
    /// be returned in mint order without parsing the path.
    index: usize,
    /// Instance whose composed subtree backs this prototype.
    canonical: Path,
    /// Every instance sharing this prototype.
    instances: Vec<Path>,
}

/// Identity of an instance prim's shared composition (spec 11.3.3): the
/// arc-introduced opinions that determine its subtree, independent of the
/// instance's own stage path. Instances with equal keys share a prototype.
#[derive(Clone, PartialEq, Eq, Hash)]
struct InstanceKey(Vec<InstanceArc>);

/// One arc contribution in an [`InstanceKey`]. Floats are stored as bit
/// patterns so the key is `Hash`/`Eq`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct InstanceArc {
    arc: u8,
    layer: String,
    path: String,
    offset_bits: u64,
    scale_bits: u64,
}

enum FieldValue {
    NotAuthored,
    Authored(Option<Value>),
}

/// Collapses the spec sentinels for "no value" ([`Value::ValueBlock`] and
/// [`Value::None`]) to `None`, passing any real value through as `Some`. An
/// authored block stops fall-through to weaker sources yet presents as absent.
fn block_to_none(value: Value) -> Option<Value> {
    match value {
        Value::ValueBlock | Value::None => None,
        other => Some(other),
    }
}

impl Cache {
    /// Creates a new composition graph from a prebuilt layer stack.
    pub(crate) fn new(stack: LayerStack, variant_fallbacks: VariantFallbackMap) -> Self {
        let relocates = Relocates::new(&stack.layers);
        Self {
            stack,
            indices: HashMap::new(),
            contexts: HashMap::new(),
            deps: Dependencies::default(),
            relocates,
            variant_fallbacks,
            clip_layers: HashMap::new(),
            prototypes: HashMap::new(),
            prototype_keys: HashMap::new(),
            prototype_count: 0,
        }
    }

    /// Loads a value-clip or manifest layer referenced by `asset_path`,
    /// anchored to the layer at `anchor_layer` (the layer that authored the
    /// clip metadata). Layers are loaded on demand through the stack's
    /// resolver and cached by resolved identifier; clip layers never enter the
    /// composition [`LayerStack`] (spec 12.3.4).
    ///
    /// Returns `Ok(None)` when the asset path cannot be resolved.
    pub(crate) fn clip_layer(&mut self, asset_path: &str, anchor_layer: usize) -> Result<Option<&sdf::Layer>> {
        // Anchor the clip asset path to the authoring layer's location so
        // relative paths resolve like any other dependency.
        let clip_id = {
            let resolver = self.stack.resolver.as_ref();
            let anchor_id = self.stack.identifier(anchor_layer).to_owned();
            match resolver.resolve(&anchor_id) {
                Some(anchor) => resolver.create_identifier(asset_path, Some(&anchor)),
                None => resolver.create_identifier(asset_path, None),
            }
        };

        if !self.clip_layers.contains_key(&clip_id) {
            let resolver = self.stack.resolver.as_ref();
            let Some(resolved) = resolver.resolve(&clip_id) else {
                return Ok(None);
            };
            let data = crate::layer::open_layer(resolver, &resolved)?;
            self.clip_layers
                .insert(clip_id.clone(), sdf::Layer::new(clip_id.clone(), data));
        }

        Ok(self.clip_layers.get(&clip_id))
    }

    /// Layer indices that make up the stage's root layer stack: the session
    /// layers plus the root layer and its sublayers. These carry "local"
    /// opinions, which outrank value-clip data (spec 12.3.4.5). Referenced and
    /// payload layer stacks contribute their own `Root`-arc nodes, so local
    /// membership is decided by layer index, not arc type.
    fn local_layers(&self) -> HashSet<usize> {
        let mut local: HashSet<usize> = (0..self.stack.session_layer_count).collect();
        let root = self.stack.session_layer_count;
        if let Some(sublayers) = self.stack.sublayer_stacks.get(&root) {
            local.extend(sublayers.iter().map(|&(index, _)| index));
        }
        local
    }

    /// Resolves an attribute's value at `time`, honoring value clips
    /// (spec 12.3.4). Strength ordering:
    ///
    /// 1. Local (`Root` arc) `timeSamples` win over clips.
    /// 2. Value clips anchored on the attribute's prim or an ancestor.
    /// 3. The strongest remaining `timeSamples` (across reference/payload arcs).
    /// 4. The strongest authored `default`.
    ///
    /// `interp` applies the stage's interpolation policy to a sample map at a
    /// given time; it is supplied by the caller so this layer stays free of any
    /// interpolation policy.
    pub(crate) fn value_at(
        &mut self,
        attr_path: &Path,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        let attr_path = &self.effective_path(attr_path)?;
        if !self.has_spec_at(attr_path)? {
            return Ok(None);
        }

        let prim = attr_path.prim_path();
        let suffix = attr_path.property_suffix().to_owned();
        let local_layers = self.local_layers();

        self.ensure_index(&prim)?;

        // 1) Local time samples take precedence over clip data.
        if let Some(samples) =
            self.indices[&prim].resolve_local_time_samples(&self.stack, Some(&suffix), &local_layers)?
        {
            return Ok(interp(&samples, time));
        }

        // 2) Local defaults also take precedence over clip data.
        if let FieldValue::Authored(value) =
            self.resolve_local_field_value(&prim, &suffix, FieldKey::Default.as_str(), &local_layers)?
        {
            return Ok(value);
        }

        // 3) Value clips, anchored on this prim or an ancestor. A clip set that
        //    owns the attribute resolves it authoritatively: an authored value
        //    block stops fall-through to weaker sources but presents as `None`,
        //    matching the local-default handling above and the default below.
        if let Some(value) = self.resolve_clip_value(&prim, &suffix, time, interp)? {
            return Ok(block_to_none(value));
        }

        // 4) Remaining time samples (reference/payload arcs), retimed.
        if let Some(samples) = self.indices[&prim].resolve_time_samples(&self.stack, Some(&suffix))? {
            return Ok(interp(&samples, time));
        }

        // 5) Fall back to the strongest authored default.
        let default = self.indices[&prim].resolve_field(FieldKey::Default.as_str(), &self.stack, Some(&suffix))?;
        Ok(default.and_then(block_to_none))
    }

    fn resolve_local_field_value(
        &self,
        prim: &Path,
        suffix: &str,
        field: &str,
        local_layers: &HashSet<usize>,
    ) -> Result<FieldValue> {
        let Some(index) = self.indices.get(prim) else {
            return Ok(FieldValue::NotAuthored);
        };

        for node in index.nodes() {
            let query_path = Path::new(&format!("{}{suffix}", node.path))?;
            for (layer, _) in node.layers() {
                if !local_layers.contains(&layer) {
                    continue;
                }
                let Some(value) = self.stack.layer(layer).try_get(&query_path, field)? else {
                    continue;
                };
                return Ok(FieldValue::Authored(block_to_none(value.into_owned())));
            }
        }

        Ok(FieldValue::NotAuthored)
    }

    /// Resolves a clip value for `attr_path` at `time` by searching the
    /// attribute's prim and then its ancestors, nearest first — a nearer clip
    /// set overrides one on an ancestor (spec 12.3.4.5).
    fn resolve_clip_value(
        &mut self,
        attr_prim: &Path,
        suffix: &str,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        let mut anchor_prim = attr_prim.clone();
        loop {
            if let Some(value) = self.clip_value_at(&anchor_prim, attr_prim, suffix, time, interp)? {
                return Ok(Some(value));
            }
            match anchor_prim.parent() {
                Some(parent) if !parent.is_abs_root() => anchor_prim = parent,
                _ => return Ok(None),
            }
        }
    }

    /// Looks for a clip set anchored on `anchor_prim` that provides a value for
    /// the attribute `attr_prim + suffix` at `time`. Returns the interpolated
    /// clip value, or `None` when no applicable clip set is found.
    fn clip_value_at(
        &mut self,
        anchor_prim: &Path,
        attr_prim: &Path,
        suffix: &str,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        // Gather the clip sets, then drop the index borrow so
        // clip layers can be loaded through `&mut self`.
        let sets = {
            self.ensure_index(anchor_prim)?;
            let index = &self.indices[anchor_prim];
            let sets = index.resolve_clip_sets(&self.stack)?;
            if sets.is_empty() {
                return Ok(None);
            }
            sets
        };

        // Path of the attribute relative to the clip anchor prim (empty when
        // the clip set is authored on the attribute's own prim).
        let relative = &attr_prim.as_str()[anchor_prim.as_str().len()..];

        for resolved in &sets {
            let set = &resolved.set;
            let base = set.prim_path.clone().unwrap_or_else(|| anchor_prim.clone());
            let clip_path = Path::new(&format!("{base}{relative}{suffix}"))?;

            // Resolve the manifest once: its declaration gates the set and its
            // default later fills a gap (spec 12.3.4.6).
            let manifest = set
                .manifest_asset
                .as_deref()
                .map(|asset| (asset, resolved.manifest_layer.unwrap_or(resolved.asset_layer)));

            // A manifest, when authored, declares which attributes the clips
            // provide. A set whose manifest does not declare this attribute is
            // skipped. A set that *does* declare it owns the attribute's
            // time-varying value (spec 12.3.4.6): a gap in the active clip
            // resolves to a manifest default or a value block, never to a
            // weaker value source.
            let manifest_declared = match manifest {
                Some((asset, layer)) => {
                    let declared = match self.clip_layer(asset, layer)? {
                        Some(opened) => opened.data().has_spec(&clip_path),
                        None => false,
                    };
                    if !declared {
                        continue;
                    }
                    true
                }
                None => false,
            };

            let Some(active) = set.active_clip(time) else {
                continue;
            };
            let Some(asset) = set.asset_paths.get(active) else {
                continue;
            };
            let clip_time = set.map_stage_to_clip(time);

            if let Some(value) = self.clip_sample_at(asset, resolved.asset_layer, &clip_path, clip_time, interp)? {
                return Ok(Some(value));
            }

            // The active clip has no sample at `clip_time`. Only a
            // manifest-declared attribute gets the gap-filling treatment;
            // without a manifest there is no assurance this set owns the
            // attribute, so fall through to weaker value sources.
            if !manifest_declared {
                continue;
            }

            // (a) Manifest default: synthesize a sample at the clip's active
            //     time (spec 12.3.4.6). Reached only when the manifest declared
            //     the attribute, so the manifest asset is authored.
            if let Some((asset, layer)) = manifest {
                if let Some(value) = self.manifest_default(asset, layer, &clip_path)? {
                    return Ok(Some(value));
                }
            }

            // (b) interpolateMissingClipValues: interpolate the gap across the
            //     nearest surrounding clips (spec 12.3.4.7).
            if set.interpolate_missing {
                if let Some(value) = self.interpolate_missing_value(resolved, &clip_path, time, interp)? {
                    return Ok(Some(value));
                }
            }

            // (c) No default and nothing to interpolate: the manifest-declared
            //     attribute is authoritatively absent — a value block — which
            //     must not fall through to weaker sources (spec 12.3.4.6).
            return Ok(Some(Value::ValueBlock));
        }

        Ok(None)
    }

    /// Reads the time samples for `clip_path` from a single clip layer and
    /// interpolates at `clip_time`. Returns `None` when the layer is
    /// unresolved or the attribute has no time samples there.
    fn clip_sample_at(
        &mut self,
        asset: &str,
        anchor_layer: usize,
        clip_path: &Path,
        clip_time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        let samples = match self.clip_layer(asset, anchor_layer)? {
            Some(layer) => match layer.data().try_get(clip_path, FieldKey::TimeSamples.as_str())? {
                Some(value) => match value.into_owned() {
                    Value::TimeSamples(samples) => Some(samples),
                    _ => None,
                },
                None => None,
            },
            None => None,
        };
        Ok(samples.and_then(|samples| interp(&samples, clip_time)))
    }

    /// Reads the manifest's authored `default` for `clip_path` (spec 12.3.4.6):
    /// when the active clip has a gap, the manifest default stands in as the
    /// sample value. Returns `None` when the manifest is unresolved or holds no
    /// usable default for the attribute.
    fn manifest_default(&mut self, manifest: &str, manifest_layer: usize, clip_path: &Path) -> Result<Option<Value>> {
        let value = match self.clip_layer(manifest, manifest_layer)? {
            Some(layer) => layer
                .data()
                .try_get(clip_path, FieldKey::Default.as_str())?
                .map(|value| value.into_owned()),
            None => None,
        };
        Ok(value.and_then(block_to_none))
    }

    /// Fills a gap in the active clip by interpolating across the nearest
    /// surrounding clips that contribute a value (spec 12.3.4.7). Each
    /// contributing clip is anchored on the stage timeline at the active stage
    /// time it owns and valued by its sample there; `interp` then brackets
    /// `time` between the nearest such anchors, exactly as if the clips' samples
    /// formed one virtual sample map. The forward bracket is the next
    /// contributing clip's start time and the backward bracket the previous
    /// one's, matching the C++ resolver. When only one side contributes, its
    /// value is held across the gap.
    fn interpolate_missing_value(
        &mut self,
        resolved: &ResolvedClipSet,
        clip_path: &Path,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        let set = &resolved.set;
        let anchor = resolved.asset_layer;
        // Position of the active clip among the `active` entries at `time`.
        let active_pos = set.active.iter().rposition(|&(stage, _)| stage <= time).unwrap_or(0);

        // Forward: nearest later clip that contributes, anchored at its start.
        let mut upper = None;
        for &(stage, idx) in set.active.iter().skip(active_pos + 1) {
            if let Some(asset) = set.asset_paths.get(idx) {
                let clip_time = set.map_stage_to_clip(stage);
                if let Some(value) = self.clip_sample_at(asset, anchor, clip_path, clip_time, interp)? {
                    upper = Some((stage, value));
                    break;
                }
            }
        }

        // Backward: nearest earlier clip that contributes, anchored at its start.
        let mut lower = None;
        for &(stage, idx) in set.active[..active_pos].iter().rev() {
            if let Some(asset) = set.asset_paths.get(idx) {
                let clip_time = set.map_stage_to_clip(stage);
                if let Some(value) = self.clip_sample_at(asset, anchor, clip_path, clip_time, interp)? {
                    lower = Some((stage, value));
                    break;
                }
            }
        }

        Ok(match (lower, upper) {
            (Some((lt, lv)), Some((ut, uv))) => interp(&vec![(lt, lv), (ut, uv)], time),
            (Some((_, value)), None) | (None, Some((_, value))) => Some(value),
            (None, None) => None,
        })
    }

    /// Read-only access to the dependency map for change-driven invalidation.
    pub(super) fn dependencies(&self) -> &Dependencies {
        &self.deps
    }

    /// Returns `true` if a composed prim index is currently cached at `path`.
    pub fn is_indexed(&self, path: &Path) -> bool {
        self.indices.contains_key(path)
    }

    /// Number of cached prim indices.
    pub fn indexed_count(&self) -> usize {
        self.indices.len()
    }

    /// Returns the number of session layers at the front of the layer stack.
    pub fn session_layer_count(&self) -> usize {
        self.stack.session_layer_count
    }

    /// Returns the number of layers in the stage.
    pub fn layer_count(&self) -> usize {
        self.stack.len()
    }

    /// Returns the layer identifiers in strength order (root first).
    pub fn layer_identifiers(&self) -> Vec<String> {
        self.stack.layers.iter().map(|l| l.identifier.clone()).collect()
    }

    /// Returns the identifier for the layer at `index` without cloning the
    /// whole identifier list. Returns `None` if the index is out of range.
    pub fn layer_identifier(&self, index: usize) -> Option<&str> {
        self.stack.layers.get(index).map(|l| l.identifier.as_str())
    }

    /// Mutable access to the layer at `index` for routed authoring writes.
    /// Returns `None` if out of range. Callers route invalidation through
    /// [`change::Changes::apply`](super::change::Changes::apply) instead of
    /// dropping the whole cache.
    pub(crate) fn layer_mut(&mut self, index: usize) -> Option<&mut sdf::Layer> {
        self.stack.layer_mut(index)
    }

    /// Drop a single prim's cached index, context, and dependency entries.
    pub(super) fn drop_index(&mut self, path: &Path) {
        self.indices.remove(path);
        self.contexts.remove(path);
        self.deps.remove(path);
    }

    /// Drop a prim's cached index and every namespace descendant. Used by
    /// [`change::Changes`](super::change::Changes) when a significant change
    /// touches `prefix` — the topology may have changed for the entire
    /// subtree, so every dependent index is invalidated.
    ///
    /// Uses `HashMap::retain` so the prefix scan and removal happen in a
    /// single pass, capturing victims into a small `Vec` only to forward to
    /// the dependency map (which has no `retain` of its own).
    //
    // TODO: replace the `has_prefix` scan with an `SdfPathTable`-like trie
    // (`FindSubtreeRange` in C++). The current shape is O(n) per
    // invalidation, fine while index counts are modest but the wrong
    // long-term primitive.
    pub(super) fn drop_index_subtree(&mut self, prefix: &Path) {
        // `Path::has_prefix("")` returns `true` for every absolute path, so
        // a default-constructed `Path` would silently wipe the entire
        // cache without any layer-stack rebuild — almost certainly a
        // caller bug. Catch it loudly in debug builds; the absolute root
        // (`/`) is the legitimate "blow everything" prefix.
        debug_assert!(
            !prefix.is_empty(),
            "drop_index_subtree called with empty prefix — use Path::abs_root() to drop everything",
        );
        let mut victims: Vec<Path> = Vec::new();
        self.indices.retain(|p, _| {
            if p.has_prefix(prefix) {
                victims.push(p.clone());
                false
            } else {
                true
            }
        });
        for v in &victims {
            self.contexts.remove(v);
            self.deps.remove(v);
        }
    }

    /// Drop every cached index, context, and dependency entry without
    /// touching the layer stack's precomputed state. Use this when the
    /// layer-stack tier has not been touched but every cached prim must
    /// be re-evaluated.
    pub(super) fn clear_all_indices(&mut self) {
        self.indices.clear();
        self.contexts.clear();
        self.deps.clear();
    }

    /// Clears the shared-prototype registry (spec 11.3.3) so stale
    /// instance-to-prototype mappings do not survive a composition change.
    /// The registry is rebuilt lazily on the next instancing query.
    ///
    /// TODO: this drops the whole registry on any invalidation; a targeted
    /// invalidation that removes only the prototypes whose instances changed
    /// would avoid recomputing unaffected keys.
    pub(super) fn invalidate_prototypes(&mut self) {
        self.prototypes.clear();
        self.prototype_keys.clear();
        // `prototype_count` stays monotonic so a `/__Prototype_N` identity is
        // never reused for a different composition within a session.
    }

    /// Recompute `LayerStack::sublayer_stacks` and `layer_offsets` from the
    /// current layer data. Called from
    /// [`change::Changes::apply`](super::change::Changes::apply) when a
    /// sublayer add/remove or sublayer-offset edit lands.
    pub(super) fn recompute_layer_stack(&mut self) {
        self.stack.calc_precomputed();
    }

    /// Recompute the cached `Relocates` from the current layer data. Called
    /// when `layerRelocates` opinions or the layer stack itself change.
    pub(super) fn recompute_relocates(&mut self) {
        self.relocates = Relocates::new(&self.stack.layers);
    }

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    pub fn has_spec(&mut self, path: &Path) -> Result<bool> {
        let path = &self.effective_path(path)?;
        self.has_spec_at(path)
    }

    /// Resolves a value over the composition nodes of a property's owning prim,
    /// strongest first, reading each contributing layer live. `path` must be a
    /// property path: it is re-anchored onto each node's prim (crossing the
    /// `.` separator) and `probe` is called with that node's layer and the
    /// re-anchored property path; the first `Some` wins.
    ///
    /// Reading live — rather than from a property-keyed index — keeps results
    /// correct after a property spec is authored, since authoring a property
    /// never reshapes the owning prim's composition graph (the prim index
    /// stays valid).
    fn find_property_node<T>(
        &mut self,
        path: &Path,
        mut probe: impl FnMut(&sdf::Layer, &Path) -> Option<T>,
    ) -> Result<Option<T>> {
        let prim_path = path.prim_path();
        self.ensure_index(&prim_path)?;
        let Some(index) = self.indices.get(&prim_path) else {
            return Ok(None);
        };
        for node in index.nodes() {
            let Some(prop_path) = path.replace_prefix(&prim_path, &node.path) else {
                continue;
            };
            for (layer, _) in node.layers() {
                if let Some(found) = probe(self.stack.layer(layer), &prop_path) {
                    return Ok(Some(found));
                }
            }
        }
        Ok(None)
    }

    /// Like [`Self::has_spec`], but assumes `path` has already been redirected
    /// through [`Self::effective_path`]. Callers that redirected the path
    /// themselves (e.g. [`Self::value_at`]) use this to avoid redirecting twice.
    fn has_spec_at(&mut self, path: &Path) -> Result<bool> {
        if path.is_property_path() {
            return Ok(self
                .find_property_node(path, |layer, p| layer.has_spec(p).then_some(()))?
                .is_some());
        }
        self.ensure_index(path)?;
        Ok(self.indices.get(path).is_some_and(|idx| !idx.is_empty()))
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    ///
    /// For a property path the type is read live from the owning prim's
    /// composition nodes (see [`Self::find_property_node`]) rather than from a
    /// property-keyed index, so a property spec added after this path was first
    /// queried is picked up instead of a stale cached `None`.
    pub fn spec_type(&mut self, path: &Path) -> Result<Option<SpecType>> {
        let path = &self.effective_path(path)?;
        if path.is_property_path() {
            return self.find_property_node(path, |layer, p| layer.spec_type(p));
        }
        self.ensure_index(path)?;
        let Some(index) = self.indices.get(path) else {
            return Ok(None);
        };
        for node in index.nodes() {
            for (layer, _) in node.layers() {
                if let Some(ty) = self.stack.layer(layer).spec_type(&node.path) {
                    return Ok(Some(ty));
                }
            }
        }
        Ok(None)
    }

    /// Returns `true` if the layer at `layer` authors `field` at `path`. Used
    /// by change classification to detect, for an inert spec add, whether the
    /// new spec carries a field (e.g. `instanceable`) that reshapes
    /// composition.
    pub(super) fn layer_authors_field(&self, layer: usize, path: &Path, field: &str) -> bool {
        self.stack
            .layers
            .get(layer)
            .is_some_and(|l| l.data().has_field(path, field))
    }

    /// Returns `true` if the composed prim index contains any non-local arc.
    pub(crate) fn has_composition_arc(&mut self, path: &Path) -> Result<bool> {
        self.ensure_index(path)?;
        Ok(self.indices.get(path).is_some_and(|index| index.has_composition_arc()))
    }

    /// Returns `true` if `path` resolves as an instance prim (spec 11.3.3):
    /// the strongest `instanceable` opinion is `true` and the prim has at
    /// least one composition arc. Reads the index directly (not through
    /// [`Self::resolve_field`]) so it is safe to call from path redirection.
    pub(crate) fn is_instance(&mut self, path: &Path) -> Result<bool> {
        if path.is_abs_root() {
            return Ok(false);
        }
        self.ensure_index(path)?;
        let index = &self.indices[path];
        if !index.has_composition_arc() {
            return Ok(false);
        }
        Ok(matches!(
            index.resolve_field(FieldKey::Instanceable.as_str(), &self.stack, None)?,
            Some(Value::Bool(true))
        ))
    }

    /// `true` for a node that is a local opinion — authored directly in the
    /// root layer stack (`Root` arc), as opposed to brought in by a
    /// composition arc. These are discarded on instance subtrees (spec
    /// 11.3.3). The `local` set is [`Self::local_layers`].
    fn is_local_opinion(node: &Node, local: &HashSet<usize>) -> bool {
        node.arc == ArcType::Root && local.contains(&node.layer_index())
    }

    /// Computes the instancing key for an already-built instance index: the
    /// arc-introduced (non-local) opinions that define the shared subtree,
    /// independent of the instance's own stage path (spec 11.3.3).
    ///
    /// TODO: variant selections are captured only implicitly via variant
    /// nodes' paths; fold the resolved selection set in explicitly if a case
    /// surfaces where that is insufficient.
    fn instance_key(&self, index: &PrimIndex, local: &HashSet<usize>) -> InstanceKey {
        let arcs = index
            .nodes()
            .filter(|node| !Self::is_local_opinion(node, local))
            .map(|node| {
                let offset = node.map_to_root.time_offset();
                InstanceArc {
                    arc: node.arc as u8,
                    layer: self.stack.identifier(node.layer_index()).to_string(),
                    path: node.path.to_string(),
                    offset_bits: offset.offset.to_bits(),
                    scale_bits: offset.scale.to_bits(),
                }
            })
            .collect();
        InstanceKey(arcs)
    }

    /// Returns the canonical instance whose composed subtree is shared by
    /// every instance with `instance`'s instancing key. The first instance
    /// registered for a key becomes canonical; later instances with the same
    /// key reuse its subtree, so it is composed only once (spec 11.3.3).
    //
    // TODO(rayon): distinct prototypes (distinct instancing keys) compose
    // independent subtrees, so the canonical instances can be composed in
    // parallel. `IndexBuilder` already takes only `&` references; this needs
    // the cache to build indices off the `&mut self` path first (e.g. compose
    // into per-prototype results, then insert), and the shared `LayerStack`
    // handed to workers as `&`/`Arc`.
    fn canonical_instance(&mut self, instance: &Path) -> Result<Path> {
        Ok(self.register_prototype(instance)?.0)
    }

    /// Registers `instance` against its prototype, minting `/__Prototype_N` and
    /// recording the instance the first time a key is seen. Returns the
    /// `(canonical instance, prototype path)` pair.
    fn register_prototype(&mut self, instance: &Path) -> Result<(Path, Path)> {
        self.ensure_index(instance)?;
        let local = self.local_layers();
        let key = self.instance_key(&self.indices[instance], &local);

        if let Some(root) = self.prototype_keys.get(&key) {
            let root = root.clone();
            let prototype = self.prototypes.get_mut(&root).expect("key index points to a prototype");
            if !prototype.instances.contains(instance) {
                prototype.instances.push(instance.clone());
            }
            return Ok((prototype.canonical.clone(), root));
        }

        let index = self.prototype_count;
        let path = Path::new(&format!("/__Prototype_{index}"))?;
        self.prototype_count += 1;
        self.prototype_keys.insert(key, path.clone());
        self.prototypes.insert(
            path.clone(),
            Prototype {
                index,
                canonical: instance.clone(),
                instances: vec![instance.clone()],
            },
        );
        Ok((instance.clone(), path))
    }

    /// Returns the synthetic prototype path (`/__Prototype_N`) shared by
    /// `instance`, registering it on first use. `None` when `instance` is not
    /// an instance prim (spec 11.3.3).
    pub(crate) fn prototype_of(&mut self, instance: &Path) -> Result<Option<Path>> {
        if !self.is_instance(instance)? {
            return Ok(None);
        }
        Ok(Some(self.register_prototype(instance)?.1))
    }

    /// Returns the instances sharing the prototype at `prototype` (a
    /// `/__Prototype_N` path), sorted by namespace path so the result does not
    /// depend on the order instances were queried. Empty for unknown paths.
    pub(crate) fn instances_of(&self, prototype: &Path) -> Vec<Path> {
        let mut instances = self
            .prototypes
            .get(prototype)
            .map(|prototype| prototype.instances.clone())
            .unwrap_or_default();
        instances.sort();
        instances
    }

    /// Returns the registered `/__Prototype_N` roots, in registration order.
    pub(crate) fn prototypes(&self) -> Vec<Path> {
        let mut roots: Vec<(&Path, &Prototype)> = self.prototypes.iter().collect();
        roots.sort_by_key(|(_, prototype)| prototype.index);
        roots.into_iter().map(|(root, _)| root.clone()).collect()
    }

    /// Returns `true` if `path` is a `/__Prototype_N` root.
    pub(crate) fn is_prototype(&self, path: &Path) -> bool {
        self.prototypes.contains_key(path)
    }

    /// Returns `true` if `path` lies within a prototype's namespace — i.e. it
    /// has a `/__Prototype_N` ancestor (spec 11.3.3).
    pub(crate) fn is_in_prototype(&self, path: &Path) -> bool {
        self.enclosing_prototype_root(path.parent()).is_some()
    }

    /// Walks the chain from `start` toward the root and returns the nearest
    /// `/__Prototype_N` root on it, or `None`. Passing the queried prim starts
    /// the walk inclusively; passing its parent excludes the prim itself.
    fn enclosing_prototype_root(&self, start: Option<Path>) -> Option<Path> {
        let mut node = start;
        while let Some(current) = node {
            if self.prototypes.contains_key(&current) {
                return Some(current);
            }
            node = current.parent();
        }
        None
    }

    /// Maps a prim path to the path that actually composes it. A descendant of
    /// a non-canonical instance is redirected into the canonical instance's
    /// subtree, so identical instances share one composition (spec 11.3.3).
    /// Other paths pass through unchanged.
    ///
    /// Nested instances work without special handling: the walk redirects to
    /// the nearest enclosing instance, so a nested instance resolves to its own
    /// shared prototype.
    fn redirect_prim(&mut self, prim: &Path) -> Result<Path> {
        match self.redirect_anchor(prim)? {
            Some((origin, canonical)) => Ok(prim.replace_prefix(&origin, &canonical).unwrap_or_else(|| prim.clone())),
            None => Ok(prim.clone()),
        }
    }

    /// If `prim` lies within a shared prototype's namespace, returns the
    /// `(origin, canonical)` prefixes that map between the queried namespace
    /// and the composed one: a `/__Prototype_N` root or a non-canonical
    /// instance prim (`origin`) and the canonical instance backing it
    /// (`canonical`). Returns `None` when `prim` composes in place.
    fn redirect_anchor(&mut self, prim: &Path) -> Result<Option<(Path, Path)>> {
        // A `/__Prototype_N[/tail]` query maps into the canonical instance's
        // subtree, so the synthetic prototype namespace is addressable.
        if let Some(root) = self.enclosing_prototype_root(Some(prim.clone())) {
            let canonical = self.prototypes[&root].canonical.clone();
            return Ok(Some((root, canonical)));
        }

        let mut ancestor = prim.parent();
        while let Some(current) = ancestor {
            if current.is_abs_root() {
                break;
            }
            if self.is_instance(&current)? {
                let canonical = self.canonical_instance(&current)?;
                if canonical != current {
                    return Ok(Some((current, canonical)));
                }
                // Nearest instance is canonical: compose this subtree in place.
                break;
            }
            ancestor = current.parent();
        }
        Ok(None)
    }

    /// Redirects `path` (prim or property) through [`Self::redirect_prim`],
    /// preserving any property suffix. Applied at every descendant-serving
    /// query entry point so non-canonical instance subtrees are never built.
    //
    // TODO(perf): every call walks the path's ancestors to find an enclosing
    // instance. The result is stable until the prototype registry is
    // invalidated, so it could be memoized per prim path and cleared alongside
    // `invalidate_prototypes`.
    fn effective_path(&mut self, path: &Path) -> Result<Path> {
        let prim = path.prim_path();
        let redirected = self.redirect_prim(&prim)?;
        if redirected == prim {
            return Ok(path.clone());
        }
        // Re-anchor any property suffix onto the redirected prim; for a prim
        // path this is the redirected prim itself.
        Ok(path.replace_prefix(&prim, &redirected).unwrap_or(redirected))
    }

    /// Resolves a field value from the strongest opinion across all composition nodes.
    ///
    /// Layer metadata authored on the pseudo-root is resolved directly from
    /// the root layer and does not compose with sublayers or arcs. The
    /// pseudo-root's `primChildren` field remains a child-list query and is
    /// handled by normal composition.
    pub fn resolve_field(&mut self, path: &Path, field: &str) -> Result<Option<Value>> {
        let path = &self.effective_path(path)?;
        if path.is_abs_root() && field != ChildrenKey::PrimChildren.as_str() {
            return self.root_layer_field(field);
        }

        if path.is_property_path() {
            let prim_path = path.prim_path();
            let prop_suffix = path.property_suffix();
            self.ensure_index(&prim_path)?;
            self.indices[&prim_path].resolve_field(field, &self.stack, Some(prop_suffix))
        } else {
            self.ensure_index(path)?;
            self.indices[path].resolve_field(field, &self.stack, None)
        }
    }

    /// Returns the composed `apiSchemas` list for a prim.
    pub fn api_schemas(&mut self, path: &Path) -> Result<Vec<String>> {
        let path = self.effective_path(&path.prim_path())?;
        self.ensure_index(&path)?;
        self.indices[&path].resolve_token_list_op(FieldKey::ApiSchemas, &self.stack, None)
    }

    /// Returns the composed `connectionPaths` list for an attribute path,
    /// folding list-op edits (prepend / append / add / delete) across every
    /// contributing layer. Non-property paths trivially return an empty list.
    pub fn connection_paths(&mut self, path: &Path) -> Result<Vec<Path>> {
        self.property_targets(path, FieldKey::ConnectionPaths)
    }

    /// Returns the composed raw `targetPaths` list for a relationship path,
    /// folding list-op edits (prepend / append / add / delete) across every
    /// contributing layer. Non-property paths trivially return an empty list.
    ///
    /// These are the raw targets (the resolved `targetPaths` list op, spec
    /// 12.4); target forwarding — recursively chasing relationship-to-
    /// relationship chains — is not applied here.
    pub fn relationship_targets(&mut self, path: &Path) -> Result<Vec<Path>> {
        self.property_targets(path, FieldKey::TargetPaths)
    }

    /// Returns the forwarded `targetPaths` for a relationship (spec 12.4):
    /// a target that resolves to a relationship is replaced, recursively, by
    /// that relationship's own forwarded targets. Every other target is kept
    /// as-is — prim paths, attribute paths, and any target that does not
    /// resolve to a relationship (a dangling or unloaded path). This matches
    /// C++ `UsdRelationship::GetForwardedTargets`, which forwards only through
    /// live relationships. Cycles are broken (each relationship is followed
    /// once) and duplicates collapse, keeping first occurrence.
    ///
    /// The walk uses an explicit stack rather than recursion (mirroring
    /// [`crate::usd::ConnectionGraph::resolve_chain`]) so a deep relationship
    /// chain cannot overflow the call stack.
    ///
    /// `is_populated` reports whether a prim is inside the stage's working set.
    /// A target relationship on a prim outside the set is not followed — its
    /// raw targets would be empty under the population mask anyway — so the
    /// forwarded result never leaks scene the mask excludes (it stays
    /// consistent with [`Self::relationship_targets`] on that path).
    pub fn forwarded_relationship_targets(
        &mut self,
        path: &Path,
        is_populated: &dyn Fn(&Path) -> bool,
    ) -> Result<Vec<Path>> {
        let mut out = Vec::new();
        let mut emitted = HashSet::new();
        let mut followed = HashSet::new();
        followed.insert(path.clone());

        // Seed with the queried relationship's raw targets. Targets are pushed
        // reversed so the strongest (first) target is popped and resolved
        // first, preserving authored order in `out`.
        let mut stack: Vec<Path> = self.relationship_targets(path)?.into_iter().rev().collect();
        while let Some(target) = stack.pop() {
            // Only property targets can be relationships; a prim-path target is
            // always terminal. Classify property targets by composed spec type.
            let is_relationship =
                target.is_property_path() && matches!(self.spec_type(&target)?, Some(SpecType::Relationship));
            if is_relationship {
                // Don't follow a relationship the mask excludes; a masked-out
                // prim contributes no composed targets.
                if !is_populated(&target.prim_path()) {
                    continue;
                }
                if !followed.insert(target.clone()) {
                    continue; // already followed — break the cycle
                }
                stack.extend(self.relationship_targets(&target)?.into_iter().rev());
            } else if emitted.insert(target.clone()) {
                out.push(target);
            }
        }
        Ok(out)
    }

    /// Composes a path-list-op property field (`connectionPaths` or
    /// `targetPaths`) by folding list-op edits across every contributing layer
    /// and mapping targets through composition arcs into the stage namespace.
    /// Both fields follow generic list-op value resolution (spec 12.2.6).
    fn property_targets(&mut self, path: &Path, field: FieldKey) -> Result<Vec<Path>> {
        if !path.is_property_path() {
            return Ok(Vec::new());
        }
        let prim = path.prim_path();
        let prop_suffix = path.property_suffix().to_owned();
        let anchor = self.redirect_anchor(&prim)?;

        // Resolve against the canonical instance's subtree when shared.
        let resolved_prim = match &anchor {
            Some((origin, canonical)) => prim.replace_prefix(origin, canonical).unwrap_or_else(|| prim.clone()),
            None => prim,
        };
        self.ensure_index(&resolved_prim)?;
        let mut targets = self.indices[&resolved_prim].resolve_path_list_op(field, &self.stack, Some(&prop_suffix))?;

        // Targets that land inside the prototype resolve into the canonical
        // instance's namespace; map them back to the queried instance (spec
        // 11.3.4 connections / relationship targets under spec 11.3.3
        // instancing).
        if let Some((origin, canonical)) = &anchor {
            for target in &mut targets {
                if let Some(remapped) = target.replace_prefix(canonical, origin) {
                    *target = remapped;
                }
            }
        }
        Ok(targets)
    }

    /// Returns pseudo-root stage metadata, composing session-layer opinions
    /// over the root layer (strongest first).
    ///
    /// Unlike [`Self::root_layer_field`] — which is root-layer-only for the
    /// spec 12.2.7 fields such as `defaultPrim` — general stage metadata
    /// (e.g. `renderSettingsPrimPath`) honors a session-layer override,
    /// matching C++ `UsdStage::GetMetadata`. A [`Value::ValueBlock`] in a
    /// stronger layer blocks weaker opinions.
    pub fn stage_metadata(&self, field: &str) -> Result<Option<Value>> {
        let root = Path::abs_root();
        // Slots `0..session_layer_count` hold the session layers; the root
        // layer sits at `session_layer_count`. Walk session-then-root so the
        // session opinion wins.
        for index in 0..=self.stack.session_layer_count {
            let Some(layer) = self.stack.layers.get(index) else {
                break;
            };
            match layer.try_get(&root, field)? {
                Some(value) if matches!(value.as_ref(), Value::ValueBlock) => return Ok(None),
                Some(value) => return Ok(Some(value.into_owned())),
                None => {}
            }
        }
        Ok(None)
    }

    /// Returns pseudo-root layer metadata from the root layer only.
    ///
    /// Session-layer and sublayer opinions are intentionally ignored here,
    /// matching spec 12.2.7.
    fn root_layer_field(&self, field: &str) -> Result<Option<Value>> {
        let root = Path::abs_root();
        let Some(root_layer) = self.stack.root_layer() else {
            return Ok(None);
        };
        let Some(value) = root_layer.try_get(&root, field)? else {
            return Ok(None);
        };
        if matches!(value.as_ref(), Value::ValueBlock) {
            return Ok(None);
        }
        Ok(Some(value.into_owned()))
    }

    /// Returns the composed list of child names for a prim path.
    ///
    /// Merges the children field across all composition nodes, returning the
    /// union with strongest-first ordering. When relocates are present,
    /// source children are hidden and target children are added. Finally,
    /// the strongest opinion of `primOrder` (if any) is applied to the
    /// resulting list (see [`sdf::apply_ordering`]).
    ///
    /// Composition note: the strongest `primOrder` opinion wins outright,
    /// matching how single-valued fields like `defaultPrim` compose. C++
    /// `Pcp` instead folds each layer's order onto the running union as
    /// nodes merge weakest-to-strongest, which can yield different results
    /// when multiple sublayers contribute partial orderings.
    pub fn prim_children(&mut self, path: &Path) -> Result<Vec<String>> {
        let path = &self.effective_path(path)?;
        let mut children = self.composed_children(path, ChildrenKey::PrimChildren)?;

        if !self.relocates.is_empty() {
            self.apply_relocates_to_children(path, &mut children);
        }

        self.apply_order_field(path, FieldKey::PrimOrder, &mut children)?;
        Ok(children)
    }

    /// Returns the composed list of property names for a prim path.
    ///
    /// Applies the strongest `propertyOrder` opinion to the unioned property
    /// list. See [`Cache::prim_children`] for the composition-rule caveat.
    pub fn prim_properties(&mut self, path: &Path) -> Result<Vec<String>> {
        let path = &self.effective_path(path)?;
        let mut properties = self.composed_children(path, ChildrenKey::PropertyChildren)?;
        self.apply_order_field(path, FieldKey::PropertyOrder, &mut properties)?;
        Ok(properties)
    }

    /// Apply the strongest opinion of `field` (a `TokenVec`) as a child-list
    /// ordering. The index for `path` must already be cached.
    fn apply_order_field(&self, path: &Path, field: FieldKey, items: &mut [String]) -> Result<()> {
        if let Some(Value::TokenVec(order)) = self.indices[path].resolve_field(field.as_str(), &self.stack, None)? {
            sdf::apply_ordering(items, &order);
        }
        Ok(())
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    ///
    /// When session layers are present, `defaultPrim` is read from the
    /// first non-session layer (the root layer), matching C++ behavior.
    pub fn default_prim(&self) -> Option<String> {
        let root = Path::abs_root();
        let value = self
            .stack
            .root_layer()?
            .get(&root, FieldKey::DefaultPrim.as_str())
            .ok()?;
        match value.into_owned() {
            Value::Token(s) | Value::String(s) => Some(s),
            _ => None,
        }
    }

    /// Collects ancestor arcs from all cached ancestors of `path`.
    ///
    /// Returns references into the cached contexts, avoiding allocation
    /// of `AncestorArc` (which contains `MapFunction` with a `Vec`).
    fn collect_ancestor_arcs(&self, path: &Path) -> Vec<&AncestorArc> {
        let mut arcs = Vec::new();
        let mut p = Some(path.clone());
        while let Some(pp) = p {
            if let Some(ctx) = self.contexts.get(&pp) {
                arcs.extend(&ctx.ancestor_arcs);
            }
            p = pp.parent();
        }
        arcs
    }

    /// Pre-caches inherit/specialize targets declared in the prim's layer
    /// data. Reads inherit paths from each layer, resolves them to composed
    /// namespace using ancestor arcs, and ensures those targets are cached.
    fn precache_inherit_targets(&mut self, path: &Path) {
        let Some(parent) = path.parent() else {
            return;
        };
        let Some(parent_index) = self.indices.get(&parent) else {
            return;
        };

        let ancestor_arcs = self.collect_ancestor_arcs(&parent);

        // Scan each parent composition node for inherit/specialize targets: the
        // parent's own path in that node's namespace, and the prim's path there
        // (the node's path extended by the prim name). A layer that authors the
        // prim directly contributes to the parent at the parent path, so it is
        // already covered here — no separate all-layers scan of the prim path is
        // needed.
        let mut nodes_to_scan: Vec<(Path, usize)> = Vec::new();
        for node in parent_index.nodes() {
            for (layer, _) in node.layers() {
                nodes_to_scan.push((node.path.clone(), layer));
                if let Some(name) = path.name() {
                    if let Ok(child_in_node) = node.path.append_path(name) {
                        nodes_to_scan.push((child_in_node, layer));
                    }
                }
            }
        }

        let mut targets_to_cache = Vec::new();
        for (scan_path, scan_layer) in &nodes_to_scan {
            for field in [FieldKey::InheritPaths, FieldKey::Specializes] {
                let Ok(val) = self.stack.layer(*scan_layer).get(scan_path, field.as_str()) else {
                    continue;
                };
                let Value::PathListOp(list_op) = val.into_owned() else {
                    continue;
                };
                for target in &list_op.flatten() {
                    // Anchor a relative inherit/specialize target at the path it
                    // is authored on (the scanned node's namespace), matching the
                    // index builder's `path.make_absolute`. Anchoring at the
                    // composed parent would mis-resolve `../` targets by a level.
                    let raw = scan_path.make_absolute(target);
                    // Try composed-namespace versions via ancestor arcs.
                    for a in &ancestor_arcs {
                        if let Some(composed) = a.map.map_source_to_target(&raw) {
                            if composed != raw && !targets_to_cache.contains(&composed) {
                                targets_to_cache.push(composed);
                            }
                        }
                    }
                    if !targets_to_cache.contains(&raw) {
                        targets_to_cache.push(raw);
                    }
                }
            }
        }

        for target in targets_to_cache {
            self.precache_path(&target);
            // Recursively precache the target's own inherit targets.
            if self.indices.contains_key(&target) {
                self.precache_inherit_targets(&target);
            }
        }
    }

    // ------------------------------------------------------------------
    // Core composition
    // ------------------------------------------------------------------

    /// Ensures the prim index for `path` is built and cached.
    ///
    /// When LIVRPS composition produces an empty index (no layer has a direct
    /// spec at the composed path), parent composition nodes are checked for
    /// child specs at their respective paths. This handles prims that only
    /// exist through ancestor inherit, specialize, or reference arcs.
    pub(super) fn ensure_index(&mut self, path: &Path) -> Result<()> {
        if self.indices.contains_key(path) {
            return Ok(());
        }

        // Compose ancestors first so the parent's `CompositionContext` (and
        // its `within_instance` flag, spec 11.3.3) is available. Composition
        // is a pure function of the layer stack, path, and parent context, so
        // building ancestors eagerly only fixes the parent context — it does
        // not change any prim's resolved opinions.
        if let Some(parent) = path.parent() {
            if !parent.is_abs_root() && !self.indices.contains_key(&parent) {
                self.precache_path(&parent);
            }
        }

        // Pre-cache inherit/specialize targets so the index builder can
        // find them. This handles the timing issue where a target prim is
        // in a sibling subtree that hasn't been traversed yet.
        self.precache_inherit_targets(path);

        let parent_ctx = path
            .parent()
            .and_then(|p| self.contexts.get(&p))
            .cloned()
            .unwrap_or_else(|| CompositionContext {
                variant_fallbacks: self.variant_fallbacks.clone(),
                ..Default::default()
            });

        // TODO(rayon): `build_with_cache` is a pure function of `&self.stack`,
        // `&parent_ctx`, and `&self.indices`, so sibling prims compose
        // independently and this is the natural per-prim `par_iter` boundary.
        // The blocker is the shared `self.indices` map that inherit/specialize
        // targets read mid-build — parallelizing the driver needs a concurrent
        // map or a topological (targets-first) build order.
        let mut index = match PrimIndex::build_with_cache(path, &self.stack, &parent_ctx, &self.indices) {
            Ok(idx) => idx,
            Err(e) => return Err(e.into()),
        };

        // For relocated prims, merge source path opinions.
        if !self.relocates.is_empty() {
            if let Some(source) = self.relocates.find_source_path(path, &self.stack, &self.indices)? {
                self.precache_path(&source);
            }
            self.relocates
                .add_relocate_nodes(path, &mut index, &self.stack, &self.indices, &self.contexts)?;
        }

        // Inside an instance, local opinions on descendants are discarded
        // (spec 11.3.3): the subtree is composed purely from the arcs the
        // instance brings in. This is enforced at composition time — the index
        // builder skips the local root site for any prim whose parent context
        // is `within_instance`, so the local arcs are never followed — rather
        // than pruned afterwards, which would leave the nodes those local arcs
        // spawned.

        // This prim is an instance when its composition declares
        // `instanceable = true` and carries an arc; its descendants then
        // inherit `within_instance`. A nested instance therefore re-arms the
        // flag for its own subtree. Computed from the freshly built index to
        // avoid re-entering `ensure_index` for `path`.
        let is_instance = index.has_composition_arc()
            && matches!(
                index.resolve_field(FieldKey::Instanceable.as_str(), &self.stack, None)?,
                Some(Value::Bool(true))
            );

        let mut child_context = index.context_for_children(&self.stack, &parent_ctx);
        child_context.within_instance = parent_ctx.within_instance || is_instance;
        self.deps.add(path, &index, self.stack.len());
        self.indices.insert(path.clone(), index);
        self.contexts.insert(path.clone(), child_context);
        Ok(())
    }

    /// Ensures a path and all its ancestors are cached (built on the fly if needed).
    fn precache_path(&mut self, path: &Path) {
        let mut to_build = Vec::new();
        let mut p = Some(path.clone());
        while let Some(pp) = p {
            if pp == Path::abs_root() || self.indices.contains_key(&pp) {
                break;
            }
            to_build.push(pp.clone());
            p = pp.parent();
        }
        for pp in to_build.into_iter().rev() {
            let _ = self.ensure_index(&pp);
        }
    }

    /// Applies relocate namespace remapping to a list of child names.
    ///
    /// Per-node layer relocates are applied first, then effective relocates
    /// remap source children to targets and add cross-hierarchy targets.
    /// Source ancestor chains are pre-cached so their prim indices are
    /// available when building relocated target indices later.
    fn apply_relocates_to_children(&mut self, path: &Path, children: &mut Vec<String>) {
        self.relocates.apply_node_relocates(path, children, &self.indices);

        let effective = self.relocates.effective_relocates(path, &self.indices);
        if !effective.is_empty() {
            for (src, _) in &effective {
                self.precache_path(src);
            }
            Relocates::apply_children_remapping(path, children, &effective);
        }
    }

    /// Merges a children field (the union, strongest-first) across every node
    /// in the prim's composition index.
    ///
    /// The recursive build grafts inherit/specialize/reference targets with
    /// their subtrees, so the index nodes already cover class children; this is
    /// a single structural walk with no separate target rediscovery. On an
    /// instance prim, `primChildren` from local opinions are dropped (spec
    /// 11.3.3) so the children come only from the composition arcs.
    fn composed_children(&mut self, path: &Path, children_field: ChildrenKey) -> Result<Vec<String>> {
        self.ensure_index(path)?;

        // An instance prim's children come only from its composition arcs;
        // local opinions contributing to `primChildren` are discarded (spec
        // 11.3.3). The instance prim's own index is otherwise left intact, so
        // its own properties still see local opinions.
        let drop_local = matches!(children_field, ChildrenKey::PrimChildren) && self.is_instance(path)?;
        let local = if drop_local {
            self.local_layers()
        } else {
            HashSet::new()
        };

        let index = &self.indices[path];
        let mut result: Vec<String> = Vec::new();

        for node in index.nodes() {
            if drop_local && Self::is_local_opinion(node, &local) {
                continue;
            }
            for (layer, _) in node.layers() {
                if let Ok(value) = self.stack.layer(layer).get(&node.path, children_field.as_str()) {
                    if let Value::TokenVec(names) = value.into_owned() {
                        for name in names {
                            if !result.contains(&name) {
                                result.push(name);
                            }
                        }
                    }
                }
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::{DefaultResolver, Resolver};

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    /// Builds a stack with the root and every layer reachable through
    /// references/sublayers collected in, so composition can resolve them
    /// (clip layers are still opened lazily by the cache).
    fn collected_stack(path: &str) -> LayerStack {
        let resolver = DefaultResolver::new();
        let layers = crate::layer::Collector::new(&resolver)
            .collect(path)
            .expect("collect layers");
        LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true)
    }

    /// Builds a one-layer stack whose root is loaded from a real path, so the
    /// resolver can anchor clip asset paths relative to it.
    fn single_layer_stack(path: &str) -> LayerStack {
        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve(path).expect("root resolves");
        let id = resolver.create_identifier(path, None);
        let data = crate::layer::open_layer(&resolver, &resolved).expect("open root");
        LayerStack::new(
            vec![sdf::Layer::new(id, data)],
            0,
            Box::new(DefaultResolver::new()),
            true,
        )
    }

    /// `clip_layer` loads a clip layer relative to the authoring layer, caches
    /// it (clip layers never enter the composition stack), and reports an
    /// unresolvable path as `None`.
    #[test]
    fn loads_and_caches_clip_layer() -> Result<()> {
        let root = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets/clip_basic/usda/root.usda",
            manifest_dir()
        );
        let mut cache = Cache::new(single_layer_stack(&root), VariantFallbackMap::new());

        {
            let clip = cache.clip_layer("./clip.usda", 0)?.expect("clip resolves");
            assert!(clip.identifier.contains("clip.usda"));
            assert!(clip.data().has_spec(&sdf::path("/Model.size")?));
        }

        // Second lookup is a cache hit; a bogus path resolves to None.
        assert!(cache.clip_layer("./clip.usda", 0)?.is_some());
        assert!(cache.clip_layer("./does_not_exist.usda", 0)?.is_none());
        Ok(())
    }

    /// A child reachable only through a chain of local-class inherits composes
    /// its own inherited grandchildren: `SymArmRig` inherits `_Class_ArmRig`
    /// (whose `ArmRegion` over inherits `Body/_class_Region`), so
    /// `SymArmRig/ArmRegion` must expose `Region`.
    #[test]
    fn inherited_child_chain_composes() -> Result<()> {
        let root = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             TrickyLocalClassHierarchyWithRelocates_root/usda/root.usd",
            manifest_dir()
        );
        let mut cache = Cache::new(collected_stack(&root), VariantFallbackMap::new());
        let arm_region = sdf::path("/C_1/ArmsRig/SymArmRig/ArmRegion")?;
        assert!(
            cache.prim_children(&arm_region)?.contains(&"Region".to_string()),
            "deep local-class inherit chain must surface the inherited grandchild"
        );
        Ok(())
    }

    /// A relocated prim's index carries relocate nodes (tagged
    /// `RELOCATE_SOURCE`) whose grafted source subtree forms a consistent
    /// tree: every stored parent link is mirrored by the parent's child list.
    #[test]
    fn relocate_nodes_form_subtree() -> Result<()> {
        use super::super::index::NodeFlags;

        let root = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             BasicRelocateToAnimInterface_root/usda/root.usd",
            manifest_dir()
        );
        let mut cache = Cache::new(collected_stack(&root), VariantFallbackMap::new());
        let path = sdf::path("/Model/Anim/Path")?;
        cache.ensure_index(&path)?;
        let index = &cache.indices[&path];

        assert!(
            index.nodes().any(|n| n.flags().contains(NodeFlags::RELOCATE_SOURCE)),
            "relocated prim has relocate nodes"
        );
        for (id, node) in index.nodes_with_ids() {
            if let Some(parent) = node.parent() {
                assert!(
                    index.children(parent).contains(&id),
                    "relocate node {id:?} parent {parent:?} missing it as a child"
                );
            }
        }
        Ok(())
    }

    /// A relocate source spanning several sublayers keeps every member in the
    /// per-site relocate node — the weaker sublayer opinion must not be lost.
    /// `/World/Src` (authored in both `root.usda` and `sub.usda`) relocates to
    /// `/World/Dst`, whose relocate node must carry both layers.
    #[test]
    fn relocate_source_spans_sublayers() -> Result<()> {
        use super::super::index::NodeFlags;

        let root = format!("{}/fixtures/relocate_multilayer/root.usda", manifest_dir());
        let mut cache = Cache::new(collected_stack(&root), VariantFallbackMap::new());
        let path = sdf::path("/World/Dst")?;
        cache.ensure_index(&path)?;
        let index = &cache.indices[&path];

        let relocate = index
            .nodes()
            .find(|n| n.flags().contains(NodeFlags::RELOCATE_SOURCE))
            .expect("relocated prim has a relocate node");
        let layers: Vec<usize> = relocate.layers().map(|(li, _)| li).collect();
        assert_eq!(
            layers,
            vec![0, 1],
            "relocate node folds both authoring sublayers, strongest first"
        );
        Ok(())
    }

    /// A template clip set (`templateAssetPath` + start/end/stride) is
    /// expanded to explicit clips and resolves end to end through
    /// `value_at` (spec 12.3.4.1.3): `clip.1.usda` drives t=1, `clip.2.usda`
    /// drives t=2.
    #[test]
    fn resolves_template_clip_values() -> Result<()> {
        let root = format!("{}/fixtures/clip_template/root.usda", manifest_dir());
        let mut cache = Cache::new(single_layer_stack(&root), VariantFallbackMap::new());
        // Exact-match sampler: each clip authors a single sample at its frame.
        let interp =
            |samples: &sdf::TimeSampleMap, t: f64| samples.iter().find(|(time, _)| *time == t).map(|(_, v)| v.clone());

        let size = |cache: &mut Cache, t: f64| cache.value_at(&sdf::path("/Model.size").unwrap(), t, &interp);
        assert_eq!(size(&mut cache, 1.0)?, Some(sdf::Value::Double(10.0)));
        assert_eq!(size(&mut cache, 2.0)?, Some(sdf::Value::Double(20.0)));
        Ok(())
    }

    /// A template clip set authored in a sublayer with a layer offset has its
    /// derived schedule retimed into stage time (spec 12.3.4): the offset of 10
    /// shifts `clip.1`'s frame to stage t=11 and `clip.2`'s to t=12.
    #[test]
    fn template_clip_schedule_retimed_by_offset() -> Result<()> {
        let root = format!("{}/fixtures/clip_template_offset/root.usda", manifest_dir());
        let mut cache = Cache::new(collected_stack(&root), VariantFallbackMap::new());
        let size = |cache: &mut Cache, t: f64| cache.value_at(&sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 11.0)?, Some(Value::Double(10.0)));
        assert_eq!(size(&mut cache, 12.0)?, Some(Value::Double(20.0)));
        Ok(())
    }

    /// When a stronger layer authors explicit `assetPaths` and a weaker
    /// sublayer authors `templateAssetPath` for the same set, the explicit
    /// paths win (spec 12.3.4.1.3) and must anchor on the layer that authored
    /// them: `@./clip.usda@` resolves next to the root, not the sublayer.
    #[test]
    fn explicit_asset_paths_anchor_over_template() -> Result<()> {
        let root = format!("{}/fixtures/clip_asset_anchor/root.usda", manifest_dir());
        let mut cache = Cache::new(collected_stack(&root), VariantFallbackMap::new());
        let size = |cache: &mut Cache, t: f64| cache.value_at(&sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(42.0)));
        Ok(())
    }

    /// Exact-match sampler: a clip resolves only at a frame it authors.
    fn exact(samples: &sdf::TimeSampleMap, t: f64) -> Option<Value> {
        samples.iter().find(|(time, _)| *time == t).map(|(_, v)| v.clone())
    }

    /// Linear sampler over `float` samples, held outside the sample range.
    fn lerp(samples: &sdf::TimeSampleMap, t: f64) -> Option<Value> {
        let as_f = |v: &Value| match v {
            Value::Float(f) => *f as f64,
            Value::Double(d) => *d,
            _ => 0.0,
        };
        let first = samples.first()?;
        if t <= first.0 {
            return Some(first.1.clone());
        }
        let last = samples.last()?;
        if t >= last.0 {
            return Some(last.1.clone());
        }
        let w = samples.windows(2).find(|w| t >= w[0].0 && t <= w[1].0)?;
        let f = (t - w[0].0) / (w[1].0 - w[0].0);
        Some(Value::Double(as_f(&w[0].1) + (as_f(&w[1].1) - as_f(&w[0].1)) * f))
    }

    /// A gap in the active clip falls to the manifest's authored default
    /// (spec 12.3.4.6): `t=0` is sampled from the clip, `t=10` (no sample)
    /// resolves to the manifest default `99.0`.
    #[test]
    fn missing_clip_value_uses_manifest_default() -> Result<()> {
        let root = format!("{}/fixtures/clip_missing_default/root.usda", manifest_dir());
        let mut cache = Cache::new(single_layer_stack(&root), VariantFallbackMap::new());
        let size = |cache: &mut Cache, t: f64| cache.value_at(&sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(5.0)));
        assert_eq!(size(&mut cache, 10.0)?, Some(Value::Float(99.0)));
        Ok(())
    }

    /// A manifest-declared attribute with no default and a gap is
    /// authoritatively absent (spec 12.3.4.6): the clip owns the attribute, so
    /// the gap blocks fall-through to the referenced time samples (`777.0`) and
    /// resolves to `None` rather than the weaker value.
    #[test]
    fn missing_clip_value_without_default_blocks() -> Result<()> {
        let root = format!("{}/fixtures/clip_missing_block/root.usda", manifest_dir());
        let mut cache = Cache::new(collected_stack(&root), VariantFallbackMap::new());
        let size = |cache: &mut Cache, t: f64| cache.value_at(&sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(5.0)));
        assert_eq!(size(&mut cache, 10.0)?, None);
        Ok(())
    }

    /// With `interpolateMissingClipValues`, a gap is filled by interpolating
    /// across the surrounding contributing clips (spec 12.3.4.7): the empty
    /// middle clip at `t=15` interpolates `0.0` (t=0 clip) and `100.0`
    /// (t=20 clip) to `75.0`.
    #[test]
    fn interpolate_missing_clip_values_across_clips() -> Result<()> {
        let root = format!("{}/fixtures/clip_missing_interp/root.usda", manifest_dir());
        let mut cache = Cache::new(single_layer_stack(&root), VariantFallbackMap::new());
        let size = |cache: &mut Cache, t: f64| cache.value_at(&sdf::path("/Model.size").unwrap(), t, &lerp);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(0.0)));
        assert_eq!(size(&mut cache, 15.0)?, Some(Value::Double(75.0)));
        assert_eq!(size(&mut cache, 20.0)?, Some(Value::Double(100.0)));
        Ok(())
    }

    /// Instances sharing a prototype compose their subtree once: a
    /// non-canonical instance's descendant is served by the canonical one and
    /// is never indexed (spec 11.3.3).
    #[test]
    fn instances_share_prototype() -> Result<()> {
        let root = format!("{}/fixtures/instancing_shared.usda", manifest_dir());
        let mut cache = Cache::new(single_layer_stack(&root), VariantFallbackMap::new());
        let interp = |_: &sdf::TimeSampleMap, _: f64| None;

        // Query /A first so it becomes the canonical instance for its key.
        let size = |cache: &mut Cache, p: &str| cache.value_at(&sdf::path(p).unwrap(), 0.0, &interp);
        assert_eq!(size(&mut cache, "/A/Child.size")?, Some(sdf::Value::Double(5.0)));
        assert_eq!(size(&mut cache, "/B/Child.size")?, Some(sdf::Value::Double(5.0)));
        assert_eq!(size(&mut cache, "/C/Child.size")?, Some(sdf::Value::Double(9.0)));

        // /A and /B share a prototype, so /B's subtree is served by /A and
        // /B/Child is never composed. /C uses a different prototype, so its
        // own subtree is composed.
        assert!(cache.is_indexed(&sdf::path("/A/Child")?));
        assert!(!cache.is_indexed(&sdf::path("/B/Child")?));
        assert!(cache.is_indexed(&sdf::path("/C/Child")?));
        Ok(())
    }

    /// `instances_of` is sorted by path, so the result is independent of the
    /// order instances were registered (spec 11.3.3).
    #[test]
    fn instances_of_sorted() -> Result<()> {
        let root = format!("{}/fixtures/instancing_shared.usda", manifest_dir());
        let mut cache = Cache::new(single_layer_stack(&root), VariantFallbackMap::new());

        // Register /B before /A so registration order is [/B, /A].
        let proto = cache.prototype_of(&sdf::path("/B")?)?.unwrap();
        assert_eq!(cache.prototype_of(&sdf::path("/A")?)?, Some(proto.clone()));

        // The returned instances are still sorted by path.
        assert_eq!(cache.instances_of(&proto), vec![sdf::path("/A")?, sdf::path("/B")?]);
        Ok(())
    }

    /// A significant change (here, flipping `instanceable`) clears the
    /// prototype registry so stale instance-to-prototype mappings do not
    /// persist (spec 11.3.3).
    #[test]
    fn instance_change_invalidates_prototypes() -> Result<()> {
        let root = format!("{}/fixtures/instancing_shared.usda", manifest_dir());
        let mut cache = Cache::new(single_layer_stack(&root), VariantFallbackMap::new());

        assert!(cache.prototype_of(&sdf::path("/A")?)?.is_some());
        assert!(!cache.prototypes().is_empty());

        let mut cl = sdf::ChangeList::new();
        cl.entry_mut(&sdf::path("/A")?)
            .info_changed
            .insert(sdf::FieldKey::Instanceable.as_str());
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(0, cl)]);
        changes.apply(&mut cache);

        assert!(cache.prototypes().is_empty());
        Ok(())
    }
}
