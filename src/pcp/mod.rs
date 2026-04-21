//! Prim Cache Population (PCP) — the composition engine.
//!
//! This module implements USD's composition algorithm, which merges opinions
//! from multiple layers into a single composed scene graph. It is the Rust
//! equivalent of [Pixar's PCP module](https://openusd.org/dev/api/pcp_page_front.html).
//!
//! # LIVERPS strength ordering
//!
//! USD composes opinions using seven arc types, ordered by strength
//! (mnemonic "liver-peas"):
//!
//! 1. **L**ocal — direct opinions in the root layer stack (sublayers)
//! 2. **I**nherits — opinions from class prims (`inherits = </Class>`)
//! 3. **V**ariants — opinions from the selected variant (`variants = { string v = "sel" }`)
//! 4. **R**elocates — non-destructive namespace remapping (`relocates = { </Src>: </Tgt> }`)
//! 5. **R**eferences — opinions from referenced layers (`references = @model.usd@</Prim>`)
//! 6. **P**ayloads — like references but deferred (`payload = @heavy.usd@</Prim>`)
//! 7. **S**pecializes — like inherits but weakest (`specializes = </Base>`)
//!
//! Within each arc type, opinions are ordered by layer strength (root layer
//! strongest, deepest sublayer weakest).
//!
//! # Relocates
//!
//! Relocates are non-destructive namespace remapping authored via
//! `relocates = { </Source>: </Target> }` in a layer's metadata. They
//! allow moving prims in the composed namespace without modifying the
//! underlying layers. The `Cache` handles relocates at the scene graph
//! level:
//!
//! - `layerRelocates` are extracted from each layer's pseudoroot at
//!   construction and mapped into the composed namespace through each
//!   layer's namespace mapping.
//! - When composing a prim that is a relocate target, the cache finds the
//!   pre-relocation source path, builds a full composition index for it,
//!   and merges the resulting nodes as `Relocate` arc nodes.
//! - Prim children are adjusted to hide relocated source children and
//!   expose target children, including children created by relocates
//!   within referenced layers.
//!
//! # Module structure
//!
//! | Item | C++ equivalent | Description |
//! |------|---------------|-------------|
//! | `LayerStack` | `PcpLayerStack` | Layers, identifiers, and precomputed sublayer stacks bundled into a single unit. |
//! | `cache` | `PcpCache` | Lazily-built composition cache. Main interface for [`Stage`](crate::Stage). Owns a `LayerStack`. |
//! | [`Error`] | `PcpErrorBase` | Composition errors: arc cycles, unresolved layers, missing/invalid `defaultPrim`. |
//! | `index` | `PcpPrimIndex` | Per-prim composition graph: arena-based DAG of [`Node`]s with parent/child/sibling and origin links. |
//! | `mapping` | `PcpMapFunction` | Namespace mapping between composition arcs — each [`Node`] carries `map_to_parent` and `map_to_root`. |
//! | [`VariantFallbackMap`] | `PcpVariantFallbackMap` | Maps variant set names to ordered fallback selections, used when no selection is authored. |
//! | `rel` | — | [`Relocates`](rel::Relocates): isolated relocate state and logic. Owned by `Cache`, receives external data through parameters. |
//!
//! Layer collection lives in [`crate::layer`] (analogous to `PcpLayerStack`).
//!
//! # Architecture
//!
//! Each [`PrimIndex`](index::PrimIndex) is an arena-based graph of [`Node`]s.
//! Nodes carry two namespace mappings: `map_to_parent` (translates paths to
//! the parent node's namespace) and `map_to_root` (translates directly to the
//! root namespace). These [`MapFunction`]s are the foundation for namespace
//! remapping across composition arcs (including relocates). After
//! construction, nodes are ordered strongest-to-weakest so value resolution
//! is a linear scan.
//!
//! Composition is driven by a [`CompositionContext`](index::CompositionContext)
//! that flows from parent prims to children. The context carries:
//!
//! - Variant selections from all ancestors, so descendant prims resolve
//!   variant sets without recomputing ancestor composition.
//! - Arc mappings from ancestors, recording how composed paths map to
//!   paths in other layers. Used for descendant namespace remapping and
//!   implied inherit propagation.
//!
//! # Variant fallbacks
//!
//! A [`VariantFallbackMap`] can be provided when opening a stage via
//! [`StageBuilder::variant_fallbacks`](crate::StageBuilder::variant_fallbacks).
//! When a prim has a variant set but no authored selection, the engine tries
//! each fallback in order. The first fallback matching an existing variant in
//! the set is used; if none match, the first variant in the set is the default.
//! Authored selections always take priority over fallbacks.
//!
//! The [`Cache`](cache::Cache) stores both the [`PrimIndex`](index::PrimIndex)
//! and the [`CompositionContext`](index::CompositionContext) for each composed
//! prim. During depth-first traversal, parents are always composed before
//! children, so the context chain is always populated. Each per-prim build
//! takes only shared references, making it suitable for future parallel
//! execution.
//!
//! Composition errors ([`Error`]) are returned from [`Cache`](cache::Cache)
//! methods and handled by the [`Stage`](crate::Stage)'s error callback.
//! The callback decides whether to skip the broken arc and continue or
//! abort composition entirely.
//!
//! See <https://openusd.org/release/glossary.html#livrps-strength-ordering>

pub(crate) mod cache;
pub(crate) mod index;
mod mapping;
mod rel;

use std::collections::{HashMap, HashSet, VecDeque};

use crate::sdf::schema::FieldKey;
use crate::sdf::{self, LayerData, Path, Value};

pub(crate) use cache::Cache;
pub use index::{ArcType, Node, NodeIndex, PrimIndex};
pub use mapping::MapFunction;

/// Maps variant set names to ordered lists of fallback selections.
///
/// When a prim has a variant set but no authored selection, the composition
/// engine tries each fallback in order before falling back to the first
/// variant defined in the set.
///
/// This is the Rust equivalent of C++ `PcpVariantFallbackMap`.
///
/// # Example
///
/// ```
/// use openusd::pcp::VariantFallbackMap;
///
/// let fallbacks = VariantFallbackMap::new()
///     .add("shadingComplexity", ["full", "simple"])
///     .add("renderQuality", ["high", "medium", "low"]);
/// ```
#[derive(Debug, Clone, Default)]
pub struct VariantFallbackMap(HashMap<String, Vec<String>>);

impl VariantFallbackMap {
    /// Creates an empty variant fallback map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds fallback selections for a variant set.
    ///
    /// The selections are tried in order — the first one matching an existing
    /// variant in the set is used.
    pub fn add(mut self, set_name: impl Into<String>, selections: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.0
            .insert(set_name.into(), selections.into_iter().map(Into::into).collect());
        self
    }

    /// Returns the fallback selections for a variant set.
    ///
    /// Returns an empty slice if no fallbacks are registered for the set.
    pub fn get(&self, set_name: &str) -> &[String] {
        self.0.get(set_name).map(Vec::as_slice).unwrap_or_default()
    }

    /// Returns `true` if no fallbacks have been registered.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Precomputed sublayer stacks, keyed by root layer index.
///
/// Each entry maps a root layer to its full sublayer stack. Each entry pairs
/// a layer index with the effective layer offset for that layer relative to
/// the stack's root (composed through nested sublayers per spec 10.3.1.1).
/// The stack root itself has [`sdf::LayerOffset::IDENTITY`].
pub(crate) type SublayerStacks = HashMap<usize, Vec<(usize, sdf::LayerOffset)>>;

/// Loaded layers with precomputed sublayer ordering.
///
/// Bundles layers, their identifiers, and the precomputed sublayer stacks
/// into a single unit passed through the composition engine. Corresponds
/// to a simplified C++ `PcpLayerStack`.
pub(crate) struct LayerStack {
    /// Layer data in strength order (session layers first, then root layer).
    pub layers: Vec<LayerData>,
    /// Layer identifiers (asset paths) matching the `layers` order.
    pub identifiers: Vec<String>,
    /// Precomputed sublayer stacks keyed by root layer index.
    pub sublayer_stacks: SublayerStacks,
    /// Number of session layers at the front of the layer stack.
    pub session_layer_count: usize,
    /// O(1) lookup: effective sublayer offset of each layer in the first
    /// stack that contains it. Precomputed from `sublayer_stacks` to keep
    /// per-prim composition off the linear-scan hot path.
    layer_offsets: HashMap<usize, sdf::LayerOffset>,
}

impl LayerStack {
    /// Creates a new layer stack, precomputing sublayer ordering.
    pub fn new(layers: Vec<LayerData>, identifiers: Vec<String>, session_layer_count: usize) -> Self {
        let sublayer_stacks: SublayerStacks = (0..layers.len())
            .map(|i| (i, Self::build_sublayer_stack(i, &layers, &identifiers)))
            .collect();
        let mut layer_offsets: HashMap<usize, sdf::LayerOffset> = HashMap::new();
        for stack in sublayer_stacks.values() {
            for &(li, off) in stack {
                layer_offsets.entry(li).or_insert(off);
            }
        }
        Self {
            layers,
            identifiers,
            sublayer_stacks,
            session_layer_count,
            layer_offsets,
        }
    }

    /// Returns the number of layers.
    pub fn len(&self) -> usize {
        self.layers.len()
    }

    /// Returns `true` if there are no layers.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.layers.is_empty()
    }

    /// Returns the layer data at the given index.
    pub fn layer(&self, index: usize) -> &LayerData {
        &self.layers[index]
    }

    /// Returns the layer identifier at the given index.
    pub fn identifier(&self, index: usize) -> &str {
        &self.identifiers[index]
    }

    /// Returns the effective sublayer offset for `layer_index` relative to
    /// whichever stack first contains it.
    ///
    /// Intended for call sites that discover a layer without threading the
    /// full stack context (ancestor-arc propagation, `cache.rs` scans, and
    /// the flat L-stage scan used by [`IndexBuilder::build`]). O(1) — backed
    /// by a map precomputed in [`LayerStack::new`].
    pub(crate) fn effective_offset_for_layer(&self, layer_index: usize) -> sdf::LayerOffset {
        self.layer_offsets
            .get(&layer_index)
            .copied()
            .unwrap_or(sdf::LayerOffset::IDENTITY)
    }

    /// Returns the layer indices + effective offsets for a sublayer stack
    /// rooted at `root_layer`. Each entry's offset is composed from the
    /// root through all nested sublayers per spec 10.3.1.1.
    pub(crate) fn build_sublayer_stack(
        root_layer: usize,
        layers: &[LayerData],
        identifiers: &[String],
    ) -> Vec<(usize, sdf::LayerOffset)> {
        let mut stack: Vec<(usize, sdf::LayerOffset)> = vec![(root_layer, sdf::LayerOffset::IDENTITY)];
        let mut seen: HashSet<usize> = HashSet::new();
        seen.insert(root_layer);
        // BFS so offsets compose with their direct parent sublayer.
        let mut queue: VecDeque<(usize, sdf::LayerOffset)> = VecDeque::new();
        queue.push_back((root_layer, sdf::LayerOffset::IDENTITY));

        while let Some((idx, parent_effective)) = queue.pop_front() {
            let root = Path::abs_root();
            let Ok(value) = layers[idx].get(&root, FieldKey::SubLayers.as_str()) else {
                continue;
            };
            let Value::StringVec(sub_paths) = value.into_owned() else {
                continue;
            };

            // Offsets live in a parallel field; missing entries fall back to
            // the identity offset per spec 16.2.18.3.
            let offsets: Vec<sdf::LayerOffset> = layers[idx]
                .get(&root, FieldKey::SubLayerOffsets.as_str())
                .ok()
                .and_then(|v| match v.into_owned() {
                    Value::LayerOffsetVec(v) => Some(v),
                    _ => None,
                })
                .unwrap_or_default();

            for (i, sub_path) in sub_paths.into_iter().enumerate() {
                let Some(sub_idx) = index::find_layer(&sub_path, identifiers) else {
                    continue;
                };
                if !seen.insert(sub_idx) {
                    continue;
                }
                let local = offsets.get(i).copied().unwrap_or_default().sanitized();
                let effective = parent_effective.concatenate(&local);
                stack.push((sub_idx, effective));
                queue.push_back((sub_idx, effective));
            }
        }

        stack
    }
}

/// An error encountered while building a [`PrimIndex`](index::PrimIndex).
///
/// These errors represent recoverable composition failures — a missing
/// layer or invalid metadata does not have to be fatal. The error handler
/// provided via [`StageBuilder::on_error`](crate::StageBuilder::on_error)
/// decides whether to skip the broken arc and continue, or abort.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// A composition arc cycle was detected.
    #[error("composition arc cycle at {path} (depth {depth})")]
    ArcCycle {
        /// The prim path where the cycle was detected.
        path: Path,
        /// Recursion depth when the cycle was detected.
        depth: usize,
    },

    /// A layer referenced by a composition arc was not found among loaded layers.
    #[error("unresolved {arc:?} layer @{asset_path}@ at {site_path}")]
    UnresolvedLayer {
        /// The asset path that could not be matched.
        asset_path: String,
        /// The composition arc type that introduced this dependency.
        arc: ArcType,
        /// The prim path where the arc was authored.
        site_path: Path,
    },

    /// An external reference/payload targets a layer without specifying a prim
    /// path, but the target layer has no `defaultPrim` metadata.
    #[error("{arc:?} target @{layer_id}@ has no defaultPrim (at {site_path})")]
    MissingDefaultPrim {
        /// Identifier of the target layer.
        layer_id: String,
        /// The composition arc type.
        arc: ArcType,
        /// The prim path where the arc was authored.
        site_path: Path,
    },

    /// The `defaultPrim` metadata on a target layer has an invalid or
    /// unexpected value.
    #[error("{arc:?} target @{layer_id}@ has invalid defaultPrim (at {site_path})")]
    InvalidDefaultPrim {
        /// Identifier of the target layer.
        layer_id: String,
        /// The composition arc type.
        arc: ArcType,
        /// The prim path where the arc was authored.
        site_path: Path,
    },
}
