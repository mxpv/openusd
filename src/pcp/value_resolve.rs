//! The shared value-resolution walk: one strength-ordered traversal of a
//! prim's contributing sites, and the vocabulary its consumers speak.
//!
//! Value resolution, property-stack collection and resolve-info collection are
//! three questions about the same walk. C++ models them as *resolvers* over one
//! driver (`ProcessLayerAtDefault` / `ProcessLayerAtTime` / `ProcessClips`,
//! driven by `UsdStage::_GetResolvedValueAtTimeImpl`); this module is the Rust
//! form of that, with [`IndexCache::resolve_property`](super::IndexCache::resolve_property)
//! as the driver and [`OpinionResolver`] as the resolver seam.
//!
//! One walk is what keeps the per-time read, the cached source, the sample
//! times and the property stack answering from the same strength order.

use crate::sdf;

use super::QueryError;
use super::asset_resolve::AssetSite;
use super::clip::{ClipCache, ClipQuery, ResolvedClipSet};
use super::layer_graph::StackIdentity;
use super::prim_graph::{ArcType, Node};
use super::{LayerGraph, LayerId, LayerStackId, LayerStackIdentifier, MapFunction};

/// Which value-resolution walk to run — the Rust form of C++
/// `UsdStage::_GetResolveInfoImpl`'s three-way dispatch on
/// `const UsdTimeCode *time`.
///
/// The mode selects the walk, not a winning tier: it decides which sites are
/// visited, whether value clips are consulted, and at what time a sample map or
/// clip schedule is probed. What counts as an answer at a visited site is the
/// resolver's decision.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum ResolveMode {
    /// No specific time (C++ `time == nullptr`). Every tier participates, but a
    /// `timeSamples` opinion counts as present merely by holding a sample and a
    /// clip set by participating — nothing is interpolated and no clip is
    /// selected. Distinct from [`Default`](Self::Default), which skips the
    /// time-varying tiers outright.
    Proximal,
    /// Strictly the default time (C++ `time->IsDefault()`). `timeSamples` and
    /// value clips are skipped: neither contributes a default.
    Default,
    /// A numeric stage time (C++ `time->IsNumeric()`). Sample maps are
    /// bracketed at this time and the clip set active at it is selected.
    Numeric(f64),
}

impl ResolveMode {
    /// Whether the walk probes `timeSamples` at each site.
    pub(crate) fn visits_time_samples(self) -> bool {
        !matches!(self, Self::Default)
    }

    /// Whether the walk consults value clips at all.
    pub(crate) fn consults_clips(self) -> bool {
        !matches!(self, Self::Default)
    }
}

/// Whether the walk continues to the next-weaker opinion — C++'s `bool` return
/// from `ProcessLayerAtTime` / `ProcessLayerAtDefault` / `ProcessClips`, named.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[must_use]
pub(crate) enum Step {
    Continue,
    Stop,
}

impl Step {
    pub(crate) fn stop(self) -> bool {
        matches!(self, Self::Stop)
    }
}

/// A field authored at a site that withholds a value from every weaker opinion
/// — the two shapes the walk can find, told apart because they withhold
/// different things.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Withheld {
    /// A `default` opinion authored `ValueBlock`. Withholds the value itself, so
    /// resolution reverts to whatever comes after the authored tiers.
    DefaultBlock,
    /// The whole `timeSamples` field is blocked. Withholds samples only: this
    /// site's `default`, and every weaker one, can still answer.
    TimeSamplesFieldBlock,
}

/// What a `timeSamples` field holds, as value resolution reads it.
///
/// Classified before the query mode decides what to do with it, so every mode
/// agrees about whether there is an opinion here at all.
pub(crate) enum SampleField<'a> {
    /// A map holding at least one sample. An empty one is no more a source than
    /// an absent field: C++ requires a layer to hold at least one sample before
    /// it counts as a `timeSamples` source.
    Map(&'a sdf::TimeSampleMap),
    /// The field is blocked, withholding samples from every weaker site.
    Blocked,
    /// Anything else — not a sample opinion, so nothing to resolve from or to
    /// report as authored.
    Unusable,
}

impl<'a> SampleField<'a> {
    /// Reads a `timeSamples` field's authored value.
    pub(crate) fn classify(value: &'a sdf::Value) -> Self {
        match value {
            sdf::Value::TimeSamples(samples) if !samples.is_empty() => Self::Map(samples),
            sdf::Value::ValueBlock | sdf::Value::None => Self::Blocked,
            _ => Self::Unusable,
        }
    }
}

/// Whether the source that answered the walk supplied a value there.
///
/// Independent of *which* source answered and of what was authored: a site can
/// hold an opinion that supplies no value, and an unauthored property has no
/// value without anything blocking it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum ValueState {
    /// A source supplied a value.
    Present,
    /// An opinion blocked the value — a blocked `default`, or a sample map whose
    /// every relevant sample is blocked, which is the shape
    /// [`Attribute::block`] authors (it blocks the `default` and each authored
    /// sample in place, where C++ clears the samples outright). The one state
    /// [`ResolveInfo::value_is_blocked`](crate::usd::ResolveInfo::value_is_blocked)
    /// reports, matching C++'s single `_valueIsBlocked` bit.
    ///
    /// [`Attribute::block`]: crate::usd::Attribute::block
    Blocked,
    /// No value, and nothing blocking one: unauthored, excluded by the
    /// population mask, or authored only as opinions that withhold samples.
    #[default]
    Absent,
}

/// What one run of the shared walk learned about a property.
///
/// The three facts are recorded independently because they are independent: an
/// authored opinion need not supply a value, a source can be selected and then
/// withhold one, and an opinion the walk did not resolve from is authored all
/// the same. Deriving any of them from another is what made
/// [`ResolveInfo`](crate::usd::ResolveInfo)'s predicates disagree with the value
/// read.
#[derive(Debug, Default)]
pub(crate) struct Resolution {
    /// Which kind of source answered, in `pcp` terms; `usd` maps it onto its
    /// public [`ResolveInfoSource`](crate::usd::ResolveInfoSource), adding the
    /// schema tier it owns.
    pub(crate) source: ResolveSourceKind,
    /// The site the answering source was found at, when a composition node
    /// supplied it.
    pub(crate) node: Option<ResolveNode>,
    /// Whether that source supplied a value.
    pub(crate) value: ValueState,
    /// Whether any layer authored an opinion at all, whatever became of it.
    /// Accumulated as the walk goes, so an opinion it declined to resolve from
    /// still counts.
    pub(crate) authored: bool,
}

/// Which kind of source answered the walk — the authored tiers only. The schema
/// fallback tier is `usd`'s to add.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum ResolveSourceKind {
    #[default]
    None,
    Default,
    TimeSamples,
    ValueClips,
}

/// Whether a `timeSamples` opinion supplies a value for a query at `time`,
/// authored in a layer whose cumulative offset to the stage is `offset`.
///
/// At a numeric time this interpolates exactly as the value read does, so an
/// introspection query and the read cannot disagree about whether the map
/// answered. Without a time it falls to [`samples_supply_any_value`].
pub(crate) fn samples_supply_value(
    samples: &sdf::TimeSampleMap,
    offset: sdf::LayerOffset,
    time: Option<f64>,
    interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<sdf::Value>,
) -> bool {
    match time {
        Some(time) => offset.sample_in_stage_time(samples, time, interp).is_some(),
        None => samples_supply_any_value(samples),
    }
}

/// Whether a `timeSamples` opinion supplies a value at any time at all.
///
/// False only for a map every one of whose samples is blocked — the shape
/// [`Attribute::block`](crate::usd::Attribute::block) leaves behind, since it
/// blocks each authored sample in place where C++ clears the samples outright.
/// Such a map answers the walk, stopping weaker sources, but is no more a value
/// source than an absent field, so it contributes no sample times either.
pub(crate) fn samples_supply_any_value(samples: &sdf::TimeSampleMap) -> bool {
    samples.iter().any(|(_, value)| !is_block(value))
}

/// Whether a value is one of the two spec sentinels for "no value".
pub(crate) fn is_block(value: &sdf::Value) -> bool {
    matches!(value, sdf::Value::ValueBlock | sdf::Value::None)
}

/// An owned, alias-free record of the composition node an opinion came from
/// (C++ `PcpNodeRef`'s identifying facts).
///
/// [`NodeId`](super::NodeId) is a bare arena index with no generation counter:
/// after an invalidation and recompose the same index silently names a
/// different node. A [`ResolveInfo`](crate::usd::ResolveInfo) outlives the index
/// it was resolved from — that is the point of caching one — so it carries the
/// node's identifying facts by value rather than a handle that could alias.
#[derive(Debug, Clone, PartialEq)]
pub struct ResolveNode {
    arc: ArcType,
    path: sdf::Path,
    map_to_root: MapFunction,
    layer_stack: ResolveStackIdentity,
}

impl ResolveNode {
    /// Captures `node`'s identity, resolving its stack against `graph`.
    ///
    /// `stage` is the composition input the walk is running under; the graph
    /// does not hold it, since a `LayerGraph` is only ever built for one.
    pub(crate) fn capture(graph: &LayerGraph, node: &Node, stage: &LayerStackIdentifier) -> Self {
        Self {
            arc: node.arc,
            path: node.path.clone(),
            map_to_root: node.map_to_root.clone(),
            layer_stack: ResolveStackIdentity {
                stage: stage.clone(),
                stack: Box::new(graph.stack_identity(node.layer_stack)),
            },
        }
    }

    /// The composition arc that introduced the node (C++
    /// `PcpNodeRef::GetArcType`).
    pub fn arc(&self) -> ArcType {
        self.arc
    }

    /// The prim path in the node's own namespace, which under a reference,
    /// variant or instancing redirect differs from the composed stage path.
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The node's namespace mapping into the root namespace.
    pub fn map_to_root(&self) -> &MapFunction {
        &self.map_to_root
    }

    /// Identity of the layer stack the node composes in.
    pub fn layer_stack(&self) -> &ResolveStackIdentity {
        &self.layer_stack
    }
}

/// Identity of the layer stack a [`ResolveNode`] composes in.
///
/// Composite because neither half suffices alone:
/// [`LayerStackIdentifier`] names a *stage's root* layer stack and cannot
/// describe a reference or payload target, while the per-stack identity is
/// meaningful only relative to a composition input — its root form carries no
/// data, so nodes from unrelated stages would compare equal. The same pairing
/// [`EditTarget`](crate::usd::EditTarget) uses.
#[derive(Debug, Clone, PartialEq)]
pub struct ResolveStackIdentity {
    stage: LayerStackIdentifier,
    /// Boxed to keep [`ResolveNode`] small, as `EditTarget` does: this is
    /// cloned per resolve-info query.
    stack: Box<StackIdentity>,
}

impl ResolveStackIdentity {
    /// The stage composition input the stack belongs to.
    pub fn stage(&self) -> &LayerStackIdentifier {
        &self.stage
    }

    /// Which stack within that composition — the root, or a reference/payload
    /// target with the variable-source chain that distinguishes two targets of
    /// the same asset.
    pub fn stack(&self) -> &StackIdentity {
        &self.stack
    }
}

/// One `(node, layer)` site the walk reached, with everything a resolver needs
/// to describe it without re-deriving the arc mapping.
pub(crate) struct OpinionSite<'a> {
    /// The contributing node.
    pub(crate) node: &'a Node,
    /// The layer that authored at this site.
    pub(crate) layer: LayerId,
    /// That layer's time offset folded to the root namespace — C++
    /// `_GetLayerToStageOffset(node, layer)`, precomputed on the spec stack.
    pub(crate) offset: sdf::LayerOffset,
    /// The property path queried in `layer`.
    pub(crate) query_path: sdf::Path,
}

/// A site the walk selected, kept by value so a consumer can act on it once the
/// walk has released the index — the same three facts a C++ resolver stashes on
/// its resolve info (`_layer`, `_layerStack`, `_primPathInLayerStack`).
///
/// Cheap to build: no string is copied, unlike the [`AssetSite`] a consumer
/// derives from it only for a value that turns out to hold asset paths.
#[derive(Debug, Clone)]
pub(crate) struct SelectedSite {
    pub(crate) layer: LayerId,
    pub(crate) layer_stack: LayerStackId,
    pub(crate) query_path: sdf::Path,
}

impl SelectedSite {
    /// Whether `(layer, node, path)` is this site.
    pub(crate) fn is(&self, layer: LayerId, node: &Node, path: &sdf::Path) -> bool {
        self.layer == layer && self.layer_stack == node.layer_stack_id() && self.query_path == *path
    }
}

impl OpinionSite<'_> {
    /// This site as a [`SelectedSite`], for a resolver whose answer is finished
    /// after the walk.
    pub(crate) fn select(&self) -> SelectedSite {
        SelectedSite {
            layer: self.layer,
            layer_stack: self.node.layer_stack_id(),
            query_path: self.query_path.clone(),
        }
    }

    /// Provenance for an `asset` value authored here. Copies two strings, so
    /// build it only for a value that actually holds asset paths.
    pub(crate) fn asset_site(&self, graph: &LayerGraph) -> AssetSite {
        AssetSite::in_graph(graph, self.node.layer_stack_id(), self.layer, &self.query_path)
    }
}

/// The value-clip work a resolver can ask of one clip set reached at a site,
/// holding the mutable half of clip resolution so the walk's own state stays
/// borrow-free.
///
/// Only the resolver that needs the expensive answer pays for it: a per-time
/// read opens the active clip, while the sample-times tier materializes every
/// clip's times.
pub(crate) struct ClipProbe<'a> {
    pub(crate) cache: &'a mut ClipCache,
    pub(crate) graph: &'a LayerGraph,
    pub(crate) set: &'a ResolvedClipSet,
    pub(crate) query: ClipQuery<'a>,
}

/// What one clip set contributes to a query at a stage time.
///
/// The single definition of "did this clip answer here", so a value read and an
/// introspection query cannot disagree about it.
pub(crate) enum ClipAnswer {
    /// The set does not source the property, so weaker sources still may.
    Absent,
    /// The set owns the property but supplies no value at this time: it is
    /// inactive there, or the clip authored a block (spec 12.3.4.6). It answers
    /// all the same, so nothing weaker contributes.
    Blocked,
    /// The set supplied a value.
    Value(sdf::Value),
}

impl ClipAnswer {
    /// What the set contributed, in the walk's shared vocabulary — the one
    /// place a clip answer is given its meaning, so a consumer decides only what
    /// to keep, never what "blocked" is.
    ///
    /// [`ValueState::Absent`] is the only state that leaves a weaker source a
    /// chance; the other two answer.
    pub(crate) fn value_state(&self) -> ValueState {
        match self {
            Self::Absent => ValueState::Absent,
            Self::Blocked => ValueState::Blocked,
            Self::Value(_) => ValueState::Present,
        }
    }

    /// The value the set supplied, if any.
    pub(crate) fn into_value(self) -> Option<sdf::Value> {
        match self {
            Self::Value(value) => Some(value),
            Self::Absent | Self::Blocked => None,
        }
    }
}

impl ClipProbe<'_> {
    /// What the set contributes at `time`, resolved exactly as the value read
    /// resolves it.
    pub(crate) fn answer_at(
        &mut self,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<sdf::Value>,
    ) -> Result<ClipAnswer, QueryError> {
        match self
            .cache
            .value_in_set(self.graph, self.set, &self.query, time, interp)?
        {
            None => Ok(ClipAnswer::Absent),
            Some(value) if is_block(&value) => Ok(ClipAnswer::Blocked),
            Some(value) => Ok(ClipAnswer::Value(value)),
        }
    }

    /// What the set contributes to a query that names no time.
    pub(crate) fn answer_untimed(&mut self) -> Result<ValueState, QueryError> {
        self.cache.untimed_answer_in_set(self.graph, self.set, &self.query)
    }

    /// The stage sample times the set contributes, and whether its schedule
    /// alone can vary the value. `None` when it does not participate.
    pub(crate) fn introspection(&mut self) -> Result<Option<(Vec<f64>, bool)>, QueryError> {
        self.cache.clip_introspection_in_set(self.graph, self.set, &self.query)
    }

    /// The layer a property stack lists for the set at `time`, with the property
    /// path inside it. `None` when the set does not source the property.
    pub(crate) fn spec_site_at(&mut self, time: f64) -> Result<Option<(String, sdf::Path)>, QueryError> {
        self.cache
            .clip_spec_site_in_set(self.graph, self.set, &self.query, time)
    }
}

/// Consumes the opinions the shared walk reaches, in strength order — the Rust
/// form of C++'s resolver concept.
///
/// Every hook borrows what it is handed and returns a [`Step`]; nothing is
/// cloned on the resolver's behalf, so a resolver that needs an owned copy
/// clones it itself. That is what lets a per-time read borrow a sample map
/// while the cached-source resolver clones it once.
pub(crate) trait OpinionResolver {
    /// Fires for every visited site before any field is probed, whether or not
    /// the site authors a value. The property stack answers here; the value
    /// resolvers leave it at the default.
    fn on_site(&mut self, _site: &OpinionSite<'_>) -> Step {
        Step::Continue
    }

    /// The strongest `timeSamples` map at this site, borrowed in the
    /// contributing layer's own time frame. Never called in
    /// [`ResolveMode::Default`].
    fn on_time_samples(&mut self, _samples: &sdf::TimeSampleMap, _site: &OpinionSite<'_>) -> Step {
        Step::Continue
    }

    /// A `default` opinion at this site, borrowed in the layer's time frame.
    fn on_default(&mut self, _value: &sdf::Value, _site: &OpinionSite<'_>) -> Step {
        Step::Continue
    }

    /// A `timeSamples` opinion the walk will not resolve from, because
    /// [`ResolveMode::Default`] answers from `default` alone. It is still an
    /// authored opinion, which is all a resolver can learn about it here.
    fn on_unresolved_samples(&mut self, _site: &OpinionSite<'_>) {}

    /// An opinion that exists and withholds a value.
    ///
    /// The default is what withholding means to a value query: a blocked
    /// `default` answers, so resolution reverts to whatever follows the authored
    /// tiers, while a blocked `timeSamples` field withholds samples alone and
    /// the walk goes on. A resolver collecting every contributor overrides it.
    fn on_withheld(&mut self, kind: Withheld, _site: &OpinionSite<'_>) -> Step {
        match kind {
            Withheld::DefaultBlock => Step::Stop,
            Withheld::TimeSamplesFieldBlock => Step::Continue,
        }
    }

    /// Whether an authored opinion at a site is that site's one answer, so a
    /// clip set introduced there is not consulted as well — C++'s
    /// `bool *foundOpinion`, which every value resolver sets and
    /// `_PropertyStackResolver` deliberately never does, since it wants both
    /// the graph spec and the clip spec at a site that has both.
    fn claims_sites(&self) -> bool {
        true
    }

    /// A value-clip set introduced at the site the walk has reached. The
    /// resolver asks `probe` for whatever it needs; returning
    /// [`Step::Continue`] walks on to the next set.
    fn on_clips(&mut self, _probe: &mut ClipProbe<'_>, _site: &OpinionSite<'_>) -> Result<Step, QueryError> {
        Ok(Step::Continue)
    }
}
