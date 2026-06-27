//! Task-queue prim indexer (C++ `Pcp_PrimIndexer` port).
//!
//! [`Indexer`] grows a [`PrimIndexGraph`] node-by-node by draining a
//! priority-ordered task queue, mirroring C++ `Pcp_BuildPrimIndex`. The queue
//! follows each composition arc structurally, so reference/payload diamonds — a
//! shared target reached by two arc paths — contribute a node on each path.
//!
//! Ancestral opinions enter through the graph-clone seed (C++
//! `_BuildInitialPrimIndexFromAncestor`): the parent prim's composed graph is
//! cloned and every site path deepened by the child name
//! ([`PrimIndexGraph::append_child_name_to_all_sites`]), so the references and
//! payloads an ancestor introduced are re-evaluated at the deepened path by the
//! same queue. Each node carries its full site layer stack, so deepening only
//! needs to recompute which layers author a spec (`has_specs`).
//!
//! Inherits compose as class-based arcs (C++ `_EvalNodeInherits` →
//! `_AddClassBasedArc`), and a class brought in through a reference is mirrored
//! into the referencing namespace by implied-class propagation (C++
//! `_EvalImpliedClasses` → `_EvalImpliedClassTree`) driven by the queue: an
//! `EvalImpliedClasses` task carries a node's class-based children one level up,
//! repeating until the class reaches the root namespace.
//!
//! An arc whose target is not a root prim is composed as its own sub-index,
//! including the opinions above the target, then grafted under the arc (C++
//! `_AddArc`'s `includeAncestralOpinions` branch → `InsertChildSubgraph`). A
//! borrowed [`Frame`] chain threads the parent graphs back through the nested
//! builds so duplicate-node skipping (C++ `_AddArc`'s `skipDuplicateNodes`)
//! drops a class reached both directly and through an ancestral reference,
//! keeping it grafted once. Ancestral inherits ride the graph-clone seed
//! alongside references and payloads, so a class an ancestor introduces
//! re-evaluates at the child path.
//!
//! Variant sets resolve through a second band of queue tasks
//! (`EvalNodeVariantSets` → `EvalNodeVariantAuthored` → `EvalNodeVariantFallback`
//! → `EvalNodeVariantNoneFound`), weaker than every arc task so the strongest
//! variant selection is known before a variant grafts (C++ `_EvalNodeVariantSets`
//! and friends). The authored/fallback tasks break ties by live node strength,
//! so [`take_best_task`](Indexer::take_best_task) selects the next task with a
//! graph-aware comparator rather than a fixed `Ord`. Selecting a variant grafts
//! the `{set=sel}` site and re-enqueues its own arc and nested-variant tasks,
//! then retries any pending fallback tasks (C++ `RetryVariantTasks`). A nested
//! sub-build skips variants (C++ `evaluateVariantsAndDynamicPayloads == false`),
//! so when its graph is grafted the top-level build re-evaluates every grafted
//! node's local variant sets and the variant sets authored above it through a
//! parallel ancestral band (`EvalNodeAncestralVariantSets` and friends, C++
//! `_EvalNodeAncestralVariantSets` / `_AddAncestralVariantArc`), stronger than
//! the local variant band but weaker than implied classes. The selection itself
//! is composed by `_ComposeVariantSelection`: the set path is first translated to
//! the strongest node it namespace-maps to, then that node's subtree is searched
//! strong-to-weak, so a stronger frame's selection only wins where the mapping
//! reaches it.
//!
//! Specializes compose as globally-weak class-based arcs (C++
//! `_EvalNodeSpecializes` / `_EvalImpliedSpecializes`). A specializes node is
//! added as an inert placeholder where it is authored and copied under the local
//! root (`_PropagateNodeToRoot`); a specializes authored across a reference is
//! carried to every namespace level by the implied-class mechanism (since
//! specializes are class-based), and each level's placeholder is copied to the
//! root too. The copies are ordered among themselves by the C++
//! `PcpCompareSiblingNodeStrength` comparison, placing the globally-weak band after every
//! other opinion (spec 10.4.1). Propagation is add-if-absent on site, so the
//! first placeholder to reach a root site claims the copy and fixes its origin;
//! the copy carries the strongest origin because the seed scan
//! ([`scan_and_enqueue`](Indexer::scan_and_enqueue)) enqueues only expressed-arc
//! tasks for the cloned ancestor graph (C++ `AddTasksForRootNode`), so the
//! seed's propagated specializes are inherited from the clone rather than
//! re-implied in a different order.
//!
//! Implied-class tasks drain descendant-before-ancestor and otherwise
//! strongest-first (C++ `Task::PriorityOrder`'s `EvalImpliedClasses` case), so
//! the strongest implied arc reaches a shared site first.
//!
//! The indexer is the sole composition path ([`Indexer::build`] returns `None`
//! only for a genuine cycle or an unestablished seed, which compose to an empty
//! prim index). It composes the root local site; reference, payload, and inherit
//! arcs to either a root-level or a sub-root target (with the ancestral sub-index
//! and duplicate-node skipping); internal references and `defaultPrim` targets;
//! ancestral reference/payload/inherit propagation through the graph-clone seed;
//! implied classes; local and ancestral variant sets (authored and fallback
//! selections, nested variants, a variant set on a sub-root arc target, and the
//! cross-frame selection composition); specializes (direct, local, and implied
//! across a reference chain — including nested specializes chains and a referenced
//! target with local overrides — copied to the root, plus ancestral specializes a
//! child inherits through the seed-deepened parent graph, whose propagated copies
//! re-evaluate their arcs at the deepened path); and relocates (`eval_node_relocations`
//! composes a relocation source as a sub-index and grafts it, with the
//! prohibited-prim elision for salted earth, and `eval_implied_relocations`
//! grafts the implied relocate up to the grandparent). Known gaps with their
//! reasons are tracked inline and in the [`pcp` module docs](super):
//! specializes/inherit authored inside a selected variant, and
//! relationship/connection target remapping through relocates.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use crate::sdf::expr;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{self, LayerOffset, Path, Value};
use crate::tf::Token;

use super::compose_site::{collect_payloads_in, compose_arc_list_in, compose_references_in};
use super::layer_graph::LayerStackId;
use super::mapping::MapFunction;
use super::prim_graph::{is_class_based_arc, ArcType, NodeFlags, NodeId, PrimIndexGraph};
use super::prim_index::{stack_has_spec, CompositionContext, Demand, PrimEntry};
use super::{CycleChain, CycleHop, Error, LayerGraph, LayerId};

/// Maximum composition-arc nesting before the prim is abandoned as a cycle,
/// composing to an empty prim index. Matches C++ `MAX_COMPOSITION_DEPTH`.
const MAX_DEPTH: usize = 100;

pub(crate) type BuildResult<T> = std::result::Result<T, BuildError>;

/// Operational failure while building a prim index.
///
/// Recoverable composition problems are recorded as [`Error`] diagnostics and
/// do not use this path.
#[derive(Debug, thiserror::Error)]
#[error("{message}")]
pub(crate) struct BuildError {
    message: String,
}

impl From<anyhow::Error> for BuildError {
    fn from(error: anyhow::Error) -> Self {
        Self {
            message: format!("{error:#}"),
        }
    }
}

impl From<sdf::DataError> for BuildError {
    fn from(error: sdf::DataError) -> Self {
        Self::from(anyhow::Error::from(error))
    }
}

/// The nearest namespace ancestor of `path` (inclusive) whose final component is
/// a variant selection, or `None` if there is none (C++
/// `_FindContainingVariantSelection`).
fn find_containing_variant_selection(path: &Path) -> Option<Path> {
    let mut p = path.clone();
    loop {
        if p.is_prim_variant_selection_path() {
            return Some(p);
        }
        p = p.parent()?;
    }
}

/// The variant-bearing ancestor of `node_path` (a path that carries `{set=sel}`
/// selections) whose stripped form equals `stripped`, i.e. the storage site for
/// an opinion at the namespace path `stripped` within this variant node.
///
/// A variant node's selection is authored under its `{set=sel}` segment, so a
/// selection read at an ancestor namespace level (`/Ref` while the node is
/// `/Ref{v1=a}Model`) lives at the variant-deepened site (`/Ref{v1=a}`). Walks
/// `node_path` up, dropping a component each step, until the variant selections
/// strip away to `stripped`.
fn variant_storage_site(node_path: &Path, stripped: &Path) -> Option<Path> {
    let mut p = node_path.clone();
    loop {
        if p.strip_all_variant_selections() == *stripped {
            return Some(p);
        }
        p = p.parent()?;
    }
}

/// Maps a class-arc parent site back across the arc to the site to inherit (C++
/// `_DetermineInheritPath`), returning `None` when the parent is outside the
/// arc's co-domain.
///
/// Variant selections address opinion storage in a layer but are not part of
/// composed namespace, so they must never appear in mapping-function paths. To
/// add a class arc at a variant-selection site we strip the selections before
/// mapping and re-add the nearest containing selection afterwards.
fn determine_inherit_path(parent_path: &Path, inherit_map: &MapFunction) -> Option<Path> {
    if !parent_path.contains_prim_variant_selection() {
        return inherit_map.map_target_to_source(parent_path);
    }
    let var_path = find_containing_variant_selection(parent_path)?;
    let stripped = parent_path.strip_all_variant_selections();
    let mapped = inherit_map.map_target_to_source(&stripped)?;
    Some(
        mapped
            .replace_prefix(&var_path.strip_all_variant_selections(), &var_path)
            .unwrap_or(mapped),
    )
}

/// A borrowed parent-frame in the recursive sub-index build chain (C++
/// `PcpPrimIndex_StackFrame`).
///
/// When an arc target needs ancestral opinions (`includeAncestralOpinions`),
/// the target is composed as its own sub-index by a nested [`Indexer`], then
/// grafted under the arc's parent. The nested indexer carries a `Frame` back to
/// the graph that introduced the arc, so cross-frame duplicate-node skipping
/// (C++ `_AddArc`'s `skipDuplicateNodes` search) can reach the parent graph's
/// already-composed nodes — the mechanism that keeps a class reached both
/// directly and through an ancestral reference from grafting twice.
struct Frame<'f> {
    /// The path the sub-index this frame introduces was requested at (C++
    /// `PcpPrimIndex_StackFrame::requestedSite.path`), used to deepen a
    /// cross-frame site lookup by the suffix the request adds.
    requested_path: Path,
    /// The path the parent graph is rooted at (its local-root site path), the
    /// prefix replaced out of a cross-frame lookup.
    root_path: Path,
    /// The parent graph, searched for an existing node at the (prefix-replaced)
    /// site during duplicate-node skipping.
    graph: &'f PrimIndexGraph,
    /// The arc that introduced this sub-build, used to label a cross-frame cycle
    /// chain ([`cycle_error`](Indexer::cycle_error)).
    arc: ArcType,
    /// The layer the requested site resolves in (the sub-build ambient's
    /// representative), naming the cross-frame cycle chain's site.
    requested_layer: LayerId,
    /// Whether duplicate-node skipping is in force for the sub-build this frame
    /// introduces, inherited from the arc that spawned it (C++ `_AddArc`'s
    /// `skipDuplicateNodes`). The top-level build has no frame and never skips.
    skip: bool,
    /// The next parent frame, or `None` at the top-level build.
    previous: Option<&'f Frame<'f>>,
}

/// Walks the parent frame chain (C++ `PcpPrimIndex_StackFrameIterator`), yielding
/// each frame paired with a target path deepened into that frame's namespace: a
/// site at the current build's root maps to the frame's requested path, a deeper
/// site has its current-root prefix replaced (C++ `ReplacePrefix` across the
/// stack frame). The cross-frame duplicate-node search and cycle check share this
/// deepening and apply their own predicate to each pair.
struct FrameSites<'f> {
    search: Path,
    current_root: Path,
    frame: Option<&'f Frame<'f>>,
}

impl<'f> Iterator for FrameSites<'f> {
    type Item = (&'f Frame<'f>, Path);

    fn next(&mut self) -> Option<Self::Item> {
        let f = self.frame?;
        self.search = if self.current_root == self.search {
            f.requested_path.clone()
        } else {
            f.requested_path
                .replace_prefix(&self.current_root, &self.search)
                .unwrap_or_else(|| f.requested_path.clone())
        };
        self.current_root = f.root_path.clone();
        self.frame = f.previous;
        Some((f, self.search.clone()))
    }
}

/// A queued unit of composition work on one node (C++ `Pcp_PrimIndexer::Task`).
///
/// [`take_best_task`](Indexer::take_best_task) drains the highest-priority task:
/// stronger [`kind`](Self::kind) first (C++ `Task::Type`), then a per-kind
/// tiebreak. The order-independent reference/payload/inherit tasks tiebreak on
/// node index; the variant tasks carry a [`variant`](Self::variant) set and
/// tiebreak on live node strength then `(vset_path, vset_num)` (C++
/// `Task::PriorityOrder`).
#[derive(Clone, PartialEq, Eq)]
struct Task {
    kind: TaskKind,
    node: NodeId,
    /// The variant set a variant task evaluates; `None` for every other kind.
    variant: Option<VariantTask>,
}

impl Task {
    /// A non-variant task on `node`.
    fn new(kind: TaskKind, node: NodeId) -> Self {
        Task {
            kind,
            node,
            variant: None,
        }
    }

    /// A variant task on `node` evaluating `vt`.
    fn variant(kind: TaskKind, node: NodeId, vt: VariantTask) -> Self {
        Task {
            kind,
            node,
            variant: Some(vt),
        }
    }
}

/// The variant set a variant task is evaluating (C++ `Task`'s `vsetPath` /
/// `vsetName` / `vsetNum`).
#[derive(Clone, PartialEq, Eq)]
struct VariantTask {
    /// The site path the variant set is authored at (the prim path for a local
    /// variant set).
    vset_path: Path,
    /// The variant set name.
    vset_name: Token,
    /// The set's position in the prim's `variantSetNames`; a lower number is
    /// stronger (C++ `vsetNum`).
    vset_num: u16,
}

/// The ported task kinds, ordered weakest-priority first so a higher
/// discriminant drains first (C++ `Task::Type`, whose numeric order runs
/// strongest-to-weakest). Variant tasks are weaker than implied classes: a
/// variant selection can depend on a stronger arc, so the arc structure is
/// composed before variants resolve.
// The `Eval` prefix mirrors the C++ `Task::Type` names.
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum TaskKind {
    /// A variant set whose fallback search also came up empty; a placeholder
    /// kept only so [`retry_variant_tasks`](Indexer::retry_variant_tasks) can
    /// re-promote it once a newly selected variant introduces opinions.
    EvalNodeVariantNoneFound,
    /// Evaluate the fallback selection for a variant set with no authored one.
    EvalNodeVariantFallback,
    /// Evaluate the authored selection for a variant set.
    EvalNodeVariantAuthored,
    /// Find the variant sets authored at a node's site.
    EvalNodeVariantSets,
    /// The ancestral analog of [`EvalNodeVariantNoneFound`](Self::EvalNodeVariantNoneFound):
    /// a fallback search for a variant set authored above the node came up empty.
    EvalNodeAncestralVariantNoneFound,
    /// Evaluate the fallback selection for an ancestral variant set.
    EvalNodeAncestralVariantFallback,
    /// Evaluate the authored selection for an ancestral variant set.
    EvalNodeAncestralVariantAuthored,
    /// Find the variant sets authored at a node's namespace ancestors, then
    /// re-expand them at the node's depth (C++ `_EvalNodeAncestralVariantSets`).
    /// Stronger than the local variant band but weaker than implied classes, so a
    /// sub-index's ancestral variant selection resolves after its arc structure.
    EvalNodeAncestralVariantSets,
    /// Propagate a node's class-based children one level up toward the root.
    EvalImpliedClasses,
    /// Copy the specializes nodes in a grafted subtree under the root for
    /// strength ordering (C++ `EvalImpliedSpecializes`). Weaker than
    /// `EvalNodeSpecializes` but stronger than the implied-class cascade, so a
    /// specializes arc is fully composed before its copy is placed.
    EvalImpliedSpecializes,
    /// Evaluate the specializes authored at the node's site.
    EvalNodeSpecializes,
    /// Evaluate the inherits authored at the node's site.
    EvalNodeInherits,
    /// Evaluate the payloads authored at the node's site.
    EvalNodePayloads,
    /// Evaluate the references authored at the node's site.
    EvalNodeReferences,
    /// Propagate a relocate arc up to the grandparent (C++ `EvalImpliedRelocations`,
    /// task bit `1<<1`).
    EvalImpliedRelocations,
    /// Add a relocate arc back to the source for a node at a relocation target
    /// (C++ `EvalRelocations`, task bit `1<<0`, the strongest task).
    EvalNodeRelocations,
}

/// The result of composing one prim: the graph and the recoverable composition
/// errors recorded along the way (C++ `Pcp_PrimIndexer`'s `allErrors`).
///
/// The graph is `None` only for an unestablished seed or the runaway-depth
/// backstop, which the cache treats as an empty prim index. An arc whose target
/// cannot be resolved is recorded in `errors` and skipped, so the prim still
/// composes — the errors travel alongside a real graph, not in place of it. A
/// nested sub-build returns its own [`BuildOutput`]; the caller merges its
/// `errors` into its own before using the `graph`.
pub(crate) struct BuildOutput {
    pub(crate) graph: Option<PrimIndexGraph>,
    pub(crate) errors: Vec<Error>,
    /// [`Demand`]s raised by a reference/payload arc whose target layer is not
    /// yet loaded. Non-empty means the build is incomplete and its `graph` must
    /// not be cached; the cache loads these and recomposes.
    pub(crate) pending_loads: Vec<Demand>,
}

/// The shared, read-only inputs to a prim build — the same across every nested
/// sub-build (C++ `PcpPrimIndexInputs` plus the `PcpCache` it reads). All
/// borrows, so it is `Copy` and threads into a sub-build unchanged.
#[derive(Clone, Copy)]
struct Inputs<'a> {
    /// The layer stack being composed.
    stack: &'a LayerGraph,
    /// Composition context flowing from the parent prim (variant selections /
    /// fallbacks, instance depth, denied prefixes, ancestor arcs).
    ctx: &'a CompositionContext,
    /// Cached prim indices from the composition cache. The parent prim's index
    /// is read from here to seed this child's graph (C++
    /// `_BuildInitialPrimIndexFromAncestor`).
    cached_indices: &'a sdf::PathTable<PrimEntry>,
}

/// The site this build composes (C++ `PcpLayerStackSite`): the layer stack the
/// root `L` site scans together with the prim path, set per (sub-)build.
struct Site {
    /// Handle to the layer stack the root `L` site scans (the stage root layer
    /// stack for a stage prim, or a referenced asset's sublayer stack for an arc
    /// target). Resolve to members through [`Inputs::stack`]. When this is
    /// [`LayerStackId::Root`] the build composes against the stage root layer
    /// stack — the only case where the stage-keyed `cached_indices` apply.
    ambient: LayerStackId,
    /// The path this build composes — the graph's local-root site path. Set at
    /// the start of [`build`](Indexer::build) and used as the current-graph root
    /// in cross-frame duplicate-node lookups.
    path: Path,
}

/// Composes a single prim by draining a task queue over a composition graph
/// grown node-by-node (C++ `Pcp_PrimIndexer`).
///
/// All borrowed inputs are shared references, so each build is an independent
/// pure function over the layer stack and incoming context (Rayon-friendly —
/// see the `TODO(rayon)` on the cross-prim driver in `index_cache.rs`).
pub(crate) struct Indexer<'a, 'f> {
    /// Shared read-only inputs (layer stack, context, cached indices).
    inputs: Inputs<'a>,
    /// The site (ambient layer stack + path) this build composes.
    site: Site,
    /// The parent frame for a recursive sub-index build, or `None` at the
    /// top-level build (C++ `Pcp_PrimIndexer::previousFrame`).
    frame: Option<&'f Frame<'f>>,
    /// Sub-index nesting depth; a build exceeding [`MAX_DEPTH`] is abandoned,
    /// bounding true composition cycles.
    frame_depth: usize,
    /// The graph grown so far.
    output: PrimIndexGraph,
    /// Open composition tasks. The highest-priority task is selected on each
    /// drain by [`take_best_task`](Self::take_best_task) (C++ `Pcp_PrimIndexer`'s
    /// `Task::PriorityOrder` heap) rather than a fixed `Ord`, because variant
    /// tasks break ties by live node strength, which a standalone `Ord` cannot
    /// see.
    tasks: Vec<Task>,
    /// `(node, kind)` pairs already enqueued for an implied-class or
    /// implied-specializes task (C++ `taskUniq`): implied propagation re-reaches
    /// the same node from several arcs, so the task is deduplicated to avoid
    /// redundant work. Keyed by kind so a node can carry one of each.
    implied_seen: HashSet<(NodeId, TaskKind)>,
    /// Whether this build's root (local) node may contribute its own specs (C++
    /// `rootNodeShouldContributeSpecs`). A relocation source is composed as a
    /// sub-index with this `false`, so its direct site is inert (salted earth)
    /// while its ancestral arc children still contribute (spooky ancestors).
    root_contributes: bool,
    /// Recoverable composition errors collected during the build (C++
    /// `Pcp_PrimIndexer`'s `allErrors`). An arc whose target cannot be resolved
    /// records its error here and contributes nothing, so the rest of the prim
    /// still composes; the cache retains these as stage composition diagnostics.
    /// Errors from nested sub-builds are merged in at their call sites.
    errors: Vec<Error>,
    /// [`Demand`]s a reference/payload arc raised for a target layer that is not
    /// yet loaded. Returned in [`BuildOutput`] (like [`errors`](Self::errors)) —
    /// a non-empty list means the build is incomplete and its graph must not be
    /// cached; the cache loads these and recomposes. Nested sub-builds merge
    /// theirs up at their call sites.
    pending_loads: Vec<Demand>,
    /// Invalid-opinion-at-relocation-source errors deferred until the build
    /// finishes, paired with the relocate node they were detected on. A relocate
    /// composed under a culled branch (an empty ancestral reference at the
    /// relocation target) reports no error, so only entries whose node survives
    /// (is not culled) are kept — matching C++'s per-contributing-arc reporting.
    pending_relocation_errors: Vec<(NodeId, Error)>,
}

impl<'a, 'f> Indexer<'a, 'f> {
    pub(crate) fn new(
        stack: &'a LayerGraph,
        ctx: &'a CompositionContext,
        cached_indices: &'a sdf::PathTable<PrimEntry>,
        ambient: LayerStackId,
    ) -> Self {
        Self {
            inputs: Inputs {
                stack,
                ctx,
                cached_indices,
            },
            site: Site {
                ambient,
                path: Path::abs_root(),
            },
            frame: None,
            frame_depth: 0,
            output: PrimIndexGraph::default(),
            tasks: Vec::new(),
            implied_seen: HashSet::new(),
            root_contributes: true,
            errors: Vec::new(),
            pending_loads: Vec::new(),
            pending_relocation_errors: Vec::new(),
        }
    }

    /// Composes `path` into a prim index graph, returning the graph and the
    /// recoverable composition errors collected along the way (an arc whose
    /// target cannot be resolved is recorded and skipped, so the rest of the prim
    /// still composes). The graph is `None` when the seed cannot be established or
    /// the runaway nesting backstop trips, which the cache treats as an empty prim
    /// index. A composition cycle is likewise recorded as [`Error::ArcCycle`] and
    /// the cycle-closing arc dropped (by [`class_arc_is_cycle`](Self::class_arc_is_cycle)
    /// for inherits/specializes and [`arc_target_in_bounds`](Self::arc_target_in_bounds)
    /// for references/payloads), so the rest of the prim still composes.
    pub(crate) fn build(mut self, path: &Path) -> BuildResult<BuildOutput> {
        // Backstop pathological growth that site-identity cycle detection cannot
        // catch — an unbounded chain of ever-deeper sites that never repeats.
        if self.frame_depth > MAX_DEPTH {
            return Ok(BuildOutput {
                graph: None,
                errors: self.errors,
                pending_loads: self.pending_loads,
            });
        }
        self.site.path = path.clone();

        // Seed the graph: a root prim starts empty (just its local site); a
        // child prim clones its parent's graph for ancestral opinions.
        if !self.seed(path)? {
            return Ok(BuildOutput {
                graph: None,
                errors: self.errors,
                pending_loads: self.pending_loads,
            });
        }

        // The local (root) site is made inert — neither contributing opinions
        // nor expressing arcs — in two cases:
        //   * a relocation source composed as a sub-index (salted earth drops
        //     the source's own opinion while its ancestral arc children still
        //     contribute, C++ `rootNodeShouldContributeSpecs`);
        //   * a prim inside an instance (spec 11.3.3): an instance descendant's
        //     local opinions and the arcs they spawn are discarded, so the
        //     subtree composes only from the shared arcs the instance brings in.
        if !self.root_contributes || self.inputs.ctx.within_instance() {
            let local_root = self.output.local_root();
            if local_root.is_valid() {
                self.output.nodes[local_root.idx()].flags |= NodeFlags::INERT;
                // A relocate source / salted-earth root is restricted at its own
                // depth so its ancestral opinions still contribute (the spooky
                // ancestors a relocation pulls through, C++
                // `rootNodeShouldContributeSpecs == false` → restriction depth =
                // the source path's element count). An instance descendant is
                // fully suppressed instead, so it keeps the depth-0 inert default.
                if !self.root_contributes {
                    self.output.nodes[local_root.idx()].restriction_depth = path.element_count() as u16;
                }
            }
        }

        // Salted-earth prohibition (C++ `_ElidePrimIndexIfProhibited`): if a
        // non-inert node sits at a relocation source in its layer stack, this
        // prim is a prohibited namespace child and contributes nothing.
        if self.elide_if_prohibited() {
            self.output.finalize_strength_order();
            return Ok(BuildOutput {
                graph: Some(self.output),
                errors: self.errors,
                pending_loads: self.pending_loads,
            });
        }

        // Recompute `has_specs` at the seeded paths and enqueue the spec-bearing
        // nodes' expressed-arc tasks (the root node and every cloned ancestral one).
        self.scan_and_enqueue();

        // Drain the queue. Each handler may append nodes and enqueue further
        // work; a not-yet-ported case leaves its arc uncomposed (see the
        // `TODO`s in the handlers) rather than aborting the whole prim.
        while let Some(task) = self.take_best_task() {
            match task.kind {
                TaskKind::EvalNodeRelocations => self.eval_node_relocations(task.node)?,
                TaskKind::EvalImpliedRelocations => self.eval_implied_relocations(task.node)?,
                TaskKind::EvalNodeReferences | TaskKind::EvalNodePayloads => self.eval_arcs(task.node, task.kind)?,
                TaskKind::EvalNodeInherits => {
                    self.eval_class_arcs(task.node, FieldKey::InheritPaths, ArcType::Inherit)?
                }
                TaskKind::EvalNodeSpecializes => {
                    self.eval_class_arcs(task.node, FieldKey::Specializes, ArcType::Specialize)?
                }
                TaskKind::EvalImpliedClasses => {
                    self.implied_seen.remove(&(task.node, TaskKind::EvalImpliedClasses));
                    self.eval_implied_classes(task.node)?;
                }
                TaskKind::EvalImpliedSpecializes => {
                    self.implied_seen.remove(&(task.node, TaskKind::EvalImpliedSpecializes));
                    self.eval_implied_specializes(task.node)?;
                }
                TaskKind::EvalNodeVariantSets => self.eval_node_variant_sets(task.node)?,
                TaskKind::EvalNodeAncestralVariantSets => self.eval_node_ancestral_variant_sets(task.node)?,
                TaskKind::EvalNodeVariantAuthored => {
                    self.eval_node_authored_variant(task.node, &task.variant, false)?
                }
                TaskKind::EvalNodeAncestralVariantAuthored => {
                    self.eval_node_authored_variant(task.node, &task.variant, true)?
                }
                TaskKind::EvalNodeVariantFallback => {
                    self.eval_node_fallback_variant(task.node, &task.variant, false)?
                }
                TaskKind::EvalNodeAncestralVariantFallback => {
                    self.eval_node_fallback_variant(task.node, &task.variant, true)?
                }
                // Placeholders kept only for `retry_variant_tasks`; nothing to do.
                TaskKind::EvalNodeVariantNoneFound | TaskKind::EvalNodeAncestralVariantNoneFound => {}
            }
        }

        // Keep only the relocation-source-opinion errors whose relocate node
        // survived composition; one composed under a culled branch (an empty
        // ancestral reference at the relocation target) reports nothing.
        for (node, error) in std::mem::take(&mut self.pending_relocation_errors) {
            if !self.output.nodes[node.idx()].is_culled() {
                self.errors.push(error);
            }
        }

        // Specializes nodes were copied under the local root (C++
        // `_PropagateNodeToRoot`), so the strength-order DFS places that
        // globally-weak band (spec 10.4.1) last.
        self.output.finalize_strength_order();
        Ok(BuildOutput {
            graph: Some(self.output),
            errors: self.errors,
            pending_loads: self.pending_loads,
        })
    }

    /// Builds the initial graph for `path` (C++ `_BuildInitialPrimIndexFromAncestor`
    /// plus the root-node setup). Returns `false` to abandon the prim.
    ///
    /// A root prim (parent is the pseudo-root) seeds an empty graph with just its
    /// local site. A child prim clones its already-composed parent's graph and
    /// deepens every site path by the child name, so the references and payloads
    /// an ancestor introduced re-evaluate at this prim's depth.
    /// A representative layer id for the synthetic, inert tree root. The root
    /// never contributes opinions, so any ambient member serves; this keeps its
    /// `same_site`/dump identity sensible.
    fn root_layer_id(&self) -> LayerId {
        self.inputs.stack.layer_stack_root(self.site.ambient)
    }

    fn seed(&mut self, path: &Path) -> BuildResult<bool> {
        let parent = path.parent();
        let needs_ancestor = matches!(&parent, Some(p) if p != &Path::abs_root());

        if !needs_ancestor {
            // Root prim: synthetic inert root plus a local site scanning ambient.
            self.output
                .init_root(self.site.ambient, self.root_layer_id(), path.clone());
            self.add_local_root(path);
            return Ok(true);
        }

        let parent = parent.expect("checked by needs_ancestor");
        // The parent's composed graph seeds this child. At the top-level build
        // in the stage root layer stack it is read from the stage cache; in a
        // recursive sub-index build it is composed afresh in the same ambient,
        // reusing the frame chain so duplicate-node skipping (C++
        // `_BuildInitialPrimIndexFromAncestor`'s else-branch
        // `Pcp_BuildPrimIndex(parentSite, …, previousFrame)`) applies.
        let graph = if self.frame.is_none() && self.site.ambient == LayerStackId::Root {
            let Some(parent_index) = self.inputs.cached_indices.get(&parent).map(|e| &e.index) else {
                return Ok(false);
            };
            parent_index.graph().clone()
        } else {
            let Some(graph) = self.merge_subindex(self.compose_ancestral_subindex(&parent)?) else {
                return Ok(false);
            };
            graph
        };

        // Only a graph composed entirely of ported arcs can be deepened
        // structurally. Relocate nodes (and the culled subtrees relocation
        // elision produces) deepen like any other site: the deepened relocate
        // node re-evaluates through the queue, carrying the relocation source's
        // ancestral opinions to the child. Inherit, specialize, and variant
        // nodes (and the inert implied-class placeholders) likewise deepen and
        // re-evaluate (C++ `AddTasksForRootNode`'s recursive `_ScanArcs`).
        if graph.nodes.iter().any(|n| {
            !n.is_inert()
                && !n.is_culled()
                && !matches!(
                    n.arc,
                    ArcType::Root
                        | ArcType::Reference
                        | ArcType::Payload
                        | ArcType::Inherit
                        | ArcType::Specialize
                        | ArcType::Variant
                        | ArcType::Relocate
                )
        }) {
            return Ok(false);
        }
        self.output = graph;
        // Deepening keeps each cloned node's full site layer stack; the set of
        // layers that author a spec changes at the deeper path, so `has_specs`
        // is recomputed for every node by `scan_and_enqueue`.
        self.output.append_child_name_to_all_sites(path);

        // The parent may have had no local opinion, leaving no Root site to
        // become this child's local root. Ensure one exists so a local opinion
        // authored only at this child still composes.
        if !self.output.local_root().is_valid() {
            self.add_local_root(path);
        }
        Ok(true)
    }

    /// Adds the prim's local site: a `Root` node over the full ambient layer
    /// stack. Its `has_specs` is computed with every other node's in
    /// `scan_and_enqueue`.
    fn add_local_root(&mut self, path: &Path) {
        self.output.add_child(
            NodeId::INVALID,
            self.site.ambient,
            self.root_layer_id(),
            path.clone(),
            ArcType::Root,
            MapFunction::identity(),
            false,
        );
    }

    /// Whether duplicate-node skipping is in force for this build, taken from the
    /// frame the arc that spawned it created (C++ `previousFrame->skipDuplicateNodes`).
    /// The top-level build has no frame and never skips.
    fn frame_skip(&self) -> bool {
        self.frame.is_some_and(|f| f.skip)
    }

    /// Builds a nested sub-indexer one frame deeper, sharing this build's layer
    /// stack, context, and cache. The caller supplies the ambient stack and the
    /// parent-frame chain (which carries the duplicate-node skip flag).
    fn new_sub<'g>(
        &self,
        ambient: LayerStackId,
        frame: Option<&'g Frame<'g>>,
        root_contributes: bool,
    ) -> Indexer<'a, 'g> {
        let mut sub = Indexer::new(self.inputs.stack, self.inputs.ctx, self.inputs.cached_indices, ambient);
        sub.frame = frame;
        sub.frame_depth = self.frame_depth + 1;
        sub.root_contributes = root_contributes;
        sub
    }

    /// Composes the ancestral parent of a sub-index in the same ambient,
    /// reusing the current frame chain (C++ `_BuildInitialPrimIndexFromAncestor`'s
    /// else-branch `Pcp_BuildPrimIndex(parentSite, …, previousFrame)`). Returns
    /// the composed graph (`None` when the parent cannot be composed — a cycle /
    /// unestablished seed) and the sub-build's recoverable errors, which the
    /// caller merges into its own.
    fn compose_ancestral_subindex(&self, parent: &Path) -> BuildResult<BuildOutput> {
        self.new_sub(self.site.ambient, self.frame, true).build(parent)
    }

    /// Composes an arc target as its own sub-index, including the ancestral
    /// opinions above the target (C++ `_AddArc`'s `includeAncestralOpinions`
    /// branch). A fresh [`Frame`] threads this graph back to the nested build so
    /// duplicate-node skipping can reach the nodes already composed here. Returns
    /// the composed graph (`None` when the target cannot be composed — a cycle /
    /// unestablished seed) and the sub-build's recoverable errors, which the
    /// caller merges into its own.
    fn compose_subindex(
        &self,
        target: &Path,
        ambient: LayerStackId,
        skip: bool,
        root_contributes: bool,
        arc: ArcType,
    ) -> BuildResult<BuildOutput> {
        let requested_layer = self.inputs.stack.layer_stack_root(ambient);
        let frame = Frame {
            requested_path: target.clone(),
            root_path: self.site.path.clone(),
            graph: &self.output,
            arc,
            requested_layer,
            skip,
            previous: self.frame,
        };
        self.new_sub(ambient, Some(&frame), root_contributes).build(target)
    }

    /// Merges a completed sub-build's recoverable errors into this build and
    /// returns its graph, so each call site handles only the `Option<graph>`.
    fn merge_subindex(&mut self, out: BuildOutput) -> Option<PrimIndexGraph> {
        self.errors.extend(out.errors);
        // A layer demanded only inside the sub-build is still needed to compose
        // this prim, so carry the demand up even when the sub-build's graph is
        // `None` (the sub-build was itself left incomplete by the missing layer).
        self.pending_loads.extend(out.pending_loads);
        // A muted target reached only inside the sub-build is still a dependency
        // of this prim, so carry its trace up before the graph is grafted.
        if let Some(graph) = &out.graph {
            self.output
                .muted_external_targets
                .extend(graph.muted_external_targets.iter().copied());
        }
        out.graph
    }

    /// Composes an arc target as its own ancestral sub-index and grafts it under
    /// `parent` (C++ `_AddArc`'s `includeAncestralOpinions` branch +
    /// `InsertChildSubgraph`), returning the grafted arc node. The grafted
    /// subtree's implied classes still need to cascade up the new arc, and its
    /// variants were skipped in the nested build, so
    /// [`add_grafted_subtree_tasks`](Self::add_grafted_subtree_tasks) enqueues
    /// both. Returns `None` when the target cannot be composed (a cycle) or has
    /// no single local root to graft.
    #[allow(clippy::too_many_arguments)]
    fn compose_and_graft(
        &mut self,
        target: &Path,
        ambient: LayerStackId,
        skip: bool,
        parent: NodeId,
        arc: ArcType,
        map: MapFunction,
        origin: NodeId,
        sibling: u16,
    ) -> BuildResult<Option<NodeId>> {
        let Some(sub) = self.merge_subindex(self.compose_subindex(target, ambient, skip, true, arc)?) else {
            return Ok(None);
        };
        let Some(grafted) = self.graft_subindex(&sub, parent, arc, map, origin, sibling) else {
            return Ok(None);
        };
        self.add_grafted_subtree_tasks(grafted);
        Ok(Some(grafted))
    }

    /// Whether a node at the arc target site `(rep_layer, site_path)` already
    /// exists in this graph or a parent frame's graph (C++ `_AddArc`'s
    /// `skipDuplicateNodes` search). Adding a duplicate would introduce the same
    /// site twice; class arcs and arcs composed inside a skip sub-build skip it.
    ///
    /// The current graph is searched at the target path; each parent frame is
    /// searched at the path the site takes once deepened by the suffix that
    /// frame's request adds (C++'s `ReplacePrefix` across the stack frame).
    fn find_duplicate(&self, rep_layer: LayerId, site_path: &Path) -> bool {
        if self.output.node_using_site(rep_layer, site_path).is_some() {
            return true;
        }
        self.frame_sites(site_path)
            .any(|(f, search)| f.graph.node_using_site(rep_layer, &search).is_some())
    }

    /// Iterates the parent frame chain, deepening `target` into each frame's
    /// namespace (C++ `PcpPrimIndex_StackFrameIterator`). See [`FrameSites`].
    fn frame_sites(&self, target: &Path) -> FrameSites<'f> {
        FrameSites {
            search: target.clone(),
            current_root: self.site.path.clone(),
            frame: self.frame,
        }
    }

    /// Grafts a composed sub-index under `parent` (C++ `InsertChildSubgraph`).
    ///
    /// The source's local root becomes the arc node, carrying `root_map`,
    /// `origin`, `sibling`, and the parent site's namespace depth; every
    /// internal node keeps its own arc, map-to-parent, and strength metadata,
    /// with node handles remapped into this graph. Returns the grafted arc node,
    /// or `None` when the source has no single local root to graft (an extra
    /// root-level arc a later phase grafts individually).
    fn graft_subindex(
        &mut self,
        source: &PrimIndexGraph,
        parent: NodeId,
        arc: ArcType,
        root_map: MapFunction,
        origin: NodeId,
        sibling: u16,
    ) -> Option<NodeId> {
        let local_root = source.local_root();
        if !local_root.is_valid() {
            return None;
        }
        // The source local root is the lone contributing child of the source's
        // synthetic root; a second one means extra root-level arcs to graft.
        let synthetic = source.root;
        let extra_roots = source[synthetic.idx()]
            .children()
            .iter()
            .any(|&c| c != local_root && !source[c.idx()].is_inert());
        if extra_roots {
            return None;
        }

        // Every node reached through a specializes arc is globally weak (spec
        // 10.4.1), so a specializes graft marks the whole grafted subtree
        // `HAS_SPECIALIZES`; the source composed it as an ordinary sub-index, so
        // its nodes do not carry the flag yet.
        let weak = arc == ArcType::Specialize;
        let parent_depth = self.node(parent).path.prim_element_count() as u16;
        let mut remap: Vec<Option<NodeId>> = vec![None; source.nodes.len()];
        let mut grafted_root = NodeId::INVALID;
        // The arena is append-only, so a node's parent always precedes it and is
        // already remapped when its turn comes.
        for sid in 0..source.nodes.len() {
            if sid == synthetic.idx() {
                continue;
            }
            let node = &source.nodes[sid];
            // The local root becomes the arc node, taking the arc's identity and
            // the parent site's strength metadata; every other node keeps its own
            // arc and metadata, with its parent and origin remapped into this
            // graph.
            let (struct_parent, node_map, node_arc, node_sibling, node_depth, node_origin) = if sid == local_root.idx()
            {
                (parent, root_map.clone(), arc, sibling, parent_depth, Some(origin))
            } else {
                let grafted_parent = node.parent().and_then(|p| remap[p.idx()]).unwrap_or(parent);
                let grafted_origin = node.origin().and_then(|o| remap[o.idx()]).or(Some(grafted_parent));
                (
                    grafted_parent,
                    node.map_to_parent.clone(),
                    node.arc,
                    node.sibling_num_at_origin,
                    node.namespace_depth,
                    grafted_origin,
                )
            };
            let new_id = self.output.add_child(
                struct_parent,
                node.layer_stack_id(),
                node.layer_id(),
                node.path.clone(),
                node_arc,
                node_map,
                false,
            );
            let n = &mut self.output.nodes[new_id.idx()];
            n.has_specs = node.has_specs;
            n.flags = node.flags;
            n.restriction_depth = node.restriction_depth;
            if weak {
                n.flags |= NodeFlags::HAS_SPECIALIZES;
            }
            n.sibling_num_at_origin = node_sibling;
            n.namespace_depth = node_depth;
            n.origin = node_origin;
            remap[sid] = Some(new_id);
            if sid == local_root.idx() {
                grafted_root = new_id;
            }
        }
        Some(grafted_root)
    }

    /// Computes `has_specs` at each non-inert node's path and enqueues the
    /// expressed-arc tasks for the spec-bearing nodes (C++ `AddTasksForRootNode`
    /// → `_AddTasksForNodeRecursively`, restricted to the ported tasks). A node
    /// with no spec at its path authors no arc, so it gets no task.
    ///
    /// Only the expressed-arc tasks are enqueued, not implied-class/specializes
    /// propagation: the seed is the cloned, already-composed ancestor graph
    /// (C++ `_BuildInitialPrimIndexFromAncestor`), whose implied classes and
    /// propagated specializes copies are inherited from the clone. The implied
    /// tasks are added per-arc by [`add_tasks_for_node`](Self::add_tasks_for_node)
    /// as arcs are newly composed (C++ keeps them off the root-node task list).
    fn scan_and_enqueue(&mut self) {
        for i in 0..self.output.nodes.len() {
            if self.output.nodes[i].is_inert() {
                continue;
            }
            let node = NodeId(i as u32);
            let has_specs = self.stack_has_spec(self.output.nodes[i].layer_stack_id(), &self.output.nodes[i].path);
            self.output.nodes[i].has_specs = has_specs;
            if has_specs {
                self.add_expressed_arc_tasks(node);
            }
            // Relocations are evaluated regardless of whether the node authors a
            // spec (C++ `CanContributeSpecs` does not require `HasSpecs`).
            self.enqueue_relocations(node);
        }
    }

    /// Enqueues a node's expressed-arc tasks (C++ `_AddTasksForNodeRecursively`'s
    /// task loop, restricted to the ported tasks): references, payloads,
    /// inherits, specializes, and — at the top level — the node's own variant
    /// sets. The implied-class/specializes tasks are added separately by
    /// [`add_tasks_for_node`](Self::add_tasks_for_node) when an arc is composed.
    fn add_expressed_arc_tasks(&mut self, node: NodeId) {
        self.tasks.push(Task::new(TaskKind::EvalNodeReferences, node));
        if self.inputs.ctx.load_payloads {
            self.tasks.push(Task::new(TaskKind::EvalNodePayloads, node));
        }
        self.tasks.push(Task::new(TaskKind::EvalNodeInherits, node));
        self.tasks.push(Task::new(TaskKind::EvalNodeSpecializes, node));
        // The node's own (local) variant sets. A recursive sub-build defers
        // variants to the top-level build (C++ `evaluateVariantsAndDynamicPayloads
        // == false`), so a node composed inside a frame enqueues no variant work.
        // Ancestral variant sets are added only when a sub-index is grafted (C++
        // `_AddArc`'s `includeAncestralOpinions` branch), not here.
        if self.frame.is_none() {
            self.tasks.push(Task::new(TaskKind::EvalNodeVariantSets, node));
        }
    }

    /// Enqueues a newly-composed node's implied-class/specializes propagation
    /// ([`add_implied_tasks_for_node`](Self::add_implied_tasks_for_node)) and its
    /// expressed-arc tasks ([`add_expressed_arc_tasks`](Self::add_expressed_arc_tasks)),
    /// the full task set for an arc node (C++ `AddTasksForNode`, restricted to
    /// the ported tasks).
    fn add_tasks_for_node(&mut self, node: NodeId) {
        self.add_implied_tasks_for_node(node);
        self.add_expressed_arc_tasks(node);
        self.enqueue_relocations(node);
    }

    /// Enqueues the implied-class and implied-specializes propagation a node
    /// triggers (C++ `AddTasksForNode`'s `EvalImpliedClasses` /
    /// `EvalImpliedSpecializes` arms).
    ///
    /// A class-based node propagates the whole class hierarchy it starts from
    /// (`_FindStartingNodeForImpliedClasses`); a non-class node that picked up
    /// class-based children (from a referenced subtree) propagates them from
    /// itself. A grafted subtree carrying specializes needs them copied to the
    /// root; only the top-level build does this (C++ `evaluateImpliedSpecializes`),
    /// a nested sub-build defers it until its graph is grafted.
    fn add_implied_tasks_for_node(&mut self, node: NodeId) {
        if is_class_based_arc(self.node(node).arc) {
            let start = self.find_starting_node_for_implied_classes(node);
            self.enqueue_implied(start);
        } else if self.has_class_based_child(node) {
            self.enqueue_implied(node);
        }
        if self.frame.is_none() && self.has_specialize_in_subtree(node) {
            self.enqueue_implied_specializes(node);
        }
    }

    /// Enqueues the tasks a freshly-grafted ancestral sub-index needs (C++
    /// `_AddArc`'s `AddTasksForNode` with `ExpressedArcTasks` stripped): the
    /// grafted root's implied-class/specializes propagation, plus — for every
    /// node in the grafted subtree at the top-level build — its local and
    /// ancestral variant sets.
    ///
    /// The nested build already evaluated references, payloads, inherits, and
    /// specializes on the subtree, but skipped all variants
    /// (`evaluateVariantsAndDynamicPayloads == false`); since the arc included
    /// ancestral opinions, the top-level build must (re-)evaluate both the local
    /// variant sets and the variant sets authored above each grafted node (C++
    /// `_EvalNodeAncestralVariantSets`).
    fn add_grafted_subtree_tasks(&mut self, root: NodeId) {
        self.add_implied_tasks_for_node(root);
        // Relocations are evaluated on every grafted node, including in a nested
        // sub-build (unlike variants, which the top-level build defers).
        for id in self.subtree_nodes(root) {
            self.enqueue_relocations(id);
        }
        if self.frame.is_some() {
            return;
        }
        // C++ `_AddTasksForNodeRecursively` visits every node in the grafted
        // subtree, inert ones included: a relocate source is inert at its own
        // site yet still feeds the ancestral variant sets above it. The handlers
        // gate per node (local sets need a contributing site, ancestral sets a
        // permissive restriction depth), so enqueuing unconditionally is safe.
        for id in self.subtree_nodes(root) {
            self.tasks.push(Task::new(TaskKind::EvalNodeVariantSets, id));
            self.tasks.push(Task::new(TaskKind::EvalNodeAncestralVariantSets, id));
        }
    }

    /// Removes and returns the highest-priority open task (C++
    /// `Pcp_PrimIndexer`'s `Task::PriorityOrder` pop). Selection is a linear scan
    /// because the per-prim task count is small and variant ties consult live
    /// node strength (see [`task_priority_cmp`](Self::task_priority_cmp)).
    fn take_best_task(&mut self) -> Option<Task> {
        let best = (0..self.tasks.len()).max_by(|&i, &j| self.task_priority_cmp(&self.tasks[i], &self.tasks[j]))?;
        Some(self.tasks.swap_remove(best))
    }

    /// Orders two tasks by drain priority — the greater task drains first (C++
    /// `Task::PriorityOrder`, inverted because that comparator sorts weak-first).
    /// Stronger task kind wins. Within a kind, the authored/fallback variant
    /// tasks break ties by live node strength (a stronger node's selection wins),
    /// then a lower `vset_num` for the same node; every other kind tiebreaks on
    /// node index.
    fn task_priority_cmp(&self, a: &Task, b: &Task) -> Ordering {
        if a.kind != b.kind {
            return a.kind.cmp(&b.kind);
        }
        match a.kind {
            TaskKind::EvalNodeVariantAuthored
            | TaskKind::EvalNodeVariantFallback
            | TaskKind::EvalNodeAncestralVariantAuthored
            | TaskKind::EvalNodeAncestralVariantFallback => {
                if a.node != b.node {
                    // The stronger node drains first: it is the "greater" task,
                    // so reverse `compare_node_strength` (which returns `Less`
                    // for the stronger node).
                    return self.output.compare_node_strength(b.node, a.node);
                }
                // Same node: a lower `vset_num` is stronger, so it must be the
                // greater task — order by the descending key.
                Self::variant_key(b).cmp(&Self::variant_key(a))
            }
            TaskKind::EvalNodeVariantNoneFound | TaskKind::EvalNodeAncestralVariantNoneFound => {
                // A placeholder; only a consistent, distinct order is needed.
                (b.node, Self::variant_key(b)).cmp(&(a.node, Self::variant_key(a)))
            }
            TaskKind::EvalImpliedClasses => {
                // Ancestors drain after their descendants (C++
                // `Task::PriorityOrder`'s `EvalImpliedClasses` case): the
                // descendant is the greater task.
                if b.node > a.node && self.output.is_ancestor_of(a.node, b.node) {
                    return Ordering::Less;
                }
                if a.node > b.node && self.output.is_ancestor_of(b.node, a.node) {
                    return Ordering::Greater;
                }
                // Otherwise the strongest implied arc drains first, so its
                // implied node keeps the stronger origin (C++ keeps these tasks
                // in strong-to-weak order). `compare_node_strength` returns
                // `Less` for the stronger node, so reverse it to make the
                // stronger node the greater task.
                self.output.compare_node_strength(b.node, a.node)
            }
            _ => a.node.cmp(&b.node),
        }
    }

    /// The `(vset_path, vset_num)` strength key of a variant task. Called only
    /// from the variant arms of [`task_priority_cmp`](Self::task_priority_cmp),
    /// where the task always carries a [`VariantTask`].
    fn variant_key(task: &Task) -> (&str, u16) {
        let v = task.variant.as_ref().expect("variant task carries a VariantTask");
        (v.vset_path.as_str(), v.vset_num)
    }

    /// Enqueues an `EvalImpliedClasses` task, deduplicated per node (C++
    /// `taskUniq`).
    fn enqueue_implied(&mut self, node: NodeId) {
        if self.implied_seen.insert((node, TaskKind::EvalImpliedClasses)) {
            self.tasks.push(Task::new(TaskKind::EvalImpliedClasses, node));
        }
    }

    /// Enqueues an `EvalImpliedSpecializes` task, deduplicated per node.
    fn enqueue_implied_specializes(&mut self, node: NodeId) {
        if self.implied_seen.insert((node, TaskKind::EvalImpliedSpecializes)) {
            self.tasks.push(Task::new(TaskKind::EvalImpliedSpecializes, node));
        }
    }

    /// Enqueues an `EvalNodeRelocations` task for a node when the stack has any
    /// relocates (C++ `AddTasksForNode`'s `EvalRelocations` arm). The handler
    /// itself decides whether the node sits at a relocation target.
    fn enqueue_relocations(&mut self, node: NodeId) {
        if self.inputs.stack.has_relocates() && !self.node(node).is_inert() {
            self.tasks.push(Task::new(TaskKind::EvalNodeRelocations, node));
        }
    }

    /// Adds a relocate arc back to the source for a node sitting at a relocation
    /// target (C++ `_EvalNodeRelocations`). The source is composed as a
    /// sub-index with ancestral opinions, its direct site inert (salted earth),
    /// and grafted as a `Relocate` arc with an identity-stripping source→target
    /// map. Ancestral child subtrees the relocation supersedes are elided first.
    fn eval_node_relocations(&mut self, node: NodeId) -> BuildResult<()> {
        {
            let n = self.node(node);
            // C++ `CanContributeSpecs`: not inert/culled/permission-denied. A
            // spec-less node still relocates, so `has_specs` is not required.
            if n.is_inert() || n.is_culled() || n.is_permission_denied() {
                return Ok(());
            }
        }
        // A node grafted from a sub-index (e.g. an inherit target) already had its
        // relocation composed — and its source-opinion error reported — in that
        // sub-build, so it carries a `Relocate` child. The relocation is still
        // re-composed here (it does namespace work at this level), but the
        // source-opinion error must not be reported a second time.
        let already_relocated = self
            .node(node)
            .children()
            .iter()
            .any(|&c| self.node(c).arc == ArcType::Relocate);
        // Relocates are resolved against the node's own layer stack (C++
        // `node.GetLayerStack()->GetIncrementalRelocatesTargetToSource()`), keyed
        // by the node's path in that layer stack's namespace. This handles both
        // stage-level relocates and relocates authored inside a referenced asset
        // (the node then carries that asset's layers and namespace).
        let node_ambient = self.node(node).layer_stack_id();
        let node_path = self.node(node).path.clone();
        let Some(source) = self.inputs.stack.relocation_source(node_ambient, &node_path) else {
            return Ok(());
        };

        // A direct opinion authored at the source path (in the node's own layer
        // stack, not the content the relocation moves in) is invalid and ignored
        // by the salted-earth elision below (C++ `PcpErrorOpinionAtRelocationSource`).
        // The error is deferred until the build finishes and kept only if the
        // relocate node survives, so a relocate composed under a culled branch
        // reports nothing; `composing` is stamped by the cache.
        let opinion_layer = if already_relocated {
            None
        } else {
            self.inputs
                .stack
                .layer_stack(node_ambient)
                .iter()
                .find(|&&(li, _)| self.inputs.stack.layer(li).data().has_spec(&source))
                .map(|&(li, _)| self.inputs.stack.layer(li).identifier.clone())
        };

        // Ancestral arcs superseded by this relocation contribute nothing; a
        // variant may still override a relocated prim, so keep variant children
        // (C++ `_EvalNodeRelocations`'s per-child-arc-type switch).
        for child in self.node(node).children().to_vec() {
            if self.node(child).arc != ArcType::Variant {
                self.elide_subtree(child);
            }
        }

        // Compose the source as a sub-index (the relocation moves its content to
        // the target). Its root is salted-earth inert; opinions and implied
        // classes carried up across the relocate node translate the source
        // namespace to the target.
        let Some(sub) = self.merge_subindex(self.compose_subindex(
            &source,
            node_ambient,
            self.frame_skip(),
            false,
            ArcType::Relocate,
        )?) else {
            return Ok(());
        };

        // If the source prim itself is also a relocation source — the same prim
        // reached through its reference chain (a reference/payload node at the
        // source's own namespace level whose site is relocated away) — then
        // `source` is a prohibited child: relocating from it would resurrect
        // opinions that relocation moved (C++ `PcpErrorArcToProhibitedChild`,
        // "CANNOT be relocated from"). A relocation source reached by an *inherit*
        // (a symmetric-rig sibling) or sitting on a *descendant* is a different,
        // handled relocation, so the match is restricted to same-depth
        // reference/payload nodes. Drop and report it.
        let source_depth = source.prim_element_count();
        if let Some((reloc_source, reloc_layer)) = sub.nodes.iter().find_map(|n| {
            if n.path != source
                && matches!(n.arc, ArcType::Reference | ArcType::Payload)
                && n.path.prim_element_count() == source_depth
            {
                self.inputs
                    .stack
                    .relocation_source_layer(n.layer_stack_id(), &n.path)
                    .map(|l| (n.path.clone(), l.to_string()))
            } else {
                None
            }
        }) {
            let site_layer = self.introducing_layer(node);
            self.errors.push(Error::ProhibitedRelocationSource {
                arc: ArcType::Relocate,
                site: node_path.clone(),
                site_layer: site_layer.clone(),
                target: source.clone(),
                target_layer: site_layer,
                reloc_source,
                reloc_layer,
                composing: self.site.path.clone(),
            });
            return Ok(());
        }

        // The relocate node maps its source to the relocation target. The source
        // sub-index excludes this same relocate from its internal arc folds (see
        // `fold_relocates_into`), so the shift is applied once, here.
        let map = MapFunction::from_pair_identity(source.clone(), node_path);
        let Some(grafted) = self.graft_subindex(&sub, node, ArcType::Relocate, map, node, 0) else {
            return Ok(());
        };
        self.output.nodes[grafted.idx()].flags |= NodeFlags::RELOCATE_SOURCE;
        if let Some(layer) = opinion_layer {
            self.pending_relocation_errors.push((
                grafted,
                Error::OpinionAtRelocationSource {
                    source_path: source.clone(),
                    layer,
                    composing: self.site.path.clone(),
                },
            ));
        }
        self.add_grafted_subtree_tasks(grafted);
        self.tasks.push(Task::new(TaskKind::EvalImpliedRelocations, grafted));
        self.elide_relocated_subtrees(grafted);
        Ok(())
    }

    /// Carries a non-ancestral relocate up to the grandparent (C++
    /// `_EvalImpliedRelocations`): when the relocation source maps through the
    /// parent's arc into the grandparent's namespace, an inert `Relocate`
    /// placeholder is added on the grandparent so the class-based arcs implied up
    /// the graph still cross the relocation, and a sub-root reference to the
    /// grandparent still sees the relocated prim.
    ///
    /// The placeholder contributes no specs itself (C++ `_AddArc` with
    /// `directNodeShouldContributeSpecs = false`); its purpose is to give
    /// [`eval_implied_class_tree`](Self::eval_implied_class_tree)'s relocate
    /// branch a node to fold the relocation into, and to record the dependency on
    /// the source site. The grandparent mapping can fail — a sub-root reference
    /// whose domain excludes the source has no corresponding site there — and
    /// then there is no implied relocation (C++ `gpRelocSource.IsEmpty()`, the
    /// `SubrootReferenceAndRelocates` case).
    fn eval_implied_relocations(&mut self, node: NodeId) -> BuildResult<()> {
        // The task is enqueued solely from `eval_node_relocations` for a
        // freshly-grafted relocate node, so `node` is always a direct (non-
        // ancestral) relocate here (C++ `node.GetArcType() == PcpArcTypeRelocate
        // && !node.IsDueToAncestor()`).
        debug_assert_eq!(
            self.node(node).arc,
            ArcType::Relocate,
            "EvalImpliedRelocations is enqueued only for relocate nodes"
        );
        let Some(parent) = self.node(node).parent() else {
            return Ok(());
        };
        let Some(gp) = self.node(parent).parent() else {
            return Ok(());
        };
        // The synthetic tree root stands in for C++'s parentless root node: when
        // the relocate's parent is the local root, C++ sees no grandparent and
        // grafts nothing (a stage-level relocate onto a root-level prim).
        if gp == self.output.root {
            return Ok(());
        }

        // Map the relocation source (the relocate node's own path) up through the
        // parent's arc into the grandparent's namespace.
        let Some(gp_reloc_source) = self
            .node(parent)
            .map_to_parent
            .map_source_to_target(&self.node(node).path)
        else {
            return Ok(());
        };

        // Skip if the grandparent already carries this implied relocate, which
        // happens when the same relocation rides up several arcs (C++ scans the
        // grandparent's `Relocate` children for one at `gpRelocSource`).
        let already = self.node(gp).children().iter().any(|&c| {
            let cn = self.node(c);
            cn.arc == ArcType::Relocate && cn.path == gp_reloc_source
        });
        if already {
            return Ok(());
        }

        // Add the inert placeholder with an identity map and the relocate node as
        // its origin. Its site is exactly `(gp_layers, gp_reloc_source)`, so
        // `has_specs` is composed from those before they move into the node.
        let (gp_stack, gp_rep) = self.node_site(gp);
        let has_specs = self.stack_has_spec(gp_stack, &gp_reloc_source);
        let new_node = self.output.add_child(
            gp,
            gp_stack,
            gp_rep,
            gp_reloc_source,
            ArcType::Relocate,
            MapFunction::identity(),
            false,
        );
        let n = &mut self.output.nodes[new_node.idx()];
        n.origin = Some(node);
        // Inert for value resolution, but its site is a relocation source, so
        // `RELOCATE_SOURCE` keeps it in `dependency_nodes`: an edit at the source
        // must recompose the prim reached through the relocation.
        n.flags |= NodeFlags::INERT | NodeFlags::RELOCATE_SOURCE;
        // The placeholder contributes neither directly nor ancestrally (C++
        // `SetSpecContributionRestrictedDepth(1)`).
        n.restriction_depth = 1;
        n.has_specs = has_specs;
        // Cascade: the placeholder is itself a relocate node, so the relocation
        // keeps propagating up the next ancestor arc (C++ `AddTasksForNode` keeps
        // `EvalImpliedRelocations` for a relocate arc; `_ScanArcs` strips the
        // expressed-arc and `EvalNodeRelocations` tasks on this inert node). The
        // chain climbs one ancestor per step and stops at the `gp == root` guard,
        // so it terminates in the finite graph depth; the `already` dedup keeps
        // two relocations that converge on one grandparent from grafting twice.
        self.tasks.push(Task::new(TaskKind::EvalImpliedRelocations, new_node));
        Ok(())
    }

    /// Whether `node` is a live (non-inert, non-culled) node whose path is a
    /// relocation source in its OWN layer stack (C++
    /// `node.GetLayerStack()->GetIncrementalRelocatesSourceToTarget().find(node.GetPath())`).
    /// The per-node layer stack matters: a node from a referenced asset is in
    /// that asset's namespace, so it must not match a stage-namespace source that
    /// merely shares its path string.
    fn node_is_relocation_source(&self, node: NodeId) -> bool {
        let n = self.node(node);
        if n.is_inert() || n.is_culled() {
            return false;
        }
        self.inputs.stack.is_relocation_source(n.layer_stack_id(), &n.path)
    }

    /// Marks `root` and its whole subtree culled so they contribute no opinions
    /// (C++ `_ElideSubtree`). An unrestricted node's spec-contribution restriction
    /// depth is also pinned to 1, so a later ancestral task (notably an ancestral
    /// variant re-evaluated at the top level) sees the elided node as
    /// non-contributing and does not graft a live arc beneath it (C++
    /// `_ElideSubtree`'s `SetSpecContributionRestrictedDepth(1)`). A node already
    /// restricted at a deeper depth — a relocate source pinned to its own path
    /// depth so its spooky-ancestor opinions stay live (see the salted-earth
    /// `restriction_depth` assignment in [`build`](Self::build)) — keeps that
    /// depth; C++ guards the assignment with `if depth == 0` for the same reason.
    fn elide_subtree(&mut self, root: NodeId) {
        for id in self.subtree_nodes(root) {
            let n = &mut self.output.nodes[id.idx()];
            n.flags |= NodeFlags::CULLED;
            if n.restriction_depth == 0 {
                n.restriction_depth = 1;
            }
        }
    }

    /// Elides any subtree in a freshly-grafted relocation source whose own site
    /// is a relocation source moved elsewhere, so its opinions are not also
    /// attributed here (C++ `_ElideRelocatedSubtrees`).
    fn elide_relocated_subtrees(&mut self, root: NodeId) {
        if !self.inputs.stack.has_relocates() {
            return;
        }
        let mut stack: Vec<NodeId> = self.node(root).children().to_vec();
        while let Some(id) = stack.pop() {
            // A relocate child already elided its own relocated subtrees.
            if self.node(id).arc == ArcType::Relocate {
                continue;
            }
            if self.node_is_relocation_source(id) {
                self.elide_subtree(id);
                continue;
            }
            stack.extend(self.node(id).children().iter().copied());
        }
    }

    /// Returns true and elides the whole index when a non-inert node sits at a
    /// relocation source in its layer stack — the prim is a prohibited namespace
    /// child under the salted-earth policy (C++ `_ElidePrimIndexIfProhibited` /
    /// `_ComposeIsProhibitedPrimChild`). The synthetic root stays as an inert
    /// placeholder; every other node is force-culled.
    fn elide_if_prohibited(&mut self) -> bool {
        if !self.inputs.stack.has_relocates() {
            return false;
        }
        let prohibited = (0..self.output.nodes.len()).any(|i| self.node_is_relocation_source(NodeId(i as u32)));
        if !prohibited {
            return false;
        }
        let root = self.output.root;
        for (i, n) in self.output.nodes.iter_mut().enumerate() {
            if NodeId(i as u32) == root {
                n.flags |= NodeFlags::INERT;
            } else {
                n.flags |= NodeFlags::CULLED;
            }
        }
        true
    }

    /// Composes the references or payloads authored at `node`'s site and adds an
    /// arc for each (C++ `_EvalNodeReferences` / `_EvalNodePayloads`). Both
    /// resolve to a uniform `(asset, prim, offset)` list and share the arc-add
    /// loop.
    fn eval_arcs(&mut self, node: NodeId, kind: TaskKind) -> BuildResult<()> {
        // An inert node (an implied-class placeholder) contributes no opinions
        // and must not re-express the arcs its origin site already composed; an
        // implied inherit at the referencing prim's own path would otherwise
        // duplicate that prim's references (C++ keeps the placeholder inert).
        if self.node(node).is_inert() {
            return Ok(());
        }
        let expr_vars = self.composed_expr_vars(node);
        let site_path = self.node(node).path.clone();
        // Recoverable arc errors (an invalid asset-path expression) are collected
        // locally so the immutable borrow of `self` taken by the composers is
        // released before they are appended to `self.errors` below.
        let mut arc_errors: Vec<Error> = Vec::new();
        let (arc, arcs) = match kind {
            TaskKind::EvalNodeReferences => {
                let refs = compose_references_in(
                    self.node_slice(node),
                    self.inputs.stack,
                    &expr_vars,
                    &site_path,
                    &mut arc_errors,
                )?;
                let arcs = refs
                    .into_iter()
                    .map(|r| (r.asset_path, r.prim_path, r.layer_offset.sanitized()))
                    .collect::<Vec<_>>();
                (ArcType::Reference, arcs)
            }
            TaskKind::EvalNodePayloads => {
                let payloads = collect_payloads_in(
                    self.node_slice(node),
                    self.inputs.stack,
                    &expr_vars,
                    &site_path,
                    &mut arc_errors,
                )?;
                let arcs = payloads
                    .into_iter()
                    .map(|p| {
                        (
                            p.asset_path,
                            p.prim_path,
                            p.layer_offset.unwrap_or_default().sanitized(),
                        )
                    })
                    .collect::<Vec<_>>();
                (ArcType::Payload, arcs)
            }
            // `eval_arcs` is dispatched only for reference and payload tasks.
            _ => unreachable!("eval_arcs handles only reference and payload tasks"),
        };
        self.errors.append(&mut arc_errors);
        for (asset_path, prim_path, offset) in &arcs {
            self.add_ref_or_payload_arc(node, asset_path, prim_path, arc, *offset, &expr_vars)?;
        }
        Ok(())
    }

    /// Composes the expression variables visible at `node` for evaluating the
    /// variable expressions in its reference/payload asset paths (C++
    /// `PcpExpressionVariables::Compute`). Walking from `node` to the root, each
    /// reference/payload arc enters a new layer stack that contributes its own
    /// authored `expressionVariables`; the closer-to-root stack overrides the
    /// farther one (the referencing layer stack wins over the referenced one).
    ///
    /// `PrimIndex::composed_expr_vars` is the value-resolution-time twin of this
    /// walk over the finished index; keep the two in sync.
    ///
    /// TODO(expr-arcs): a reference authored inside a sub-root arc target is
    /// composed in a nested sub-build whose graph holds only the target's
    /// subtree, so this walk stops at the sub-build root and misses the outer
    /// frames' overrides. Thread the variables across the [`Frame`] chain to
    /// cover that case.
    ///
    /// TODO(perf): this runs per reference/payload eval task and reads each
    /// boundary layer's `expressionVariables` even when no asset path is an
    /// expression (the common case). Compute it lazily — only once an authored
    /// asset path is a backtick expression.
    fn composed_expr_vars(&self, node: NodeId) -> HashMap<String, Value> {
        // Walk node→root, applying each reference/payload boundary's variables so
        // the closer-to-root stack (applied last) overrides the farther one.
        let mut composed = HashMap::new();
        let mut cur = Some(node);
        while let Some(id) = cur {
            let n = &self.output.nodes[id.idx()];
            if matches!(n.arc, ArcType::Root | ArcType::Reference | ArcType::Payload) {
                composed.extend(self.layer_stack_expr_vars(n.layer_stack_id()));
            }
            cur = n.parent;
        }
        composed
    }

    /// Reads the `expressionVariables` authored by a layer stack's own layers,
    /// composing them across the stack with the strongest member winning.
    fn layer_stack_expr_vars(&self, ambient: LayerStackId) -> HashMap<String, Value> {
        let mut vars = HashMap::new();
        // Members are strongest-first; apply weakest-first so the strongest wins.
        for &(layer, _) in self.inputs.stack.layer_stack(ambient).iter().rev() {
            if let Ok(dict) = expr::read_expression_variables(self.inputs.stack.layer(layer).data()) {
                expr::compose_over(&mut vars, &dict);
            }
        }
        vars
    }

    /// Composes the class-based arcs (inherits or specializes) authored at
    /// `node`'s site, one node per arc (C++ `_EvalNodeInherits` /
    /// `_EvalNodeSpecializes` → `_AddClassBasedArcs`). `field` selects the arc
    /// list ([`FieldKey::InheritPaths`] or [`FieldKey::Specializes`]) and `arc`
    /// the arc type; [`add_class_based_arc`](Self::add_class_based_arc) routes a
    /// specializes through the inert-placeholder / copy-to-root path.
    fn eval_class_arcs(&mut self, node: NodeId, field: FieldKey, arc: ArcType) -> BuildResult<()> {
        // An inert node (a non-contributing implied placeholder) authors nothing.
        if self.node(node).is_inert() {
            return Ok(());
        }
        let arcs = compose_arc_list_in::<Path>(self.node_slice(node), field, self.inputs.stack)?;
        let node_path = self.node(node).path.clone();
        let node_ambient = self.node(node).layer_stack_id();
        for (arc_num, class_path) in arcs.iter().enumerate() {
            let resolved = node_path.make_absolute(class_path);
            // A class arc must target a prim, not a variant selection. A target
            // that resolves to a variant-selection path is left uncomposed (the
            // strip/re-add of selections is future work, see `add_class_based_arc`).
            if resolved.is_prim_variant_selection_path() {
                continue;
            }
            // Inheriting/specializing a prim that is itself a relocation source —
            // or a child of one — is prohibited (salted earth, C++
            // `PcpErrorArcToProhibitedChild`): the source is empty after
            // relocation, so the arc is dropped and reported.
            if let Some((reloc_source, reloc_layer)) = self.prohibiting_relocation_source(node_ambient, &resolved) {
                let site_layer = self.introducing_layer(node);
                self.errors.push(Error::ProhibitedRelocationSource {
                    arc,
                    site: node_path.clone(),
                    site_layer: site_layer.clone(),
                    target: resolved.clone(),
                    target_layer: site_layer,
                    reloc_source,
                    reloc_layer,
                    composing: self.site.path.clone(),
                });
                continue;
            }
            // The class-arc map sends the class to the instance; every other
            // path (notably root classes) maps through the added root identity.
            // The target strips variant selections (C++
            // `_CreateMapExpressionForArc`) so they never enter mapping
            // functions; the node's site path keeps them for opinion storage.
            let class_map = self
                .fold_relocates_into(
                    MapFunction::from_pair(resolved, node_path.strip_all_variant_selections()),
                    node,
                )
                .with_root_identity();
            self.add_class_based_arc(node, node, class_map, arc_num as u16, None, arc, false)?;
        }
        Ok(())
    }

    /// Finds the variant sets authored at `node`'s own site and enqueues an
    /// authored-selection task for each (C++ `_EvalNodeVariantSets` →
    /// `_EvalVariantSetsAtSite`).
    fn eval_node_variant_sets(&mut self, node: NodeId) -> BuildResult<()> {
        if !self.node_can_contribute_specs(node) {
            return Ok(());
        }
        let site_path = self.node(node).path.clone();
        self.eval_variant_sets_at_site(node, &site_path, false)
    }

    /// Finds the variant sets authored at `node`'s namespace ancestors and
    /// enqueues an ancestral authored-selection task for each (C++
    /// `_EvalNodeAncestralVariantSets`). Walks from the node's parent path up to
    /// the root, stopping at the first variant-selection path — variant sets
    /// above it were already handled when that selection was made.
    fn eval_node_ancestral_variant_sets(&mut self, node: NodeId) -> BuildResult<()> {
        let mut path = self.node(node).path.parent();
        while let Some(p) = path {
            if p == Path::abs_root() {
                break;
            }
            // A node restricted below this depth (a relocate source past its own
            // site) contributes no opinions here, so skip the set scan (C++
            // `_NodeCanContributeAncestralOpinions`).
            if self.node_can_contribute_ancestral(node, &p) {
                self.eval_variant_sets_at_site(node, &p, true)?;
            }
            if p.is_prim_variant_selection_path() {
                break;
            }
            path = p.parent();
        }
        Ok(())
    }

    /// Enqueues an authored-selection task for each variant set composed at
    /// `site_path` across `node`'s layer stack (C++ `_EvalVariantSetsAtSite`).
    /// The sets keep their declaration order, so a lower `vset_num` is stronger;
    /// `is_ancestral` selects the ancestral task band when the set sits above the
    /// node's own path.
    fn eval_variant_sets_at_site(&mut self, node: NodeId, site_path: &Path, is_ancestral: bool) -> BuildResult<()> {
        let sets = self.compose_token_children(node, site_path, ChildrenKey::VariantSetChildren)?;
        let kind = if is_ancestral {
            TaskKind::EvalNodeAncestralVariantAuthored
        } else {
            TaskKind::EvalNodeVariantAuthored
        };
        for (vset_num, vset_name) in sets.into_iter().enumerate() {
            self.tasks.push(Task::variant(
                kind,
                node,
                VariantTask {
                    vset_path: site_path.clone(),
                    vset_name,
                    vset_num: vset_num as u16,
                },
            ));
        }
        Ok(())
    }

    /// Resolves the authored selection for a variant set and adds the variant
    /// arc, deferring to the fallback when none is authored (C++
    /// `_EvalNodeAuthoredVariant`). `is_ancestral` routes the selection through
    /// the ancestral variant arc and the ancestral fallback task.
    fn eval_node_authored_variant(
        &mut self,
        node: NodeId,
        vt: &Option<VariantTask>,
        is_ancestral: bool,
    ) -> BuildResult<()> {
        let Some(vt) = vt else { return Ok(()) };
        if !self.node_can_contribute_variant(node, &vt.vset_path, is_ancestral) {
            return Ok(());
        }
        match self.compose_variant_selection(node, &vt.vset_path, &vt.vset_name)? {
            // An explicit empty selection chooses no variant, the same as no
            // authored selection — both defer to the fallback (C++ treats an
            // empty `vsel` as unauthored).
            Some(sel) if !sel.is_empty() => self.add_variant_arc(node, vt, &sel, is_ancestral)?,
            _ => {
                let kind = if is_ancestral {
                    TaskKind::EvalNodeAncestralVariantFallback
                } else {
                    TaskKind::EvalNodeVariantFallback
                };
                self.tasks.push(Task::variant(kind, node, vt.clone()));
            }
        }
        Ok(())
    }

    /// Selects the fallback variant for a set with no authored selection (C++
    /// `_EvalNodeFallbackVariant`). Adds the variant arc when a fallback applies,
    /// else enqueues a none-found placeholder for [`retry_variant_tasks`].
    fn eval_node_fallback_variant(
        &mut self,
        node: NodeId,
        vt: &Option<VariantTask>,
        is_ancestral: bool,
    ) -> BuildResult<()> {
        let Some(vt) = vt else { return Ok(()) };
        if !self.node_can_contribute_variant(node, &vt.vset_path, is_ancestral) {
            return Ok(());
        }
        let options = self.compose_variant_options(node, &vt.vset_path, &vt.vset_name)?;
        // A configured fallback selects the first of its ordered options that
        // exists in the set. With no authored selection and no applicable
        // fallback the set stays unselected (C++ `_EvalNodeFallbackVariant`
        // enqueues a none-found placeholder); there is no implicit first-variant
        // default.
        let fallback = self
            .inputs
            .ctx
            .variant_fallbacks
            .get(&vt.vset_name)
            .iter()
            .find(|fb| options.iter().any(|o| o == *fb))
            .cloned();
        match fallback {
            Some(sel) => self.add_variant_arc(node, vt, &sel, is_ancestral)?,
            None => {
                let kind = if is_ancestral {
                    TaskKind::EvalNodeAncestralVariantNoneFound
                } else {
                    TaskKind::EvalNodeVariantNoneFound
                };
                self.tasks.push(Task::variant(kind, node, vt.clone()));
            }
        }
        Ok(())
    }

    /// Composes the strongest authored selection for variant set `vset` (C++
    /// `_ComposeVariantSelection`). A selection authored on a stronger site (a
    /// referencing layer) overrides a weaker one (spec 12.2), but only among the
    /// sites that namespace-map to `vset_path` — for an ancestral variant set, the
    /// search is rooted at the strongest node the set path maps to, so an arc
    /// boundary that blocks the mapping also blocks stronger frames' selections
    /// from leaking in. Returns the selection, or `None` when none is authored.
    fn compose_variant_selection(&self, origin: NodeId, vset_path: &Path, vset: &str) -> BuildResult<Option<String>> {
        // The strongest node the set path maps to, and the path in its namespace
        // (C++ `Pcp_TranslatePathFromNodeToRootOrClosestNode`).
        let (start, path_in_start) = self.translate_path_to_root_or_closest(origin, vset_path);
        // TODO(perf): this rebuilds and re-sorts the subtree node list (each
        // `compare_node_strength` walks parent chains) for every authored-variant
        // task. A prim with several variant sets re-sorts once per set; the order
        // is stable between grafts, so it could be computed once per drain pass.
        let mut nodes: Vec<NodeId> = self
            .subtree_nodes(start)
            .into_iter()
            .filter(|&n| !self.node(n).is_inert())
            .collect();
        nodes.sort_by(|&a, &b| self.output.compare_node_strength(a, b));
        for n in nodes {
            let node = self.node(n);
            // Each candidate's site is the set path mapped from `start` down the
            // arc chain to that candidate (C++ `_ComposeVariantSelectionAcrossNodes`).
            // The per-arc walk drops a path that leaves any arc's co-domain, so a
            // stronger frame's ancestral selection cannot leak across a reference
            // boundary the way a shortcut through the composed `map_to_root`
            // catch-all would (the reason `translate_path_to_root_or_closest`
            // likewise walks arc-by-arc).
            let Some(site) = self.map_path_down(start, n, &path_in_start) else {
                continue;
            };
            // The mapped path may carry an enclosing variant's `{set=sel}`
            // qualifier; the storage site is
            // computed from the variant-free path (C++
            // `_ComposeVariantSelectionAcrossNodes`'s `info.sitePath`). A class or
            // reference node reads its selection at that plain path. A variant
            // node re-inserts its own selection, so a selection authored inside
            // one variant (`/Ref{v1=a}` authoring `v2`) is read at the `{set=sel}`
            // site: walk the node's variant-bearing path up to the ancestor whose
            // stripped form is `path_in_node`.
            let path_in_node = site.strip_all_variant_selections();
            let site = if node.arc == ArcType::Variant {
                variant_storage_site(&node.path, &path_in_node).unwrap_or(path_in_node)
            } else {
                path_in_node
            };
            for &(layer, _) in self.inputs.stack.layer_stack(node.layer_stack_id()).iter() {
                let Some(value) = self
                    .inputs
                    .stack
                    .layer(layer)
                    .data()
                    .try_field(&site, FieldKey::VariantSelection.as_str())?
                else {
                    continue;
                };
                if let Value::VariantSelectionMap(map) = value.into_owned() {
                    if let Some(sel) = map.get(vset) {
                        return Ok(Some(sel.clone()));
                    }
                }
            }
        }
        Ok(None)
    }

    /// Translates `path` from `node`'s namespace up to the root node, or to the
    /// closest node where the translation last succeeded (C++
    /// `Pcp_TranslatePathFromNodeToRootOrClosestNode`). For an ancestral variant
    /// set, the mapping can fail at an arc boundary, marking the strongest site
    /// that could carry a relevant selection.
    fn translate_path_to_root_or_closest(&self, node: NodeId, path: &Path) -> (NodeId, Path) {
        let local_root = self.output.local_root();
        // Namespace mappings never include variant selections.
        let mut cur_path = path.strip_all_variant_selections();
        let mut cur_node = node;
        // Walk up one arc at a time via `map_to_parent`, resting at the first arc
        // whose domain does not contain the path (C++ walks the node chain rather
        // than jumping through the composed `map_to_root`). A shortcut through
        // `map_to_root` would follow its `(/, /)` catch-all straight to the root
        // and let a stronger frame's ancestral selection leak across a reference
        // boundary the per-arc maps actually block.
        while cur_node != local_root && cur_node != self.output.root {
            let Some(in_parent) = self.node(cur_node).map_to_parent.map_source_to_target(&cur_path) else {
                break;
            };
            let Some(parent) = self.node(cur_node).parent() else {
                break;
            };
            cur_node = parent;
            cur_path = in_parent;
        }
        // Re-apply a variant selection the resting node carries at introduction,
        // so the storage site lookup hits the right `{set=sel}` namespace.
        let intro = self.node(cur_node).path_at_introduction();
        let stripped = intro.strip_all_variant_selections();
        if intro != stripped {
            if let Some(p) = cur_path.replace_prefix(&stripped, &intro) {
                cur_path = p;
            }
        }
        (cur_node, cur_path)
    }

    /// Maps `path` (in `ancestor`'s namespace) down into `descendant`'s namespace
    /// by applying each arc's reverse map (`map_target_to_source`) along the
    /// chain from `ancestor` to `descendant`. Returns `None` if the path leaves
    /// any arc's co-domain. Scopes a variant-set search to the start node's frame:
    /// the per-arc walk blocks a path a reference/payload boundary excludes, which
    /// a shortcut through the composed `map_to_root` catch-all would let through.
    fn map_path_down(&self, ancestor: NodeId, descendant: NodeId, path: &Path) -> Option<Path> {
        let mut chain = Vec::new();
        let mut cur = descendant;
        while cur != ancestor {
            chain.push(cur);
            cur = self.node(cur).parent()?;
        }
        let mut p = path.clone();
        for &node in chain.iter().rev() {
            p = self.node(node).map_to_parent.map_target_to_source(&p)?;
        }
        Some(p)
    }

    /// Collects `root` and all its descendants (C++ `Pcp_GetSubtreeRange`).
    fn subtree_nodes(&self, root: NodeId) -> Vec<NodeId> {
        let mut out = Vec::new();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            out.push(id);
            stack.extend(self.node(id).children().iter().copied());
        }
        out
    }

    /// Composes the variant names available in set `vset` at `vset_path`, across
    /// `node`'s layer stack (C++ `PcpComposeSiteVariantSetOptions`).
    fn compose_variant_options(&self, node: NodeId, vset_path: &Path, vset: &str) -> BuildResult<Vec<String>> {
        let set_path = vset_path.append_variant_selection(vset, "");
        // Variant names compose as tokens, but they are matched against the
        // `String`-keyed `VariantFallbackMap`, so flatten to `String` here.
        Ok(self
            .compose_token_children(node, &set_path, ChildrenKey::VariantChildren)?
            .into_iter()
            .map(String::from)
            .collect())
    }

    /// Adds the selected variant `{vset=vsel}` site as a `Variant` arc node under
    /// `node` and re-enqueues its arc and nested-variant tasks (C++
    /// `_AddVariantArc` / `_AddAncestralVariantArc`). Selecting a variant can
    /// surface new authored selections, so pending fallback/none-found variant
    /// tasks are retried as authored.
    ///
    /// A local variant set selects at the node's own path; an ancestral one
    /// (`is_ancestral`) inserts the selection at `vt.vset_path` above the node,
    /// keeps the node's deeper path below it, and composes the result as a
    /// sub-index with ancestral opinions before grafting it.
    fn add_variant_arc(&mut self, node: NodeId, vt: &VariantTask, vsel: &str, is_ancestral: bool) -> BuildResult<()> {
        if is_ancestral {
            return self.add_ancestral_variant_arc(node, vt, vsel);
        }
        let n = self.node(node);
        let base = n.path.clone();
        let stack_id = n.layer_stack_id();
        let rep = n.layer_id();
        let var_path = base.append_variant_selection(&vt.vset_name, vsel);
        let has_specs = self.stack_has_spec(stack_id, &var_path);
        // A variant does not remap the scenegraph namespace; the map only strips
        // the `{vset=vsel}` storage segment off the composed path.
        let map = MapFunction::from_pair_identity(var_path.clone(), base);
        let new_node = self
            .output
            .add_child(node, stack_id, rep, var_path, ArcType::Variant, map, false);
        let n = &mut self.output.nodes[new_node.idx()];
        n.sibling_num_at_origin = vt.vset_num;
        n.has_specs = has_specs;
        // A selected variant whose `{vset=vsel}` site authors no spec is culled
        // like an empty reference/payload target so a later inert spec at the site
        // rebuilds the index.
        if !has_specs {
            self.cull_empty(new_node);
        }
        self.add_tasks_for_node(new_node);
        self.retry_variant_tasks();
        Ok(())
    }

    /// Inserts an ancestral variant selection at `vt.vset_path` with the node's
    /// deeper path below it and grafts it as a sub-index carrying ancestral
    /// opinions (C++ `_AddAncestralVariantArc`).
    fn add_ancestral_variant_arc(&mut self, node: NodeId, vt: &VariantTask, vsel: &str) -> BuildResult<()> {
        let n = self.node(node);
        let node_path = n.path.clone();
        let stack_id = n.layer_stack_id();
        let rep = n.layer_id();
        let selected = vt.vset_path.append_variant_selection(&vt.vset_name, vsel);
        let Some(var_path) = node_path.replace_prefix(&vt.vset_path, &selected) else {
            return Ok(());
        };
        // The variant only strips its `{vset=vsel}` storage segment off the
        // composed path; the rest of the namespace is identity.
        let map = MapFunction::from_pair_identity(var_path.clone(), node_path);
        // Skip duplicate nodes when the variant descends from a class-based arc
        // introduced at this namespace level, matching the skip the class arc set.
        let skip = self.variant_arc_skips_duplicates(node);
        // The grafted variant *root* site is not dup-checked by the sub-build
        // (that guards only the arcs composed inside it), so cull it here when
        // skipping: an implied class propagated across a variant arc reaches the
        // same `{set=sel}` target the direct class already grafted, and grafting
        // it again would duplicate that site (C++ `_AddArc`'s `skipDuplicateNodes`
        // covering the arc's own target node).
        if skip && self.find_duplicate(rep, &var_path) {
            return Ok(());
        }
        let grafted = self.compose_and_graft(
            &var_path,
            stack_id,
            skip,
            node,
            ArcType::Variant,
            map,
            node,
            vt.vset_num,
        )?;
        if grafted.is_some() {
            self.retry_variant_tasks();
        }
        Ok(())
    }

    /// Whether an ancestral variant arc added under `node` should skip duplicate
    /// nodes — true when `node` descends from a contributing class-based arc
    /// introduced at this namespace level (C++ `_AddAncestralVariantArc`'s
    /// `skipDuplicateNodes` predicate).
    fn variant_arc_skips_duplicates(&self, node: NodeId) -> bool {
        let mut cur = node;
        loop {
            let n = self.node(cur);
            if is_class_based_arc(n.arc) && n.depth_below_introduction() == 0 && !n.is_inert() {
                return true;
            }
            match n.parent() {
                Some(p) if p != self.output.root => cur = p,
                _ => return false,
            }
        }
    }

    /// Promotes every pending fallback/none-found variant task back to authored
    /// (C++ `RetryVariantTasks`): a newly selected variant may have introduced
    /// authored selections that those sets should now see.
    fn retry_variant_tasks(&mut self) {
        for task in &mut self.tasks {
            task.kind = match task.kind {
                TaskKind::EvalNodeVariantFallback | TaskKind::EvalNodeVariantNoneFound => {
                    TaskKind::EvalNodeVariantAuthored
                }
                TaskKind::EvalNodeAncestralVariantFallback | TaskKind::EvalNodeAncestralVariantNoneFound => {
                    TaskKind::EvalNodeAncestralVariantAuthored
                }
                other => other,
            };
        }
    }

    /// Marks `node` as a culled empty arc target (C++ culling): it stays in the
    /// graph for change tracking and dependency registration but contributes no
    /// opinions to value resolution. The target authors no spec, so recording
    /// `has_specs = false` lets a later spec at the site be detected as a
    /// `has_specs` flip by the spec-tier rescan, which then un-culls the arc and
    /// grafts the target's subtree.
    fn cull_empty(&mut self, node: NodeId) {
        let n = &mut self.output.nodes[node.idx()];
        n.flags |= NodeFlags::CULLED;
        n.has_specs = false;
    }

    /// Adds a single class-based arc under `parent` (C++ `_AddClassBasedArc`),
    /// returning the new or existing node. The arc may be a directly-authored
    /// inherit or an implied class propagated from `origin` in another subtree.
    ///
    /// A sub-root class target is composed as its own ancestral sub-index
    /// (`includeAncestralOpinions`) and grafted under `parent`; a class reached
    /// both directly and through an ancestral reference grafts once thanks to
    /// duplicate-node skipping (C++ `skipDuplicateNodes`).
    #[allow(clippy::too_many_arguments)]
    fn add_class_based_arc(
        &mut self,
        parent: NodeId,
        origin: NodeId,
        inherit_map: MapFunction,
        arc_num: u16,
        ignore_if_same_as_site: Option<(LayerId, Path)>,
        arc: ArcType,
        implied: bool,
    ) -> BuildResult<Option<NodeId>> {
        let parent_path = self.node(parent).path.clone();
        // Map the parent site back across the arc to find the site to inherit.
        // An empty result means there is no appropriate site (the parent is
        // outside the arc's co-domain); that is not an error, just no node.
        let Some(inherit_path) = determine_inherit_path(&parent_path, &inherit_map) else {
            return Ok(None);
        };

        let (parent_stack, rep) = self.node_site(parent);

        // A class arc whose target is nested with an ancestor node's site — in the
        // same layer stack, the target path being a prefix of, or prefixed by, that
        // site — is a composition cycle: the inheriting prim would contain, or be
        // contained by, what it inherits, so following the arc re-introduces the
        // same prim forever (the self- and co-recursive inherits in `ErrorArcCycle`).
        // Record the cycle and drop the arc; the rest of the prim still composes
        // (C++ `_CheckForCycle` / `_HasAncestorCycle`). Only directly-authored
        // arcs are checked: an implied class arc is a propagated copy of one
        // already vetted where it was authored, and propagation deliberately
        // lands it at nested namespace sites (the spooky / symmetric-rig inherits),
        // which the cycle test would otherwise reject (C++ excludes implied
        // class-based arcs under relocates from the check).
        if !implied && self.class_arc_is_cycle(parent, rep, &inherit_path) {
            self.errors
                .push(Error::ArcCycle(self.cycle_error(parent, arc, rep, inherit_path)));
            return Ok(None);
        }

        // Dedup: a matching child already inherits this site.
        if let Some(existing) = self.find_matching_child(parent, rep, &inherit_path, arc, &inherit_map, origin) {
            return Ok(Some(existing));
        }

        // Specializes need the inert-placeholder / copy-to-root structure (C++
        // `_AddClassBasedArc`). Unless the parent is the local root at the top
        // level — in which case a contributing specialize is added directly
        // below — add an inert placeholder where the arc is authored; at the top
        // level copy it under the root immediately (a sub-build defers that to
        // the `EvalImpliedSpecializes` task run after its graph is grafted).
        if arc == ArcType::Specialize {
            let add_placeholder = parent != self.output.local_root() || self.frame.is_some();
            if add_placeholder {
                let has_specs = self.stack_has_spec(parent_stack, &inherit_path);
                let placeholder =
                    self.output
                        .add_child(parent, parent_stack, rep, inherit_path, arc, inherit_map, true);
                {
                    let n = &mut self.output.nodes[placeholder.idx()];
                    n.origin = Some(origin);
                    n.sibling_num_at_origin = arc_num;
                    n.has_specs = has_specs;
                    n.flags |= NodeFlags::INERT;
                    if implied {
                        n.flags |= NodeFlags::IMPLIED_CLASS;
                    }
                }
                // An implied placeholder still seeds the implied-class/specializes
                // propagation its own arc triggers, the same way the contributing
                // path below does through `add_tasks_for_node`. Without it the
                // chain stops here: a specializes authored in a variant under an
                // outer `/A specializes /_class_` would never imply
                // `/A/defaultImplementation` across that outer arc.
                if implied {
                    self.add_implied_tasks_for_node(placeholder);
                }
                if self.frame.is_none() && !self.is_relocates_placeholder_implied_arc(placeholder) {
                    let propagated = self.propagate_node_to_root(placeholder)?;
                    // A pre-existing propagated node (whose origin is not this
                    // placeholder) still needs the placeholder's classes implied
                    // upward, which its own propagation would otherwise skip.
                    if matches!(propagated, Some(p) if self.node(p).origin() != Some(placeholder)) {
                        self.enqueue_implied(placeholder);
                    }
                    return Ok(propagated);
                }
                return Ok(Some(placeholder));
            }
        }

        let same_as_ignore = ignore_if_same_as_site
            .as_ref()
            .is_some_and(|(li, p)| *li == rep && *p == inherit_path);
        let direct_should = inherit_path != parent_path && !same_as_ignore;
        // A contributing class arc skips a duplicate site; an inert placeholder
        // (mapping unchanged) is kept to keep propagating. The skip also carries
        // in from a parent frame (C++ `_AddArc`'s `|= previousFrame->skip`).
        let skip = direct_should || self.frame_skip();
        if skip && self.find_duplicate(rep, &inherit_path) {
            return Ok(None);
        }

        // A sub-root class needs the opinions above it: compose the target as its
        // own ancestral sub-index and graft it under the parent.
        if direct_should && !inherit_path.is_root_prim() {
            let grafted = self.compose_and_graft(
                &inherit_path,
                parent_stack,
                skip,
                parent,
                arc,
                inherit_map,
                origin,
                arc_num,
            )?;
            if implied {
                if let Some(g) = grafted {
                    self.output.nodes[g.idx()].flags |= NodeFlags::IMPLIED_CLASS;
                }
            }
            return Ok(grafted);
        }

        let has_specs = self.stack_has_spec(parent_stack, &inherit_path);
        let new_node = self.output.add_child(
            parent,
            parent_stack,
            rep,
            inherit_path,
            arc,
            inherit_map,
            arc == ArcType::Specialize,
        );
        let n = &mut self.output.nodes[new_node.idx()];
        n.origin = Some(origin);
        n.sibling_num_at_origin = arc_num;
        n.has_specs = has_specs;
        if implied {
            n.flags |= NodeFlags::IMPLIED_CLASS;
        }
        // A redundant arc (mapping the site unchanged, or onto the ignored site)
        // is kept to propagate but contributes no opinions.
        if !direct_should {
            n.flags |= NodeFlags::INERT;
        }
        // A target authoring no spec is culled like an empty reference/payload
        // target, so a later inert spec at the site rebuilds rather than flipping
        // `has_specs` in place. The node still drives implied-class propagation
        // through the tasks below, so the cull only adds the flag.
        if !has_specs {
            self.cull_empty(new_node);
        }

        self.add_tasks_for_node(new_node);
        Ok(Some(new_node))
    }

    /// Propagates `node`'s class-based children one level up to its parent (C++
    /// `_EvalImpliedClasses`): the queue repeats this, carrying a class brought
    /// in through a reference up the arc chain into the referencing namespace.
    fn eval_implied_classes(&mut self, node: NodeId) -> BuildResult<()> {
        let Some(parent) = self.node(node).parent() else {
            return Ok(());
        };
        // The local root stands in for C++'s parentless root node (whose
        // `_EvalImpliedClasses` early-returns). Its only parent is the synthetic
        // inert tree root, which is not a composition site, so classes must not
        // be propagated up into it.
        if parent == self.output.root {
            return Ok(());
        }
        if !self.has_class_based_child(node) {
            return Ok(());
        }
        // The map to the parent gets the root identity so a root class still
        // maps across a restricted (reference) arc domain.
        let transfer = self.node(node).map_to_parent.with_root_identity();
        self.eval_implied_class_tree(parent, node, &transfer, true)
    }

    /// Propagates the class hierarchy under `src` to `dest`, conjugating each
    /// class arc through `transfer` (C++ `_EvalImpliedClassTree`).
    fn eval_implied_class_tree(
        &mut self,
        dest: NodeId,
        src: NodeId,
        transfer: &MapFunction,
        start_of_tree: bool,
    ) -> BuildResult<()> {
        // Implied classes are not propagated onto a relocate node (its class
        // children are only placeholders); instead they go directly to the
        // relocate node's parent, with the relocate's map folded into the
        // transfer function (C++ `_EvalImpliedClassTree`'s relocate branch).
        // The relocate node still needs its own ancestral class hierarchies
        // propagated, so re-enqueue `EvalImpliedClasses` on it.
        if self.node(dest).arc == ArcType::Relocate {
            if let Some(dest_parent) = self.node(dest).parent() {
                let new_transfer = self
                    .node(dest)
                    .map_to_parent
                    .clone()
                    .with_root_identity()
                    .compose(transfer);
                self.eval_implied_class_tree(dest_parent, src, &new_transfer, start_of_tree)?;
            }
            self.enqueue_implied(dest);
            return Ok(());
        }

        let src_is_class = is_class_based_arc(self.node(src).arc);
        let src_depth = self.node(src).depth_below_introduction();
        // Crossing a sub-root arc (a reference/payload to a non-root prim)
        // collapses depth: the transfer maps the deep target (`/Set/Model`) to
        // the referencing prim, but a class the seed deepened keeps its map at the
        // introduction level (`/Inherit → /Set`). For such an arc, align each
        // class child's map to its node's true depth (`/Inherit/Model →
        // /Set/Model`) so the conjugation lands the implied node at the deepened
        // class site instead of the arc's own prim (see `MapFunction::deepen_to`).
        // A depth-preserving root reference (`/CharRig → /Char`) needs no
        // deepening — and deepening there would shrink the implied class map's
        // domain and break ancestral variant-selection lookups. Only a
        // reference/payload collapses depth this way; crossing an inherit or
        // specialize keeps the class at its namespace level.
        let crosses_subroot_ref =
            matches!(self.node(src).arc, ArcType::Reference | ArcType::Payload) && !self.node(src).path.is_root_prim();
        // A specializes node keeps its children on the copy under the root, so
        // iterate those (C++ `_EvalImpliedClassTree` reads the propagated node's
        // children when `srcNode` is a specializes node).
        let src_owner = self.output.get_propagated_specializes_node(src).unwrap_or(src);
        let src_children = self.node(src_owner).children().to_vec();

        for child in src_children {
            let c = self.node(child);
            if !is_class_based_arc(c.arc) {
                continue;
            }
            // Skip the arc that continues an ancestral class chain rather than a
            // true namespace child: it must not be implied directly to dest.
            if start_of_tree && src_is_class && src_depth == c.depth_below_introduction() {
                continue;
            }

            let child_arc = c.arc;
            let child_map = if crosses_subroot_ref {
                c.map_to_parent.deepen_to(&c.path)
            } else {
                c.map_to_parent.clone()
            };
            let child_site = (c.layer_id(), c.path.clone());
            let sibling = c.sibling_num_at_origin;
            // A reference or inherit moves both the class and its instance, so the
            // class arc conjugates through the transfer. A relocate moves only the
            // instance — the class keeps its pre-relocation path — so the transfer
            // post-composes onto the class arc's target instead, preserving a
            // relocated leaf (e.g. `Seg2 -> Knee`) on the instance while the class
            // stays `Seg2`. The relocation's own `source -> target` pair is not a
            // class-to-instance mapping, so it is dropped (it would otherwise alias
            // the instance and make the inherit-path lookup ambiguous).
            let dest_class_func = if self.node(src).arc == ArcType::Relocate {
                transfer.compose(&child_map).dropping_source(&self.node(src).path)
            } else {
                transfer.implied_class(&child_map)
            };

            // Reuse the implied node already propagated for this child, else add
            // it; either may be absent (no appropriate site to inherit).
            let dest_child = match self.find_implied_child(dest, child) {
                Some(existing) => Some(existing),
                None => self.add_class_based_arc(
                    dest,
                    child,
                    dest_class_func.clone(),
                    sibling,
                    Some(child_site),
                    child_arc,
                    true,
                )?,
            };

            // Recurse into nested classes under the child.
            if let Some(dest_child) = dest_child {
                if self.has_class_based_child(child) {
                    let child_transfer = dest_class_func.inverse().compose(&transfer.compose(&child_map));
                    // A specializes destination keeps its children on the copy
                    // under the root, so recurse there (C++ invariant: only
                    // propagated specializes nodes have children).
                    let recurse_into = self
                        .output
                        .get_propagated_specializes_node(dest_child)
                        .unwrap_or(dest_child);
                    self.eval_implied_class_tree(recurse_into, child, &child_transfer, false)?;
                }
            }
        }
        Ok(())
    }

    /// Finds the node where implied-class propagation for class-based node `n`
    /// should start, so the whole class hierarchy propagates as a unit (C++
    /// `_FindStartingNodeForImpliedClasses`).
    fn find_starting_node_for_implied_classes(&self, n: NodeId) -> NodeId {
        let mut start = n;
        while is_class_based_arc(self.node(start).arc) {
            let (instance, class) = self.output.starting_node_of_class_hierarchy(start);
            start = instance;
            if is_class_based_arc(self.node(instance).arc) {
                let ancestral = self.node(instance).path_at_introduction();
                if self.node(class).path.has_prefix(&ancestral) {
                    break;
                }
            }
        }
        start
    }

    /// Returns an existing child of `parent` that already represents the arc
    /// being added (C++ `_FindMatchingChild`).
    ///
    /// Normally a child matches by site `(rep_layer, path)`. Under a relocate
    /// parent the site is not meaningful (implied classes beneath a relocate
    /// source map identically), so a child matches by arc type, map-to-parent,
    /// and its origin's depth below introduction instead — keeping two classes
    /// inherited by the same relocated prim from collapsing into one.
    ///
    /// A relocate-source sub-index's own local root counts as a relocate parent:
    /// once grafted it becomes the relocate node, and the relocation folded into
    /// its arcs makes two distinct classes map to the same site there.
    fn find_matching_child(
        &self,
        parent: NodeId,
        rep_layer: LayerId,
        path: &Path,
        arc: ArcType,
        map: &MapFunction,
        origin: NodeId,
    ) -> Option<NodeId> {
        let parent_is_relocate = self.node(parent).arc == ArcType::Relocate
            || (!self.root_contributes && parent == self.output.local_root());
        let origin_depth = self.node(origin).depth_below_introduction();
        self.node(parent).children().iter().copied().find(|&c| {
            let cn = self.node(c);
            if parent_is_relocate {
                cn.arc == arc
                    && cn.map_to_parent == *map
                    && cn.origin().map(|o| self.node(o).depth_below_introduction()) == Some(origin_depth)
            } else {
                cn.layer_id() == rep_layer && &cn.path == path
            }
        })
    }

    /// Returns the child of `dest` already propagated for the implied class
    /// `src_child`, identified by its origin (C++ `_EvalImpliedClassTree`'s
    /// origin dedup). A propagated specializes node for `src_child` is skipped:
    /// it is the copy made for strength ordering, not a previously-implied node,
    /// so treating it as one would drop valid implied opinions.
    fn find_implied_child(&self, dest: NodeId, src_child: NodeId) -> Option<NodeId> {
        self.node(dest)
            .children()
            .iter()
            .copied()
            .find(|&c| self.node(c).origin() == Some(src_child) && !self.output.is_propagated_specializes(c))
    }

    /// Whether `node` has any class-based (inherit/specialize) child (C++
    /// `_HasClassBasedChild`). A specializes node keeps its children on the copy
    /// under the root, so that copy is checked instead.
    fn has_class_based_child(&self, node: NodeId) -> bool {
        let target = self.output.get_propagated_specializes_node(node).unwrap_or(node);
        self.node(target)
            .children()
            .iter()
            .any(|&c| is_class_based_arc(self.node(c).arc))
    }

    /// Whether `node` or any node in its subtree is a specializes node (C++
    /// `_HasSpecializesChildInSubtree`).
    // TODO(perf): re-walks the subtree on every `add_implied_tasks_for_node`; a
    // node high in the tree is re-scanned as composition grows. Could track a
    // "has specialize below" flag incrementally instead.
    fn has_specialize_in_subtree(&self, node: NodeId) -> bool {
        let mut stack = vec![node];
        while let Some(id) = stack.pop() {
            if self.node(id).arc == ArcType::Specialize {
                return true;
            }
            stack.extend(self.node(id).children().iter().copied());
        }
        false
    }

    /// Whether `node` is only a placeholder implied under a relocate node (C++
    /// `_IsRelocatesPlaceholderImpliedArc`): its parent is a relocate at the same
    /// site and is not its origin. Such placeholders are not valid opinion
    /// sources, so specializes propagation skips them.
    fn is_relocates_placeholder_implied_arc(&self, node: NodeId) -> bool {
        let n = self.node(node);
        let Some(parent) = n.parent() else {
            return false;
        };
        n.origin() != Some(parent)
            && self.node(parent).arc == ArcType::Relocate
            && self.node(parent).layer_id() == n.layer_id()
            && self.node(parent).path == n.path
    }

    /// Copies a specializes node under the local root for strength ordering (C++
    /// `_PropagateNodeToRoot`). The copy carries the source's map-to-root,
    /// site, sibling number, and the source as its origin, so it is recognised
    /// as a propagated specializes node. A sub-root target is composed with its
    /// ancestral opinions and grafted; a root-prim target is added directly.
    /// Returns the existing or new node, or `None` when a duplicate site is
    /// skipped.
    fn propagate_node_to_root(&mut self, src: NodeId) -> BuildResult<Option<NodeId>> {
        let root = self.output.local_root();
        if !root.is_valid() {
            return Ok(None);
        }
        let map = self.node(src).map_to_root.clone();
        let (src_stack, rep) = self.node_site(src);
        let src_path = self.node(src).path.clone();
        let sibling = self.node(src).sibling_num_at_origin;

        if let Some(existing) = self.find_matching_child(root, rep, &src_path, ArcType::Specialize, &map, src) {
            return Ok(Some(existing));
        }
        // C++ `_AddArc` with `skipDuplicateNodes`: a site already reached by
        // another path is not copied again (the inert placeholder at `src` is
        // skipped by `node_using_site`, so it is not its own duplicate).
        if self.find_duplicate(rep, &src_path) {
            return Ok(None);
        }

        // A sub-root specialize target needs the opinions above it (C++
        // `includeAncestralOpinions = !IsRootPrimPath`).
        if !src_path.is_root_prim() {
            return self.compose_and_graft(&src_path, src_stack, true, root, ArcType::Specialize, map, src, sibling);
        }

        let has_specs = self.stack_has_spec(src_stack, &src_path);
        let new_node = self
            .output
            .add_child(root, src_stack, rep, src_path, ArcType::Specialize, map, true);
        {
            let n = &mut self.output.nodes[new_node.idx()];
            n.origin = Some(src);
            n.sibling_num_at_origin = sibling;
            n.has_specs = has_specs;
        }
        // An empty specialize target is culled like an empty reference/payload
        // target so a later inert spec at the site rebuilds the index.
        if !has_specs {
            self.cull_empty(new_node);
        }
        self.add_tasks_for_node(new_node);
        Ok(Some(new_node))
    }

    /// Copies every specializes node in a grafted subtree under the root (C++
    /// `_EvalImpliedSpecializes`). A no-op at the root node, which has no parent.
    fn eval_implied_specializes(&mut self, node: NodeId) -> BuildResult<()> {
        if self.node(node).parent().is_none() {
            return Ok(());
        }
        self.find_specializes_to_propagate_to_root(node)
    }

    /// Walks the subtree under `node`, copying each specializes node to the root
    /// (C++ `_FindSpecializesToPropagateToRoot`).
    fn find_specializes_to_propagate_to_root(&mut self, node: NodeId) -> BuildResult<()> {
        if self.is_relocates_placeholder_implied_arc(node) {
            return Ok(());
        }
        if self.node(node).arc == ArcType::Specialize {
            self.propagate_node_to_root(node)?;
        }
        let children = self.node(node).children().to_vec();
        for child in children {
            self.find_specializes_to_propagate_to_root(child)?;
        }
        Ok(())
    }

    /// Resolves a reference or payload to its target layer stack, adds the target
    /// node under `parent`, and enqueues that node's own reference/payload tasks
    /// (C++ `_AddArc` for an arc without ancestral opinions).
    ///
    /// Targets outside the ported set — internal references, `defaultPrim`
    /// resolution, sub-root targets, unresolved layers, empty targets — abandon
    /// the prim to the recursive indexer.
    fn add_ref_or_payload_arc(
        &mut self,
        parent: NodeId,
        asset_path: &str,
        prim_path: &Path,
        arc: ArcType,
        arc_offset: LayerOffset,
        expr_vars: &HashMap<String, Value>,
    ) -> BuildResult<()> {
        let is_internal = asset_path.is_empty();
        let parent_path = self.node(parent).path.clone();

        // Resolve the target layer stack. An internal reference targets the
        // referencing node's own layer stack (C++ `node.GetLayerStack()`); an
        // external one resolves the asset's sublayer stack. `external_target`
        // carries the resolved external root layer for the muted-target trace.
        let mut external_target = None;
        let target_stack = if is_internal {
            self.node(parent).layer_stack_id()
        } else {
            let layer_index = match self.inputs.stack.id_of(asset_path) {
                Some(layer_index) => {
                    // The target is loaded, but if this arc carries expression
                    // variables and reaches a target that has a `${VAR}` sublayer yet
                    // was interned unseeded (by an earlier variable-free arc to the
                    // same target), demand a re-seed so that sublayer resolves against
                    // this context. The load barrier seeds the already-loaded target,
                    // reloads the sublayers the new context resolves, and recomposes;
                    // once seeded the target is not demanded again, so this converges.
                    if !expr_vars.is_empty()
                        && !self.inputs.stack.is_seeded(layer_index)
                        && self.inputs.stack.has_expr_sublayer(layer_index)
                    {
                        self.pending_loads.push(Demand {
                            asset_path: asset_path.to_string(),
                            expr_vars: expr_vars.clone(),
                        });
                        return Ok(());
                    }
                    layer_index
                }
                // The target is not loaded. The authoring layer's location gates
                // both the `.usdz` guard and the relative-mute anchor, so resolve
                // it once here — only on a lookup miss, leaving an already-loaded
                // arc (the steady state) doing no filesystem work.
                None => {
                    // TODO(perf): this resolves the authoring layer's location
                    // only to read its extension for the usdz guard; the layer's
                    // in-memory identifier already carries the extension, so the
                    // guard could test that and skip the filesystem resolve.
                    let anchor = self.inputs.stack.anchor_location(Some(self.node(parent).layer_id()));
                    // A reference/payload authored inside a `.usdz` package would
                    // need to open a sibling layer within the archive, which is not
                    // yet supported (the eager collector bailed the same way for a
                    // usdz inner layer's sublayers). Report it explicitly rather
                    // than letting the package-relative target fail as a generic
                    // unresolved layer.
                    if anchor.as_ref().is_some_and(|resolved| resolved.extension() == "usdz") {
                        self.errors.push(Error::UnsupportedUsdzReference {
                            asset_path: asset_path.to_string(),
                            arc,
                            introduced_by: self.introducing_layer(parent),
                            site_path: parent_path,
                        });
                        return Ok(());
                    }
                    // A muted target contributes nothing and is never opened: drop
                    // the arc (it then composes as if absent) and record the muted
                    // reference as a diagnostic. Checked before the load demand so a
                    // muted target's file is not read.
                    if self.arc_target_muted(parent, asset_path) {
                        self.errors.push(Error::MutedAssetPath {
                            asset_path: asset_path.to_string(),
                            arc,
                            introduced_by: self.introducing_layer(parent),
                            site_path: parent_path,
                        });
                        return Ok(());
                    }
                    // A resolvable-but-not-yet-loaded target is demanded, not an
                    // error: record it in `pending_loads` and leave the arc
                    // uncomposed this pass. The stage's query loop opens the layer
                    // and recomposes, so composition drives layer loading and an
                    // un-visited subtree never loads. A target a prior load attempt
                    // failed to read is not re-demanded — it falls through to the
                    // malformed-layer error below so the prim's index can finally
                    // cache.
                    if self.inputs.stack.layer_registry().resolve(asset_path).is_some()
                        && !self.inputs.stack.load_failed(asset_path)
                    {
                        self.pending_loads.push(Demand {
                            asset_path: asset_path.to_string(),
                            expr_vars: expr_vars.clone(),
                        });
                        return Ok(());
                    }
                    // A target the load barrier resolved but could not read or
                    // parse: report it with the underlying reason and skip the arc.
                    if self.inputs.stack.load_failed(asset_path) {
                        self.errors.push(Error::MalformedLayer {
                            asset_path: asset_path.to_string(),
                            arc,
                            introduced_by: self.introducing_layer(parent),
                            site_path: parent_path,
                            reason: self
                                .inputs
                                .stack
                                .load_failure_reason(asset_path)
                                .unwrap_or_default()
                                .to_string(),
                        });
                        return Ok(());
                    }
                    // An unresolvable asset is a recoverable error (C++ "Could not
                    // open asset … for {arc}"): record it and skip the arc so the
                    // rest of the prim — including its own local opinions — still
                    // composes.
                    self.errors.push(Error::UnresolvedLayer {
                        asset_path: asset_path.to_string(),
                        arc,
                        introduced_by: self.introducing_layer(parent),
                        site_path: parent_path,
                    });
                    return Ok(());
                }
            };
            external_target = Some(layer_index);
            self.inputs.stack.sublayer_stack_id(layer_index)
        };

        // A muted target root drops out of its own `sublayer_stack`, leaving the
        // stack empty. Skip the arc rather than indexing the empty stack, recording
        // both the muted target (so unmuting it can find this index to recompose —
        // a skipped arc grafts no node, so the recorded id is the only other trace
        // of the dependency) and the diagnostic.
        let Some(rep) = self.inputs.stack.layer_stack(target_stack).first().map(|&(li, _)| li) else {
            if let Some(layer_index) = external_target {
                self.output.muted_external_targets.push(layer_index);
                self.errors.push(Error::MutedAssetPath {
                    asset_path: asset_path.to_string(),
                    arc,
                    introduced_by: self.introducing_layer(parent),
                    site_path: parent_path,
                });
            }
            return Ok(());
        };

        // Resolve the source prim path, falling back to the target layer's
        // `defaultPrim` when the arc names no prim (C++ `_GetDefaultPrimPath`).
        let source = if prim_path.is_empty() {
            let Some(p) = self.resolve_default_prim(target_stack)? else {
                // Missing target `defaultPrim` is likewise recoverable: record it
                // and skip the arc; the prim's other opinions still compose.
                self.errors.push(Error::MissingDefaultPrim {
                    layer_id: self.inputs.stack.layer(rep).identifier.clone(),
                    arc,
                    site_path: parent_path,
                });
                return Ok(());
            };
            p
        } else {
            prim_path.clone()
        };

        // A duplicate site reached inside a skip sub-build is skipped, keeping a
        // class reached both directly and through this arc from grafting twice.
        if self.frame_skip() && self.find_duplicate(rep, &source) {
            return Ok(());
        }
        // A reference/payload that lands back on an active ancestor site closes a
        // composition cycle (C++ `_CheckForCycle`): record it and skip just this
        // arc, leaving the chain composed so far intact, rather than abandoning the
        // whole prim. The reference diamond `GroupRoot → A → B → A` keeps its
        // `[GroupRoot, GroupA, GroupB]` stack and drops only the closing `B → A`.
        if !self.arc_target_in_bounds(parent, rep, &source) {
            self.errors
                .push(Error::ArcCycle(self.cycle_error(parent, arc, rep, source)));
            return Ok(());
        }
        // Referencing a prim that is a relocation source — or a child of one — is
        // prohibited (C++ `PcpErrorArcToProhibitedChild`, "CANNOT reference"): the
        // target is empty after relocation. Drop the arc and report it.
        if let Some((reloc_source, reloc_layer)) = self.prohibiting_relocation_source(target_stack, &source) {
            self.errors.push(Error::ProhibitedRelocationSource {
                arc,
                site: parent_path.clone(),
                site_layer: self.introducing_layer(parent),
                target: source.clone(),
                target_layer: self.inputs.stack.layer(rep).identifier.clone(),
                reloc_source,
                reloc_layer,
                composing: self.site.path.clone(),
            });
            return Ok(());
        }

        // Variant selections address opinion storage but are not part of
        // composed namespace, so the arc map's target strips them (C++
        // `_CreateMapExpressionForArc`). The variant node's own map already
        // folds the strip into `map_to_root`; keeping it out of `map_to_parent`
        // stops it leaking into implied-class transfer functions.
        let mut map = MapFunction::from_pair(source.clone(), parent_path.strip_all_variant_selections())
            .with_time_offset(arc_offset);
        // Opinions reached across this arc land at their post-relocation paths
        // (folded before the root identity, matching C++ `_CreateMapExpressionForArc`).
        map = self.fold_relocates_into(map, parent);
        if is_internal {
            // Internal references keep full namespace visibility outside the
            // source and target (C++ `mapExpr.AddRootIdentity()`).
            map = map.with_root_identity();
        }

        // A sub-root target needs the opinions above it: compose it as its own
        // ancestral sub-index and graft it under the parent. A `None` result means
        // the target could not be composed — e.g. its own ancestral chain closes a
        // cycle — leaving the reference prim path unresolved (C++
        // `PcpErrorUnresolvedPrimPath`).
        if !source.is_root_prim() {
            let before = self.errors.len();
            let grafted =
                self.compose_and_graft(&source, target_stack, self.frame_skip(), parent, arc, map, parent, 0)?;
            // The target is unresolved only when composing it hit a cycle (its own
            // ancestral chain loops back) that left nothing — not when it is merely
            // empty so far (e.g. a variant supplies its opinions later).
            let hit_cycle = self.errors[before..].iter().any(|e| matches!(e, Error::ArcCycle(_)));
            let unresolved = hit_cycle && !grafted.is_some_and(|g| self.subtree_has_specs(g));
            if unresolved {
                self.errors.push(Error::UnresolvedPrimPath {
                    arc,
                    target_layer: self.inputs.stack.layer(rep).identifier.clone(),
                    prim_path: source.clone(),
                    introduced_by: self.introducing_layer(parent),
                    site_path: parent_path.clone(),
                });
            }
            return Ok(());
        }

        // An arc target authoring no spec is kept as a culled node (C++
        // culling): visible to change tracking and dependency registration, but
        // contributing no opinions to value resolution. A resolved-layer payload
        // to such a prim is additionally an unresolved-prim-path error (C++
        // `PcpErrorUnresolvedPrimPath`); the node is still culled.
        let empty = !self.stack_has_spec(target_stack, &source);
        if empty && !is_internal && arc == ArcType::Payload {
            self.errors.push(Error::UnresolvedPrimPath {
                arc,
                target_layer: self.inputs.stack.layer(rep).identifier.clone(),
                prim_path: source.clone(),
                introduced_by: self.introducing_layer(parent),
                site_path: parent_path.clone(),
            });
        }
        let new_node = self
            .output
            .add_child(parent, target_stack, rep, source, arc, map, false);
        if empty {
            self.cull_empty(new_node);
            return Ok(());
        }

        // The new node may itself author references, payloads, and inherits.
        self.add_tasks_for_node(new_node);
        Ok(())
    }

    /// Resolves the `defaultPrim` of a layer stack's root layer to a root-prim
    /// path (C++ `_GetDefaultPrimPath`), or `None` when it is absent or invalid.
    ///
    /// `defaultPrim` is root-layer metadata (spec 12.2.7) and does not compose
    /// with sublayers or session layers. The stage root layer stack carries its
    /// session layers ahead of the root layer, so the lookup uses the strongest
    /// non-session member rather than `target_stack[0]` — which for an internal
    /// reference on a stage with a session layer would be the session.
    fn resolve_default_prim(&self, target_stack: LayerStackId) -> BuildResult<Option<Path>> {
        let members = self.inputs.stack.layer_stack(target_stack);
        let root_layer = members
            .iter()
            .map(|&(li, _)| li)
            .find(|li| !self.inputs.stack.session_layers().contains(li))
            .or_else(|| members.first().map(|&(li, _)| li))
            .unwrap_or(LayerId::INVALID);
        let Some(value) = self
            .inputs
            .stack
            .layer(root_layer)
            .data()
            .try_field(&Path::abs_root(), FieldKey::DefaultPrim.as_str())?
        else {
            return Ok(None);
        };
        Ok(value
            .into_owned()
            .try_as_token()
            .and_then(|name| Path::new(&format!("/{name}")).ok()))
    }

    /// Identifier of the layer that authored an arc on `node` — its
    /// representative (strongest) layer. Used to name the introducing layer in
    /// recoverable arc errors.
    fn introducing_layer(&self, node: NodeId) -> String {
        self.inputs.stack.layer(self.node(node).layer_id()).identifier.clone()
    }

    /// Whether the reference/payload target `asset_path` names a muted layer,
    /// matched by the canonical identifier it would be interned under. A reference
    /// may be authored on any member of `node`'s layer stack — a sublayer in a
    /// different directory than the node's representative — so the target is
    /// canonicalized against each member's location and looked up in the muted set
    /// (C++ `_EvalRefOrPayloadArcs` checks the specific authoring `srcLayer`). The
    /// muted set is keyed by identifiers anchored against the stage root, so a
    /// nested target is muted by the path that resolves from the root to its
    /// identifier. Guarded by [`has_muted_layers`](LayerGraph::has_muted_layers) so
    /// the common unmuted stage does no anchoring work.
    ///
    /// TODO(perf): on a muted stage this resolves each member's anchor and
    /// canonicalizes `asset_path` against it (a filesystem syscall apiece) for
    /// every not-yet-loaded reference/payload arc. Cache the per-member anchors, or
    /// track the specific authoring layer per arc entry so only one canonicalize
    /// runs (the `srcLayer` C++ uses).
    fn arc_target_muted(&self, node: NodeId, asset_path: &str) -> bool {
        let graph = self.inputs.stack;
        graph.has_muted_layers()
            && graph
                .layer_stack(self.node(node).layer_stack_id())
                .iter()
                .any(|&(layer, _)| graph.is_asset_muted(asset_path, graph.anchor_location(Some(layer)).as_ref()))
    }

    /// Builds the cycle chain for an [`Error::ArcCycle`]: the arcs from the
    /// composing prim down to the cycle-closing arc `(closing_arc, closing_layer,
    /// closing_path)`. Walks `parent`'s ancestry (the no-parent node is the chain
    /// root), records each intermediate site's arc, then appends the closing arc.
    fn cycle_error(
        &self,
        parent: NodeId,
        closing_arc: ArcType,
        closing_layer: LayerId,
        closing_path: Path,
    ) -> CycleChain {
        // Walk up to the local root — the node whose parent is the synthetic,
        // inert graph root (or which has no parent). The local root is the chain
        // root, displayed on its own line, not a hop.
        let mut hops = Vec::new();
        let mut cur = parent;
        let root_node = loop {
            let n = self.node(cur);
            match n.parent() {
                Some(p) if !self.node(p).is_inert() => {
                    hops.push(CycleHop {
                        arc: n.arc,
                        layer: self.introducing_layer(cur),
                        path: n.path.clone(),
                    });
                    cur = p;
                }
                _ => break cur,
            }
        };
        hops.reverse();
        // When the local root sits inside a parent frame (its site comes in
        // through a sub-build), the chain begins above this build: prepend each
        // frame's introduced site, outermost first, so the chain root is the
        // top-level composing prim.
        let mut composing = self.site.path.clone();
        let mut root_layer = self.introducing_layer(root_node);
        let mut frame_hops = Vec::new();
        let mut frame = self.frame;
        while let Some(f) = frame {
            frame_hops.push(CycleHop {
                arc: f.arc,
                layer: self.inputs.stack.layer(f.requested_layer).identifier.clone(),
                path: composing.clone(),
            });
            composing = f.root_path.clone();
            root_layer = self.inputs.stack.layer(f.requested_layer).identifier.clone();
            frame = f.previous;
        }
        frame_hops.reverse();
        frame_hops.extend(hops);
        let mut hops = frame_hops;
        hops.push(CycleHop {
            arc: closing_arc,
            layer: self.inputs.stack.layer(closing_layer).identifier.clone(),
            path: closing_path,
        });
        CycleChain {
            composing,
            root_layer,
            hops,
        }
    }

    /// Whether `node` or any descendant contributes a spec — used to tell a
    /// sub-root arc whose target composed real opinions from one whose target was
    /// elided to nothing (e.g. by a cycle in its own ancestral chain), which is an
    /// unresolved prim path.
    fn subtree_has_specs(&self, node: NodeId) -> bool {
        let n = self.node(node);
        if n.has_specs() {
            return true;
        }
        n.children().iter().any(|&c| self.subtree_has_specs(c))
    }

    /// The relocation source making `path` (or its nearest ancestor) a prohibited
    /// child in `ambient` — the path itself if it is relocated away, else the
    /// closest ancestor that is, paired with the layer authoring that relocation.
    /// `None` when neither `path` nor any ancestor is a relocation source.
    fn prohibiting_relocation_source(&self, ambient: LayerStackId, path: &Path) -> Option<(Path, String)> {
        let mut p = Some(path.clone());
        while let Some(cur) = p {
            if let Some(layer) = self.inputs.stack.relocation_source_layer(ambient, &cur) {
                return Some((cur, layer.to_string()));
            }
            if cur.is_abs_root() {
                break;
            }
            p = cur.parent();
        }
        None
    }

    /// Whether a class-based arc (inherit/specialize) to `(rep, path)` under
    /// `parent` closes a composition cycle (C++ `_CheckForCycle` /
    /// `_HasAncestorCycle`): walking the parent chain, an ancestor node in the
    /// same layer stack whose site is nested with `path` — its path a prefix of,
    /// or prefixed by, `path` — means the arc would re-introduce a prim that
    /// contains or is contained by the inheriting one. Variant arcs are not
    /// class-based and never reach here.
    fn class_arc_is_cycle(&self, parent: NodeId, rep: LayerId, path: &Path) -> bool {
        let mut cur = parent;
        while cur.is_valid() {
            let n = self.node(cur);
            if n.layer_id() == rep && n.path.is_nested_with(path) {
                return true;
            }
            cur = n.parent().unwrap_or(NodeId::INVALID);
        }
        // Continue across parent frames: a class arc landing back on a frame's
        // build root inherits from an ancestor still under composition — the
        // cross-frame mutual-inherit cycle (e.g. `Child1` inherits `Child2`, which
        // inherits `Child1`, each composed as the other's sub-build).
        for (f, search) in self.frame_sites(path) {
            if search == f.root_path && f.graph.node_using_site(rep, &search).is_some() {
                return true;
            }
        }
        false
    }

    /// Returns `true` when an arc to `(root_layer, path)` under `parent` is
    /// within the depth bound and is not a composition cycle (C++
    /// `_CheckForCycle`). The walk crosses stack frames: it visits the target's
    /// ancestor sites in this graph, then each parent frame still under
    /// composition, rejecting an arc that lands back on an active ancestor site.
    /// An ancestor site in the same layer stack that is nested with `path` (its
    /// path a prefix of, or prefixed by, the target) closes the cycle — covering
    /// the ancestral reference cycle `AnotherChild → Model → AnotherParent`, where
    /// the target is a namespace ancestor of the composing prim.
    fn arc_target_in_bounds(&self, parent: NodeId, root_layer: LayerId, path: &Path) -> bool {
        // Count the arc target node itself, then each ancestor up to the root.
        let mut depth = 1;
        let mut cur = parent;
        while cur.is_valid() {
            let n = self.node(cur);
            if n.layer_id() == root_layer && n.path.is_nested_with(path) {
                return false;
            }
            depth += 1;
            cur = n.parent().unwrap_or(NodeId::INVALID);
        }
        // Continue across parent frames (C++ `PcpPrimIndex_StackFrameIterator`):
        // each frame is a sub-build still in progress, so an arc landing back on
        // a frame's build root targets an ancestor under composition — a cycle.
        for (f, search) in self.frame_sites(path) {
            // The arc lands on a frame's build root (a node already composing there)
            // or on a namespace ancestor of it — both are sites still under
            // composition in a parent frame. The ancestor case closes the
            // sub-root-reference cycle where the target's own ancestral chain
            // re-introduces a prim above the referrer.
            let at_root = search == f.root_path && f.graph.node_using_site(root_layer, &search).is_some();
            let above_root = search != f.root_path
                && f.root_path.has_prefix(&search)
                && f.graph.node_using_site(root_layer, &f.root_path).is_some();
            if at_root || above_root {
                return false;
            }
            depth += 1;
        }
        depth <= MAX_DEPTH
    }

    /// Whether any layer in the stack `stack` authors a spec at `path`.
    fn stack_has_spec(&self, stack: LayerStackId, path: &Path) -> bool {
        stack_has_spec(self.inputs.stack, stack, path)
    }

    /// Whether `node` can contribute opinions (C++ `PcpNodeRef::CanContributeSpecs`):
    /// a non-inert site that authors a spec at its path.
    fn node_can_contribute_specs(&self, node: NodeId) -> bool {
        let n = self.node(node);
        !n.is_inert() && n.has_specs
    }

    /// Folds the relocations affecting `parent`'s site into an arc map whose
    /// target is `parent`'s namespace (C++ `_CreateMapExpressionForArc`'s
    /// `reloMapExpr.Compose(arcExpr)`).
    ///
    /// An arc anchored at a site with relocations at or below it carries opinions
    /// from across the arc to their post-relocation paths. A relocate-source
    /// sub-index excludes the relocate that moves its own root: that one is
    /// applied by the relocate arc node's own map at graft time, so folding it
    /// here too would rename the source's class arcs onto the relocated path.
    fn fold_relocates_into(&self, map: MapFunction, parent: NodeId) -> MapFunction {
        if !self.inputs.stack.has_relocates() {
            return map;
        }
        let layers = self.node(parent).layer_stack_id();
        let site = self.node(parent).path.strip_all_variant_selections();
        // A relocate-source sub-index must not fold the relocate that moves its
        // own root: that shift is applied by the relocate arc at graft time, and
        // folding it here would rename the source's class arcs onto the relocated
        // path. Other relocations (descendants, ancestors) still apply.
        let exclude = (!self.root_contributes).then_some(&self.site.path);
        match self.inputs.stack.relocates_expression_at(layers, &site, exclude) {
            Some(reloc) => reloc.compose(&map),
            None => map,
        }
    }

    /// Whether `node` may contribute opinions to the ancestral site `path` (C++
    /// `_NodeCanContributeAncestralOpinions`).
    ///
    /// A node restricted at depth `d` contributes only at paths shallower than
    /// `d`, so a relocate source (restricted at its own depth) still feeds the
    /// spooky-ancestor opinions above it while suppressing its own site. An inert
    /// node carrying no explicit restriction depth (an implied placeholder, an
    /// elided subtree, the synthetic root) is treated as fully restricted.
    fn node_can_contribute_ancestral(&self, node: NodeId, path: &Path) -> bool {
        let n = self.node(node);
        if n.restriction_depth == 0 {
            return !n.is_inert();
        }
        n.restriction_depth as usize > path.element_count()
    }

    /// Whether `node` may contribute a variant selection. A local variant set
    /// must be authored at the node's own contributing site; an ancestral set
    /// sits above the node at `vset_path`, gated by
    /// [`node_can_contribute_ancestral`](Self::node_can_contribute_ancestral).
    fn node_can_contribute_variant(&self, node: NodeId, vset_path: &Path, is_ancestral: bool) -> bool {
        if is_ancestral {
            self.node_can_contribute_ancestral(node, vset_path)
        } else {
            self.node_can_contribute_specs(node)
        }
    }

    /// Unions a node's named children (a `TokenVec` field) at `path` across its
    /// layer stack, keeping declaration order and dropping duplicates. Used to
    /// gather a site's variant set names and a set's variant options.
    fn compose_token_children(&self, node: NodeId, path: &Path, key: ChildrenKey) -> BuildResult<Vec<Token>> {
        let mut out: Vec<Token> = Vec::new();
        for &(layer, _) in self.inputs.stack.layer_stack(self.node(node).layer_stack_id()).iter() {
            let Some(value) = self.inputs.stack.layer(layer).data().try_field(path, key.as_str())? else {
                continue;
            };
            if let Value::TokenVec(names) = value.into_owned() {
                for name in names {
                    if !out.contains(&name) {
                        out.push(name);
                    }
                }
            }
        }
        Ok(out)
    }

    /// Borrows the node behind a handle in the graph being grown.
    fn node(&self, id: NodeId) -> &super::prim_graph::Node {
        &self.output[id.idx()]
    }

    /// A one-element slice over `node`, for the `compose_*_in` helpers that read
    /// a field across a node's member layers.
    fn node_slice(&self, node: NodeId) -> &[super::prim_graph::Node] {
        &self.output[node.idx()..=node.idx()]
    }

    /// A node's site identity — its layer-stack handle and representative layer —
    /// the pair every added/grafted node is created from, read in one arena lookup.
    fn node_site(&self, node: NodeId) -> (LayerStackId, LayerId) {
        let n = self.node(node);
        (n.layer_stack_id(), n.layer_id())
    }
}

#[cfg(test)]
mod tests {
    use super::super::prim_index::PrimIndex;
    use super::*;

    fn stack(text: &str) -> LayerGraph {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        let layer = sdf::Layer::new("root.usd", Box::new(sdf::Data::from_specs(data)));
        LayerGraph::from_layers(vec![layer], 0, sdf::LayerRegistry::default())
    }

    fn multi_stack(layers: &[(&str, &str)]) -> LayerGraph {
        session_stack(layers, 0)
    }

    fn build(stack: &LayerGraph, prim: &str) -> Option<PrimIndexGraph> {
        let ctx = CompositionContext::default();
        let ambient = stack.root_layer_stack_id();
        Indexer::new(stack, &ctx, &sdf::PathTable::new(), ambient)
            .build(&Path::from(prim))
            .expect("indexer build")
            .graph
    }

    /// Builds a layer stack whose first `session` layers are session layers.
    fn session_stack(layers: &[(&str, &str)], session: usize) -> LayerGraph {
        let layers = layers
            .iter()
            .map(|(id, text)| {
                let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
                sdf::Layer::new(*id, Box::new(sdf::Data::from_specs(data)))
            })
            .collect();
        LayerGraph::from_layers(layers, session, sdf::LayerRegistry::default())
    }

    /// An internal default reference (`references = <>`) resolves `defaultPrim`
    /// from the root layer, not the stronger session layer that authors none
    /// (spec 12.2.7). With the session at `target_stack[0]`, reading the session
    /// would find no `defaultPrim` and drop the reference.
    #[test]
    fn internal_default_ref_skips_session() {
        let s = session_stack(
            &[
                ("session.usd", "#usda 1.0\n"),
                (
                    "root.usd",
                    "#usda 1.0\n(\n    defaultPrim = \"Target\"\n)\ndef \"Target\" { custom double x = 1 }\ndef \"P\" (\n    references = <>\n) {}\n",
                ),
            ],
            1,
        );
        let graph = build(&s, "/P").expect("an internal default reference resolves via the root layer");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/Target" && n.has_specs()),
            "the internal default reference targets the root layer's defaultPrim, got {:?}",
            graph.iter().map(|n| n.path.as_str()).collect::<Vec<_>>()
        );
    }

    #[test]
    fn local_prim_supported() {
        let s = stack("#usda 1.0\ndef \"World\" {\n  def \"Sphere\" {}\n}\n");
        let graph = build(&s, "/World").expect("a purely local prim is supported");
        // The synthetic inert root plus one Root-arc site node.
        let arcs: Vec<ArcType> = graph.iter().filter(|n| !n.is_inert()).map(|n| n.arc).collect();
        assert_eq!(arcs, vec![ArcType::Root]);
    }

    #[test]
    fn local_inherit_composed() {
        let s = stack("#usda 1.0\nclass \"C\" { custom double x = 1 }\ndef \"World\" (\n    inherits = </C>\n) {\n}\n");
        let graph = build(&s, "/World").expect("a local inherit to a root class is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Inherit && n.path.as_str() == "/C" && n.has_specs()),
            "the inherit arc to /C contributes the class opinion"
        );
    }

    /// A local specializes arc to a root class composes as a globally-weak
    /// `Specialize` node copied under the local root (C++ `_PropagateNodeToRoot`),
    /// after every other opinion in the strength order.
    #[test]
    fn local_specialize_composed() {
        let s =
            stack("#usda 1.0\nclass \"C\" { custom double x = 1 }\ndef \"World\" (\n    specializes = </C>\n) {\n}\n");
        let graph = build(&s, "/World").expect("a local specialize to a root class is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Specialize && n.path.as_str() == "/C" && n.has_specs() && !n.is_inert()),
            "the specialize arc to /C contributes the class opinion"
        );
        // The specialize node is globally weak: it sorts last in strength order.
        let order: Vec<ArcType> = graph.strength_order.iter().map(|&id| graph[id.idx()].arc).collect();
        assert_eq!(
            order.last(),
            Some(&ArcType::Specialize),
            "the specialize opinion is weakest, got {order:?}"
        );
    }

    /// An authored variant selection grafts the `{set=sel}` site as a `Variant`
    /// arc node carrying the selected branch's opinions.
    #[test]
    fn authored_variant_composed() {
        let s = stack(
            "#usda 1.0\ndef \"World\" (\n    variantSets = \"v\"\n    variants = { string v = \"hi\" }\n) {\n  variantSet \"v\" = {\n    \"hi\" { custom double x = 1 }\n    \"lo\" { custom double x = 2 }\n  }\n}\n",
        );
        let graph = build(&s, "/World").expect("a prim with an authored variant selection is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Variant && n.path.as_str() == "/World{v=hi}" && n.has_specs()),
            "the selected variant {{v=hi}} contributes a node, got {:?}",
            graph.iter().map(|n| n.path.as_str()).collect::<Vec<_>>()
        );
    }

    /// With no authored selection and no configured fallback, the set stays
    /// unselected — no variant arc is added (C++ `_EvalNodeFallbackVariant`).
    #[test]
    fn variant_no_selection_unselected() {
        let s = stack(
            "#usda 1.0\ndef \"World\" (\n    variantSets = \"v\"\n) {\n  variantSet \"v\" = {\n    \"a\" { custom double x = 1 }\n    \"b\" { custom double x = 2 }\n  }\n}\n",
        );
        let graph = build(&s, "/World").expect("a prim with an unselected variant set is composed");
        assert!(
            graph.iter().all(|n| n.arc != ArcType::Variant),
            "no variant arc is added without a selection, got {:?}",
            graph.iter().map(|n| n.path.as_str()).collect::<Vec<_>>()
        );
    }

    #[test]
    fn subroot_inherit_composed() {
        // A class nested under another prim composes through the ancestral
        // sub-index build (C++ `includeAncestralOpinions`).
        let s = stack(
            "#usda 1.0\ndef \"Scope\" {\n  class \"C\" { custom double x = 1 }\n}\ndef \"World\" (\n    inherits = </Scope/C>\n) {\n}\n",
        );
        let graph = build(&s, "/World").expect("a sub-root class inherit is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Inherit && n.path.as_str() == "/Scope/C" && n.has_specs()),
            "the sub-root inherit arc to /Scope/C contributes the class opinion"
        );
    }

    /// A class brought in through a reference is mirrored into the referencing
    /// namespace as an implied class node, so an outer opinion on the class
    /// contributes (C++ `_EvalImpliedClassTree`).
    #[test]
    fn implied_class_from_reference() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"Model\" (\n    references = @ref.usd@</Model>\n) {}\nclass \"Class\" { custom double x = 1 }\n",
            ),
            (
                "ref.usd",
                "#usda 1.0\ndef \"Model\" (\n    inherits = </Class>\n) {}\nclass \"Class\" {}\n",
            ),
        ]);
        let graph = build(&s, "/Model").expect("reference + class is composed by the indexer");
        // The referenced class node, plus the implied class node in root.usd.
        let class_layers: Vec<LayerId> = graph
            .iter()
            .filter(|n| n.arc == ArcType::Inherit && n.path.as_str() == "/Class")
            .map(|n| n.layer_id())
            .collect();
        let root_id = s.id_of("root.usd").expect("root.usd present");
        let ref_id = s.id_of("ref.usd").expect("ref.usd present");
        assert!(
            class_layers.contains(&root_id) && class_layers.contains(&ref_id),
            "the class is composed in both the referenced and referencing layers, got {class_layers:?}"
        );
    }

    #[test]
    fn internal_reference_composed() {
        let s = stack(
            "#usda 1.0\ndef \"Base\" { custom double x = 1 }\ndef \"World\" (\n    references = </Base>\n) {\n}\n",
        );
        let graph = build(&s, "/World").expect("an internal reference to a root prim is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/Base" && n.has_specs()),
            "the internal reference arc to /Base contributes its opinion"
        );
    }

    /// The task queue composes a reference diamond: `/Root` references `A` and
    /// `B`, both of which reference `C`. The shared target `C` is reached by two
    /// arc paths, so it contributes a node on each — the no-dedup behavior that
    /// distinguishes the queue from the recursive indexer's global set.
    #[test]
    fn reference_diamond_two_targets() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"Root\" (\n    references = [@A.usd@</A>, @B.usd@</B>]\n) {}\n",
            ),
            ("A.usd", "#usda 1.0\ndef \"A\" (\n    references = @C.usd@</C>\n) {}\n"),
            ("B.usd", "#usda 1.0\ndef \"B\" (\n    references = @C.usd@</C>\n) {}\n"),
            ("C.usd", "#usda 1.0\ndef \"C\" { custom double x = 1 }\n"),
        ]);
        let graph = build(&s, "/Root").expect("a pure reference diamond is composed by the indexer");
        let c_nodes = graph.iter().filter(|n| n.path.as_str() == "/C").count();
        assert_eq!(c_nodes, 2, "the shared reference target appears once per arc path");
    }

    /// Ancestral references propagate to a child through the graph-clone seed:
    /// `/Root` references `A`, and `A/Child` is reachable at the deepened site
    /// `/A/Child` in the referenced layer.
    #[test]
    fn ancestral_reference_propagates_to_child() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"Root\" (\n    references = @A.usd@</A>\n) {}\n",
            ),
            (
                "A.usd",
                "#usda 1.0\ndef \"A\" {\n    def \"Child\" { custom double x = 1 }\n}\n",
            ),
        ]);
        let ctx = CompositionContext::default();
        let ambient = s.root_layer_stack_id();
        // Seed the child build with the parent's composed index, as the cache does.
        let root_index = PrimIndex::build_with_context(&Path::from("/Root"), &s, &ctx).expect("root index build");
        let mut cached = sdf::PathTable::new();
        cached.insert(
            Path::from("/Root"),
            PrimEntry {
                index: root_index,
                context: CompositionContext::default(),
                errors: Vec::new(),
            },
        );
        let child = Indexer::new(&s, &ctx, &cached, ambient)
            .build(&Path::from("/Root/Child"))
            .expect("indexer build")
            .graph
            .expect("child composed by indexer");
        assert!(
            child
                .iter()
                .any(|n| n.path.as_str() == "/A/Child" && n.arc == ArcType::Reference && n.has_specs()),
            "the ancestral reference contributes the child's opinion at the deepened site"
        );
    }

    /// Composes `path` and every namespace ancestor as the cache does, returning
    /// the target prim's composition graph — a graph-returning wrapper over the
    /// shared [`build_with_fallbacks`](crate::pcp::prim_index::tests::build_with_fallbacks).
    fn compose_chain(s: &LayerGraph, path: &str) -> PrimIndexGraph {
        crate::pcp::prim_index::tests::build_with_fallbacks(s, path, crate::pcp::VariantFallbackMap::new())
            .graph()
            .clone()
    }

    /// The implied relocate placeholder grafted by `eval_implied_relocations`: a
    /// `Relocate` node whose origin is itself a `Relocate` node (the relocate it
    /// was implied from), which tells it apart from a real relocate node (whose
    /// origin is the relocation target). Searches the whole graph, since the
    /// placeholder is grafted onto the relocate's grandparent — the local root in
    /// these tests, but any ancestor in the general case.
    fn implied_placeholder(graph: &PrimIndexGraph) -> Option<NodeId> {
        graph.iter().enumerate().find_map(|(i, n)| {
            (n.arc == ArcType::Relocate && n.origin().is_some_and(|o| graph[o.idx()].arc == ArcType::Relocate))
                .then_some(NodeId(i as u32))
        })
    }

    /// A relocate composed beneath a reference grafts an inert relocate
    /// placeholder onto the grandparent at the source mapped into the
    /// grandparent's namespace, so implied class arcs keep crossing the
    /// relocation (C++ `_EvalImpliedRelocations`).
    #[test]
    fn implied_relocation_grafts_placeholder() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"Ref\" (\n    references = @model.usd@</Model>\n) {}\n",
            ),
            (
                "model.usd",
                "#usda 1.0\n(\n    relocates = { </Model/Rig>: </Model/Scope> }\n)\ndef \"Model\" {\n  def \"Rig\" { custom double x = 1 }\n}\n",
            ),
        ]);
        let graph = compose_chain(&s, "/Ref/Scope");
        let id = implied_placeholder(&graph).expect("an implied relocate placeholder is grafted onto the grandparent");
        let placeholder = &graph[id.idx()];
        assert_eq!(
            placeholder.path.as_str(),
            "/Ref/Rig",
            "the source maps through the reference into the grandparent's namespace"
        );
        assert!(placeholder.is_inert(), "the placeholder contributes no specs");
        assert!(
            placeholder.is_relocate_source(),
            "the placeholder records the source-site dependency"
        );
    }

    /// When the relocation source lies outside a sub-root reference's domain it
    /// has no image in the grandparent's namespace, so no implied relocate is
    /// grafted (C++ `gpRelocSource.IsEmpty()`, the `SubrootReferenceAndRelocates`
    /// case).
    #[test]
    fn implied_relocation_skips_outside_domain() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"P\" (\n    references = @groups.usd@</Group/Dst>\n) {}\n",
            ),
            (
                "groups.usd",
                "#usda 1.0\n(\n    relocates = { </Group/Src/Child>: </Group/Dst/Child> }\n)\ndef \"Group\" {\n  def \"Src\" {\n    def \"Child\" { custom double x = 1 }\n  }\n  def \"Dst\" {}\n}\n",
            ),
        ]);
        let graph = compose_chain(&s, "/P/Child");
        assert!(
            implied_placeholder(&graph).is_none(),
            "no implied relocate is grafted when the source is outside the reference domain"
        );
    }

    /// A stage-level relocate onto a root-level prim has no grandparent above the
    /// local root (C++'s root node is parentless), so no implied relocate is
    /// grafted onto the synthetic tree root.
    #[test]
    fn implied_relocation_skips_root_prim() {
        let s = stack(
            "#usda 1.0\n(\n    relocates = { </Group/Rig>: </Group/Scope> }\n)\ndef \"Group\" {\n  def \"Rig\" { custom double x = 1 }\n}\n",
        );
        let graph = compose_chain(&s, "/Group/Scope");
        assert!(
            implied_placeholder(&graph).is_none(),
            "a relocate whose target sits directly under the local root grafts no implied relocate"
        );
    }
}
