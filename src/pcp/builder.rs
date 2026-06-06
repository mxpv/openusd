//! Task-queue prim builder (C++ `Pcp_PrimIndexer` port).
//!
//! [`Builder`] grows a [`PrimIndexGraph`] node-by-node by draining a
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
//! so [`take_best_task`](Builder::take_best_task) selects the next task with a
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
//! root too. The copies are ordered among themselves by the faithful
//! `PcpCompareSiblingNodeStrength`, placing the globally-weak band after every
//! other opinion (spec 10.4.1). Propagation is add-if-absent on site, so the
//! first placeholder to reach a root site claims the copy and fixes its origin;
//! the copy carries the strongest origin because the seed scan
//! ([`scan_and_enqueue`](Builder::scan_and_enqueue)) enqueues only expressed-arc
//! tasks for the cloned ancestor graph (C++ `AddTasksForRootNode`), so the
//! seed's propagated specializes are inherited from the clone rather than
//! re-implied in a different order.
//!
//! Implied-class tasks drain descendant-before-ancestor and otherwise
//! strongest-first (C++ `Task::PriorityOrder`'s `EvalImpliedClasses` case), so
//! the strongest implied arc reaches a shared site first.
//!
//! The builder is the sole composition path ([`Builder::build`] returns `None`
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
//! prohibited-prim elision for salted earth). Known gaps with their reasons are
//! tracked inline and in the `SKIP_PCP_COMPLIANCE` list: variant-gated and
//! cross-arc implied relocations (`eval_implied_relocations`), specializes/inherit
//! authored inside a selected variant, and relationship/connection target
//! remapping through relocates.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf::expr;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{AbstractData, LayerOffset, Path, Value};

use super::graph::{is_class_based_arc, ArcType, NodeFlags, NodeId, PrimIndexGraph};
use super::index::{
    collect_payloads_in, compose_arc_list_in, compose_references_in, find_layer, CompositionContext, PrimIndex,
};
use super::mapping::MapFunction;
use super::{Error, LayerStack};

/// Maximum composition-arc nesting before the prim is abandoned as a cycle,
/// composing to an empty prim index. Matches C++ `MAX_COMPOSITION_DEPTH`.
const MAX_DEPTH: usize = 100;

/// Whether `path` is a root prim (`/Foo`), whose composition needs no ancestral
/// opinions because its only namespace ancestor is the pseudo-root.
fn is_root_prim(path: &Path) -> bool {
    path.parent().is_some_and(|p| p == Path::abs_root())
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
/// the target is composed as its own sub-index by a nested [`Builder`], then
/// grafted under the arc's parent. The nested builder carries a `Frame` back to
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
/// [`take_best_task`](Builder::take_best_task) drains the highest-priority task:
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
    vset_name: String,
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
    /// kept only so [`retry_variant_tasks`](Builder::retry_variant_tasks) can
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
}

/// The shared, read-only inputs to a prim build — the same across every nested
/// sub-build (C++ `PcpPrimIndexInputs` plus the `PcpCache` it reads). All
/// borrows, so it is `Copy` and threads into a sub-build unchanged.
#[derive(Clone, Copy)]
struct Inputs<'a> {
    /// The layer stack being composed.
    stack: &'a LayerStack,
    /// Composition context flowing from the parent prim (variant selections /
    /// fallbacks, instance depth, denied prefixes, ancestor arcs).
    ctx: &'a CompositionContext,
    /// Cached prim indices from the composition cache. The parent prim's index
    /// is read from here to seed this child's graph (C++
    /// `_BuildInitialPrimIndexFromAncestor`).
    cached_indices: &'a HashMap<Path, PrimIndex>,
}

/// The site this build composes (C++ `PcpLayerStackSite`): the layer stack the
/// root `L` site scans together with the prim path, set per (sub-)build.
struct Site<'a> {
    /// Layer stack the root `L` site scans (the stage root layer stack for a
    /// stage prim, or a referenced asset's sublayer stack for an arc target).
    ambient: &'a [(usize, LayerOffset)],
    /// Whether [`ambient`](Self::ambient) is the stage's root layer stack, the
    /// only case where the stage-keyed `cached_indices` apply.
    is_root: bool,
    /// The path this build composes — the graph's local-root site path. Set at
    /// the start of [`build`](Builder::build) and used as the current-graph root
    /// in cross-frame duplicate-node lookups.
    path: Path,
}

/// Composes a single prim by draining a task queue over a composition graph
/// grown node-by-node (C++ `Pcp_PrimIndexer`).
///
/// All borrowed inputs are shared references, so each build is an independent
/// pure function over the layer stack and incoming context (Rayon-friendly —
/// see the `TODO(rayon)` on the cross-prim driver in `cache.rs`).
pub(crate) struct Builder<'a, 'f> {
    /// Shared read-only inputs (layer stack, context, cached indices).
    inputs: Inputs<'a>,
    /// The site (ambient layer stack + path) this build composes.
    site: Site<'a>,
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
    /// still composes; the cache routes these to the stage error handler. Errors
    /// from nested sub-builds are merged in at their call sites.
    errors: Vec<Error>,
}

impl<'a, 'f> Builder<'a, 'f> {
    pub(crate) fn new(
        stack: &'a LayerStack,
        ctx: &'a CompositionContext,
        cached_indices: &'a HashMap<Path, PrimIndex>,
        ambient: &'a [(usize, LayerOffset)],
        ambient_is_root: bool,
    ) -> Self {
        Self {
            inputs: Inputs {
                stack,
                ctx,
                cached_indices,
            },
            site: Site {
                ambient,
                is_root: ambient_is_root,
                path: Path::abs_root(),
            },
            frame: None,
            frame_depth: 0,
            output: PrimIndexGraph::default(),
            tasks: Vec::new(),
            implied_seen: HashSet::new(),
            root_contributes: true,
            errors: Vec::new(),
        }
    }

    /// Composes `path` into a prim index graph, returning the graph and the
    /// recoverable composition errors collected along the way (an arc whose
    /// target cannot be resolved is recorded and skipped, so the rest of the prim
    /// still composes). The graph is `None` when the seed cannot be established or
    /// the runaway nesting backstop trips, which the cache treats as an empty prim
    /// index. A genuine composition cycle aborts the build as
    /// [`Error::ArcCycle`] by [`arc_target_in_bounds`](Self::arc_target_in_bounds).
    pub(crate) fn build(mut self, path: &Path) -> Result<BuildOutput, Error> {
        // Backstop pathological growth that site-identity cycle detection cannot
        // catch — an unbounded chain of ever-deeper sites that never repeats.
        if self.frame_depth > MAX_DEPTH {
            return Ok(BuildOutput {
                graph: None,
                errors: self.errors,
            });
        }
        self.site.path = path.clone();

        // Seed the graph: a root prim starts empty (just its local site); a
        // child prim clones its parent's graph for ancestral opinions.
        if !self.seed(path)? {
            return Ok(BuildOutput {
                graph: None,
                errors: self.errors,
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

        // Specializes nodes were copied under the local root (C++
        // `_PropagateNodeToRoot`), so the strength-order DFS places that
        // globally-weak band (spec 10.4.1) last.
        self.output.finalize_strength_order();
        Ok(BuildOutput {
            graph: Some(self.output),
            errors: self.errors,
        })
    }

    /// Builds the initial graph for `path` (C++ `_BuildInitialPrimIndexFromAncestor`
    /// plus the root-node setup). Returns `false` to abandon the prim.
    ///
    /// A root prim (parent is the pseudo-root) seeds an empty graph with just its
    /// local site. A child prim clones its already-composed parent's graph and
    /// deepens every site path by the child name, so the references and payloads
    /// an ancestor introduced re-evaluate at this prim's depth.
    fn seed(&mut self, path: &Path) -> Result<bool, Error> {
        let parent = path.parent();
        let needs_ancestor = matches!(&parent, Some(p) if p != &Path::abs_root());

        if !needs_ancestor {
            // Root prim: synthetic inert root plus a local site scanning ambient.
            self.output.init_root(path.clone());
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
        let graph = if self.frame.is_none() && self.site.is_root {
            let Some(parent_index) = self.inputs.cached_indices.get(&parent) else {
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
        self.output.add_site_child(
            NodeId::INVALID,
            self.site.ambient.to_vec(),
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

    /// Builds a nested sub-builder one frame deeper, sharing this build's layer
    /// stack, context, and cache. The caller supplies the ambient stack and the
    /// parent-frame chain (which carries the duplicate-node skip flag).
    fn new_sub<'b, 'g>(
        &self,
        ambient: &'b [(usize, LayerOffset)],
        ambient_is_root: bool,
        frame: Option<&'g Frame<'g>>,
        root_contributes: bool,
    ) -> Builder<'b, 'g>
    where
        'a: 'b,
    {
        let mut sub = Builder::new(
            self.inputs.stack,
            self.inputs.ctx,
            self.inputs.cached_indices,
            ambient,
            ambient_is_root,
        );
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
    fn compose_ancestral_subindex(&self, parent: &Path) -> Result<BuildOutput, Error> {
        self.new_sub(self.site.ambient, self.site.is_root, self.frame, true)
            .build(parent)
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
        ambient: &[(usize, LayerOffset)],
        ambient_is_root: bool,
        skip: bool,
        root_contributes: bool,
    ) -> Result<BuildOutput, Error> {
        let frame = Frame {
            requested_path: target.clone(),
            root_path: self.site.path.clone(),
            graph: &self.output,
            skip,
            previous: self.frame,
        };
        self.new_sub(ambient, ambient_is_root, Some(&frame), root_contributes)
            .build(target)
    }

    /// Merges a completed sub-build's recoverable errors into this build and
    /// returns its graph, so each call site handles only the `Option<graph>`.
    fn merge_subindex(&mut self, out: BuildOutput) -> Option<PrimIndexGraph> {
        self.errors.extend(out.errors);
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
        ambient: &[(usize, LayerOffset)],
        ambient_is_root: bool,
        skip: bool,
        parent: NodeId,
        arc: ArcType,
        map: MapFunction,
        origin: NodeId,
        sibling: u16,
    ) -> Result<Option<NodeId>, Error> {
        let Some(sub) = self.merge_subindex(self.compose_subindex(target, ambient, ambient_is_root, skip, true)?)
        else {
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
    fn find_duplicate(&self, rep_layer: usize, site_path: &Path) -> bool {
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
            let new_id = self.output.add_site_child(
                struct_parent,
                node.layer_stack().to_vec(),
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
            let has_specs = self.stack_has_spec(self.output.nodes[i].layer_stack(), &self.output.nodes[i].path);
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
        if self.inputs.stack.load_payloads {
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
        if self.inputs.stack.has_relocates && !self.node(node).is_inert() {
            self.tasks.push(Task::new(TaskKind::EvalNodeRelocations, node));
        }
    }

    /// Adds a relocate arc back to the source for a node sitting at a relocation
    /// target (C++ `_EvalNodeRelocations`). The source is composed as a
    /// sub-index with ancestral opinions, its direct site inert (salted earth),
    /// and grafted as a `Relocate` arc with an identity-stripping source→target
    /// map. Ancestral child subtrees the relocation supersedes are elided first.
    fn eval_node_relocations(&mut self, node: NodeId) -> Result<(), Error> {
        {
            let n = self.node(node);
            // C++ `CanContributeSpecs`: not inert/culled/permission-denied. A
            // spec-less node still relocates, so `has_specs` is not required.
            if n.is_inert() || n.is_culled() || n.is_permission_denied() {
                return Ok(());
            }
        }
        // Relocates are resolved against the node's own layer stack (C++
        // `node.GetLayerStack()->GetIncrementalRelocatesTargetToSource()`), keyed
        // by the node's path in that layer stack's namespace. This handles both
        // stage-level relocates and relocates authored inside a referenced asset
        // (the node then carries that asset's layers and namespace).
        let node_ambient = self.node(node).layer_stack().to_vec();
        let node_path = self.node(node).path.clone();
        let Some(source) = self.inputs.stack.relocation_source(&node_ambient, &node_path) else {
            return Ok(());
        };

        // Ancestral arcs superseded by this relocation contribute nothing; a
        // variant may still override a relocated prim, so keep variant children
        // (C++ `_EvalNodeRelocations`'s per-child-arc-type switch).
        for child in self.node(node).children().to_vec() {
            if self.node(child).arc != ArcType::Variant {
                self.elide_subtree(child);
            }
        }

        // The relocate node maps its source to the relocation target: opinions
        // and implied classes carried up across it translate the source namespace
        // to the target. The source sub-index excludes this same relocate from its
        // internal arc folds (see `fold_relocates_into`), so the shift is applied
        // once, here.
        let map = MapFunction::from_pair_identity(source.clone(), node_path);
        let ambient_is_root = self.ambient_is_root_for(&node_ambient);
        let Some(sub) = self.merge_subindex(self.compose_subindex(
            &source,
            &node_ambient,
            ambient_is_root,
            self.frame_skip(),
            false,
        )?) else {
            return Ok(());
        };
        let Some(grafted) = self.graft_subindex(&sub, node, ArcType::Relocate, map, node, 0) else {
            return Ok(());
        };
        self.output.nodes[grafted.idx()].flags |= NodeFlags::RELOCATE_SOURCE;
        self.add_grafted_subtree_tasks(grafted);
        self.tasks.push(Task::new(TaskKind::EvalImpliedRelocations, grafted));
        self.elide_relocated_subtrees(grafted);
        Ok(())
    }

    /// Carries a non-ancestral relocate up to the grandparent (C++
    /// `_EvalImpliedRelocations`): when the relocation source maps through the
    /// parent's arc into the grandparent's namespace, C++ adds an inert `Relocate`
    /// arc on the grandparent so a sub-root reference to it still sees the
    /// relocation. Currently a no-op: the common stage-level case maps to nothing,
    /// and the cross-arc graft is not yet ported.
    ///
    // TODO(relocates): port the grandparent graft together with the spooky
    // implied-inherit-across-relocate machinery it feeds (C++ `_AddArc` for the
    // gp relocate, `_EvalImpliedClassTree`'s relocate branch, and
    // `_FindMatchingChild`'s relocate-arc comparison). The graft alone composes
    // no new opinion, so it lands with that cluster (TrickySpookyInherits*,
    // TrickyConnectionToRelocatedAttribute, TrickyMultipleRelocationsAndClasses2).
    fn eval_implied_relocations(&mut self, _node: NodeId) -> Result<(), Error> {
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
        self.inputs.stack.is_relocation_source(n.layer_stack(), &n.path)
    }

    /// Marks `root` and its whole subtree culled so they contribute no opinions
    /// (C++ `_ElideSubtree`). The spec-contribution restriction depth is also
    /// pinned to 1, so a later ancestral task (notably an ancestral variant
    /// re-evaluated at the top level) sees the elided node as non-contributing
    /// and does not graft a live arc beneath it (C++ `_ElideSubtree`'s
    /// `SetSpecContributionRestrictedDepth(1)`).
    fn elide_subtree(&mut self, root: NodeId) {
        for id in self.subtree_nodes(root) {
            let n = &mut self.output.nodes[id.idx()];
            n.flags |= NodeFlags::CULLED;
            n.restriction_depth = 1;
        }
    }

    /// Elides any subtree in a freshly-grafted relocation source whose own site
    /// is a relocation source moved elsewhere, so its opinions are not also
    /// attributed here (C++ `_ElideRelocatedSubtrees`).
    fn elide_relocated_subtrees(&mut self, root: NodeId) {
        if !self.inputs.stack.has_relocates {
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
        if !self.inputs.stack.has_relocates {
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
    fn eval_arcs(&mut self, node: NodeId, kind: TaskKind) -> Result<(), Error> {
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
                    &self.inputs.stack.layers,
                    &*self.inputs.stack.resolver,
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
                    &self.inputs.stack.layers,
                    &*self.inputs.stack.resolver,
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
            self.add_ref_or_payload_arc(node, asset_path, prim_path, arc, *offset)?;
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
                composed.extend(self.layer_stack_expr_vars(n.layer_stack()));
            }
            cur = n.parent;
        }
        composed
    }

    /// Reads the `expressionVariables` authored by a layer stack's own layers,
    /// composing them across the stack with the strongest member winning.
    fn layer_stack_expr_vars(&self, members: &[(usize, LayerOffset)]) -> HashMap<String, Value> {
        let mut vars = HashMap::new();
        // Members are strongest-first; apply weakest-first so the strongest wins.
        for &(layer, _) in members.iter().rev() {
            if let Ok(dict) = expr::read_expression_variables(self.inputs.stack.layer(layer).data()) {
                vars.extend(dict);
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
    fn eval_class_arcs(&mut self, node: NodeId, field: FieldKey, arc: ArcType) -> Result<(), Error> {
        // An inert node (a non-contributing implied placeholder) authors nothing.
        if self.node(node).is_inert() {
            return Ok(());
        }
        let arcs = compose_arc_list_in::<Path>(self.node_slice(node), field, &self.inputs.stack.layers)?;
        let node_path = self.node(node).path.clone();
        for (arc_num, class_path) in arcs.iter().enumerate() {
            let resolved = node_path.make_absolute(class_path);
            // A class arc must target a prim, not a variant selection. A target
            // that resolves to a variant-selection path is left uncomposed (the
            // strip/re-add of selections is future work, see `add_class_based_arc`).
            if resolved.is_prim_variant_selection_path() {
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
    fn eval_node_variant_sets(&mut self, node: NodeId) -> Result<(), Error> {
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
    fn eval_node_ancestral_variant_sets(&mut self, node: NodeId) -> Result<(), Error> {
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
    fn eval_variant_sets_at_site(&mut self, node: NodeId, site_path: &Path, is_ancestral: bool) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
    fn compose_variant_selection(&self, origin: NodeId, vset_path: &Path, vset: &str) -> Result<Option<String>, Error> {
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
            for &(layer, _) in node.layer_stack() {
                let Some(value) = self
                    .inputs
                    .stack
                    .layer(layer)
                    .try_get(&site, FieldKey::VariantSelection.as_str())?
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
    fn compose_variant_options(&self, node: NodeId, vset_path: &Path, vset: &str) -> Result<Vec<String>, Error> {
        let set_path = vset_path.append_variant_selection(vset, "");
        self.compose_token_children(node, &set_path, ChildrenKey::VariantChildren)
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
    fn add_variant_arc(&mut self, node: NodeId, vt: &VariantTask, vsel: &str, is_ancestral: bool) -> Result<(), Error> {
        if is_ancestral {
            return self.add_ancestral_variant_arc(node, vt, vsel);
        }
        let n = self.node(node);
        let base = n.path.clone();
        let layers = n.layer_stack().to_vec();
        let var_path = base.append_variant_selection(&vt.vset_name, vsel);
        let has_specs = self.stack_has_spec(&layers, &var_path);
        // A variant does not remap the scenegraph namespace; the map only strips
        // the `{vset=vsel}` storage segment off the composed path.
        let map = MapFunction::from_pair_identity(var_path.clone(), base);
        let new_node = self
            .output
            .add_site_child(node, layers, var_path, ArcType::Variant, map, false);
        let n = &mut self.output.nodes[new_node.idx()];
        n.sibling_num_at_origin = vt.vset_num;
        n.has_specs = has_specs;
        self.add_tasks_for_node(new_node);
        self.retry_variant_tasks();
        Ok(())
    }

    /// Inserts an ancestral variant selection at `vt.vset_path` with the node's
    /// deeper path below it and grafts it as a sub-index carrying ancestral
    /// opinions (C++ `_AddAncestralVariantArc`).
    fn add_ancestral_variant_arc(&mut self, node: NodeId, vt: &VariantTask, vsel: &str) -> Result<(), Error> {
        let n = self.node(node);
        let node_path = n.path.clone();
        let layers = n.layer_stack().to_vec();
        let ambient_is_root = self.ambient_is_root_for(&layers);
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
        if skip && self.find_duplicate(layers[0].0, &var_path) {
            return Ok(());
        }
        let grafted = self.compose_and_graft(
            &var_path,
            &layers,
            ambient_is_root,
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
        ignore_if_same_as_site: Option<(usize, Path)>,
        arc: ArcType,
        implied: bool,
    ) -> Result<Option<NodeId>, Error> {
        let parent_path = self.node(parent).path.clone();
        // Map the parent site back across the arc to find the site to inherit.
        // An empty result means there is no appropriate site (the parent is
        // outside the arc's co-domain); that is not an error, just no node.
        let Some(inherit_path) = determine_inherit_path(&parent_path, &inherit_map) else {
            return Ok(None);
        };

        let parent_layers = self.node(parent).layer_stack().to_vec();
        let rep = parent_layers[0].0;

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
                let has_specs = self.stack_has_spec(&parent_layers, &inherit_path);
                let placeholder =
                    self.output
                        .add_site_child(parent, parent_layers, inherit_path, arc, inherit_map, true);
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
        if direct_should && !is_root_prim(&inherit_path) {
            let target_is_root = self.ambient_is_root_for(&parent_layers);
            let grafted = self.compose_and_graft(
                &inherit_path,
                &parent_layers,
                target_is_root,
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

        let has_specs = self.stack_has_spec(&parent_layers, &inherit_path);
        let new_node = self.output.add_site_child(
            parent,
            parent_layers,
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

        self.add_tasks_for_node(new_node);
        Ok(Some(new_node))
    }

    /// Propagates `node`'s class-based children one level up to its parent (C++
    /// `_EvalImpliedClasses`): the queue repeats this, carrying a class brought
    /// in through a reference up the arc chain into the referencing namespace.
    fn eval_implied_classes(&mut self, node: NodeId) -> Result<(), Error> {
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
    ) -> Result<(), Error> {
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
            matches!(self.node(src).arc, ArcType::Reference | ArcType::Payload) && !is_root_prim(&self.node(src).path);
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
            let child_site = (c.layer_index(), c.path.clone());
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
        rep_layer: usize,
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
                cn.layer_index() == rep_layer && &cn.path == path
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
    /// sources, so specializes propagation skips them. Returns false until
    /// `TODO(relocates)` composes relocate nodes; the guard mirrors C++ so the
    /// propagation stays correct once they exist.
    fn is_relocates_placeholder_implied_arc(&self, node: NodeId) -> bool {
        let n = self.node(node);
        let Some(parent) = n.parent() else {
            return false;
        };
        n.origin() != Some(parent)
            && self.node(parent).arc == ArcType::Relocate
            && self.node(parent).layer_index() == n.layer_index()
            && self.node(parent).path == n.path
    }

    /// Copies a specializes node under the local root for strength ordering (C++
    /// `_PropagateNodeToRoot`). The copy carries the source's map-to-root,
    /// site, sibling number, and the source as its origin, so it is recognised
    /// as a propagated specializes node. A sub-root target is composed with its
    /// ancestral opinions and grafted; a root-prim target is added directly.
    /// Returns the existing or new node, or `None` when a duplicate site is
    /// skipped.
    fn propagate_node_to_root(&mut self, src: NodeId) -> Result<Option<NodeId>, Error> {
        let root = self.output.local_root();
        if !root.is_valid() {
            return Ok(None);
        }
        let map = self.node(src).map_to_root.clone();
        let src_layers = self.node(src).layer_stack().to_vec();
        let rep = src_layers[0].0;
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
        if !is_root_prim(&src_path) {
            let target_is_root = self.ambient_is_root_for(&src_layers);
            return self.compose_and_graft(
                &src_path,
                &src_layers,
                target_is_root,
                true,
                root,
                ArcType::Specialize,
                map,
                src,
                sibling,
            );
        }

        let has_specs = self.stack_has_spec(&src_layers, &src_path);
        let new_node = self
            .output
            .add_site_child(root, src_layers, src_path, ArcType::Specialize, map, true);
        {
            let n = &mut self.output.nodes[new_node.idx()];
            n.origin = Some(src);
            n.sibling_num_at_origin = sibling;
            n.has_specs = has_specs;
        }
        self.add_tasks_for_node(new_node);
        Ok(Some(new_node))
    }

    /// Copies every specializes node in a grafted subtree under the root (C++
    /// `_EvalImpliedSpecializes`). A no-op at the root node, which has no parent.
    fn eval_implied_specializes(&mut self, node: NodeId) -> Result<(), Error> {
        if self.node(node).parent().is_none() {
            return Ok(());
        }
        self.find_specializes_to_propagate_to_root(node)
    }

    /// Walks the subtree under `node`, copying each specializes node to the root
    /// (C++ `_FindSpecializesToPropagateToRoot`).
    fn find_specializes_to_propagate_to_root(&mut self, node: NodeId) -> Result<(), Error> {
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
    /// the prim to the recursive builder.
    fn add_ref_or_payload_arc(
        &mut self,
        parent: NodeId,
        asset_path: &str,
        prim_path: &Path,
        arc: ArcType,
        arc_offset: LayerOffset,
    ) -> Result<(), Error> {
        let is_internal = asset_path.is_empty();
        let parent_path = self.node(parent).path.clone();

        // Resolve the target layer stack. An internal reference targets the
        // referencing node's own layer stack (C++ `node.GetLayerStack()`); an
        // external one resolves the asset's sublayer stack.
        let (target_stack, target_is_root) = if is_internal {
            let stack = self.node(parent).layer_stack().to_vec();
            let is_root = self.ambient_is_root_for(&stack);
            (stack, is_root)
        } else {
            let Some(layer_index) = find_layer(asset_path, &self.inputs.stack.layers, &*self.inputs.stack.resolver)
            else {
                // An unresolvable asset is a recoverable error (C++
                // `PcpErrorUnresolvedPrimPath`): record it and skip the arc so the
                // rest of the prim — including its own local opinions — still composes.
                self.errors.push(Error::UnresolvedLayer {
                    asset_path: asset_path.to_string(),
                    arc,
                    site_path: parent_path,
                });
                return Ok(());
            };
            (self.inputs.stack.sublayer_stack(layer_index), false)
        };

        // Resolve the source prim path, falling back to the target layer's
        // `defaultPrim` when the arc names no prim (C++ `_GetDefaultPrimPath`).
        let source = if prim_path.is_empty() {
            let Some(p) = self.resolve_default_prim(&target_stack)? else {
                // Missing target `defaultPrim` is likewise recoverable: record it
                // and skip the arc; the prim's other opinions still compose.
                self.errors.push(Error::MissingDefaultPrim {
                    layer_id: self.inputs.stack.layer(target_stack[0].0).identifier.clone(),
                    arc,
                    site_path: parent_path,
                });
                return Ok(());
            };
            p
        } else {
            prim_path.clone()
        };

        let rep = target_stack[0].0;
        // A duplicate site reached inside a skip sub-build is skipped, keeping a
        // class reached both directly and through this arc from grafting twice.
        if self.frame_skip() && self.find_duplicate(rep, &source) {
            return Ok(());
        }
        if !self.arc_target_in_bounds(parent, rep, &source) {
            return Err(Error::ArcCycle {
                path: self.site.path.clone(),
                depth: self.frame_depth,
            });
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
        // ancestral sub-index and graft it under the parent.
        if !is_root_prim(&source) {
            self.compose_and_graft(
                &source,
                &target_stack,
                target_is_root,
                self.frame_skip(),
                parent,
                arc,
                map,
                parent,
                0,
            )?;
            return Ok(());
        }

        // An arc target authoring no spec is kept as a culled node (C++
        // culling): visible to change tracking and dependency registration, but
        // contributing no opinions to value resolution.
        let empty = !self.stack_has_spec(&target_stack, &source);
        let new_node = self
            .output
            .add_site_child(parent, target_stack, source, arc, map, false);
        if empty {
            self.output.nodes[new_node.idx()].flags |= NodeFlags::CULLED;
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
    fn resolve_default_prim(&self, target_stack: &[(usize, LayerOffset)]) -> Result<Option<Path>, Error> {
        let root_layer = target_stack
            .iter()
            .map(|&(li, _)| li)
            .find(|&li| li >= self.inputs.stack.session_layer_count)
            .unwrap_or(target_stack[0].0);
        let Some(value) = self
            .inputs
            .stack
            .layer(root_layer)
            .try_get(&Path::abs_root(), FieldKey::DefaultPrim.as_str())?
        else {
            return Ok(None);
        };
        match value.into_owned() {
            Value::Token(name) | Value::String(name) => Ok(Path::new(&format!("/{name}")).ok()),
            _ => Ok(None),
        }
    }

    /// Returns `true` when an arc to `(root_layer, path)` under `parent` is
    /// within the depth bound and is not a composition cycle (C++
    /// `_CheckForCycle`). The walk crosses stack frames: it visits the target's
    /// ancestor sites in this graph, then each parent frame still under
    /// composition, rejecting an arc that lands back on an active ancestor site.
    fn arc_target_in_bounds(&self, parent: NodeId, root_layer: usize, path: &Path) -> bool {
        // Count the arc target node itself, then each ancestor up to the root.
        let mut depth = 1;
        let mut cur = parent;
        while cur.is_valid() {
            let n = self.node(cur);
            if n.layer_index() == root_layer && &n.path == path {
                return false;
            }
            depth += 1;
            cur = n.parent().unwrap_or(NodeId::INVALID);
        }
        // Continue across parent frames (C++ `PcpPrimIndex_StackFrameIterator`):
        // each frame is a sub-build still in progress, so an arc landing back on
        // a frame's build root targets an ancestor under composition — a cycle.
        for (f, search) in self.frame_sites(path) {
            if search == f.root_path && f.graph.node_using_site(root_layer, &search).is_some() {
                return false;
            }
            depth += 1;
        }
        depth <= MAX_DEPTH
    }

    /// Whether `layers` is the stage root layer stack — the only ambient where
    /// an arc target is composed at root and the stage-keyed `cached_indices`
    /// apply. A sub-index composed in this ambient is keyed in the stage cache.
    fn ambient_is_root_for(&self, layers: &[(usize, LayerOffset)]) -> bool {
        self.site.is_root && layers == self.site.ambient
    }

    /// Whether any layer in `stack` authors a spec at `path`.
    fn stack_has_spec(&self, stack: &[(usize, LayerOffset)], path: &Path) -> bool {
        stack.iter().any(|&(li, _)| self.inputs.stack.layer(li).has_spec(path))
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
        if !self.inputs.stack.has_relocates {
            return map;
        }
        let layers = self.node(parent).layer_stack();
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
    fn compose_token_children(&self, node: NodeId, path: &Path, key: ChildrenKey) -> Result<Vec<String>, Error> {
        let mut out: Vec<String> = Vec::new();
        for &(layer, _) in self.node(node).layer_stack() {
            let Some(value) = self.inputs.stack.layer(layer).try_get(path, key.as_str())? else {
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
    fn node(&self, id: NodeId) -> &super::graph::Node {
        &self.output[id.idx()]
    }

    /// A one-element slice over `node`, for the `compose_*_in` helpers that read
    /// a field across a node's member layers.
    fn node_slice(&self, node: NodeId) -> &[super::graph::Node] {
        &self.output[node.idx()..=node.idx()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;

    fn stack(text: &str) -> LayerStack {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        let layer = crate::sdf::Layer::new("root.usd", Box::new(crate::usda::TextReader::from_data(data)));
        LayerStack::new(vec![layer], 0, Box::new(DefaultResolver::new()), true)
    }

    fn multi_stack(layers: &[(&str, &str)]) -> LayerStack {
        session_stack(layers, 0)
    }

    fn build(stack: &LayerStack, prim: &str) -> Option<PrimIndexGraph> {
        let ctx = CompositionContext::default();
        let ambient = stack.root_layer_stack();
        Builder::new(stack, &ctx, &HashMap::new(), &ambient, true)
            .build(&Path::from(prim))
            .expect("builder build")
            .graph
    }

    /// Builds a layer stack whose first `session` layers are session layers.
    fn session_stack(layers: &[(&str, &str)], session: usize) -> LayerStack {
        let layers = layers
            .iter()
            .map(|(id, text)| {
                let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
                crate::sdf::Layer::new(*id, Box::new(crate::usda::TextReader::from_data(data)))
            })
            .collect();
        LayerStack::new(layers, session, Box::new(DefaultResolver::new()), true)
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
        let graph = build(&s, "/Model").expect("reference + class is composed by the builder");
        // The referenced class node, plus the implied class node in root.usd.
        let class_layers: Vec<usize> = graph
            .iter()
            .filter(|n| n.arc == ArcType::Inherit && n.path.as_str() == "/Class")
            .map(|n| n.layer_index())
            .collect();
        assert!(
            class_layers.contains(&0) && class_layers.contains(&1),
            "the class is composed in both the referenced (1) and referencing (0) layers, got {class_layers:?}"
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
    /// distinguishes the queue from the recursive builder's global set.
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
        let graph = build(&s, "/Root").expect("a pure reference diamond is composed by the builder");
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
        let ambient = s.root_layer_stack();
        // Seed the child build with the parent's composed index, as the cache does.
        let root_index = PrimIndex::build_with_context(&Path::from("/Root"), &s, &ctx).expect("root index build");
        let mut cached = HashMap::new();
        cached.insert(Path::from("/Root"), root_index);
        let child = Builder::new(&s, &ctx, &cached, &ambient, true)
            .build(&Path::from("/Root/Child"))
            .expect("builder build")
            .graph
            .expect("child composed by builder");
        assert!(
            child
                .iter()
                .any(|n| n.path.as_str() == "/A/Child" && n.arc == ArcType::Reference && n.has_specs()),
            "the ancestral reference contributes the child's opinion at the deepened site"
        );
    }
}
