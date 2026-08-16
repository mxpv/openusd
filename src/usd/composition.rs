//! The stage's composition: the layer graph, the indices composed from it, the
//! queue of edits awaiting a recompose, and the operations that drive them.
//!
//! A [`Stage`](super::Stage) delegates here rather than holding the three cells
//! itself, so that every `RefCell` borrow of them — and every operation whose
//! correctness depends on their borrow scopes — lives in one file. The named
//! accessors below govern what crosses the module boundary; inside, operations
//! scope their own borrows around the callbacks and loads they drive. `Stage`
//! keeps policy: edit targets, population masking, public handles, authoring,
//! and sink management. What composition needs back from it is
//! [`CompositionHooks`].
//!
//! A layer edit does not recompose inline. Each layer's aggregator sink records
//! a change list into the queue while the graph is borrowed, and reconciliation
//! drains it later, so a read taken before that drain sees stale composition.
//! Settled access is access entered through a `Stage` method that has completed
//! [`process_pending`](StageComposition::process_pending). The `debug_assert!`
//! on an empty queue is a backstop, not the definition: reconciliation empties
//! the queue before applying its snapshot, so during that window the queue is
//! empty while the cache has yet to incorporate the changes.
//!
//! Authoring paths take the graph without a drain, through
//! [`authoring_graph`](StageComposition::authoring_graph) and its `_mut` twin: a
//! transaction resolving its target, or a sublayer-metadata edit whose own
//! commit queues the next edit. `grep authoring_graph` audits that escape — it
//! is confinement, naming, and a debug-build backstop rather than structural
//! enforcement, since choosing the wrong operation stays a caller's mistake to
//! make.

use std::cell::{Ref, RefCell, RefMut};
use std::collections::HashSet;

use anyhow::Result;

use crate::{pcp, sdf};

use super::sink::{Payload, Provenance};

/// One committed layer edit awaiting composed processing.
pub(super) struct PendingEdit {
    /// The transaction it committed under, so a drain groups a transaction's
    /// layers together.
    pub(super) generation: u64,
    /// The edited layer.
    pub(super) layer: pcp::LayerId,
    /// What the commit recorded.
    pub(super) changes: sdf::ChangeList,
    /// The [`Provenance`] a stage authoring method staged for this edit, or
    /// `None` for a direct edit, which resolves against local-layer membership
    /// when the queue drains.
    pub(super) provenance: Option<Provenance>,
}

/// One reconciled transaction, handed to [`CompositionHooks::notify`] with every
/// composition borrow released.
///
/// Owns what [`CommittedChange`](super::CommittedChange) borrows, so delivery
/// outlives the drain that produced it; `Stage` turns it back into the borrowed
/// view through [`Payload::committed_change`].
pub(super) struct CompositionNotice {
    pub(super) payload: Payload,
    pub(super) provenance: Provenance,
    pub(super) generation: u64,
    pub(super) layer_identifier: String,
}

/// What composition needs from the stage that owns it.
///
/// The coordinator drives graph and cache directly; these are the three things
/// it cannot reach — minting the weak handle an aggregator holds, knowing
/// whether a sink is installed, and delivering to sinks, which re-enters the
/// stage.
pub(super) trait CompositionHooks {
    /// Attaches the stage's change aggregator to a freshly interned layer.
    ///
    /// Runs while the graph is borrowed mutably, which is safe because it only
    /// installs a sink — it reads no composition state and re-enters nothing.
    /// [`notify`](Self::notify) is the hook that requires the borrows released.
    fn attach_layer_sink(&self, id: pcp::LayerId, layer: &mut sdf::Layer);

    /// Whether a committed-change payload is worth building, checked once per
    /// transaction group so the no-sink path stays allocation-free.
    fn wants_notice(&self) -> bool;

    /// Delivers a reconciled transaction. Called with no composition borrow
    /// held, so a sink may read the settled stage or author into it.
    fn notify(&self, notice: CompositionNotice);
}

/// The stage's composed state: the loaded layers, the indices composed from
/// them, and the edits recorded but not yet composed.
///
/// Each is its own cell so a borrow of one leaves the others free: composition
/// reads layer data while building into the cache, and an aggregator sink
/// appends to the queue with the graph already borrowed.
pub(super) struct StageComposition {
    /// The loaded layers and their sublayer DAG.
    layers: RefCell<pcp::LayerGraph>,
    /// Lazily-built composition cache of per-prim indices and contexts.
    cache: RefCell<pcp::IndexCache>,
    /// Layer edits recorded by each layer's aggregator sink (installed by
    /// [`intern_layer`](Self::intern_layer)), awaiting composed processing by
    /// [`process_pending`](Self::process_pending).
    ///
    /// Recording an edit and recomposing for it are deliberately split across
    /// this queue rather than recomposing straight from the aggregator
    /// callback, because:
    ///
    /// - Borrows. The aggregator fires inside [`Layer::edit`](sdf::Layer::edit)'s
    ///   commit, which the stage reaches by holding [`layers`](Self::layers) borrowed
    ///   mutably (the layer lives in the graph). Recomposing needs that same
    ///   borrow, plus [`cache`](Self::cache) — so the callback can only append
    ///   to this independent cell, and the drain runs the recompose once the
    ///   graph borrow is released. A layer cannot recompose the stage from the
    ///   middle of its own mutation.
    /// - Batching. A multi-layer edit (a namespace edit across the local stack)
    ///   commits N layers, each firing its aggregator, so N records accumulate
    ///   and the drain drives one recompose for the whole batch instead of N.
    /// - One path for every editor. A direct edit through `Stage::layer_mut`
    ///   fires the same aggregator with no stage borrow held; the callback
    ///   can't tell, so it records uniformly and the recompose happens on the
    ///   next composed read (drain-on-read). Stage-routed and raw layer edits
    ///   flow through the identical path.
    pending: RefCell<Vec<PendingEdit>>,
}

impl StageComposition {
    /// Wraps a freshly built graph and cache.
    pub(super) fn new(layers: pcp::LayerGraph, cache: pcp::IndexCache) -> Self {
        Self {
            layers: RefCell::new(layers),
            cache: RefCell::new(cache),
            pending: RefCell::new(Vec::new()),
        }
    }

    // Settled operations: the caller has already drained.

    /// The layer graph, for a caller that has completed `process_pending`.
    pub(super) fn settled_graph(&self) -> Ref<'_, pcp::LayerGraph> {
        self.assert_settled();
        self.layers.borrow()
    }

    /// The layer graph mutably, for an authoring helper that edits its layers
    /// directly after a drain; the caller drives composition invalidation from
    /// the resulting change lists.
    pub(super) fn settled_graph_mut(&self) -> RefMut<'_, pcp::LayerGraph> {
        self.assert_settled();
        self.layers.borrow_mut()
    }

    /// The composition cache, for a caller that has completed `process_pending`.
    pub(super) fn settled_cache(&self) -> Ref<'_, pcp::IndexCache> {
        self.assert_settled();
        self.cache.borrow()
    }

    /// The composition cache mutably, for a settled mutation that touches the
    /// cache alone (installing load rules).
    fn settled_cache_mut(&self) -> RefMut<'_, pcp::IndexCache> {
        self.assert_settled();
        self.cache.borrow_mut()
    }

    /// Runs one composed-query pass: the graph shared, the cache mutably.
    ///
    /// The arc demands the pass recorded are moved into `demands` before the
    /// borrows release, so the caller can open the demanded layers — which
    /// needs the graph mutably — and run another pass. `demands` is the
    /// caller's reused buffer, so a warmed-up load loop allocates nothing.
    fn query_pass<T>(
        &self,
        query: impl FnOnce(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T>,
        demands: &mut Vec<pcp::Demand>,
    ) -> Result<T> {
        self.assert_settled();
        let layers = self.layers.borrow();
        let mut cache = self.cache.borrow_mut();
        let result = query(&layers, &mut cache);
        cache.swap_pending_loads(demands);
        result
    }

    // Authoring access: the graph without a drain.

    /// Applies a change to graph and cache together, both mutably.
    ///
    /// `f` must be closed: no layer authoring, no stage sink, no layer loading,
    /// nothing that can re-enter the stage while both borrows are held. It is
    /// for self-contained work — `pcp::Changes::apply`, cache invalidation,
    /// stack mark-and-sweep. Notification and demand resolution belong after
    /// the call, once the borrows are gone. Establishing the phase is the
    /// caller's job: reconciliation applies a part-applied snapshot through
    /// here, while `apply_mute` drains first.
    fn update_pair<T>(&self, f: impl FnOnce(&mut pcp::LayerGraph, &mut pcp::IndexCache) -> T) -> T {
        let mut layers = self.layers.borrow_mut();
        let mut cache = self.cache.borrow_mut();
        f(&mut layers, &mut cache)
    }

    /// The layer graph for an authoring path that intentionally tolerates
    /// queued work: a transaction resolving its target, or a sublayer-metadata
    /// edit whose own commit is what queues the next edit. A drain here would
    /// recompose against a half-applied edit.
    pub(super) fn authoring_graph(&self) -> Ref<'_, pcp::LayerGraph> {
        self.layers.borrow()
    }

    /// The layer graph mutably for an authoring path, with the same contract as
    /// [`authoring_graph`](Self::authoring_graph).
    pub(super) fn authoring_graph_mut(&self) -> RefMut<'_, pcp::LayerGraph> {
        self.layers.borrow_mut()
    }

    // The pending-edit queue.

    /// Appends a committed layer edit for the next drain.
    pub(super) fn record_pending(&self, edit: PendingEdit) {
        self.pending.borrow_mut().push(edit);
    }

    /// Whether the queue is empty, for the drain's fast path — the check a read
    /// on a clean stage pays before returning.
    fn pending_is_empty(&self) -> bool {
        self.pending.borrow().is_empty()
    }

    /// Takes the queued edits as an owned snapshot, leaving an empty queue.
    ///
    /// The snapshot is owned and the queue borrow is released before it
    /// returns, so processing it can fire sinks that author: their edits record
    /// onto the emptied queue and belong to the next snapshot, which is what
    /// lets [`process_pending`](Self::process_pending) repeat until the queue stays empty.
    fn take_pending(&self) -> Vec<PendingEdit> {
        self.pending.take()
    }

    /// Drain the layer edits recorded by the aggregators and drive one composition
    /// recompose per snapshot, delivering the composed
    /// [`CommittedChange`](super::CommittedChange) to the stage sinks. The
    /// deferred counterpart to a layer commit: an aggregator records the edit
    /// while the layer graph is borrowed, and this runs once that borrow is
    /// released — after each authoring call, and before any composed read. A
    /// no-op when nothing is pending, so a read on a clean stage costs only the
    /// empty check.
    ///
    /// Runs to quiescence. A sink may author from `after_commit`, and a direct
    /// [`layer_mut`](super::Stage::layer_mut) commit there records onto a queue this
    /// call has already snapshotted; without the repeat, that edit would sit
    /// unprocessed and the read that triggered the drain would compose without
    /// it. Each snapshot is one whole pass — failure clearing, its transaction
    /// groups, reclamation, and the requeue all travel with it — so every group
    /// in a snapshot completes before an edit its own notifications recorded is
    /// processed, and events stay in commit order.
    ///
    /// The loop terminates when sinks stop producing edits. A sink that authors
    /// on every notification never does, so this never returns for it —
    /// unbounded recursion through a stage authoring method, an unbounded spin
    /// through [`layer_mut`](super::Stage::layer_mut).
    //
    // TODO: a re-entrant drain is still possible — a sink authoring through a
    // stage method hits that method's own trailing `process_pending`, which
    // processes the nested edit inside this one rather than after it, so
    // notification order depends on which authoring route the sink took.
    // `layer_identifier` here exists to keep this pass off that path. The
    // generalization is a re-entrancy flag making a nested drain a no-op, which
    // the loop above makes safe (the outer pass picks the work up); it needs a
    // decision on what a sink reading composed state within itself should see.
    pub(super) fn process_pending(&self, hooks: &dyn CompositionHooks) {
        while !self.pending_is_empty() {
            let mut drained = self.take_pending();
            // An edit changes the layers, so a target that previously failed to read
            // may now be readable: forget recorded load failures and drop the indices
            // that recorded one, so the next query re-demands and recomposes them.
            let failures_cleared = self.layers.borrow_mut().clear_failed_loads();
            if failures_cleared {
                self.cache.borrow_mut().drop_load_failed_indices();
            }
            // Entries committed under one transaction id are contiguous — a
            // transaction's layers record together, and the id increases across
            // transactions — so grouping by adjacent equal id carves the queue into
            // per-transaction groups. Each group applies as its own composed change,
            // so unrelated edits (a direct `layer_mut` commit sitting pending when the
            // next stage edit lands) stay separate rather than merging into one event.
            for group in drained.chunk_by_mut(|a, b| a.generation == b.generation) {
                let generation = group[0].generation;
                let provenance = self.resolve_group_provenance(group);
                let edits: Vec<(pcp::LayerId, &sdf::ChangeList)> =
                    group.iter().map(|edit| (edit.layer, &edit.changes)).collect();
                self.apply_change_sets(generation, &edits, provenance, hooks);
            }
            // Sweep before the requeue below: a sweep retires a reclaimed stack's
            // failure diagnostics, so requeueing never re-derives a demand whose
            // barrier would read a reclaimed stack's variables.
            self.reclaim_stale_stacks();
            // A cleared sublayer failure retries even when this round's edits
            // rebuilt no stack: the failure diagnostics requeue as demands, so a
            // repaired asset loads and a still-broken one re-records the same
            // diagnostic.
            if failures_cleared {
                let requeued = self.layers.borrow().requeue_failed_sublayers();
                self.resolve_sublayer_demands(requeued, hooks);
            }
        }
    }

    /// Classify one transaction's committed [`sdf::ChangeList`]s — one per edited
    /// layer — through a single [`pcp::Changes`] cycle and apply the resulting
    /// cache invalidation, delivering one [`CommittedChange`](super::CommittedChange)
    /// (tagged with the transaction `generation`) to the installed sinks.
    ///
    /// [`pcp::Changes::did_change`] takes the per-layer split because
    /// classification is layer-relative; the event instead reports the merged
    /// record, attributed to the strongest edited layer. `provenance` says how the
    /// records' layer-namespace paths reach stage namespace — a batched namespace
    /// edit is [`Provenance::LocalStack`], the local layer stack sharing the
    /// stage's namespace.
    fn apply_change_sets(
        &self,
        generation: u64,
        edits: &[(pcp::LayerId, &sdf::ChangeList)],
        provenance: Provenance,
        hooks: &dyn CompositionHooks,
    ) {
        let mut pcp_changes = pcp::Changes::new();
        {
            let cache = self.cache.borrow();
            pcp_changes.did_change(&cache, edits);
        }
        // Snapshot the after-commit payload before `apply` consumes
        // `pcp_changes`, and only when a sink is installed — the no-sink path
        // stays allocation-free. The event carries both the merged change list
        // (the union, keyed to the strongest layer) and the per-layer records
        // ([`layer_changes`]), so a sink deriving a per-layer diff reads each
        // layer's own record rather than mis-reading a sublayer's change against
        // the strongest layer's data.
        let mut payload = hooks.wants_notice().then(|| {
            let layer_changes: Vec<(String, sdf::ChangeList)> = edits
                .iter()
                .map(|(id, changes)| (self.layer_identifier(*id), (*changes).clone()))
                .collect();
            let mut merged = sdf::ChangeList::new();
            for (_, changes) in edits {
                merged.merge_from(changes);
            }
            Payload::new(&pcp_changes, &merged, layer_changes, &provenance)
        });
        let outcome = self.update_pair(|graph, cache| pcp_changes.apply(cache, graph));
        // The layer-stack tier's paths are known only after `apply` ran — a
        // vars-only edit resyncs its dependents, and names the subtrees whose
        // asset values may re-resolve, exactly when the rebuild changed some
        // stack's composed variables — so they land on the payload here rather
        // than at the snapshot above.
        if let Some(payload) = payload.as_mut() {
            payload.finish(outcome);
        }
        // TODO: the demand resolution below can drop further indices, and the
        // payload is already final, so those never reach
        // `CommittedChange::resynced`. Closing this needs a seam that lets a
        // finished payload take a late addition, and `IndexCache::invalidate_layers`
        // widened to report what it dropped.

        // The recompose may have demanded sublayers — a `${VAR}` entry the
        // edited variables newly select, or a just-authored literal naming an
        // unloaded layer; open them before observers read the settled stage.
        self.resolve_recorded_demands(hooks);

        if let Some(payload) = payload {
            let layer_identifier = edits
                .first()
                .map(|(id, _)| self.layer_identifier(*id))
                .unwrap_or_default();
            hooks.notify(CompositionNotice {
                payload,
                provenance,
                generation,
                layer_identifier,
            });
        }
    }

    /// The [`Provenance`] for one transaction's group of recorded edits. A staged
    /// provenance (published by a stage authoring method) rides the first layer
    /// the transaction committed; an unstaged direct edit resolves from
    /// local-layer membership — [`Provenance::LocalStack`] when the edited layer
    /// is in the root layer stack (its paths are stage paths), else
    /// [`Provenance::DirectLayerEdit`]. A multi-layer group with no staged
    /// provenance is a local-stack batch (its layers share the stage namespace).
    fn resolve_group_provenance(&self, group: &mut [PendingEdit]) -> Provenance {
        if let Some(provenance) = group.iter_mut().find_map(|edit| edit.provenance.take()) {
            return provenance;
        }
        match group {
            [edit]
                if !self
                    .layers
                    .borrow()
                    .root_layer_stack()
                    .iter()
                    .any(|&(lid, _)| lid == edit.layer) =>
            {
                Provenance::DirectLayerEdit
            }
            _ => Provenance::LocalStack,
        }
    }

    /// Reclaims layer-stack instances nothing live references — no cached
    /// prim index, no pending demand, no eager graph root, no live
    /// descendant's variable-source ancestry — see `LayerGraph::sweep_stacks`.
    /// The sweep runs when a stack lost its last cache owner
    /// (`IndexCache::ownership_lost`, unthresholded: a cached entry's removal
    /// releases its stacks immediately, and the next edit seam collects and
    /// retires the orphans' diagnostics) or when registry creation churn
    /// passed the gate (`LayerGraph::sweep_ripe`, which amortizes re-keying
    /// mints and interner value churn).
    ///
    /// Called only at edit seams — the end of a pending-edit drain, a mute, a
    /// deliberate load-rules mutation — never inside the load path: an edit
    /// strands an instance by re-keying its source or by dropping its last
    /// owning index, while [`load_demanded`](Self::load_demanded) and
    /// [`resolve_authoring_stack`](Self::resolve_authoring_stack) hold
    /// freshly resolved handles that no cached index references yet, which a
    /// sweep there would reclaim out from under them.
    fn reclaim_stale_stacks(&self) {
        self.update_pair(|graph, cache| {
            if !cache.ownership_lost() && !graph.sweep_ripe() {
                return;
            }
            cache.reset_ownership_lost();
            let mut marks = pcp::StackMarks::default();
            cache.mark_live_stacks(&mut marks);
            graph.sweep_stacks(marks);
        });
    }

    /// Add `layer` to the stage's graph, returning its id and whether it newly
    /// joined (a duplicate identifier collapses onto the existing node). The one
    /// seam by which a layer joins the stage — both opening (`make_stage`) and
    /// [`insert_layer`](super::Stage::insert_layer) go through it. A freshly-added layer
    /// gets the stage's change aggregator: a [`sdf::LayerSink`] that records the
    /// layer's commits into [`StageComposition`]'s pending queue for
    /// [`process_pending`](Self::process_pending) to recompose, so every layer the
    /// stage owns reports its edits no matter who authors them. The sink holds a
    /// a weak stage handle, so it does not form a reference cycle (the stage owns the
    /// layer, which owns the sink).
    pub(super) fn intern_layer(&self, layer: sdf::Layer, hooks: &dyn CompositionHooks) -> (pcp::LayerId, bool) {
        let mut layers = self.layers.borrow_mut();
        let (id, fresh) = layers.ensure_layer(layer);
        if fresh {
            let node = layers.get_mut(id).expect("just-interned layer is live");
            hooks.attach_layer_sink(id, &mut node.layer);
        }
        (id, fresh)
    }

    /// Opens the layers a composition pass demanded but that were not yet loaded.
    ///
    /// Each demanded asset path is opened together with its sublayer stack and
    /// interned through [`intern_layer`](Self::intern_layer), so the new layers join
    /// the graph with a change sink; the sublayer DAG is then rewired. A
    /// missing or unreadable sublayer of an on-demand target surfaces through
    /// the sublayer-demand pass below: the rewired stack demands the entry,
    /// whose failed open records the per-referrer, per-stack diagnostic the
    /// graph regenerates on each rebuild. A target that cannot be opened is
    /// marked failed with what went wrong, so the next composition pass
    /// reports it — [`MalformedLayer`](pcp::Error::MalformedLayer) for a
    /// read/parse failure, [`UnresolvedLayer`](pcp::Error::UnresolvedLayer)
    /// for a resolve failure — rather than demanding it again; otherwise the
    /// demanding prim's index would never cache.
    ///
    /// Returns whether the pass made progress — a layer joined or a target was
    /// newly marked failed — so the caller recomposes once more; a demanded path
    /// already loaded or already known unreadable is skipped.
    fn load_demanded(&self, pending: &[pcp::Demand], hooks: &dyn CompositionHooks) -> bool {
        let before = self.layers.borrow().len();
        let mut newly_failed = false;
        let mut newly_interned = false;
        // Whether an open ran for each demand this pass: the mint loop below
        // trusts such a demand's contextual selection to be loaded, while a
        // demand whose open decision was made against a target that joined only
        // mid-pass (its sublayer edges not yet wired) is re-checked there.
        let mut opened_this_pass = vec![false; pending.len()];
        for (demand, opened_flag) in pending.iter().zip(&mut opened_this_pass) {
            let asset_path = demand.asset_path.as_str();
            // Whether the target needs opening, and `reload` whether it is a re-open
            // of an already-interned target reached by a new expression-variable
            // context with no contextual instance yet. A re-open (re)loads the
            // `${VAR}` sublayers the new context resolves — including ones nested
            // below a literal sublayer — that an earlier context's open left
            // unloaded. A target a prior open could not read is not retried, and
            // one that failed to resolve is retried only once the resolver can
            // find it — the asset has since appeared.
            let open = {
                let graph = self.layers.borrow();
                let retry_blocked = match graph.load_failure(asset_path) {
                    Some(pcp::LoadFailure::Unreadable(_)) => true,
                    Some(pcp::LoadFailure::Unresolved) => graph.layer_registry().resolve(asset_path).is_none(),
                    None => false,
                };
                if retry_blocked {
                    None
                } else {
                    match graph.id_of(asset_path) {
                        None => Some(false),
                        Some(target) if graph.needs_contextual_open(target, demand.context) => Some(true),
                        Some(_) => None,
                    }
                }
            };
            if let Some(reload) = open {
                *opened_flag = true;
                // The shared graph borrow is dropped before `intern_layer` /
                // `mark_load_failed` take a mutable one. The arc anchored `asset_path`
                // to an absolute identifier, so no anchor is needed. Nested sublayer
                // failures surface through the sublayer-demand pass below, which
                // regenerates each one's diagnostic per stack.
                let opened = {
                    let graph = self.layers.borrow();
                    graph.layer_registry().open_stack(
                        asset_path,
                        None,
                        graph.stack_expression_variables(demand.context),
                        reload,
                        &|_| Ok(()),
                        &|id| graph.id_of(id).is_some(),
                    )
                };
                let failure = match opened {
                    Ok(Some(layers)) => {
                        for layer in layers {
                            self.intern_layer(layer, hooks);
                        }
                        None
                    }
                    // No layer resolved. When the raw asset still resolves —
                    // the layer-level resolution (a package's default layer,
                    // say) is what failed — the failure is recorded as
                    // unreadable: it is terminal, where the arc demand gate
                    // retries a resolvable asset whose failure was
                    // `Unresolved` and would re-run this open every pass.
                    Ok(None) => {
                        let graph = self.layers.borrow();
                        Some(match graph.layer_registry().resolve(asset_path) {
                            None => pcp::LoadFailure::Unresolved,
                            Some(_) => {
                                pcp::LoadFailure::Unreadable(format!("failed to resolve asset path: {asset_path}"))
                            }
                        })
                    }
                    Err(err) => Some(pcp::LoadFailure::Unreadable(format!("{err:#}"))),
                };
                if let Some(failure) = failure {
                    let mut graph = self.layers.borrow_mut();
                    // Only a first failure counts as progress: re-marking an
                    // asset that failed the same way on an earlier pass must
                    // not keep the caller recomposing forever.
                    newly_failed |= graph.load_failure(asset_path).is_none();
                    graph.mark_load_failed(asset_path, failure);
                }
            }
        }
        let grew = self.layers.borrow().len() != before;
        // Newly joined layers need their plain sublayer edges (and relocates) wired
        // before any stack is composed against them.
        if grew {
            // TODO(perf): rebuild only the new subtrees rather than the whole DAG.
            let relocated = self.layers.borrow_mut().recompute_sublayers(None).affected;
            // A demanded layer that introduces relocates restructures prims
            // composed against its stack; drop their cached indices so they
            // recompose with the relocates applied.
            if !relocated.is_empty() {
                self.cache.borrow_mut().invalidate_layers(&relocated);
            }
        }
        // Mint each demand's layer stack now that the edges are wired. The layer
        // graph applies the stack-selection policy idempotently, so a stack the
        // rebuild above already minted, or a context reached before, is left
        // unchanged. A demand whose layers were already loaded (a first-touch
        // context to a known target) lands here directly — interned without a
        // reload. One exception: a demand whose open decision ran against a
        // target that joined only this pass (two same-batch demands for one
        // not-yet-loaded target under different contexts) saw unwired sublayer
        // edges and may have skipped a contextual open it needs; interning it
        // now would permanently record a stack missing its context-selected
        // sublayers, so re-check against the wired graph and leave it for the
        // next pass, which re-demands and reopens correctly. A failed target is
        // exempt (nothing further can load) and interns whatever is present.
        {
            let mut graph = self.layers.borrow_mut();
            for (demand, &was_opened) in pending.iter().zip(&opened_this_pass) {
                let asset_path = demand.asset_path.as_str();
                if let Some(root) = graph.id_of(asset_path) {
                    if !was_opened
                        && !graph.load_failed(asset_path)
                        && graph.needs_contextual_open(root, demand.context)
                    {
                        continue;
                    }
                    newly_interned |= graph.intern_external(root, demand.context).1;
                }
            }
        }
        // The recompute above and any fresh mint can demand sublayers — a
        // `${VAR}` entry whose selected layer nothing has loaded, including a
        // target's own self-selected sublayer under an empty inherited context;
        // open them under each demanding stack's composed variables.
        let sublayers_loaded = self.resolve_recorded_demands(hooks);
        grew || newly_failed || newly_interned || sublayers_loaded
    }

    /// Opens the sublayers a graph recompose or stack mint demanded — a
    /// `${VAR}`-selected (or newly authored literal) `subLayers` entry naming a
    /// layer not yet in the graph — to a fixed point, the sublayer counterpart
    /// of [`load_demanded`](Self::load_demanded).
    ///
    /// Each demand opens the entry's layer, with its own sublayer subtree,
    /// under the demanding stack's composed expression variables unchanged — a
    /// sublayer contributes no variables (C++ `PcpExpressionVariables`,
    /// `LayerRegistry::open_sublayer_tree`). The sublayer DAG is then rewired,
    /// the indices reading the affected stacks are dropped, and the loop
    /// continues on the demands the recompose re-derives — a nested `${VAR}`
    /// below a just-opened literal converges across rounds — until a round
    /// opens nothing. A demand whose layer another stack's demand interned
    /// this round schedules its own stack's recompose instead of an open; one
    /// whose `(identifier, stack)` pair was already attempted this call is
    /// skipped, and the attempted set grows monotonically while a failure is
    /// terminal until an edit clears the recorded load failures, so the loop
    /// terminates.
    ///
    /// A failed open is framed as this referrer's diagnostic and recorded in
    /// the demanding stack's regenerable bucket
    /// (`LayerGraph::record_sublayer_error`) — a known-failed identifier is
    /// not retried, but every referrer that demands it still gets its own
    /// diagnostic, matching open-time collection — and marked failed so later
    /// rebuilds regenerate the diagnostic instead of retrying. A failure
    /// nested inside an opened subtree surfaces next round, when the rewired
    /// stack re-derives the failing entry as its own demand.
    ///
    /// Returns whether any layer joined the graph.
    fn resolve_sublayer_demands(&self, mut demands: Vec<pcp::SublayerDemand>, hooks: &dyn CompositionHooks) -> bool {
        let mut attempted: HashSet<(String, pcp::LayerStackId)> = HashSet::new();
        let mut recomposed: HashSet<(pcp::LayerId, String)> = HashSet::new();
        let mut reported: HashSet<(String, pcp::LayerStackId, pcp::LayerId)> = HashSet::new();
        let mut loaded_any = false;
        while !demands.is_empty() {
            let mut opened_parents: HashSet<pcp::LayerId> = HashSet::new();
            for demand in demands.drain(..) {
                // Re-anchoring also refreshes the graph's resolution memo, so
                // the round's recompose resolves the entry the same way this
                // check just did.
                let open = {
                    let mut graph = self.layers.borrow_mut();
                    graph
                        .refresh_demanded_sublayer(demand.parent, &demand.evaluated)
                        .err()
                        .map(|identifier| (identifier, graph.identifier(demand.parent).to_string()))
                };
                let Some((identifier, parent_identifier)) = open else {
                    // The layer is interned — another demand this round loaded
                    // it — so the demanding stack needs the round's recompose
                    // to pick the member up. One recompose credit per entry:
                    // a recompose that could not resolve the member settles it
                    // for this call.
                    if recomposed.insert((demand.parent, demand.evaluated.clone())) {
                        opened_parents.insert(demand.parent);
                    }
                    continue;
                };
                {
                    // One diagnostic per (referrer, stack, canonical id): a
                    // second authored spelling of the same entry reports
                    // nothing more, matching open-time collection.
                    let mut graph = self.layers.borrow_mut();
                    if let Some(failure) = graph.load_failure(&identifier) {
                        if reported.insert((identifier.clone(), demand.stack, demand.parent)) {
                            let error = failure.sublayer_error(&demand.evaluated, &parent_identifier);
                            graph.record_sublayer_error(demand.stack, error);
                        }
                        continue;
                    }
                }
                if !attempted.insert((identifier.clone(), demand.stack)) {
                    continue;
                }
                // The shared graph borrow is dropped before `intern_layer` /
                // `mark_load_failed` take a mutable one, as in `load_demanded`.
                let opened = {
                    let graph = self.layers.borrow();
                    graph.layer_registry().open_sublayer_tree(
                        &identifier,
                        graph.stack_expression_variables(demand.stack),
                        &|id| graph.id_of(id).is_some(),
                    )
                };
                let failure = match opened {
                    Ok(Some(layers)) => {
                        for layer in layers {
                            self.intern_layer(layer, hooks);
                        }
                        opened_parents.insert(demand.parent);
                        None
                    }
                    Ok(None) => Some(pcp::LoadFailure::Unresolved),
                    Err(err) => Some(pcp::LoadFailure::Unreadable(format!("{err:#}"))),
                };
                if let Some(load_failure) = failure {
                    let mut graph = self.layers.borrow_mut();
                    reported.insert((identifier.clone(), demand.stack, demand.parent));
                    let error = load_failure.sublayer_error(&demand.evaluated, &parent_identifier);
                    graph.record_sublayer_error(demand.stack, error);
                    graph.mark_load_failed(&identifier, load_failure);
                }
            }
            if opened_parents.is_empty() {
                break;
            }
            loaded_any = true;
            // Rewire the DAG scoped to the parents whose subtrees grew — their
            // changed edges name every stack the new layers join — and drop the
            // indices reading an affected stack so they recompose against the
            // extended members. The recompose re-derives the pending demand set
            // for the next round.
            let (affected, next) = {
                let mut graph = self.layers.borrow_mut();
                let affected = graph.recompute_sublayers(Some(&opened_parents)).affected;
                (affected, graph.take_sublayer_demands())
            };
            if !affected.is_empty() {
                self.cache.borrow_mut().invalidate_layers(&affected);
            }
            demands = next;
        }
        loaded_any
    }

    /// A layer's identifier read without draining, for the reconciliation pass:
    /// a drain there would run against a part-applied snapshot, and — once an
    /// earlier group's sink has authored — would process that edit ahead of the
    /// snapshot's remaining groups, putting notifications out of commit order.
    /// Empty for a layer no longer in the graph.
    fn layer_identifier(&self, id: pcp::LayerId) -> String {
        self.layers.borrow().try_identifier(id).unwrap_or_default().to_string()
    }

    /// Runs a composed query, driving on-demand layer loading to a fixpoint.
    ///
    /// Each pass takes the graph shared and the cache mutably, mirroring how
    /// composition reads layer data while lazily building the index. A
    /// reference or payload arc to a not-yet-loaded layer records a demand
    /// instead of composing (the index is left uncached); after the pass the
    /// borrows are released, the demanded layers are opened, and the query
    /// re-runs. The loop ends when a pass demands nothing, or when a demanded
    /// target cannot be opened, so loading makes no progress. Composition thus
    /// drives layer loading: an un-visited subtree never loads.
    pub(super) fn query<T>(
        &self,
        mut query: impl FnMut(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T>,
        hooks: &dyn CompositionHooks,
    ) -> Result<T> {
        // Reused across passes: swapped with the cache's queue so neither
        // reallocates once warmed up.
        let mut pending: Vec<pcp::Demand> = Vec::new();
        loop {
            let result = self.query_pass(&mut query, &mut pending);
            // The pass left a reference/payload arc uncomposed pending these
            // layers; open them and recompose. `load_demanded` reports false once a
            // pass neither loads a layer nor newly marks one failed, so the loop
            // ends after an unopenable target is marked failed and the following
            // pass recomposes its prim — recording the arc unresolved — without it.
            if pending.is_empty() || !self.load_demanded(&pending, hooks) {
                return result;
            }
            pending.clear();
        }
    }

    /// Applies a muted-set mutation and recomposes when it reports a change,
    /// returning the canonical identifier whose muted state toggled and the
    /// paths the toggle invalidated (`None` when the set was unchanged).
    ///
    /// Drains first so the mute recomposes against a current graph and cache
    /// rather than stranding queued changes, then resolves any `${VAR}`
    /// sublayer the new selection newly exposed and reclaims the stacks a
    /// flipped variable source stranded — both with the borrows released.
    pub(super) fn apply_mute(
        &self,
        mutate: impl FnOnce(&mut pcp::LayerGraph) -> Option<pcp::MuteChange>,
        hooks: &dyn CompositionHooks,
    ) -> Option<(String, Vec<sdf::Path>)> {
        self.process_pending(hooks);
        let (changed, resynced, demands) = self.update_pair(|graph, cache| {
            let change = mutate(graph)?;
            // The mutation already rebuilt the graph's sublayer stacks, relocates, and
            // cycle diagnostics; only the cache needs work. Removing a session variable
            // drops the root `${VAR}` sublayer it selected — the graph re-resolves the
            // already-interned layer out of the stack. Dropping the affected indices by
            // both the toggled layer's fanout and its canonical identifier reaches a
            // referrer that skipped this target while it was muted-and-never-loaded, so
            // unmuting recomposes it and the load barrier finally opens the target.
            let resynced = cache.invalidate_muting(&change.affected, &change.changed);
            Some((change.changed, resynced, graph.take_sublayer_demands()))
        })?;
        // The set gathered above is the whole answer, though resolving the demands
        // invalidates again: `mute_fanout` answers a session mute — the only kind
        // that can move a stack's composed variables — with the root layer and so
        // with every index, and a sublayer an unmute newly exposes joins only
        // stacks that already held the unmuted layer. Either way the second pass
        // reaches what the first already named.
        self.resolve_sublayer_demands(demands, hooks);
        // A mute can flip a stack's variable source (its authored variables
        // stop contributing), stranding the old-keyed instance — the mute path
        // discards variable deltas, so the sweep is what reclaims it. Discarding
        // them costs no notice; `LayerGraph::recompose_for_mute` carries the
        // argument.
        self.reclaim_stale_stacks();
        Some((changed, resynced))
    }

    /// Resolves the layer stack an edit target authors into, loading whatever
    /// the resolution demands.
    ///
    /// `authoring` is the target's captured stack identity, taken by value:
    /// loading re-enters the stage, so the caller must clone it out of the edit
    /// target rather than hold that borrow across this call. An arc target
    /// carries the exact stack it authors into by value identity, resolved
    /// against this graph. The walk is read-only and demand-driven: a chain
    /// layer not loaded here, or a contextual stack not yet composed, comes back
    /// as the demand the load barrier satisfies (opening any `${VAR}`-selected
    /// sublayers its context resolves before interning), and the walk re-runs.
    /// It ends when the identity resolves, or `Err` names the chain layer that
    /// could not be opened — authoring into a substitute stack would seed the
    /// relocate plan from the wrong members and expression variables.
    pub(super) fn resolve_authoring_stack(
        &self,
        target_layer: pcp::LayerId,
        authoring: Option<Box<pcp::StackIdentity>>,
        hooks: &dyn CompositionHooks,
    ) -> Result<pcp::LayerStackId, String> {
        if let Some(identity) = authoring {
            loop {
                let demand = match self.layers.borrow().resolve_stack_identity(&identity) {
                    Ok(id) => return Ok(id),
                    Err(demand) => demand,
                };
                let layer = demand.asset_path.clone();
                if !self.load_demanded(&[demand], hooks) {
                    return Err(layer);
                }
            }
        }
        // A target without a captured authoring stack (a local or variant
        // target) is inferred from layer membership: the root stack when
        // `target_layer` belongs to it, else the root-sourced stack rooted at
        // the layer itself — minted when the target was never composed in this
        // session rather than falling back to an unrelated stack (which would
        // seed the relocate plan from the wrong layers).
        self.process_pending(hooks);
        {
            let layers = self.settled_graph();
            if layers.root_layer_stack().iter().any(|&(id, _)| id == target_layer) {
                return Ok(pcp::LayerStackId::ROOT);
            }
        }
        let (id, demands) = {
            let mut graph = self.layers.borrow_mut();
            let id = graph.intern_external(target_layer, pcp::LayerStackId::ROOT).0;
            (id, graph.take_sublayer_demands())
        };
        self.resolve_sublayer_demands(demands, hooks);
        Ok(id)
    }

    /// Opens whatever sublayers the graph has recorded as demanded, reporting
    /// whether any layer joined. The single seam between a graph mutation and
    /// the `${VAR}` selections it newly exposed.
    fn resolve_recorded_demands(&self, hooks: &dyn CompositionHooks) -> bool {
        let demands = self.layers.borrow_mut().take_sublayer_demands();
        self.resolve_sublayer_demands(demands, hooks)
    }

    /// Brings a freshly built stage's composition up: interns every collected
    /// layer, wires the sublayer DAG, seeds the muted set and the loader's
    /// recorded failures, and opens whatever the finalize recompose demanded, so
    /// the opened stage starts settled.
    ///
    /// `layers` arrives in strength order with the session layers first, so the
    /// root is the first non-session entry. A duplicate identifier (a dependency
    /// reached through both the session and root collections) collapses onto one
    /// node, which is why only fresh session layers count toward the session
    /// span and the root is captured at its original slot.
    pub(super) fn initialize(
        &self,
        layers: Vec<sdf::Layer>,
        session_layer_count: usize,
        muted: HashSet<String>,
        failures: Vec<(String, String, pcp::LoadFailure)>,
        hooks: &dyn CompositionHooks,
    ) {
        // Every layer joins through the one intern seam, so each gets its change
        // aggregator as it joins.
        let mut root = None;
        let mut session_count = 0;
        for (i, layer) in layers.into_iter().enumerate() {
            let (id, fresh) = self.intern_layer(layer, hooks);
            if i == session_layer_count {
                root = Some(id);
            }
            if fresh && i < session_layer_count {
                session_count += 1;
            }
        }
        self.layers.borrow_mut().finalize(session_count, root);
        if !muted.is_empty() {
            // Seed the graph's muted set (it drops any root-layer request and
            // re-resolves identifiers on each later rebuild). The cache is still
            // empty (composition is lazy), so no cache invalidation is needed yet.
            // The raw collection diagnostics stay as the loader recorded them; the
            // muted ones are filtered out at report time (`Stage::composition_errors`)
            // against the current composed state, so an unmute restores a diagnostic
            // a muted branch had hidden.
            self.layers.borrow_mut().set_muted_identifiers(muted);
        }
        {
            let mut graph = self.layers.borrow_mut();
            for (asset_path, introduced_by, failure) in failures {
                if let Some(parent) = graph.id_of(&introduced_by)
                    && let Err(identifier) = graph.resolve_relative(&asset_path, parent)
                {
                    graph.mark_load_failed(&identifier, failure);
                }
            }
        }
        // Loading collected the initial `${VAR}` selections, but a composed
        // stack can still name an unloaded layer — an eager target's sublayer
        // selected by its own variables, or a selection open-time muting
        // exposed; drain the demands the finalize recompose recorded.
        self.resolve_recorded_demands(hooks);
        // That drain re-derived the sublayer failures of every region — the
        // session region, the root region, and each target stack all re-resolve
        // per rebuild — as per-stack regenerable diagnostics; the loader's
        // one-shot copies of those would double-report and outlive a later fix,
        // so they are dropped.
        let superseded: Vec<pcp::Error> = {
            let graph = self.layers.borrow();
            graph
                .errors()
                .into_iter()
                .filter(|error| {
                    matches!(
                        error,
                        pcp::Error::UnresolvedSublayer { .. }
                            | pcp::Error::MalformedSublayer { .. }
                            | pcp::Error::InvalidExpression { .. }
                    )
                })
                .collect()
        };
        if !superseded.is_empty() {
            self.cache.borrow_mut().discard_collection_errors(&superseded);
        }
    }

    /// Reads the load rules, applies `edit`, installs the result, and reclaims
    /// the stacks the change stranded — the deliberate mutation entry.
    ///
    /// Returns the bounded set of paths whose cached index was dropped (empty
    /// for a no-op edit). An unload can leave payload-target stacks
    /// unreferenced for a long stretch, so this reclaims while the seam is
    /// quiet, whenever accumulated registry churn has ripened the trigger.
    pub(super) fn install_load_rules(
        &self,
        edit: impl FnOnce(&mut pcp::LoadRules),
        hooks: &dyn CompositionHooks,
    ) -> Vec<sdf::Path> {
        // Drain before reading: a queued edit's notification may itself install
        // load rules, and `edit` is applied to whatever this read returns, so a
        // pre-drain snapshot would overwrite that change on the way back out.
        self.process_pending(hooks);
        let mut rules = self.settled_cache().load_rules().clone();
        edit(&mut rules);
        let victims = self.swap_load_rules(rules, hooks);
        self.reclaim_stale_stacks();
        victims
    }

    /// Installs `rules` in place of the current table, returning the bounded set
    /// of paths whose cached index was dropped.
    ///
    /// Drains first so the mutation recomposes against a current graph and
    /// cache, matching [`apply_mute`](Self::apply_mute). Reclaims nothing: this
    /// is also the transient swap behind the loadability walk, which must leave
    /// the payload-target stacks it composes untouched.
    pub(super) fn swap_load_rules(&self, rules: pcp::LoadRules, hooks: &dyn CompositionHooks) -> Vec<sdf::Path> {
        self.process_pending(hooks);
        self.settled_cache_mut().set_load_rules(rules)
    }

    /// Backstop for the settled operations: the queue being empty is necessary
    /// for settledness, not sufficient (see the module doc).
    fn assert_settled(&self) {
        debug_assert!(
            self.pending.borrow().is_empty(),
            "settled composition access with edits still queued: drain through Stage::process_pending first"
        );
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use super::*;

    fn composition() -> StageComposition {
        StageComposition::new(
            pcp::LayerGraph::new(sdf::LayerRegistry::default()),
            pcp::IndexCache::new(pcp::VariantFallbackMap::new(), pcp::LoadRules::all(), Vec::new()),
        )
    }

    fn edit() -> PendingEdit {
        PendingEdit {
            generation: 0,
            layer: pcp::LayerId::from_raw(0),
            changes: sdf::ChangeList::new(),
            provenance: None,
        }
    }

    /// An empty queue is settled, so the settled reads run.
    #[test]
    fn settled_access_when_empty() {
        let composition = composition();
        assert_eq!(composition.settled_graph().len(), 0);
        assert_eq!(composition.settled_cache().indexed_count(), 0);
    }

    /// A queued edit leaves the state unsettled, and the backstop says so.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "settled composition access with edits still queued")]
    fn settled_access_asserts_queued() {
        let composition = composition();
        composition.record_pending(edit());
        let _ = composition.settled_graph();
    }

    /// Draining the queue restores settled access.
    #[test]
    fn drain_restores_settled_access() {
        let composition = composition();
        composition.record_pending(edit());
        assert_eq!(composition.take_pending().len(), 1);
        assert_eq!(composition.settled_graph().len(), 0);
    }

    /// The snapshot is owned, so recording while it is being processed succeeds
    /// and the new edit lands in a fresh queue for the next drain.
    #[test]
    fn drain_snapshot_is_owned() {
        let composition = composition();
        composition.record_pending(edit());

        let snapshot = composition.take_pending();
        // Standing in for a sink authoring from `after_commit`.
        composition.record_pending(edit());
        assert_eq!(snapshot.len(), 1, "the snapshot is unaffected by the new edit");

        assert_eq!(composition.take_pending().len(), 1, "the new edit awaits its own drain");
        assert!(composition.take_pending().is_empty());
    }

    /// Hooks that accept every notice, for exercising the operations that need
    /// a stage without one existing.
    struct StubHooks;

    impl CompositionHooks for StubHooks {
        fn attach_layer_sink(&self, _id: pcp::LayerId, _layer: &mut sdf::Layer) {}

        fn wants_notice(&self) -> bool {
            true
        }

        fn notify(&self, _notice: CompositionNotice) {}
    }

    /// `swap_load_rules` drains before installing, so a queued edit is
    /// reconciled rather than stranded by the mutation.
    #[test]
    fn swap_rules_drains_first() {
        let composition = composition();
        composition.record_pending(edit());

        composition.swap_load_rules(pcp::LoadRules::none(), &StubHooks);

        assert!(
            composition.pending_is_empty(),
            "the queued edit was reconciled by the swap's drain"
        );
        assert_eq!(
            composition
                .settled_cache()
                .load_rules()
                .effective_rule(&sdf::Path::abs_root()),
            pcp::Rule::None
        );
    }

    /// A rule change made from a notification fired during the install's own
    /// drain survives: the table is read after the drain, so the install does not
    /// overwrite it with a pre-drain snapshot.
    #[test]
    fn install_rules_keeps_reentrant_change() {
        struct RuleSetter<'a>(&'a StageComposition, Cell<bool>);
        impl CompositionHooks for RuleSetter<'_> {
            fn attach_layer_sink(&self, _id: pcp::LayerId, _layer: &mut sdf::Layer) {}
            fn wants_notice(&self) -> bool {
                true
            }
            fn notify(&self, _notice: CompositionNotice) {
                // Standing in for a sink installing load rules from `after_commit`.
                if !self.1.replace(true) {
                    self.0.install_load_rules(|rules| *rules = pcp::LoadRules::none(), self);
                }
            }
        }

        let composition = composition();
        composition.record_pending(edit());
        let hooks = RuleSetter(&composition, Cell::new(false));

        // A no-op batch: everything it installs comes from the table it read.
        composition.install_load_rules(|_| {}, &hooks);

        assert_eq!(
            composition
                .settled_cache()
                .load_rules()
                .effective_rule(&sdf::Path::abs_root()),
            pcp::Rule::None,
            "the re-entrant rule change was not overwritten"
        );
    }

    /// `notify` runs with no composition borrow held, so a sink may read the
    /// stage or author into it.
    #[test]
    fn notify_runs_unborrowed() {
        struct BorrowProbe<'a>(&'a StageComposition, Cell<bool>);
        impl CompositionHooks for BorrowProbe<'_> {
            fn attach_layer_sink(&self, _id: pcp::LayerId, _layer: &mut sdf::Layer) {}
            fn wants_notice(&self) -> bool {
                true
            }
            fn notify(&self, _notice: CompositionNotice) {
                self.1
                    .set(self.0.layers.try_borrow_mut().is_ok() && self.0.cache.try_borrow_mut().is_ok());
            }
        }

        let composition = composition();
        let probe = BorrowProbe(&composition, Cell::new(false));
        composition.record_pending(edit());
        composition.process_pending(&probe);
        assert!(probe.1.get(), "notify saw both cells free");
    }

    /// A query pass releases both borrows and hands back what it demanded, so
    /// the caller can take the graph mutably to open the demanded layers.
    #[test]
    fn query_pass_releases_borrows() {
        let composition = composition();
        let mut demands = Vec::new();
        let count = composition
            .query_pass(|layers, cache| Ok(layers.len() + cache.indexed_count()), &mut demands)
            .expect("query runs");
        assert_eq!(count, 0);
        assert!(demands.is_empty(), "an empty stage demands nothing");
        // Both borrows are gone, so a mutable pair is available immediately.
        composition.update_pair(|layers, _| assert_eq!(layers.len(), 0));
    }
}
