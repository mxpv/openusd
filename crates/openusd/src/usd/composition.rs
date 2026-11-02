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
//! A layer edit does not recompose inline. Each layer's recorder queues a
//! change list as the commit lands, while the layers are borrowed, and
//! reconciliation drains it later, so a read taken before that drain sees
//! stale composition.
//! Settled access is access entered through a `Stage` method that has completed
//! [`process_pending`](StageComposition::process_pending). The assertions
//! behind it are a backstop, not the definition: reconciliation empties the
//! queue before applying its snapshot, and the drain it runs is what marks
//! that window.
//!
//! Composition runs user code (a resolver, a file format) while it reads
//! layers and while it rebuilds their composition. A panic out of it leaves
//! the composition half-built, so it poisons the stage
//! ([`Poisoned`]), which composes nothing more.
//!
//! Authoring paths take the graph without a drain, through
//! [`authoring_graph`](StageComposition::authoring_graph) and its `_mut` twin: a
//! transaction resolving its target, or a sublayer-metadata edit whose own
//! commit queues the next edit. `grep authoring_graph` audits that escape — it
//! is confinement, naming, and a debug-build backstop rather than structural
//! enforcement, since choosing the wrong operation stays a caller's mistake to
//! make.

use std::cell::{Cell, RefCell};
use std::collections::{HashSet, VecDeque};
use std::mem;
use std::rc::Rc;
use std::sync::Arc;
use std::thread;

use crate::{Result, ar, pcp, sdf, tf};

use super::sink::{Payload, Provenance, ResyncPaths};

/// One transaction outcome awaiting reconciliation, in commit order.
pub(super) enum Pending {
    /// A layer edit that landed.
    Edit(PendingEdit),
    /// A transaction that began committing and did not land, by id: one entry
    /// per layer it reached.
    Aborted(u64),
    /// A change to the stage that no layer edit made.
    Stage(StageNotice),
}

/// One committed layer edit awaiting composed processing.
pub(super) struct PendingEdit {
    /// The transaction it committed under, so a drain groups a transaction's
    /// layers together.
    pub(super) generation: u64,
    /// The edited layer.
    pub(super) layer: pcp::LayerId,
    /// What the commit recorded.
    pub(super) changes: sdf::ChangeList,
    /// Whether the edit is the stage's own (see
    /// [`CommittedChange::is_own`](super::CommittedChange::is_own)).
    pub(super) own: bool,
    /// The [`Provenance`] a stage authoring method staged for this edit, or
    /// `None` for a direct edit, which resolves against local-layer membership
    /// when the queue drains.
    pub(super) provenance: Option<Rc<Provenance>>,
    /// The layer's `defaultPrim` before this commit, captured at the commit seam
    /// because the change record carries field names, not prior values. See
    /// [`pcp::LayerChanges::prior_default_prim`].
    pub(super) prior_default_prim: Option<tf::Token>,
    /// The specs and fields the edit touched, kept for the stage's
    /// transaction observers and `None` when it has none.
    pub(super) footprint: Option<Rc<sdf::Footprint>>,
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
    pub(super) own: bool,
    pub(super) layer_identifier: String,
    /// Each edited layer's footprint, for the stage's transaction observers.
    pub(super) footprints: Vec<(pcp::LayerId, Rc<sdf::Footprint>)>,
}

/// What composition needs from the stage that owns it.
///
/// The coordinator drives graph and cache directly; these are the three things
/// it cannot reach — minting the weak handle the stage's layer observers hold, knowing
/// whether a sink is installed, and delivering to sinks, which re-enters the
/// stage.
pub(super) trait CompositionHooks {
    /// Subscribes the stage's recorder to a freshly interned layer's commits,
    /// returning the subscription for the layer's node to hold.
    ///
    /// Runs while the graph is borrowed mutably, which is safe because it only
    /// subscribes — it reads no composition state and re-enters nothing.
    /// [`notify`](Self::notify) is the hook that requires the borrows released.
    fn subscribe_layer(&self, id: pcp::LayerId, layer: &sdf::LayerHandle) -> sdf::Subscription;

    /// Whether a committed-change payload is worth building, checked once per
    /// transaction group so the no-sink path stays allocation-free.
    fn wants_notice(&self) -> bool;

    /// Whether a delivered notice reaches anyone: a payload an internal
    /// observer wanted is not queued for delivery when no sink is installed.
    fn delivers(&self) -> bool {
        self.wants_notice()
    }

    /// Delivers a reconciled transaction. Called with no composition borrow
    /// held, so a sink may read the settled stage or author into it.
    fn notify(&self, notice: CompositionNotice);

    /// Delivers that the transaction `generation` began committing to one of
    /// the stage's layers and did not land. Called as
    /// [`notify`](Self::notify) is.
    fn aborted(&self, generation: u64) {
        let _ = generation;
    }

    /// Delivers a change to the stage that no layer edit made. Called as
    /// [`notify`](Self::notify) is.
    fn notify_stage(&self, notice: &StageNotice) {
        let _ = notice;
    }

    /// Tells the stage's internal observers that `notice`'s transaction was
    /// reconciled. Called by the drain with its borrows released, before the
    /// next transaction reconciles; it runs no user code.
    fn observe(&self, notice: &CompositionNotice) {
        let _ = notice;
    }

    /// Tells the stage's internal observers that the transaction `generation`
    /// did not land. Called as [`observe`](Self::observe) is.
    fn observe_abort(&self, generation: u64) {
        let _ = generation;
    }

    /// Tells the stage's internal observers that the layers in `layers` are
    /// about to leave the graph, or were reloaded: history on them is stale.
    /// Runs no user code.
    fn departed(&self, layers: &HashSet<pcp::LayerId>) {
        let _ = layers;
    }

    /// The identifiers of the stage's edit target layer and of the layers
    /// its open edit contexts will restore as the target, which a layer
    /// reclamation keeps.
    fn edit_target_identifiers(&self) -> Vec<String> {
        Vec::new()
    }
}

/// One notice waiting in the outbox for delivery.
enum Notice {
    /// A transaction that landed.
    Committed(Box<CompositionNotice>),
    /// A transaction that did not land, by id.
    Aborted(u64),
    /// A change to the stage that no layer edit made.
    Stage(StageNotice),
}

/// A change to the stage that no layer edit made, delivered in order with the
/// committed transactions.
pub(super) enum StageNotice {
    /// The edit target changed.
    EditTarget,
    /// The load rules changed, resyncing these paths.
    LoadRules(ResyncPaths),
    /// The failed loads were tried again, resyncing these paths.
    LoadsRetried(ResyncPaths),
    /// What an operation discovered that no other notice carries: the prims
    /// a read's or a mutation's layer loads dropped or restaled.
    Recomposed(ResyncPaths),
    /// A layer was muted or unmuted, resyncing these paths.
    Muting {
        layer: String,
        muted: bool,
        resynced: ResyncPaths,
    },
}

/// Whether a [`fixpoint`](StageComposition::fixpoint)'s caller drained the
/// queue of recorded edits first, or runs inside the drain that took it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Settled {
    /// The queue was drained: a read, or a settlement a mutation runs. Edits
    /// the fixpoint's own loads queue are reconciled before its next pass.
    Required,
    /// A drain took the queue and is composing it. Edits the fixpoint's
    /// loads queue go to that drain, which applies them in commit order.
    Taken,
}

/// Why a [`fixpoint`](StageComposition::fixpoint) stopped before its pass
/// settled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Interrupted {
    /// Its loads ran user code (a resolver, a file format) that committed to
    /// a layer of the stage, queueing edits the drain it runs inside applies
    /// first.
    NewWork,
}

/// What a load-rules change's `victims` mean to an observer. An ancestor
/// whose effective rule the change only derived again recomposes in place.
/// One whose inclusion flipped changed its subtree when it has a payload of
/// its own (in `payloads`), which the flip includes or leaves out.
/// They join `paths`, which comes back normalized.
fn classify(victims: pcp::RuleVictims, payloads: &HashSet<sdf::Path>, mut paths: ResyncPaths) -> ResyncPaths {
    paths.subtrees.extend(victims.subtrees);
    for (ancestor, flipped) in victims.ancestors {
        if flipped && payloads.contains(&ancestor) {
            paths.subtrees.push(ancestor);
        } else {
            paths.prims.push(ancestor);
        }
    }
    paths.normalize();
    paths
}

/// What a panic interrupted when it poisoned the stage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Poisoned {
    /// Applying the change of the transaction with this id, or loading what
    /// it demanded.
    Apply(u64),
    /// Composing around a transaction: a drain, a read, a layer load, or a
    /// mutation of the stage's composition.
    Compose,
}

impl Poisoned {
    /// The error a poisoned stage fails with.
    fn error(self) -> pcp::QueryError {
        pcp::QueryError::Poisoned(match self {
            Self::Apply(generation) => Some(generation),
            Self::Compose => None,
        })
    }
}

/// The stage's composed state: the loaded layers, the indices composed from
/// them, and the edits recorded but not yet composed.
///
/// Each is its own cell so a borrow of one leaves the others free: composition
/// reads layer data while building into the cache, and the stage's recorder
/// appends to the queue as a commit lands, with the graph already borrowed.
pub(super) struct StageComposition {
    /// The loaded layers and their sublayer DAG.
    layers: sdf::HeldCell<pcp::LayerGraph>,
    /// The store holding the graph's layers, kept beside the graph's cell so a
    /// [`pcp::LayerView`] can borrow both for as long as it lives: a borrow of
    /// the graph cannot lend the graph's own store for that long.
    store: Rc<sdf::LayerStore>,
    /// Lazily-built composition cache of per-prim indices and contexts.
    cache: sdf::HeldCell<pcp::IndexCache>,
    /// Layer edits recorded by each layer's recorder (subscribed by
    /// [`intern_layer`](Self::intern_layer)) as their commits land, awaiting
    /// composed processing by [`process_pending`](Self::process_pending).
    ///
    /// Recording an edit and recomposing for it are deliberately split across
    /// this queue rather than recomposing straight from the recorder, because:
    ///
    /// - Borrows. The recorder runs inside the commit, with the layers' store
    ///   borrowed and, for a stage edit, [`layers`](Self::layers) too.
    ///   Recomposing needs both, plus [`cache`](Self::cache) — so the recorder
    ///   can only append to this independent cell, and the drain runs the
    ///   recompose once the borrows are released. A layer cannot recompose the
    ///   stage from the middle of its own mutation.
    /// - Batching. A multi-layer edit (a namespace edit across the local stack)
    ///   commits N layers, each recording one entry, so N records accumulate
    ///   and the drain drives one recompose for the whole batch instead of N.
    /// - One path for every editor. A direct edit through `Stage::layer_handle`
    ///   reaches the same recorder with no stage borrow held, so it records
    ///   uniformly and the recompose happens on the next composed read
    ///   (drain-on-read). Stage-routed and raw layer edits flow through the
    ///   identical path.
    pending: RefCell<Vec<Pending>>,
    /// Notices the drain reconciled, and those a mutation queues behind them
    /// (a retry of the failed loads), delivered in order by
    /// [`deliver_notices`](Self::deliver_notices). A drain made from inside a
    /// delivery only reconciles: what it adds waits behind the notices already
    /// here.
    outbox: RefCell<VecDeque<Notice>>,
    /// What reads and other operations outside a drain found that no notice
    /// carries ([`discover`](Self::discover)): the next drain's snapshot
    /// reports it with its own findings.
    discovered: RefCell<ResyncPaths>,
    /// What a panic interrupted, when one left the composition half-built:
    /// it cannot be finished, so the stage composes nothing more.
    poisoned: Cell<Option<Poisoned>>,
    /// How many snapshots drains have reconciled, so a read can tell whether
    /// settling after it applied edits.
    snapshots: Cell<u64>,
    /// Whether settling is suspended, while a walk composes under load rules
    /// it swapped in for itself ([`suspend_settling`](Self::suspend_settling)).
    suspended: Cell<bool>,
    /// Whether a delivery is running.
    delivering: Cell<bool>,
    /// Whether a drain is reconciling, so the composition is part-applied:
    /// user code its loads run (a resolver, a file format) that reaches the
    /// stage finds it busy.
    reconciling: Cell<bool>,
    /// Whether a layer load is running user code (a resolver, a file
    /// format). An edit that code commits stays queued, since a drain
    /// started from inside the load would apply it in the middle of the
    /// caller's loading round: a read reconciles it before its next pass,
    /// and any other caller leaves it to the next drain.
    loading: Cell<bool>,
    /// How many times the recorded load failures were forgotten
    /// ([`retries`](Self::retries)).
    retries: Cell<u64>,
}

impl StageComposition {
    /// Wraps a freshly built graph and cache.
    pub(super) fn new(layers: pcp::LayerGraph, cache: pcp::IndexCache) -> Self {
        let store = Rc::clone(layers.store());
        Self {
            layers: sdf::HeldCell::new(layers, Rc::clone(&store)),
            cache: sdf::HeldCell::new(cache, Rc::clone(&store)),
            store,
            pending: RefCell::new(Vec::new()),
            outbox: RefCell::default(),
            discovered: RefCell::default(),
            poisoned: Cell::new(None),
            snapshots: Cell::new(0),
            suspended: Cell::new(false),
            delivering: Cell::new(false),
            reconciling: Cell::new(false),
            loading: Cell::new(false),
            retries: Cell::new(0),
        }
    }

    // Edit-invariant operations: nothing a pending edit can change, so neither
    // a drain nor the index cache is involved.

    /// The registry every asset path resolves through.
    pub(super) fn layer_registry(&self) -> sdf::Held<'_, sdf::LayerRegistry> {
        sdf::Held::map(self.layers.borrow(), pcp::LayerGraph::layer_registry)
    }

    // Settled operations: the caller has already drained.

    /// The layer graph, for a caller that has completed `process_pending`.
    pub(super) fn settled_graph(&self) -> sdf::Held<'_, pcp::LayerGraph> {
        self.assert_settled();
        self.layers.borrow()
    }

    /// The layer graph with its layers' content as it stands, without a drain
    /// or a settledness check: for an observer reading the layers as a
    /// transaction reconciles. Panics while an edit of the stage's layers is in
    /// progress.
    pub(super) fn current_view(&self) -> pcp::LayerView<'_> {
        pcp::LayerView::of(self.layers.borrow(), &self.store)
            .expect("the stage's layers are not read from inside an edit of one of them")
    }

    /// The layer graph with its layers' content, for a caller that has
    /// completed `process_pending`. Panics while an edit of the stage's layers
    /// is in progress, as a borrow of the graph itself does.
    pub(super) fn settled_view(&self) -> pcp::LayerView<'_> {
        pcp::LayerView::of(self.settled_graph(), &self.store)
            .expect("the stage's layers are not read from inside an edit of one of them")
    }

    /// Fails with [`sdf::LayerError::Busy`] while a read or an edit of one of
    /// the stage's layers holds them, before a caller loads one.
    pub(super) fn ensure_writable(&self) -> Result<(), sdf::LayerError> {
        self.store.ensure_writable()
    }

    /// Deliver a stage commit's notifications through the layers' store, once
    /// the caller released the graph, and return whether it changed anything.
    /// The commit reconciles first, unless something blocks the drain (see
    /// [`reconcile`](Self::reconcile)), which leaves it queued for the next.
    /// An observer then reads the layers as it left them, before a sink can
    /// commit again. A panic out of the drain poisons the stage, and the
    /// commit's own layer notifications are not delivered.
    pub(super) fn deliver(&self, committed: sdf::Committed, hooks: &dyn CompositionHooks) -> bool {
        // A blocked drain leaves the edits queued, which is all it can do.
        let _ = self.reconcile(true, hooks);
        self.store.deliver(committed)
    }

    /// The composition cache, for a caller that has completed `process_pending`.
    pub(super) fn settled_cache(&self) -> sdf::Held<'_, pcp::IndexCache> {
        self.assert_settled();
        self.cache.borrow()
    }

    /// Every recoverable diagnostic the composed stage currently holds, in one
    /// list with no repeats.
    ///
    /// The graph and the cache each hold buckets with their own lifetimes, and
    /// one failure can sit in more than one of them — a sublayer the loader
    /// recorded once at open and the graph regenerates per stack. Folding them
    /// through one collection drops the repeat; since the two copies are equal,
    /// what the fold order decides is only where the survivor reads:
    ///
    /// 1. the graph's, replaced on every rebuild;
    /// 2. the cache's, in its own order — one-shot collection diagnostics,
    ///    then per-prim build diagnostics, then the transient query channel,
    ///    then settlement failures.
    ///
    /// Both borrows are taken here, beside the two cells, so no caller has
    /// to hold one across the other. The caller still owes the other half of
    /// the settled protocol — pending edits drained first — which
    /// [`assert_settled`](Self::assert_settled) checks in debug builds.
    pub(super) fn settled_errors(&self) -> Vec<pcp::CompositionDiagnostic> {
        let graph = self.settled_graph();
        let mut held = graph.errors();
        held.extend(graph.retain_contributing(self.settled_cache().composition_errors()));
        held.into_vec()
    }

    /// The composition cache mutably, for a settled mutation that touches the
    /// cache alone (installing load rules).
    fn settled_cache_mut(&self) -> sdf::HeldMut<'_, pcp::IndexCache> {
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
        query: impl FnOnce(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
        demands: &mut Vec<pcp::Demand>,
        clips: &mut Vec<String>,
    ) -> Result<T, pcp::QueryError> {
        let layers = self.layers.borrow();
        let view = layers.view()?;
        let mut cache = self.cache.borrow_mut();
        let reported = cache.query_diagnostic_count();
        let result = query(&view, &mut cache);
        cache.swap_pending_loads(demands);
        cache.swap_clip_loads(clips, reported);
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
    pub(super) fn authoring_graph(&self) -> sdf::Held<'_, pcp::LayerGraph> {
        self.layers.borrow()
    }

    // The pending-edit queue.

    /// Appends a committed layer edit for the next drain. A poisoned stage,
    /// which drains nothing, records nothing.
    pub(super) fn record_pending(&self, edit: PendingEdit) {
        self.record(Pending::Edit(edit));
    }

    /// Queue `notice` behind the transactions already committed, and deliver
    /// them all unless a delivery is running, which delivers them in turn.
    pub(super) fn announce(&self, notice: StageNotice, hooks: &dyn CompositionHooks) {
        self.record(Pending::Stage(notice));
        self.process_pending(hooks);
    }

    /// Record that the transaction `generation` began committing to one of
    /// the stage's layers and did not land, for the next drain to report.
    pub(super) fn record_aborted(&self, generation: u64) {
        self.record(Pending::Aborted(generation));
    }

    /// Queues `pending` for the next drain, unless the stage is poisoned.
    fn record(&self, pending: Pending) {
        if self.poisoned.get().is_none() {
            self.pending.borrow_mut().push(pending);
        }
    }

    /// Whether the queue is empty, for the drain's fast path — the check a read
    /// on a clean stage pays before returning.
    pub(super) fn pending_is_empty(&self) -> bool {
        self.pending.borrow().is_empty()
    }

    /// Whether the composition answers for every recorded edit, and a read
    /// can compose against it: none is queued, neither a drain nor a layer
    /// load is part-way through, and the stage is not poisoned.
    fn is_settled(&self) -> bool {
        !self.reconciling.get() && !self.loading.get() && self.pending_is_empty() && self.poisoned.get().is_none()
    }

    /// [`process_pending`](Self::process_pending) for a fallible read. Fails
    /// with [`sdf::LayerError::Busy`] from inside a read or an edit of one of
    /// the stage's layers while edits of them are queued, which stay queued
    /// for the next drain, and from user code a layer load runs (a resolver,
    /// a file format), while the load or the drain it serves has the stage
    /// part-composed. Fails with [`pcp::QueryError::Poisoned`] on a poisoned
    /// stage.
    pub(super) fn settle(&self, hooks: &dyn CompositionHooks) -> Result<(), pcp::QueryError> {
        self.process_pending(hooks);
        if let Some(poisoned) = self.poisoned.get() {
            return Err(poisoned.error());
        }
        match self.is_settled() {
            true => Ok(()),
            false => Err(sdf::LayerError::Busy.into()),
        }
    }

    /// Marks a layer load as running user code until the returned guard
    /// drops, unless an enclosing load marked it already.
    fn begin_load(&self) -> Option<sdf::StopRunning<'_>> {
        (!self.loading.replace(true)).then(|| sdf::StopRunning(&self.loading))
    }

    /// Runs `step`, composition that runs user code (a resolver, a file
    /// format), poisoning the stage with `cause` when a panic leaves it
    /// before it returns. The innermost step a panic leaves names the cause.
    fn guarded<T>(&self, cause: Poisoned, step: impl FnOnce() -> T) -> T {
        let mut guard = Unwind {
            poisoned: &self.poisoned,
            cause,
            armed: true,
        };
        let out = step();
        guard.armed = false;
        out
    }

    /// Whether the stage is not poisoned, for an operation that cannot fail:
    /// it panics on a poisoned stage, unless a panic is unwinding already,
    /// when the operation leaves the stage as it is.
    fn sound(&self) -> bool {
        let Some(poisoned) = self.poisoned.get() else {
            return true;
        };
        assert!(thread::panicking(), "{}", poisoned.error());
        false
    }

    /// Whether the stage is poisoned: it records no more edits of its layers.
    pub(super) fn is_poisoned(&self) -> bool {
        self.poisoned.get().is_some()
    }

    /// Takes the queued edits as an owned snapshot, leaving an empty queue.
    ///
    /// The snapshot is owned and the queue borrow is released before it
    /// returns, so what records while it is processed (a layer load's edits,
    /// or a sink's commits during the delivery that follows) lands on the
    /// emptied queue and belongs to the next snapshot, which is what lets
    /// [`process_pending`](Self::process_pending) repeat until the queue stays
    /// empty.
    fn take_pending(&self) -> Vec<Pending> {
        self.pending.take()
    }

    /// Drain the layer edits the stage's recorders queued and drive one
    /// composition recompose per snapshot, delivering the composed
    /// [`CommittedChange`](super::CommittedChange) to the stage sinks. The
    /// deferred counterpart to a layer commit: a recorder queues the edit as
    /// the commit lands, with the layers borrowed, and this runs once they are
    /// released — after each authoring call, and before any composed read. A
    /// no-op when nothing is pending, so a read on a clean stage costs only the
    /// empty check.
    ///
    /// Runs to quiescence: a sink may commit while it is delivered to, and
    /// the drain reconciles and delivers again until nothing is queued. A sink
    /// that commits on every notification never lets it return.
    ///
    /// The drain reconciles into the outbox, then delivers it. A drain made
    /// from inside a delivery (a sink authoring or reading the stage) only
    /// reconciles: its notices wait behind the ones being delivered. Every
    /// sink sees transactions in commit order, and a read inside a sink still
    /// composes with every committed edit. C++ `UsdStage` delivers a
    /// listener's nested edit within the outer notice instead, depth-first.
    ///
    /// A poisoned stage reconciles and delivers nothing: it drops what is
    /// queued.
    pub(super) fn process_pending(&self, hooks: &dyn CompositionHooks) {
        if self.poisoned.get().is_some() {
            self.pending.take();
            self.outbox.take();
            self.discovered.take();
            return;
        }
        if self.pending_is_empty() && self.outbox.borrow().is_empty() {
            return;
        }
        // A layer freed while the drain or a delivery runs drops at the end,
        // once nothing is reconciling or delivering.
        let _hold = self.store.hold();
        loop {
            if self.reconcile(true, hooks).is_err() {
                break;
            }
            self.deliver_notices(hooks);
            // A sink can commit while it is delivered to, through a layer
            // handle, and its edit queues for another pass. A nested drain
            // leaves that pass to the delivery it runs inside, and a drain the
            // store blocks, before delivering anything, leaves it to a later one.
            if self.pending_is_empty() || self.delivering.get() {
                break;
            }
        }
    }

    /// The reconciling half of [`process_pending`](Self::process_pending):
    /// compose every recorded outcome and queue its notice, in commit order,
    /// running no user code but the layer loads composition demands.
    ///
    /// Fails with [`sdf::LayerError::Busy`] when blocked: by the store, by a
    /// drain or a layer load already running, or by a borrow of the
    /// composition. The drain's or the load's user code asked for this one,
    /// and what it queued waits for that drain, after its own snapshot, or
    /// for the load's caller; a borrow of the composition keeps it queued for
    /// the next drain. Fails with [`pcp::QueryError::Poisoned`] on a poisoned
    /// stage, which reconciles nothing; a panic out of the drain poisons it.
    ///
    /// With `retry`, the edits it takes first forget the recorded load
    /// failures. Those the drain's own loads commit later do not: such an
    /// edit is committed before the failure its load records.
    pub(super) fn reconcile(&self, retry: bool, hooks: &dyn CompositionHooks) -> Result<(), pcp::QueryError> {
        if let Some(poisoned) = self.poisoned.get() {
            return Err(poisoned.error());
        }
        if self.reconciling.get() || self.loading.get() || self.layers.is_borrowed() || self.cache.is_borrowed() {
            return Err(sdf::LayerError::Busy.into());
        }
        // No layer is freed, and so no sink of one runs, while transactions
        // are applied: a freed layer's sink could commit and be reconciled
        // ahead of the snapshot.
        let _hold = self.store.hold();
        self.reconciling.set(true);
        let _reconciling = sdf::StopRunning(&self.reconciling);
        // A drain the stage's caller starts, which retries the failed loads,
        // starts a settlement round; one a read's loads need does not.
        if retry {
            self.begin_round();
        }
        self.guarded(Poisoned::Compose, || self.drain(retry, hooks))
    }

    /// Reconciles snapshots of the queue until it stays empty, for
    /// [`reconcile`](Self::reconcile).
    fn drain(&self, retry: bool, hooks: &dyn CompositionHooks) -> Result<(), pcp::QueryError> {
        // A drain the stage's caller starts settles what it drops. One a
        // read's loads need leaves that to the read, which settles after its
        // passes, so its parked demands stay the cache's through this drain.
        let settles = retry;
        let mut retry = retry;
        while !self.pending_is_empty() {
            // A drain reads, and may load, the stage's layers. From inside a
            // read or an edit of one of them it would find the store held, so
            // the edits stay queued for a later drain: a fallible read then
            // fails with `Busy` (`Stage::settle`), and a settled access panics
            // (`assert_settled`) before it answers from stale composition.
            self.store.ensure_writable()?;
            let mut drained: VecDeque<Pending> = self.take_pending().into();
            self.snapshots.set(self.snapshots.get() + 1);
            let edited = drained.iter().any(|pending| matches!(pending, Pending::Edit(_)));
            // A reload's retry is reported to the stage's sinks, as C++
            // `UsdStage::Reload` reports what `PcpCache::Reload` resyncs; the
            // retry any other edit makes recomposes what it reaches unreported.
            let reloaded = drained
                .iter()
                .any(|pending| matches!(pending, Pending::Edit(edit) if edit.changes.did_reload_content()));
            // An edit changes the layers, so a target that previously failed to read
            // may now be readable: forget recorded load failures and drop the indices
            // that recorded one, so settlement re-demands and recomposes them.
            let retried = match edited && mem::take(&mut retry) {
                true => self.forget_failed_loads(),
                false => None,
            };
            // What operations found since the last drain is reported with
            // what this snapshot finds, after its transactions.
            let mut found = self.discovered.take();
            while let Some(group) = next_group(&mut drained) {
                match group {
                    Group::Aborted(generation) => {
                        hooks.observe_abort(generation);
                        if hooks.delivers() {
                            self.outbox.borrow_mut().push_back(Notice::Aborted(generation));
                        }
                    }
                    Group::Stage(notice) => self.outbox.borrow_mut().push_back(Notice::Stage(notice)),
                    Group::Edit(group) => self.apply_group(group, hooks),
                }
            }
            // The prims the snapshot dropped settle before the stacks they
            // held are swept. Edits their loads commit go to the next
            // snapshot, which settles what is left after it.
            if settles {
                self.settle_work(Settled::Taken, hooks, &mut found);
            }
            if edited {
                // Sweep before the requeue below: a sweep retires a reclaimed stack's
                // failure diagnostics, so requeueing never re-derives a demand whose
                // barrier would read a reclaimed stack's variables.
                self.reclaim_stale_stacks();
                // A cleared sublayer failure retries even when this round's edits
                // rebuilt no stack: the failure diagnostics requeue as demands, so a
                // repaired asset loads and a still-broken one re-records the same
                // diagnostic.
                if let Some(dropped) = retried {
                    let mut again = ResyncPaths::default();
                    self.retry_sublayers(dropped, hooks, &mut again);
                    // A failed load the retry opens settles the prims it dropped,
                    // and the stacks they released are swept. A reload's
                    // settling is part of its retry, as in `retry_failed_loads`.
                    if settles {
                        self.settle_work(Settled::Taken, hooks, if reloaded { &mut again } else { &mut found });
                        self.reclaim_stale_stacks();
                    }
                    if reloaded {
                        self.report(StageNotice::LoadsRetried, again, hooks);
                    }
                }
            }
            // What settling the snapshot's work found follows its notices.
            self.report(StageNotice::Recomposed, found, hooks);
        }
        Ok(())
    }

    /// Starts a settlement round, at a drain or a mutation the stage's caller
    /// makes: a prim whose settling failed before is tried again in it.
    fn begin_round(&self) {
        self.cache.borrow_mut().begin_round();
    }

    /// Settles the work set: each prim an invalidation dropped is composed
    /// again or shown to be gone ([`pcp::IndexCache::settle_pass`]), in the
    /// current round, loading what that demands. A store a read or an edit
    /// holds leaves the rest for a later settlement; a failure settling a
    /// prim is recorded on it. Does nothing while
    /// [suspended](Self::suspend_settling).
    ///
    /// Under [`Settled::Taken`] it stops for edits its loads commit
    /// ([`Interrupted::NewWork`]), which the drain it runs inside applies
    /// first. Under [`Settled::Required`] edits loads the caller ran before
    /// it committed are reconciled first. What its loads drop joins `found`.
    fn settle_work(&self, settled: Settled, hooks: &dyn CompositionHooks, found: &mut ResyncPaths) {
        if self.suspended.get() || !self.cache.borrow().has_work() {
            return;
        }
        if settled == Settled::Required && !self.pending_is_empty() && self.reconcile(false, hooks).is_err() {
            return;
        }
        let _ = self.fixpoint(|view, cache| cache.settle_pass(view), settled, hooks, found);
    }

    /// Settles the work set on a settled stage, for a caller whose own
    /// change dropped prims (a walk under rules it swapped), reporting what
    /// the settling's loads find.
    pub(super) fn settle_now(&self, hooks: &dyn CompositionHooks) {
        let mut found = ResyncPaths::default();
        self.settle_work(Settled::Required, hooks, &mut found);
        self.discover(found, hooks);
    }

    /// Records `found`, what an operation outside a drain (a read, a
    /// mutation's own loads) dropped that no notice carries, for the next
    /// drain to report. Nothing is kept with no sink to tell.
    fn discover(&self, found: ResyncPaths, hooks: &dyn CompositionHooks) {
        if found.is_empty() || !hooks.delivers() {
            return;
        }
        let mut discovered = self.discovered.borrow_mut();
        discovered.subtrees.extend(found.subtrees);
        discovered.prims.extend(found.prims);
    }

    /// Queues `notice` naming `paths`, what an operation found, behind the
    /// notices queued before it, for the next delivery to hand the stage's
    /// sinks. Nothing is queued for no paths, or with no sink to tell.
    fn report(&self, notice: fn(ResyncPaths) -> StageNotice, mut paths: ResyncPaths, hooks: &dyn CompositionHooks) {
        if paths.is_empty() || !hooks.delivers() {
            return;
        }
        paths.normalize();
        self.outbox.borrow_mut().push_back(Notice::Stage(notice(paths)));
    }

    /// Joins `joined`, a layer an edit just sublayered, to the stage, then
    /// delivers the edit's notifications: its sinks then compose the layer
    /// given here, not a copy read from its file. The anchors whose clip
    /// sets read it are reported.
    pub(super) fn join_edited(
        &self,
        joined: sdf::LoadedLayer,
        committed: sdf::Committed,
        hooks: &dyn CompositionHooks,
    ) {
        let mut found = ResyncPaths::default();
        self.intern_layer(joined, hooks, &mut found);
        self.discover(found, hooks);
        self.deliver(committed, hooks);
    }

    /// Suspends settling until the returned guard drops, for a walk that
    /// composes under load rules it swapped in for itself: the prims the swap
    /// dropped settle under the rules restored.
    /// A suspension nested in another leaves it to the outer one to end.
    pub(super) fn suspend_settling(&self) -> Option<sdf::StopRunning<'_>> {
        (!self.suspended.replace(true)).then(|| sdf::StopRunning(&self.suspended))
    }

    /// Applies one transaction's recorded edits, a group of the drain's
    /// snapshot. A panic out of it poisons the stage, naming the transaction.
    fn apply_group(&self, mut group: Vec<PendingEdit>, hooks: &dyn CompositionHooks) {
        let generation = group[0].generation;
        self.guarded(Poisoned::Apply(generation), || {
            let own = group[0].own;
            let footprints = group
                .iter_mut()
                .filter_map(|edit| Some((edit.layer, edit.footprint.take()?)))
                .collect();
            let provenance = self.resolve_group_provenance(&mut group);
            let edits: Vec<pcp::LayerChanges<'_>> = group
                .iter()
                .map(|edit| pcp::LayerChanges {
                    layer: edit.layer,
                    changes: &edit.changes,
                    prior_default_prim: edit.prior_default_prim.clone(),
                })
                .collect();
            self.apply_change_sets(generation, own, &edits, footprints, provenance, hooks);
        });
    }

    /// Forgets the recorded load failures (C++ `PcpChanges::DidMaybeFixAsset`
    /// and `DidMaybeFixSublayer`), so a target or sublayer that failed to load
    /// may load now: the prims whose indices reported one compose again, and
    /// each failed sublayer entry is demanded again. The stage's
    /// sinks hear what this resyncs ([`StageNotice::LoadsRetried`]) at the
    /// next delivery.
    pub(super) fn retry_failed_loads(&self, hooks: &dyn CompositionHooks) {
        if !self.sound() {
            return;
        }
        self.begin_round();
        if let Some(dropped) = self.forget_failed_loads() {
            // The sweep goes first, as in a drain: it retires a reclaimed
            // stack's failure diagnostics, so the requeue never demands a
            // sublayer for a stack nothing uses.
            self.reclaim_stale_stacks();
            self.guarded(Poisoned::Compose, || {
                let mut again = ResyncPaths::default();
                self.retry_sublayers(dropped, hooks, &mut again);
                self.settle_work(Settled::Required, hooks, &mut again);
                self.report(StageNotice::LoadsRetried, again, hooks);
            });
            // The stacks the settled prims released are swept too.
            self.reclaim_stale_stacks();
        }
    }

    /// How many times the recorded load failures were forgotten, so a caller
    /// can tell whether a drain retried them.
    pub(super) fn retries(&self) -> u64 {
        self.retries.get()
    }

    /// Forgets the recorded load failures and drops the indices that reported
    /// one, returning their paths, or `None` when no failure was recorded.
    fn forget_failed_loads(&self) -> Option<Vec<sdf::Path>> {
        let cleared = self.layers.borrow_mut().clear_failed_loads();
        if cleared {
            self.retries.set(self.retries.get() + 1);
        }
        cleared.then(|| self.cache.borrow_mut().drop_load_failed_indices())
    }

    /// The second half of a retry of the failed loads, once
    /// [`forget_failed_loads`](Self::forget_failed_loads) dropped the indices
    /// at `dropped`: demands again each sublayer entry whose load failed.
    /// What the retry resyncs, `dropped` included, joins `found`.
    fn retry_sublayers(&self, dropped: Vec<sdf::Path>, hooks: &dyn CompositionHooks, found: &mut ResyncPaths) {
        found.subtrees.extend(dropped);
        let requeued = self.layers.borrow().requeue_failed_sublayers();
        self.resolve_sublayer_demands(requeued, hooks, found);
    }

    /// The delivering half of [`process_pending`](Self::process_pending): hand
    /// the outbox to the stage's sinks in order. A no-op while a delivery is
    /// running, which picks up what was added. A sink that panics leaves the
    /// notices after it for the next delivery.
    fn deliver_notices(&self, hooks: &dyn CompositionHooks) {
        if self.delivering.replace(true) {
            return;
        }
        // A sink can drop a layer's last handle; the layer is freed once the
        // delivery is over. Declared before the running flag, so the flag is
        // cleared first and a drain a freed layer's sink starts delivers.
        let _hold = self.store.hold();
        let _running = sdf::StopRunning(&self.delivering);
        loop {
            // A sink that poisons the stage, catching the panic, ends the
            // delivery: a poisoned stage delivers nothing more.
            if self.poisoned.get().is_some() {
                self.outbox.take();
                break;
            }
            let next = self.outbox.borrow_mut().pop_front();
            match next {
                Some(Notice::Committed(notice)) => hooks.notify(*notice),
                Some(Notice::Aborted(generation)) => hooks.aborted(generation),
                Some(Notice::Stage(notice)) => hooks.notify_stage(&notice),
                None => break,
            }
        }
    }

    /// Classify one transaction's committed [`sdf::ChangeList`]s — one per edited
    /// layer — through a single [`pcp::Changes`] cycle and apply the resulting
    /// cache invalidation, queuing one
    /// [`CommittedChange`](super::CommittedChange) (tagged with the
    /// transaction `generation`) for the stage's observers and sinks.
    ///
    /// [`pcp::Changes::did_change`] takes the per-layer split because
    /// classification is layer-relative; the event instead reports the merged
    /// record, attributed to the strongest edited layer. `provenance` says how the
    /// records' layer-namespace paths reach stage namespace.
    fn apply_change_sets(
        &self,
        generation: u64,
        own: bool,
        edits: &[pcp::LayerChanges<'_>],
        footprints: Vec<(pcp::LayerId, Rc<sdf::Footprint>)>,
        provenance: Provenance,
        hooks: &dyn CompositionHooks,
    ) {
        // Classification collects the notice's path-sets only when a sink is
        // listening; the invalidation half runs either way.
        let wants_notice = hooks.wants_notice();
        // A reload that changed a layer's content brings it to a new baseline
        // its undo history was not recorded against, so that history is
        // dropped, as for a layer that leaves the stage. It goes before any
        // observer or sink hears of the reload. A reload that found the
        // content as it was leaves the history.
        let reloaded: HashSet<pcp::LayerId> = edits
            .iter()
            .filter(|edit| edit.changes.did_reload_content() && !edit.changes.entries().is_empty())
            .map(|edit| edit.layer)
            .collect();
        if !reloaded.is_empty() {
            hooks.departed(&reloaded);
        }
        let mut pcp_changes = match wants_notice {
            true if matches!(provenance, Provenance::DirectLayerEdit) => pcp::Changes::reporting().with_authors(),
            true => pcp::Changes::reporting(),
            false => pcp::Changes::new(),
        };
        {
            let cache = self.cache.borrow();
            let layers = self.layers.borrow();
            pcp_changes.did_change(&cache, &layers, edits);
        }
        // Snapshot the after-commit payload before `apply` consumes
        // `pcp_changes`, and only when a sink is installed — the no-sink path
        // stays allocation-free. The event carries both the merged change list
        // (the union, keyed to the strongest layer) and the per-layer records
        // ([`layer_changes`]), so a sink deriving a per-layer diff reads each
        // layer's own record rather than mis-reading a sublayer's change against
        // the strongest layer's data.
        let mut payload = wants_notice.then(|| {
            let layer_changes: Vec<(String, sdf::ChangeList)> = edits
                .iter()
                .map(|edit| (self.layer_identifier(edit.layer), edit.changes.clone()))
                .collect();
            let mut merged = sdf::ChangeList::new();
            for edit in edits {
                merged.merge_from(edit.changes);
            }
            let layers = self.layers.borrow();
            let is_local = |layer| layers.in_root_stack(layer);
            Payload::new(&pcp_changes, &merged, layer_changes, &provenance, &is_local)
        });
        let outcome = self.update_pair(|graph, cache| pcp_changes.apply(cache, graph));
        // The recompose may have demanded sublayers — a `${VAR}` entry the
        // edited variables newly select, or a just-authored literal naming an
        // unloaded layer; open them before observers read the settled stage.
        // The prims their joins drop are this transaction's too.
        let mut found = ResyncPaths::default();
        self.resolve_recorded_demands(hooks, &mut found);
        // The layer-stack tier's paths are known only after `apply` ran — a
        // vars-only edit resyncs its dependents, and names the subtrees whose
        // asset values may re-resolve, exactly when the rebuild changed some
        // stack's composed variables — so they land on the payload here rather
        // than at the snapshot above.
        if let Some(payload) = payload.as_mut() {
            payload.finish(outcome, found);
        }

        if let Some(payload) = payload {
            let layer_identifier = edits
                .first()
                .map(|edit| self.layer_identifier(edit.layer))
                .unwrap_or_default();
            let notice = Box::new(CompositionNotice {
                payload,
                provenance,
                generation,
                own,
                layer_identifier,
                footprints,
            });
            hooks.observe(&notice);
            if hooks.delivers() {
                self.outbox.borrow_mut().push_back(Notice::Committed(notice));
            }
        }
    }

    /// The [`Provenance`] for one transaction's group of recorded edits. A staged
    /// provenance (published by a stage authoring method) rides the first layer
    /// the transaction committed. A group with none resolves from local-layer
    /// membership: [`Provenance::LocalStack`] when every edited layer is in
    /// the root layer stack (its paths are stage paths), else
    /// [`Provenance::DirectLayerEdit`].
    fn resolve_group_provenance(&self, group: &mut [PendingEdit]) -> Provenance {
        // Every layer of the transaction shares its provenance: once all but
        // the first are dropped, the first is the only owner.
        let mut shared = None;
        for edit in group.iter_mut() {
            if let Some(provenance) = edit.provenance.take() {
                shared.get_or_insert(provenance);
            }
        }
        if let Some(provenance) = shared {
            return Rc::unwrap_or_clone(provenance);
        }
        let layers = self.layers.borrow();
        if group.iter().all(|edit| layers.in_root_stack(edit.layer)) {
            Provenance::LocalStack
        } else {
            Provenance::DirectLayerEdit
        }
    }

    /// Reclaims layer-stack instances nothing live references — no cached
    /// prim index, no pending demand, no eager graph root, no live
    /// descendant's variable-source ancestry — see `LayerGraph::sweep_stacks`.
    /// The sweep runs when a stack lost its last cache owner
    /// (`IndexCache::ownership_lost`, unthresholded: a work-set entry that
    /// settles or retires stops owning its stacks, and the next edit seam
    /// collects and retires the orphans' diagnostics) or when registry
    /// creation churn
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

    /// Drops the layers no live layer stack uses and nothing else keeps
    /// (`LayerGraph::unused_layers`) once a load-rules change has unloaded
    /// what used them, or, with [`pcp::Reclaim::Muted`], once a mute has
    /// pruned them: each first reaches the stage's observers as
    /// [`departed`](CompositionHooks::departed), then leaves the graph, and
    /// the registry frees it unless something else holds it (C++ releases a
    /// payload's layer stacks, and with them its layers, as its prim indices
    /// go). A clip set on one is dropped, and a clip layer stays while a clip
    /// set a cached prim holds names it. Also kept is a layer with no file to
    /// read it from again, anonymous or built in memory.
    ///
    /// Kept besides are a layer with unsaved edits and the edit target's
    /// layer, the layers open edit contexts restore included. C++ frees a
    /// dirty layer nothing holds and holds the edit target's weakly. A prim an
    /// edit dropped and settlement has not decided (its settling failed, or a
    /// store a read or an edit held stopped it) keeps the stacks it used, and
    /// with them their layers.
    fn reclaim_unused_layers(&self, hooks: &dyn CompositionHooks, reclaim: pcp::Reclaim) {
        // A layer leaves only once its last stack has. One a pin kept (a save
        // not yet made, an edit target), or one the registry's read or edit
        // held from a reclaim, leaves at the next load-rules change after.
        if !self.layers.borrow().reclaim_due(reclaim) || self.store.ensure_writable().is_err() {
            return;
        }
        // TODO(perf): every reclaim walks every stack's members and every
        // graph layer. `LayerStackRegistry::sweep` returning the layers whose
        // `using` entry emptied would make those the only candidates.
        let edit_targets = hooks.edit_target_identifiers();
        let pcp::Reclaimable { unused, demoted, retry } = self.update_pair(|graph, cache| {
            let (mut kept, mut clips) = (HashSet::new(), HashSet::new());
            cache.mark_live_layers(graph, &mut kept, &mut clips);
            let pins = edit_targets.iter().filter_map(|target| graph.id_of(target)).collect();
            graph.unused_layers(kept, &clips, &pins, reclaim)
        });
        if !unused.is_empty() {
            hooks.departed(&unused);
        }
        // Removing the layers rebuilds the stacks that held them.
        let departed = self.guarded(Poisoned::Compose, || {
            self.update_pair(|graph, cache| {
                // A layer composition left that a clip still reads stays, for the
                // clip alone.
                let departed = graph.remove_layers(&unused, &demoted, retry);
                cache.forget_layers(&unused, &departed.identifiers);
                departed
            })
        });
        // Freed with every composition borrow released: a freed layer's sinks
        // drop with it, and they may reach the stage.
        drop(departed);
        self.store.sweep();
    }

    /// Add `layer` to the stage's graph, returning its id and whether it newly
    /// joined (a duplicate identifier collapses onto the existing node). The
    /// seam by which a layer joins the stage: opening (`StageBuilder::assemble`),
    /// [`insert_layer`](super::Stage::insert_layer) and the load barrier go
    /// through it, and a clip layer through [`join_layer`](Self::join_layer),
    /// its first half. A freshly-added layer gets the stage's recorder,
    /// subscribed to its commits: it forwards each staged edit to the stage's
    /// sinks and queues the commit into [`StageComposition`]'s pending queue
    /// for [`process_pending`](Self::process_pending) to recompose, so every
    /// layer the stage holds reports its edits no matter who authors them.
    /// The layer's node holds the subscription, which ends when the layer
    /// leaves the graph.
    ///
    /// The anchors whose clip sets read the layer, which read it now, join
    /// `found` as prims.
    fn intern_layer(
        &self,
        layer: sdf::LoadedLayer,
        hooks: &dyn CompositionHooks,
        found: &mut ResyncPaths,
    ) -> (pcp::LayerId, bool) {
        let (id, fresh, named) = self.join_layer(layer, false, hooks);
        let restaled = self
            .cache
            .borrow_mut()
            .invalidate_clip_sources(named.iter().map(String::as_str));
        found.prims.extend(restaled);
        (id, fresh)
    }

    /// [`intern_layer`](Self::intern_layer) without invalidating the clip
    /// sets that read the layer, returning the identifiers to invalidate them
    /// by. A clip the query loop opens needs no invalidation. With `clip`, a
    /// layer new to the graph joins it for value clips only
    /// ([`LayerGraph::join_clip`](pcp::LayerGraph::join_clip)); without, a
    /// layer held for clips only joins composition too and is reported fresh.
    fn join_layer(
        &self,
        layer: sdf::LoadedLayer,
        clip: bool,
        hooks: &dyn CompositionHooks,
    ) -> (pcp::LayerId, bool, Vec<String>) {
        // Joining is a value-source change for a clip that named this identifier
        // while nothing was interned under it: the clip read nothing from it,
        // and now reads the graph's layer. No edit accompanies the join, so no
        // change round would otherwise reach the prims sourcing from it. A stage
        // with no clips never pays for the identifier, which every demand-loaded
        // layer would otherwise allocate.
        // A clip names the layer by the spelling it asked for, which also names
        // the layer when it joins as an alias of a held layer's other spelling.
        let mut layers = self.layers.borrow_mut();
        // A clip join names nothing to invalidate: its caller discards them.
        let clips = !clip && self.cache.borrow().has_clip_sources();
        let mut named = Vec::new();
        if clips && layers.id_of(&layer.identifier).is_none() {
            named.push(layer.identifier.clone());
        }
        let (id, fresh) = if clip {
            layers.join_clip(layer)
        } else {
            layers.ensure_layer(layer)
        };
        // A layer promoted from clips only is subscribed already, and the
        // clip sets that read it read it as it is.
        if fresh && !layers.is_subscribed(id) {
            let subscription = hooks.subscribe_layer(id, layers.handle(id));
            layers.subscribe(id, subscription);
            let own = layers.identifier(id);
            if clips && !named.iter().any(|requested| requested == own) {
                named.push(own.to_owned());
            }
        }
        (id, fresh, named)
    }

    /// Opens the clip and manifest layers value reads named, each alone (C++
    /// `SdfLayer::FindOrOpenRelativeToLayer`), and holds it in the graph for
    /// value clips only ([`LayerGraph::join_clip`](pcp::LayerGraph::join_clip)),
    /// so the next pass reads it from the graph and the stage hears its edits
    /// while it takes no part in composition. An arc or sublayer entry that
    /// names it later loads it into composition like any unloaded layer. One
    /// that does not resolve or cannot be read is marked failed, so the next
    /// pass reads nothing from it rather than asking again.
    ///
    /// Returns whether a layer joined or a failure was newly marked.
    fn load_clips(&self, clips: &[String], hooks: &dyn CompositionHooks, found: &mut ResyncPaths) -> bool {
        let _loading = self.begin_load();
        let registry = self.layers.borrow().layer_registry().clone();
        let mut progress = false;
        // The clips that failed to open on an earlier read and open now.
        let mut recovered = Vec::new();
        for identifier in clips {
            let failure = match registry.find_or_read(identifier) {
                Ok(Some(layer)) => {
                    if self.layers.borrow_mut().forget_load_failure(identifier) {
                        recovered.push(identifier.as_str());
                    }
                    self.join_layer(layer, true, hooks);
                    progress = true;
                    continue;
                }
                Ok(None) => self.unopened(identifier),
                // A borrow conflict is not the clip's failure: the next read
                // asks for it again.
                Err(sdf::layer_registry::LoadError::Layer(sdf::LayerError::Busy)) => continue,
                Err(error) => pcp::LoadFailure::Unreadable(Arc::new(error)),
            };
            progress |= self.record_load_failure(identifier, failure, found);
        }
        // The clip sets that name a clip opened for the first time need no
        // invalidation: the only pass that read it as still to open is the
        // one the query loop discards. One that read a recovered clip as
        // missing answered other reads with it, which now change. The anchors
        // join `found` as prims.
        if !recovered.is_empty() {
            let restaled = self.cache.borrow_mut().invalidate_clip_sources(recovered);
            found.prims.extend(restaled);
        }
        progress
    }

    /// The failure an open of `asset_path` that found no layer records. When
    /// the raw asset still resolves, the layer-level resolution (a package's
    /// default layer, say) is what failed, and the failure is unreadable: it
    /// is terminal, where a resolvable asset whose failure was `Unresolved`
    /// would be opened again every pass.
    fn unopened(&self, asset_path: &str) -> pcp::LoadFailure {
        match self.layers.borrow().layer_registry().resolve(asset_path) {
            None => pcp::LoadFailure::Unresolved,
            Some(_) => pcp::LoadFailure::Unreadable(Arc::new(sdf::layer_registry::LoadError::Unresolved {
                asset_path: asset_path.to_owned(),
            })),
        }
    }

    /// Wires the layers in `joined`, which just joined composition (newly
    /// loaded, or promoted from clips only), into the graph's sublayer edges
    /// and relocates before any stack is composed against them. The cached
    /// prims that drops join `found`.
    fn wire_joined(&self, joined: &HashSet<pcp::LayerId>, found: &mut ResyncPaths) {
        let mut graph = self.layers.borrow_mut();
        // A layer joined, and an asset may have appeared: one recorded as
        // unresolved that the resolver now finds is forgotten, and the
        // indices that reported a failed target recompose and demand it.
        // The failure is looked up by the identifier it was recorded under,
        // which an asset that did not exist then need not share with the
        // one it has now.
        if graph.forget_resolvable_failures() {
            found
                .subtrees
                .extend(self.cache.borrow_mut().drop_load_failed_indices());
        }
        let relocated = graph.wire_joined(joined);
        // A joined layer that introduces relocates restructures prims composed
        // against its stack; drop their cached indices so they recompose with
        // the relocates applied.
        if !relocated.is_empty() {
            found
                .subtrees
                .extend(self.cache.borrow_mut().invalidate_layers(&graph, &relocated));
        }
    }

    /// Records that opening `asset_path` failed with `failure`, returning
    /// whether that is progress: a first failure, or one of another kind than
    /// the asset failed with before (a target that was missing and is now
    /// there but cannot be read). Re-marking an asset that failed the same way
    /// on an earlier pass must not keep the query loop running forever, and a
    /// read failure is never retried, so the kind changes at most once. The
    /// cached prims that drops join `found`.
    fn record_load_failure(&self, asset_path: &str, failure: pcp::LoadFailure, found: &mut ResyncPaths) -> bool {
        let mut graph = self.layers.borrow_mut();
        let prior = graph.load_failure(asset_path).map(mem::discriminant);
        let changed = prior != Some(mem::discriminant(&failure));
        graph.mark_load_failed(asset_path, failure);
        // The indices built since the earlier failure reported it; they
        // recompose to report this one.
        if changed && prior.is_some() {
            found
                .subtrees
                .extend(self.cache.borrow_mut().drop_load_failed_indices());
        }
        changed
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
    /// reports it — [`MalformedLayer`](pcp::CompositionDiagnostic::MalformedLayer) for a
    /// read/parse failure, [`UnresolvedLayer`](pcp::CompositionDiagnostic::UnresolvedLayer)
    /// for a resolve failure — rather than demanding it again; otherwise the
    /// demanding prim's index would never cache.
    ///
    /// Returns whether the pass made progress — a layer joined or a target was
    /// newly marked failed — so the caller recomposes once more; a demanded path
    /// already loaded or already known unreadable is skipped. The cached
    /// prims the loads drop or restale join `found`.
    fn load_demanded(&self, pending: &[pcp::Demand], hooks: &dyn CompositionHooks, found: &mut ResyncPaths) -> bool {
        if pending.is_empty() {
            return false;
        }
        let _loading = self.begin_load();
        // One cache scope spans the pass. Every probe and load of a package
        // within it shares one open of that package.
        let _scope = ar::CacheScope::begin();
        // The layers that join the graph this pass.
        let mut joined: HashSet<pcp::LayerId> = HashSet::new();
        let mut newly_failed = false;
        let mut newly_interned = false;
        // Whether a demanded identifier the graph did not name now names a layer:
        // one that joined, or one the registry held under another spelling.
        let mut resolved = false;
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
                if graph.blocking_failure(asset_path).is_some() {
                    None
                } else {
                    match graph.composing_id(asset_path) {
                        None => Some(false),
                        Some(target) if graph.needs_contextual_open(target, demand.context) => Some(true),
                        Some(_) => None,
                    }
                }
            };
            if let Some(reload) = open {
                *opened_flag = true;
                // The shared graph borrow is dropped before `intern_layer` /
                // `mark_load_failed` take a mutable one. The arc anchored
                // `asset_path` to its canonical identifier, which opens as is.
                // Nested sublayer failures surface through the sublayer-demand
                // pass below, which regenerates each one's diagnostic per stack.
                let opened = {
                    let graph = self.layers.borrow();
                    graph.layer_registry().open_stack(
                        asset_path,
                        graph.stack_variables(demand.context),
                        reload,
                        &|_| Ok(()),
                        &|id| graph.presence(id),
                    )
                };
                let failure = match opened {
                    Ok(Some(layers)) => {
                        for layer in layers {
                            let (id, fresh) = self.intern_layer(layer, hooks, found);
                            if fresh {
                                joined.insert(id);
                            }
                        }
                        resolved |= !reload;
                        None
                    }
                    Ok(None) => Some(self.unopened(asset_path)),
                    // A borrow conflict clears with the borrow: the demand stays for a later
                    // pass.
                    Err(sdf::layer_registry::LoadError::Layer(sdf::LayerError::Busy)) => None,
                    Err(err) => Some(pcp::LoadFailure::Unreadable(Arc::new(err))),
                };
                if let Some(failure) = failure {
                    newly_failed |= self.record_load_failure(asset_path, failure, found);
                }
            }
        }
        let grew = !joined.is_empty();
        if grew {
            self.wire_joined(&joined, found);
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
                if let Some(root) = graph.composing_id(asset_path) {
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
        let sublayers_loaded = self.resolve_recorded_demands(hooks, found);
        grew || resolved || newly_failed || newly_interned || sublayers_loaded
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
    /// Returns whether any layer joined the graph. The cached prims the
    /// joins drop or restale join `found`.
    fn resolve_sublayer_demands(
        &self,
        mut demands: Vec<pcp::SublayerDemand>,
        hooks: &dyn CompositionHooks,
        found: &mut ResyncPaths,
    ) -> bool {
        let _loading = self.begin_load();
        // One cache scope spans the pass. Every probe and load of a package
        // within it shares one open of that package.
        let _scope = ar::CacheScope::begin();
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
                    graph
                        .layer_registry()
                        .open_sublayer_tree(&identifier, graph.stack_variables(demand.stack), &|id| {
                            graph.presence(id)
                        })
                };
                let failure = match opened {
                    Ok(Some(layers)) => {
                        for layer in layers {
                            self.intern_layer(layer, hooks, found);
                        }
                        opened_parents.insert(demand.parent);
                        None
                    }
                    Ok(None) => Some(pcp::LoadFailure::Unresolved),
                    // A borrow conflict clears with the borrow: the demand stays for a later
                    // pass.
                    Err(sdf::layer_registry::LoadError::Layer(sdf::LayerError::Busy)) => None,
                    Err(err) => Some(pcp::LoadFailure::Unreadable(Arc::new(err))),
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
            let mut graph = self.layers.borrow_mut();
            let affected = graph.recompute_sublayers(Some(&opened_parents)).affected;
            if !affected.is_empty() {
                found
                    .subtrees
                    .extend(self.cache.borrow_mut().invalidate_layers(&graph, &affected));
            }
            demands = graph.take_sublayer_demands();
        }
        loaded_any
    }

    /// A layer's identifier read without draining, for the reconciliation
    /// pass: a drain there would run against a part-applied snapshot.
    /// Empty for a layer no longer in the graph.
    fn layer_identifier(&self, id: pcp::LayerId) -> String {
        self.layers.borrow().try_identifier(id).unwrap_or_default().to_string()
    }

    /// Runs a composed query on a settled stage, driving on-demand layer
    /// loading to a fixpoint (see [`fixpoint`](Self::fixpoint)).
    pub(super) fn query<T>(
        &self,
        query: impl FnMut(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
        hooks: &dyn CompositionHooks,
    ) -> Result<T, pcp::QueryError> {
        // The passes build indices through the resolver, and the loads
        // between them run it too.
        let mut query = query;
        let mut found = ResyncPaths::default();
        let result = self.guarded(Poisoned::Compose, || {
            loop {
                let evictions = self.cache.borrow().evictions();
                let result = match self.fixpoint(&mut query, Settled::Required, hooks, &mut found) {
                    Ok(result) => result,
                    Err(Interrupted::NewWork) => unreachable!("a settled fixpoint reconciles new work itself"),
                };
                // The prims the read's own loads dropped (a joined layer that
                // relocates, a failure recorded) settle before it returns.
                // Work a drain or a mutation left, a prim whose settling
                // failed, waits for the next.
                if self.cache.borrow().evictions() == evictions {
                    return result;
                }
                let snapshots = self.snapshots.get();
                self.settle_work(Settled::Required, hooks, &mut found);
                // Settling reconciled edits its loads committed, which can
                // change the answer: the query runs again.
                if self.snapshots.get() == snapshots {
                    return result;
                }
            }
        });
        // What the read's loads found reaches the stage's sinks at the next
        // delivery: a read delivers nothing.
        self.discover(found, hooks);
        result
    }

    /// Runs `pass` to a fixpoint over on-demand layer loading.
    ///
    /// Each pass takes the graph shared and the cache mutably, mirroring how
    /// composition reads layer data while lazily building the index. A
    /// reference or payload arc to a not-yet-loaded layer records a demand
    /// instead of composing (the index is left uncached); after the pass the
    /// borrows are released, the demanded layers are opened, and the pass
    /// re-runs. A value read naming a clip or manifest layer the graph does
    /// not hold reads nothing from it that pass, and the layer is opened
    /// before the next. The loop ends when a pass demands nothing, or when a
    /// demanded layer cannot be opened, so loading makes no progress.
    /// Composition thus drives layer loading: an un-visited subtree never
    /// loads.
    ///
    /// Loading runs user code, which can commit to a layer of the stage.
    /// Under [`Settled::Required`] the edits it queued are reconciled before
    /// the next pass, so the answer never comes from stale composition; their
    /// notices wait for the next delivery, since a read delivers nothing.
    /// Under [`Settled::Taken`] the fixpoint stops with
    /// [`Interrupted::NewWork`], for the drain it runs inside to apply them
    /// in commit order. User code that commits on every load never lets a
    /// [`Settled::Required`] fixpoint return.
    pub(super) fn fixpoint<T>(
        &self,
        mut pass: impl FnMut(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
        settled: Settled,
        hooks: &dyn CompositionHooks,
        found: &mut ResyncPaths,
    ) -> Result<Result<T, pcp::QueryError>, Interrupted> {
        // Reused across passes: swapped with the cache's queue so neither
        // reallocates once warmed up.
        let mut pending: Vec<pcp::Demand> = Vec::new();
        let mut clips: Vec<String> = Vec::new();
        // A cache scope from the first pass that demands a layer to the end
        // of the query. The loads and the passes that follow them share one
        // open of each package. A query that demands nothing, the usual one,
        // begins no scope.
        let mut scope = None;
        // A load's edit is reconciled before the next pass, so the first
        // pass is the one settledness is checked for.
        if settled == Settled::Required {
            self.assert_settled();
        }
        // No layer is freed, and so no sink of one runs, until the passes
        // and the loads between them are over.
        let _hold = self.store.hold();
        loop {
            let result = self.query_pass(&mut pass, &mut pending, &mut clips);
            // The pass left a reference/payload arc uncomposed, or a clip unread,
            // pending these layers; open them and recompose. Each loader reports
            // false once a pass neither loads a layer nor newly marks one failed,
            // so the loop ends after an unopenable layer is marked failed and the
            // following pass recomposes without it.
            if pending.is_empty() && clips.is_empty() {
                return Ok(result);
            }
            // Opening a layer adds it to the store, which a read or an edit of
            // any layer of the stage's registry holds. The demands go back to the
            // cache, for the next query to load; a clip read names its layer
            // again.
            if let Err(busy) = self.store.ensure_writable() {
                self.cache.borrow_mut().swap_pending_loads(&mut pending);
                return Ok(Err(busy.into()));
            }
            scope.get_or_insert_with(ar::CacheScope::begin);
            let loaded = self.load_demanded(&pending, hooks, found);
            if settled == Settled::Taken && !self.pending_is_empty() {
                return Err(Interrupted::NewWork);
            }
            let clipped = self.load_clips(&clips, hooks, found);
            if !self.pending_is_empty() {
                match settled {
                    Settled::Taken => return Err(Interrupted::NewWork),
                    Settled::Required => {
                        // Reconciled without a delivery, which the next drain
                        // makes, and with the demands the cache's, so a sweep
                        // keeps the stacks this read's loads minted. A store a
                        // read or an edit holds keeps the edits queued, and
                        // the read fails as `settle` would.
                        let mut cache = self.cache.borrow_mut();
                        cache.swap_pending_loads(&mut pending);
                        drop(cache);
                        let reconciled = self.reconcile(false, hooks);
                        self.cache.borrow_mut().swap_pending_loads(&mut pending);
                        if let Err(blocked) = reconciled {
                            return Ok(Err(blocked));
                        }
                    }
                }
            } else if !(loaded || clipped) {
                return Ok(result);
            }
            pending.clear();
            clips.clear();
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
    ) -> Option<(String, ResyncPaths)> {
        // A mute rebuilds and may load the stage's layers, which a read or an
        // edit of one of them holds.
        assert!(
            self.store.ensure_writable().is_ok(),
            "a layer of the stage is muted from inside a read or an edit of its registry's layers"
        );
        self.process_pending(hooks);
        if !self.sound() {
            return None;
        }
        // From inside a load or a drain the composition is part-built.
        self.assert_settled();
        self.begin_round();
        let (changed, mut resynced, demands) = self.guarded(Poisoned::Compose, || {
            self.update_pair(|graph, cache| {
                let change = mutate(graph)?;
                // The mutation already rebuilt the graph's sublayer stacks, relocates, and
                // cycle diagnostics; only the cache needs work. Removing a session variable
                // drops the root `${VAR}` sublayer it selected — the graph re-resolves the
                // already-interned layer out of the stack. Dropping the affected indices by
                // both the toggled layer's fanout and its canonical identifier reaches a
                // referrer that skipped this target while it was muted-and-never-loaded, so
                // unmuting recomposes it and the load barrier finally opens the target.
                let resynced = cache.invalidate_muting(&change);
                Some((change.changed, resynced, graph.take_sublayer_demands()))
            })
        })?;
        // An unmuted sublayer that left the graph while muted has no fanout to
        // name the prims it reaches: it joins again here, and the prims its
        // join dropped are the resyncs it adds.
        let mut found = self.guarded(Poisoned::Compose, || {
            let mut found = ResyncPaths::default();
            self.resolve_sublayer_demands(demands, hooks, &mut found);
            // The prims the mute dropped settle before the stacks they held
            // are swept.
            self.settle_work(Settled::Required, hooks, &mut found);
            found
        });
        found.subtrees.append(&mut resynced);
        // A mute can flip a stack's variable source (its authored variables
        // stop contributing), stranding the old-keyed instance — the mute path
        // discards variable deltas, so the sweep is what reclaims it. Discarding
        // them costs no notice; `LayerGraph::recompose_for_mute` carries the
        // argument.
        self.reclaim_stale_stacks();
        self.reclaim_unused_layers(hooks, pcp::Reclaim::Muted);
        Some((changed, found))
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
            let mut found = ResyncPaths::default();
            let resolved = self.guarded(Poisoned::Compose, || {
                loop {
                    let demand = match self.layers.borrow().resolve_stack_identity(&identity) {
                        Ok(id) => return Ok(id),
                        Err(demand) => demand,
                    };
                    let layer = demand.asset_path.clone();
                    if !self.load_demanded(&[demand], hooks, &mut found) {
                        return Err(layer);
                    }
                }
            });
            self.discover(found, hooks);
            return resolved;
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
            if layers.in_root_stack(target_layer) {
                return Ok(pcp::LayerStackId::ROOT);
            }
        }
        let (id, demands) = {
            let mut graph = self.layers.borrow_mut();
            let id = graph.intern_external(target_layer, pcp::LayerStackId::ROOT).0;
            (id, graph.take_sublayer_demands())
        };
        let mut found = ResyncPaths::default();
        self.resolve_sublayer_demands(demands, hooks, &mut found);
        self.discover(found, hooks);
        Ok(id)
    }

    /// Opens whatever sublayers the graph has recorded as demanded, reporting
    /// whether any layer joined. The single seam between a graph mutation and
    /// the `${VAR}` selections it newly exposed.
    fn resolve_recorded_demands(&self, hooks: &dyn CompositionHooks, found: &mut ResyncPaths) -> bool {
        let demands = self.layers.borrow_mut().take_sublayer_demands();
        self.resolve_sublayer_demands(demands, hooks, found)
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
        layers: Vec<sdf::LoadedLayer>,
        session_layer_count: usize,
        muted: HashSet<String>,
        failures: Vec<pcp::LoadFailureSeed>,
        hooks: &dyn CompositionHooks,
    ) {
        // One cache scope spans the pass. Every probe and load of a package
        // within it shares one open of that package.
        let _scope = ar::CacheScope::begin();
        // Every layer joins through the one intern seam, which subscribes the
        // stage's recorder to it.
        let mut root = None;
        let mut session_count = 0;
        // A stage opening has no sink to tell what its loads find.
        let mut found = ResyncPaths::default();
        for (i, layer) in layers.into_iter().enumerate() {
            let (id, fresh) = self.intern_layer(layer, hooks, &mut found);
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
        self.resolve_recorded_demands(hooks, &mut found);
        // That drain re-derived the sublayer failures of every region — the
        // session region, the root region, and each target stack all re-resolve
        // per rebuild — as per-stack regenerable diagnostics; the loader's
        // one-shot copies of those would double-report and outlive a later fix,
        // so they are dropped.
        let superseded: Vec<pcp::CompositionDiagnostic> = {
            let graph = self.layers.borrow();
            graph
                .errors()
                .into_iter()
                .filter(|error| {
                    matches!(
                        error,
                        pcp::CompositionDiagnostic::UnresolvedSublayer { .. }
                            | pcp::CompositionDiagnostic::MalformedSublayer { .. }
                            | pcp::CompositionDiagnostic::InvalidExpression { .. }
                    )
                })
                .collect()
        };
        if !superseded.is_empty() {
            self.cache.borrow_mut().discard_collection_errors(&superseded);
        }
        // The open leaves out a layer muted by the identifier it opens under;
        // one muted by another spelling, its real path, was read, and leaves
        // the stage like one muted later.
        self.reclaim_unused_layers(hooks, pcp::Reclaim::Muted);
        // The opened stage starts settled: an edit the loads' user code
        // committed is reconciled.
        self.process_pending(hooks);
    }

    /// Reads the load rules, applies `edit`, installs the result, and reclaims
    /// the stacks the change stranded — the deliberate mutation entry.
    ///
    /// Returns what the change means to the stage's sinks, normalized: empty
    /// for a no-op edit, or when no sink listens. An unload can leave
    /// payload-target stacks
    /// unreferenced for a long stretch, so this reclaims while the seam is
    /// quiet, whenever accumulated registry churn has ripened the trigger.
    pub(super) fn install_load_rules(
        &self,
        edit: impl FnOnce(&mut pcp::LoadRules),
        hooks: &dyn CompositionHooks,
    ) -> ResyncPaths {
        // Drain before reading: a queued edit's notification may itself install
        // load rules, and `edit` is applied to whatever this read returns, so a
        // pre-drain snapshot would overwrite that change on the way back out.
        self.process_pending(hooks);
        if !self.sound() {
            return ResyncPaths::default();
        }
        self.begin_round();
        let mut rules = self.settled_cache().load_rules().clone();
        edit(&mut rules);
        let payloads = match hooks.delivers() {
            true => self.flipped_payloads(&rules, hooks),
            false => HashSet::new(),
        };
        let victims = self.swap_load_rules(rules, hooks);
        // The prims the change dropped settle before the stacks they held are
        // swept: an unloaded payload's prims are retired, and a loaded one's
        // rebuilt.
        let mut found = ResyncPaths::default();
        self.guarded(Poisoned::Compose, || {
            self.settle_work(Settled::Required, hooks, &mut found);
        });
        self.reclaim_stale_stacks();
        self.reclaim_unused_layers(hooks, pcp::Reclaim::Unused);
        if !hooks.delivers() {
            return ResyncPaths::default();
        }
        classify(victims, &payloads, found)
    }

    /// The ancestors installing `rules` would flip the inclusion of, that
    /// have a payload of their own, asked under the rules in force, so
    /// composing one to ask loads nothing beneath it. One whose payload the
    /// stage cannot read is taken to have one.
    fn flipped_payloads(&self, rules: &pcp::LoadRules, hooks: &dyn CompositionHooks) -> HashSet<sdf::Path> {
        let flipped: Vec<sdf::Path> = self
            .settled_cache()
            .rule_ancestors(rules)
            .into_iter()
            .filter_map(|(ancestor, flipped)| flipped.then_some(ancestor))
            .collect();
        if flipped.is_empty() {
            return HashSet::new();
        }
        let answers = self.query(
            |view, cache| {
                let has = |path: &sdf::Path| cache.has_payload(view, path).unwrap_or(true);
                Ok(flipped.iter().map(has).collect::<Vec<bool>>())
            },
            hooks,
        );
        match answers {
            Ok(answers) => flipped
                .into_iter()
                .zip(answers)
                .filter_map(|(path, has)| has.then_some(path))
                .collect(),
            Err(_) => flipped.into_iter().collect(),
        }
    }

    /// Installs `rules` in place of the current table, returning what it
    /// dropped ([`pcp::RuleVictims`]).
    ///
    /// Drains first so the mutation recomposes against a current graph and
    /// cache, matching [`apply_mute`](Self::apply_mute). Reclaims nothing: this
    /// is also the transient swap behind the loadability walk, which must leave
    /// the payload-target stacks it composes untouched.
    pub(super) fn swap_load_rules(&self, rules: pcp::LoadRules, hooks: &dyn CompositionHooks) -> pcp::RuleVictims {
        self.process_pending(hooks);
        if !self.sound() {
            return pcp::RuleVictims::default();
        }
        self.settled_cache_mut().set_load_rules(rules)
    }

    /// Backstop for the settled operations: the queue being empty is necessary
    /// for settledness, not sufficient (see the module doc).
    /// Edits a drain left queued because a read or an edit held the stage's
    /// layers would make the access stale. That case panics in every build.
    fn assert_settled(&self) {
        if self.is_settled() {
            return;
        }
        // A poisoned stage reached while a panic unwinds is read as it was
        // left: a second panic would abort.
        if !self.sound() {
            return;
        }
        assert!(
            !self.reconciling.get() && !self.loading.get(),
            "the stage is read by user code a layer load runs (a resolver, a file format), while it is part-composed"
        );
        assert!(
            self.store.ensure_writable().is_ok(),
            "the stage is read from inside a read or an edit of its registry's layers, with edits queued"
        );
        debug_assert!(
            false,
            "settled composition access with edits still queued: drain through Stage::process_pending first"
        );
    }
}

/// One transaction's entries, the next a drain reconciles.
enum Group {
    /// A transaction that did not land, by id.
    Aborted(u64),
    /// A change to the stage that no layer edit made.
    Stage(StageNotice),
    /// A transaction's layer edits, one per layer it committed.
    Edit(Vec<PendingEdit>),
}

/// Takes the next transaction's entries off a drain's snapshot. Entries
/// committed under one transaction id are contiguous — a transaction's layers
/// record together, and the id increases across transactions — so grouping by
/// adjacent equal id carves the queue into per-transaction groups. Each group
/// applies as its own composed change, so unrelated edits (a direct
/// `layer_handle` commit sitting pending when the next stage edit lands) stay
/// separate rather than merging into one event. An aborted transaction leaves
/// one entry per layer it reached, and reports once, in its place among the
/// commits.
fn next_group(queue: &mut VecDeque<Pending>) -> Option<Group> {
    Some(match queue.pop_front()? {
        Pending::Aborted(generation) => {
            let same = |next: &mut Pending| matches!(next, Pending::Aborted(g) if *g == generation);
            while queue.pop_front_if(same).is_some() {}
            Group::Aborted(generation)
        }
        Pending::Stage(notice) => Group::Stage(notice),
        Pending::Edit(edit) => {
            let generation = edit.generation;
            let same = |next: &mut Pending| matches!(next, Pending::Edit(edit) if edit.generation == generation);
            let mut group = vec![edit];
            while let Some(Pending::Edit(edit)) = queue.pop_front_if(same) {
                group.push(edit);
            }
            Group::Edit(group)
        }
    })
}

/// Poisons the stage when dropped armed: a panic left the step it guards
/// ([`StageComposition::guarded`]).
struct Unwind<'a> {
    poisoned: &'a Cell<Option<Poisoned>>,
    cause: Poisoned,
    armed: bool,
}

impl Drop for Unwind<'_> {
    fn drop(&mut self) {
        if self.armed && self.poisoned.get().is_none() {
            self.poisoned.set(Some(self.cause));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::panic::{self, AssertUnwindSafe};

    use super::*;

    fn composition() -> StageComposition {
        StageComposition::new(
            pcp::LayerGraph::new(sdf::LayerRegistry::default()),
            pcp::IndexCache::new(
                pcp::VariantFallbackMap::new(),
                pcp::LoadRules::all(),
                pcp::PopulationMask::all(),
                pcp::Diagnostics::default(),
            ),
        )
    }

    fn edit() -> PendingEdit {
        PendingEdit {
            generation: 0,
            own: false,
            layer: pcp::LayerId::from_raw(0),
            changes: sdf::ChangeList::new(),
            provenance: None,
            prior_default_prim: None,
            footprint: None,
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

    /// A subscriber that captures nothing, for hooks with no stage to record.
    struct Unobserved;

    impl sdf::Subscriber for Unobserved {
        fn prepare(&self, _commit: &sdf::PendingCommit<'_>) -> Option<Box<dyn sdf::Prepared>> {
            None
        }
    }

    /// A subscription to `layer` that records nothing.
    fn unobserved(layer: &sdf::LayerHandle) -> sdf::Subscription {
        layer
            .subscribe(Rc::new(Unobserved))
            .expect("the layer joins between edits")
    }

    /// Hooks that accept every notice, for exercising the operations that need
    /// a stage without one existing.
    struct StubHooks;

    impl CompositionHooks for StubHooks {
        fn subscribe_layer(&self, _id: pcp::LayerId, layer: &sdf::LayerHandle) -> sdf::Subscription {
            unobserved(layer)
        }

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
            fn subscribe_layer(&self, _id: pcp::LayerId, layer: &sdf::LayerHandle) -> sdf::Subscription {
                unobserved(layer)
            }
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
            fn subscribe_layer(&self, _id: pcp::LayerId, layer: &sdf::LayerHandle) -> sdf::Subscription {
                unobserved(layer)
            }
            fn wants_notice(&self) -> bool {
                true
            }
            fn notify(&self, _notice: CompositionNotice) {
                // A mutable borrow of each cell succeeds only while neither is
                // borrowed.
                let free = panic::catch_unwind(AssertUnwindSafe(|| {
                    drop(self.0.layers.borrow_mut());
                    drop(self.0.cache.borrow_mut());
                }));
                self.1.set(free.is_ok());
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
            .query_pass(
                |layers, cache| Ok(layers.len() + cache.indexed_count()),
                &mut demands,
                &mut Vec::new(),
            )
            .expect("query runs");
        assert_eq!(count, 0);
        assert!(demands.is_empty(), "an empty stage demands nothing");
        // Both borrows are gone, so a mutable pair is available immediately.
        composition.update_pair(|layers, _| assert_eq!(layers.len(), 0));
    }
}
