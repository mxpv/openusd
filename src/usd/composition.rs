//! The stage's composition state and the borrow protocol around it.
//!
//! A [`Stage`](super::Stage) holds its layer graph, composition cache, and
//! pending-edit queue here rather than as sibling cells, so that every
//! `RefCell` borrow of them lives in one place. What that buys is naming: a
//! layer edit does not recompose inline — it lands in the queue, and
//! `Stage::process_pending` drains it later — so a read taken before that drain
//! sees stale composition. Callers state which side of the drain they are on by
//! the operation they pick.
//!
//! Settled access is access entered through a `Stage` method that has completed
//! `process_pending`. The `debug_assert!` on an empty queue is a backstop, not
//! the definition: `process_pending` empties the queue before applying its
//! snapshot, so during that window the queue is empty while the cache has yet
//! to incorporate the changes. The unsettled operations name themselves for
//! exactly this reason — reconciliation, loading, construction, and authoring
//! are the phases where a drain is either impossible or wrong, and each is
//! audited by which operation it calls.
//!
//! The guarantee is confinement, naming, a debug-build backstop, and an
//! auditable set of callers — short of structural enforcement, since choosing
//! the wrong operation stays a caller's mistake to make. `grep unsettled_` is
//! that audit, and it should return only methods belonging to one of:
//!
//! - Reconciliation, which applies a snapshot and cannot drain into itself.
//! - Loading, where draining or reclaiming would strand freshly resolved
//!   handles.
//! - Construction, which has no stage to drain yet.
//! - Authoring, where a drain mid-transaction would recompose against a
//!   half-applied edit.

use std::cell::{Ref, RefCell, RefMut};

use anyhow::Result;

use crate::{pcp, sdf};

use super::sink::Provenance;

/// One committed layer edit awaiting composed processing: the transaction id it
/// committed under (so a drain groups a transaction's layers together), the
/// edited layer, its change record, and the [`Provenance`] staged for it
/// (`None` for a direct edit, resolved against local-layer membership when the
/// queue drains).
pub(super) type PendingEdit = (u64, pcp::LayerId, sdf::ChangeList, Option<Provenance>);

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
    /// `Stage::add_layer`), awaiting composed processing by
    /// `Stage::process_pending`.
    ///
    /// Recording an edit and recomposing for it are deliberately split across
    /// this queue rather than recomposing straight from the aggregator
    /// callback, because:
    ///
    /// - Borrows. The aggregator fires inside [`Layer::commit`](sdf::Layer::commit),
    ///   which the stage reaches by holding [`layers`](Self::layers) borrowed
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
    pub(super) fn settled_cache_mut(&self) -> RefMut<'_, pcp::IndexCache> {
        self.assert_settled();
        self.cache.borrow_mut()
    }

    /// Runs one composed-query pass: the graph shared, the cache mutably.
    ///
    /// The arc demands the pass recorded are moved into `demands` before the
    /// borrows release, so the caller can open the demanded layers — which
    /// needs the graph mutably — and run another pass. `demands` is the
    /// caller's reused buffer, so a warmed-up load loop allocates nothing.
    pub(super) fn query_pass<T>(
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

    /// Applies a change to graph and cache together, both mutably, for a caller
    /// that has completed `process_pending`.
    ///
    /// `f` must be closed: no layer authoring, no stage sink, no layer loading,
    /// nothing that can re-enter the stage while both borrows are held. It is
    /// for self-contained work — `pcp::Changes::apply`, cache invalidation,
    /// stack mark-and-sweep. Notification and demand resolution belong after
    /// the call, once the borrows are gone.
    pub(super) fn settled_update_pair<T>(&self, f: impl FnOnce(&mut pcp::LayerGraph, &mut pcp::IndexCache) -> T) -> T {
        self.assert_settled();
        self.unsettled_update_pair(f)
    }

    // Unsettled operations: reconciliation, loading, construction, authoring.
    // Every caller of these is allowlisted; see the module doc.

    /// Applies a change to graph and cache together without a drain, for
    /// reconciliation (which applies a part-applied snapshot through here) and
    /// for a caller whose phase is established elsewhere. Carries the same
    /// closed-closure contract as
    /// [`settled_update_pair`](Self::settled_update_pair).
    pub(super) fn unsettled_update_pair<T>(
        &self,
        f: impl FnOnce(&mut pcp::LayerGraph, &mut pcp::IndexCache) -> T,
    ) -> T {
        let mut layers = self.layers.borrow_mut();
        let mut cache = self.cache.borrow_mut();
        f(&mut layers, &mut cache)
    }

    /// The layer graph without a drain, for a phase where draining is
    /// impossible or wrong.
    pub(super) fn unsettled_graph(&self) -> Ref<'_, pcp::LayerGraph> {
        self.layers.borrow()
    }

    /// The layer graph mutably without a drain.
    pub(super) fn unsettled_graph_mut(&self) -> RefMut<'_, pcp::LayerGraph> {
        self.layers.borrow_mut()
    }

    /// The composition cache without a drain.
    pub(super) fn unsettled_cache(&self) -> Ref<'_, pcp::IndexCache> {
        self.cache.borrow()
    }

    /// The composition cache mutably without a drain.
    pub(super) fn unsettled_cache_mut(&self) -> RefMut<'_, pcp::IndexCache> {
        self.cache.borrow_mut()
    }

    // The pending-edit queue.

    /// Appends a committed layer edit for the next drain.
    pub(super) fn record_pending(&self, edit: PendingEdit) {
        self.pending.borrow_mut().push(edit);
    }

    /// Whether the queue is empty, for the drain's fast path — the check a read
    /// on a clean stage pays before returning.
    pub(super) fn pending_is_empty(&self) -> bool {
        self.pending.borrow().is_empty()
    }

    /// Takes the queued edits as an owned snapshot, leaving an empty queue.
    ///
    /// The snapshot is owned and the queue borrow is released before it
    /// returns, so processing it can fire sinks that author: their edits record
    /// onto the emptied queue and belong to the next snapshot, which is what
    /// lets `Stage::process_pending` repeat until the queue stays empty.
    pub(super) fn take_pending(&self) -> Vec<PendingEdit> {
        self.pending.take()
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
    use super::*;

    fn composition() -> StageComposition {
        StageComposition::new(
            pcp::LayerGraph::new(sdf::LayerRegistry::default()),
            pcp::IndexCache::new(pcp::VariantFallbackMap::new(), pcp::LoadRules::all(), Vec::new()),
        )
    }

    fn edit() -> PendingEdit {
        (0, pcp::LayerId::from_raw(0), sdf::ChangeList::new(), None)
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
        composition.settled_update_pair(|layers, _| assert_eq!(layers.len(), 0));
    }
}
