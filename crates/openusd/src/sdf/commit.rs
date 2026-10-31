//! The commit protocol of a layer transaction: the facts a commit records
//! ([`TxnContext`], [`CommitRecord`], [`Footprint`]), the crate-internal
//! observers prepared ahead of it ([`Subscriber`], [`Prepared`]), and the
//! notification of its [`LayerSink`]s once every borrow is released
//! ([`Committed`], [`Dispatch`]).
//!
//! [`edit_layers`](super::edit_layers) runs a transaction in this order:
//!
//! 1. Every layer's [`LayerSink::before_commit`] runs, and any one may veto.
//!    A veto rolls the group back before any subscriber has seen it.
//! 2. Every subscriber's [`Subscriber::prepare`] runs while the pre-edit data
//!    still exists, returning whatever it captured as a [`Prepared`] the
//!    transaction owns. A transaction that stops past this point drops its
//!    prepared objects uncommitted; dropping one is the abort.
//! 3. The overlays drain, and each prepared object is consumed by
//!    [`Prepared::commit`] with its layer's [`CommitRecord`], all before the
//!    transaction returns.
//! 4. The caller releases its borrows and [`dispatches`](Committed::dispatch)
//!    the returned [`Committed`], which runs each layer's
//!    [`LayerSink::after_commit`].
//!
//! A subscriber is crate-internal, but its [`prepare`](Subscriber::prepare)
//! may forward the staged edit to user observers of its own (a stage's
//! `StageSink::before_commit`), which run under the same borrow and can
//! panic there, dropping every prepared object uncommitted.
//! [`Prepared::commit`] and a prepared object's `Drop` run no user code.

use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::rc::Rc;

use super::{ChangeList, CommittedLayerChange, LayerSink, Patch, Path, PathMap, PendingLayerChange, is_children_field};

/// The id of one atomic transaction: shared by every layer it commits,
/// distinct from every other transaction's, and increasing in the order
/// transactions begin.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TxnId(u64);

impl TxnId {
    /// A fresh id, after every id minted before it.
    pub(crate) fn next() -> Self {
        Self(crate::next_id())
    }

    /// The id as a number, as [`PendingLayerChange::generation`] carries it.
    pub(crate) fn get(self) -> u64 {
        self.0
    }
}

/// The identity of an editor — a stage — that a transaction is attributed to.
/// Opaque: an editor mints its own and compares a record's
/// [`origin`](CommitRecord::origin) against it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct EditorId(u64);

impl EditorId {
    /// A fresh editor identity.
    pub(crate) fn next() -> Self {
        Self(crate::next_id())
    }
}

/// What a transaction carries from its start to every record it commits:
/// its id and the editor it is attributed to. It is fixed when the transaction
/// begins. Neither a cloned handle nor a delayed notification changes it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct TxnContext {
    /// The transaction's id.
    pub id: TxnId,
    /// The editor that made the edit, or `None` for an edit no editor claims.
    pub origin: Option<EditorId>,
}

impl TxnContext {
    /// A new transaction attributed to `origin`.
    pub(crate) fn new(origin: Option<EditorId>) -> Self {
        Self {
            id: TxnId::next(),
            origin,
        }
    }
}

/// The specs and fields one layer's commit touched, read from its staged
/// [`Patch`]es before they drain.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct Footprint {
    /// Every spec created ([`Patch::Created`]) or erased ([`Patch::Tombstone`]).
    pub specs: Vec<Path>,
    /// Every `(path, field)` set or erased on a spec that already existed
    /// ([`Patch::Edited`]).
    pub fields: Vec<(Path, String)>,
}

impl Footprint {
    /// Whether this footprint and `other`, both of one layer, touch the same
    /// state: a field both set or erase, a spec one creates or erases that
    /// holds a spec or a field the other touches, or the reverse. A spec's
    /// child-name lists are bookkeeping its children's specs stand for, so two
    /// edits that each add or remove a different child do not overlap.
    pub(crate) fn overlaps(&self, other: &Self) -> bool {
        // TODO(perf): the spec tests scan every pair; indexing one side's
        // `specs` in an `sdf::PathTable` would answer each through
        // `contains_ancestor` and `subtree`.
        let under = |specs: &[Path], fields: &[(Path, String)]| {
            specs.iter().any(|spec| {
                fields
                    .iter()
                    .any(|(path, field)| !is_children_field(field) && beneath(path, spec))
            })
        };
        self.fields
            .iter()
            .any(|field| !is_children_field(&field.1) && other.fields.binary_search(field).is_ok())
            || self.specs.iter().any(|spec| {
                other
                    .specs
                    .iter()
                    .any(|path| beneath(path, spec) || beneath(spec, path))
            })
            || under(&self.specs, &other.fields)
            || under(&other.specs, &self.fields)
    }

    /// The footprint of the edits staged in `overlay`, in path order.
    pub(crate) fn of(overlay: &PathMap<Patch>) -> Self {
        let mut footprint = Self::default();
        for (path, patch) in overlay {
            match patch {
                Patch::Created(_) | Patch::Tombstone => footprint.specs.push(path.clone()),
                Patch::Edited { set, erased } => {
                    let fields = set.iter().map(|(field, _)| field).chain(erased);
                    footprint
                        .fields
                        .extend(fields.map(|field| (path.clone(), field.clone())));
                }
            }
        }
        // `PathMap` iterates in hash order; sort so the record is stable.
        footprint.specs.sort();
        footprint.fields.sort();
        footprint
    }
}

/// What one layer's commit recorded: the facts every consumer of a commit
/// shares, with no consumer's interpretation of them.
#[derive(Debug)]
pub(crate) struct CommitRecord {
    /// The committed layer's identifier.
    pub identifier: String,
    /// The transaction the commit belongs to.
    pub txn: TxnId,
    /// The composition record derived from the edit.
    pub changes: ChangeList,
    /// The specs and fields the edit touched, read only for a layer with a
    /// [`Subscriber`] and empty for one without.
    pub footprint: Rc<Footprint>,
    /// The editor the transaction is attributed to.
    #[cfg_attr(not(test), expect(dead_code, reason = "only the tests read a record's origin"))]
    pub origin: Option<EditorId>,
}

/// Whether `path` is the spec `spec` or lies beneath it. A variant set's spec
/// (`/P{v=}`) holds the set's variants (`/P{v=a}`) and what lies beneath them.
fn beneath(path: &Path, spec: &Path) -> bool {
    path.has_prefix(spec)
        || spec.as_str().strip_suffix("=}").is_some_and(|set| {
            path.as_str()
                .strip_prefix(set)
                .is_some_and(|selection| selection.starts_with('='))
        })
}

/// A staged edit offered to a [`Subscriber`]: the layer's pending change and
/// the transaction it belongs to.
pub(crate) struct PendingCommit<'a> {
    /// The pre-edit base, the staged overlay and the derived change list.
    pub change: &'a PendingLayerChange<'a>,
    /// The transaction's context.
    pub txn: &'a TxnContext,
}

/// A crate-internal observer of one layer's commits, subscribed through a
/// [`LayerHandle`](super::LayerHandle). It is offered every transaction that
/// changes the layer — one whose [`ChangeList`] is not empty — while the
/// pre-edit data still exists, after every [`LayerSink`] has accepted it.
pub(crate) trait Subscriber {
    /// Capture what this subscriber needs from `commit` before the old data
    /// is gone, into an object the transaction owns, or `None` when it needs
    /// nothing. It runs with the layer's registry borrowed and reads no layer
    /// through a handle. A pre-commit observer it forwards to runs under that
    /// borrow too.
    fn prepare(&self, commit: &PendingCommit<'_>) -> Option<Box<dyn Prepared>>;
}

/// A subscriber's capture for one transaction. Consumed by
/// [`commit`](Self::commit) when the transaction lands; dropped uncommitted
/// when it does not (a veto, an error or a panic), which is the abort. Its
/// `Drop` therefore runs no user code.
pub(crate) trait Prepared {
    /// The transaction landed with `record`. Runs before the transaction
    /// returns, with the registry still borrowed: it records and runs no user
    /// code. It may hand back a sink, which the transaction notifies with
    /// `record` after every layer sink, once the borrows are released.
    fn commit(self: Box<Self>, record: &CommitRecord) -> Option<Rc<dyn LayerSink>>;
}

/// A landed transaction whose [`LayerSink::after_commit`] notifications are
/// still to run. It owns everything they need: the caller releases every
/// borrow first, then calls [`dispatch`](Self::dispatch).
#[must_use = "a committed transaction notifies its sinks only when dispatched"]
pub(crate) struct Committed {
    /// Each sink's notification, layer by layer in commit order.
    notifications: Vec<Notification>,
    /// Whether any layer's edit produced a composition change.
    changed: bool,
}

/// One sink's `after_commit` for one layer's record.
pub(crate) struct Notification {
    /// The sink to call.
    pub sink: Rc<dyn LayerSink>,
    /// The record it is called with.
    pub record: Rc<CommitRecord>,
}

impl Committed {
    /// A transaction that queued `notifications`; `changed` is whether any
    /// layer's edit produced a composition change.
    pub(crate) fn new(notifications: Vec<Notification>, changed: bool) -> Self {
        Self { notifications, changed }
    }

    /// Run every notification now, through a queue of this transaction's own,
    /// and return whether the transaction changed anything. For a layer no
    /// registry holds: an edit a callback makes to it is delivered within that
    /// callback.
    pub(crate) fn dispatch(self) -> bool {
        self.dispatch_via(&Dispatch::default())
    }

    /// Queue every notification on `queue` and run the queue, returning
    /// whether the transaction changed anything. A dispatch already running
    /// on the queue (this transaction was made from inside one of its
    /// callbacks) delivers them after the notifications ahead of them.
    pub(crate) fn dispatch_via(self, queue: &Dispatch) -> bool {
        queue.items.borrow_mut().extend(self.notifications);
        queue.run();
        self.changed
    }
}

/// A registry's queue of `after_commit` notifications, delivered in commit
/// order.
///
/// One notification is one sink's callback for one layer's record. A callback
/// that panics loses only its own notification: the rest stay queued in order
/// for the next [`run`](Self::run), and the panic propagates to its caller.
#[derive(Default)]
pub(crate) struct Dispatch {
    /// The notifications not yet delivered, oldest first.
    items: RefCell<VecDeque<Notification>>,
    /// Set while a [`run`](Self::run) is delivering. A nested run returns and
    /// leaves its notifications to the running loop.
    running: Cell<bool>,
}

impl Dispatch {
    /// Deliver every queued notification, oldest first, unless a delivery is
    /// already running. The queue is borrowed only to pop, never across a
    /// callback.
    fn run(&self) {
        if self.running.replace(true) {
            return;
        }
        let _stop = StopRunning(&self.running);
        // Each pop is a statement of its own, so the queue's borrow ends before
        // the callback runs and a nested edit can queue behind it.
        loop {
            let Some(Notification { sink, record }) = self.items.borrow_mut().pop_front() else {
                break;
            };
            sink.after_commit(&CommittedLayerChange {
                layer_identifier: &record.identifier,
                change_list: &record.changes,
                generation: record.txn.get(),
            });
        }
    }
}

/// Clears a running flag when the run it guards ends, a callback's panic
/// included.
pub(crate) struct StopRunning<'a>(pub(crate) &'a Cell<bool>);

impl Drop for StopRunning<'_> {
    fn drop(&mut self) {
        self.0.set(false);
    }
}
