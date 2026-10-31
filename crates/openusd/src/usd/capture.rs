//! Recording stage wrappers: [`UndoStage`] and [`ReplayStage`].
//!
//! Both wrap a [`Stage`] and install recorders that capture a [`Diff`] of every
//! edit the stage commits into a shared log, as each transaction reconciles:
//!
//! - [`UndoStage`] records the *inverse* of each transaction — the operations
//!   that restore the pre-edit state — onto an undo stack;
//!   [`undo`](UndoStage::undo) replays the newest to revert it.
//! - [`ReplayStage`] records the *forward* diff of each edit — a redo/replay log
//!   fed to [`Stage::apply_diff`] to reproduce the edits here or on a mirror.
//!
//! Recording is opt-in: a plain [`Stage`] captures nothing. The shared
//! `CaptureStage` plumbing installs the recorders on construction and removes
//! them when the wrapper drops — through `into_inner` or by going out of scope
//! — so recording always stops with the wrapper, even if a [`Stage`] clone
//! outlives it.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::mem;
use std::ops::Deref;
use std::rc::Rc;

use crate::Result;
use crate::{pcp, sdf};

use super::diff::{apply_edits_verbatim, forward_diff, inverse_diff};
use super::sink::{CommittedChange, PendingChange, TxnObserver};
use super::stage::{Stage, StageAuthoringError};
use super::{Diff, Edit};

/// The default depth of an [`UndoStage`]'s undo stack.
const DEFAULT_CAPACITY: usize = 128;

/// A [`Stage`] that records the inverse of every edit it commits, for undo.
///
/// Derefs to the wrapped [`Stage`], so it authors and reads exactly like one.
/// The undo stack holds steps: each committed transaction is a step of its
/// own, and the transactions committed inside [`group`](Self::group) are one
/// step together, so one user action undoes and is evicted as a whole.
/// [`undo`](Self::undo) reverts the newest step, [`reset`](Self::reset)
/// discards the stack, and [`into_inner`](Self::into_inner) stops recording.
///
/// The inverse is derived at the layer's commit seam, the one moment the
/// pre-edit values are still readable — after the commit drains they are
/// gone — ahead of the stage's sinks, so no sink's order or panic reaches the
/// record. Each layer's inverse is buffered against its transaction id
/// ([`PendingChange::generation`]) and sealed into one entry when that
/// transaction reconciles, before its notices are delivered; a transaction
/// that does not land drops its buffered captures. Only the stage's own edits
/// are recorded ([`PendingChange::is_own`]). The stack is bounded
/// ([`with_capacity`](Self::with_capacity)); once full, the oldest step is
/// dropped and becomes permanent.
///
/// The stage's layers may be shared with other stages and handles on its
/// registry. An edit made elsewhere that touches what a step's inverse would
/// restore — a field the step changed, or a spec it created or erased, or one
/// beneath either — makes the step stale: that step and every older one are
/// dropped, and an open [`group`](Self::group) loses what it recorded, so an
/// undo never overwrites the other editor's work.
pub struct UndoStage {
    capture: CaptureStage<Journal>,
}

impl From<Stage> for UndoStage {
    /// Wrap `stage` and begin recording, with a default undo depth (see
    /// [`with_capacity`](Self::with_capacity) to choose one).
    fn from(stage: Stage) -> Self {
        Self::with_capacity(stage, DEFAULT_CAPACITY)
    }
}

impl UndoStage {
    /// Wrap `stage` and begin recording, keeping at most `capacity` undo steps
    /// (at least one). Beyond that the oldest step is dropped and becomes
    /// permanent.
    pub fn with_capacity(stage: Stage, capacity: usize) -> Self {
        let journal = Journal {
            stack: VecDeque::new(),
            in_flight: Vec::new(),
            groups: Vec::new(),
            reverting: Vec::new(),
            capacity: capacity.max(1),
        };
        let capture = CaptureStage::new(stage, journal, |journal| UndoRecorder { journal });
        Self { capture }
    }

    /// Run `edit` as one undo step: every transaction it commits is undone
    /// together by one [`undo`](Self::undo), and evicted together once the
    /// stack is full. A group that commits nothing records no step.
    ///
    /// When `edit` returns an error, the transactions it committed are
    /// reverted and no step is recorded. A group run inside another joins it,
    /// its error reverting only what it committed itself.
    ///
    /// ```
    /// use openusd::usd::{Stage, UndoStage};
    ///
    /// let undo = UndoStage::from(Stage::builder().in_memory("scene.usda")?);
    /// undo.group(|stage| {
    ///     stage.define_prim("/World")?.set_type_name("Xform")?;
    ///     Ok::<_, openusd::Error>(())
    /// })?;
    /// assert_eq!(undo.undo_depth(), 1);
    /// undo.undo()?;
    /// assert!(!undo.prim("/World")?.is_valid()?);
    /// # Ok::<(), openusd::Error>(())
    /// ```
    pub fn group<T, E>(&self, edit: impl FnOnce(&Self) -> Result<T, E>) -> Result<T, E>
    where
        E: From<StageAuthoringError>,
    {
        // An edit committed before the group, still pending, is not part of it.
        self.capture.process_pending();
        self.capture.log().borrow_mut().groups.push(Vec::new());
        let _close = CloseGroup(self.capture.log());
        let result = edit(self);
        // Reconcile what the group committed, which seals it into the group.
        self.capture.process_pending();
        let Err(error) = result else {
            return result;
        };
        let committed = mem::take(
            self.capture
                .log()
                .borrow_mut()
                .groups
                .last_mut()
                .expect("a group is open until its guard drops"),
        );
        // What could not be reverted stays in the group, still undoable.
        if let Err((revert, unreverted)) = self.revert(committed) {
            self.capture
                .log()
                .borrow_mut()
                .groups
                .last_mut()
                .expect("a group is open until its guard drops")
                .extend(unreverted);
            return Err(revert.into());
        }
        Err(error)
    }

    /// Revert the most recent step, replaying the inverse of each of its
    /// transactions, newest first, onto the layers it touched. Returns whether
    /// anything was undone (`false` when the stack is empty). Repeated calls
    /// unwind further.
    ///
    /// The revert is itself an edit but is not recorded: capture is suspended
    /// for its duration, so an undone step leaves the stack shorter, not
    /// longer. Each transaction reverts atomically; one that fails leaves the
    /// transactions not yet reverted on the stack as the newest step. An edit
    /// made elsewhere while the step replays, overlapping one of its
    /// transactions not yet replayed, ends the revert before that one, so the
    /// step is undone in part and the other editor's work stays.
    //
    // TODO: an own edit a sink makes while a revert replays is not recorded,
    // and a later transaction of the revert can overwrite it. Telling such an
    // edit from the revert's own replays needs the replays' transaction ids.
    ///
    /// Inside an open [`group`](Self::group) nothing is undone, and this
    /// returns `false`: the group's own edits are newer than every step.
    pub fn undo(&self) -> Result<bool, StageAuthoringError> {
        // Reconcile every committed edit before reading the stack. One still
        // queued (made from inside a sink's delivery) then seals before the
        // pop, not in the replay's own drain after it.
        self.capture.settle()?;
        let step = {
            let mut journal = self.capture.log().borrow_mut();
            if !journal.groups.is_empty() {
                return Ok(false);
            }
            journal.stack.pop_back()
        };
        let Some(step) = step else {
            return Ok(false);
        };
        match self.revert(step) {
            Ok(()) => Ok(true),
            Err((error, unreverted)) => {
                self.capture.log().borrow_mut().stack.push_back(unreverted);
                Err(error)
            }
        }
    }

    /// Discard the recorded undo stack, keeping the current scene. Cheap — the
    /// captured inverse diffs are dropped without replaying. Recording continues
    /// for subsequent edits, a group still open included, and an undo in
    /// progress replays to its end.
    pub fn reset(&self) {
        self.capture.log().borrow_mut().discard();
    }

    /// Whether [`undo`](Self::undo) would revert a step: one is recorded and no
    /// [`group`](Self::group) is open. Every committed edit counts: this
    /// reconciles first.
    pub fn can_undo(&self) -> bool {
        self.capture.process_pending();
        let journal = self.capture.log().borrow();
        journal.groups.is_empty() && !journal.stack.is_empty()
    }

    /// The number of recorded steps on the undo stack. Reconciles first, so
    /// every committed edit counts.
    pub fn undo_depth(&self) -> usize {
        self.capture.process_pending();
        self.capture.log().borrow().stack.len()
    }

    /// Stop recording and return the wrapped [`Stage`], removing the
    /// recorder.
    pub fn into_inner(self) -> Stage {
        self.capture.into_inner()
    }

    /// Replay the inverse of each of `transactions`, newest first, with
    /// capture suspended. On a failure, returns the error with the
    /// transactions not yet reverted, the failed one included, oldest first.
    ///
    /// The transactions not yet replayed wait in the journal, where an edit
    /// elsewhere that makes one stale ([`Journal::invalidate`]) drops them, and
    /// the revert ends there.
    fn revert(&self, transactions: Vec<Transaction>) -> Result<(), (StageAuthoringError, Vec<Transaction>)> {
        let journal = self.capture.log();
        // Ends the revert even if a replay panics (a user sink could panic
        // mid-commit), so a panic can never leave capture suspended.
        let _reverting = Reverting::begin(journal, transactions);
        loop {
            let next = journal.borrow_mut().reverting.last_mut().and_then(Vec::pop);
            let Some(transaction) = next else {
                return Ok(());
            };
            // A single-mapping replay is atomic, so a failure applied nothing.
            if let Err(error) = self.replay(&transaction) {
                let mut journal = journal.borrow_mut();
                let rest = journal
                    .reverting
                    .last_mut()
                    .expect("a revert holds its list until it ends");
                rest.push(transaction);
                return Err((error, mem::take(rest)));
            }
        }
    }

    /// Replay `transaction`'s per-layer inverse edits as one atomic
    /// [`author_layers_txn`] (all-or-nothing) through its shared edit-target
    /// mapping.
    fn replay(&self, transaction: &Transaction) -> Result<(), StageAuthoringError> {
        self.capture.settle()?;
        let ids: Vec<pcp::LayerId> = transaction.layers.iter().map(|inverse| inverse.layer).collect();
        self.capture
            .author_layers_txn(&ids, transaction.mapping.as_ref(), true, |realized, edits| {
                for (edit, &id) in edits.iter_mut().zip(realized) {
                    if let Some(inverse) = transaction.layers.iter().find(|inverse| inverse.layer == id) {
                        apply_edits_verbatim(edit, &inverse.edits).map_err(StageAuthoringError::from)?;
                    }
                }
                Ok(())
            })
            .map(|_changed| ())
    }
}

impl Deref for UndoStage {
    type Target = Stage;

    fn deref(&self) -> &Stage {
        &self.capture
    }
}

/// The recorded inverse of one atomic transaction: its per-layer inverses and
/// the one edit-target mapping they were authored through — a transaction's
/// layers share it, so it is stored once.
struct Transaction {
    mapping: Option<pcp::MapFunction>,
    layers: Vec<Inverse>,
}

impl Transaction {
    /// Whether an edit elsewhere that touched each layer in `footprints` with
    /// its footprint overlaps what this transaction's inverse would restore.
    fn overlaps(&self, footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)]) -> bool {
        self.layers.iter().any(|inverse| {
            footprint_of(footprints, inverse.layer).is_some_and(|footprint| inverse.footprint.overlaps(footprint))
        })
    }
}

/// One layer's part of a recorded transaction: the edits that restore it, and
/// what the transaction touched on it.
struct Inverse {
    /// The layer, by its id in the stage's graph, which no other layer ever
    /// takes.
    layer: pcp::LayerId,
    edits: Vec<Edit>,
    /// Empty until the transaction reconciles.
    footprint: Rc<sdf::Footprint>,
}

/// A transaction's captures buffered as its layers commit, awaiting its
/// reconciliation, keyed by the transaction id
/// ([`PendingChange::generation`]).
struct InFlight {
    generation: u64,
    transaction: Transaction,
}

/// An [`UndoStage`]'s recording state.
struct Journal {
    /// The undo stack, oldest at the front (the eviction end), newest at the
    /// back (the [`undo`](UndoStage::undo) end). Each step is the
    /// transactions one [`undo`](UndoStage::undo) reverts, oldest first.
    stack: VecDeque<Vec<Transaction>>,
    /// Per-transaction captures awaiting their reconciliation, which seals a
    /// landed transaction's bucket and drops an aborted one's.
    in_flight: Vec<InFlight>,
    /// The transactions sealed inside each open [`group`](UndoStage::group),
    /// oldest first, the innermost group last; empty outside one.
    groups: Vec<Vec<Transaction>>,
    /// The transactions each revert in progress has still to replay, newest
    /// last, the innermost revert last. While one runs capture is suspended,
    /// so the revert's own commits are not recorded.
    reverting: Vec<Vec<Transaction>>,
    /// The maximum number of steps on [`stack`](Self::stack).
    capacity: usize,
}

impl Journal {
    /// Push `transactions` as the newest step, evicting the oldest past
    /// capacity.
    fn push_step(&mut self, transactions: Vec<Transaction>) {
        self.stack.push_back(transactions);
        if self.stack.len() > self.capacity {
            self.stack.pop_front();
        }
    }

    /// Whether a revert is replaying inverses, which capture skips.
    fn suspended(&self) -> bool {
        !self.reverting.is_empty()
    }

    /// Drop every recorded step and capture, the open groups' included. A
    /// revert in progress replays to its end.
    fn discard(&mut self) {
        self.in_flight.clear();
        self.stack.clear();
        for open in &mut self.groups {
            open.clear();
        }
    }

    /// Drop what an edit elsewhere, which touched each layer in `footprints`
    /// with its footprint, made stale. Undo replays newest first, so the newest
    /// transaction it overlaps goes with every older one, and the newer ones
    /// stay. From oldest to newest, the transactions run through the stack's
    /// steps, the open groups from the outermost, and the reverts in progress
    /// from the outermost, each holding its transactions oldest first. A
    /// capture still in flight is of an edit made after it, and stays.
    fn invalidate(&mut self, footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)]) {
        // TODO(perf): every foreign commit scans every recorded transaction; a
        // per-layer index of the steps touching each layer would skip the
        // layers no step touched.
        let stale = |transaction: &Transaction| transaction.overlaps(footprints);
        let held = self.groups.iter_mut().chain(&mut self.reverting);
        let newest = held
            .enumerate()
            .filter_map(|(level, transactions)| Some((level, transactions.iter().rposition(stale)?)))
            .last();
        if let Some((level, at)) = newest {
            for (index, transactions) in self.groups.iter_mut().chain(&mut self.reverting).enumerate() {
                match index.cmp(&level) {
                    Ordering::Less => transactions.clear(),
                    Ordering::Equal => {
                        transactions.drain(..=at);
                    }
                    Ordering::Greater => {}
                }
            }
            self.stack.clear();
            return;
        }
        let stale = self.stack.iter().rposition(|step| step.iter().any(stale));
        if let Some(newest) = stale {
            self.stack.drain(..=newest);
        }
    }
}

/// A revert in progress, which suspends capture until dropped, so a panic
/// mid-replay cannot leave capture suspended.
struct Reverting<'a>(&'a RefCell<Journal>);

impl<'a> Reverting<'a> {
    /// Begin reverting `transactions`, newest last.
    fn begin(journal: &'a RefCell<Journal>, transactions: Vec<Transaction>) -> Self {
        journal.borrow_mut().reverting.push(transactions);
        Self(journal)
    }
}

impl Drop for Reverting<'_> {
    fn drop(&mut self) {
        self.0.borrow_mut().reverting.pop();
    }
}

/// Closes a [`group`](UndoStage::group) when dropped, as its edit returns or
/// unwinds: what it committed joins the enclosing group, or is recorded as
/// one step when there is none.
struct CloseGroup<'a>(&'a RefCell<Journal>);

impl Drop for CloseGroup<'_> {
    fn drop(&mut self) {
        let mut journal = self.0.borrow_mut();
        // Every transaction the group committed has reconciled: a stage edit
        // reconciles as its commit is delivered.
        let own = journal.groups.pop().unwrap_or_default();
        if let Some(outer) = journal.groups.last_mut() {
            outer.extend(own);
        } else if !own.is_empty() {
            journal.push_step(own);
        }
    }
}

/// The observer an [`UndoStage`] installs: it captures each layer's inverse
/// as the layer commits, and seals, drops or invalidates as each transaction
/// reconciles.
struct UndoRecorder {
    journal: Rc<RefCell<Journal>>,
}

impl TxnObserver for UndoRecorder {
    fn capture(&self, _stage: &Stage, change: &PendingChange<'_>, layer: pcp::LayerId) {
        // Only the stage's own edits are undoable: another editor's edit to a
        // layer the stage holds, or one made through a layer handle, is not
        // this stage's to revert.
        if !change.is_own() {
            return;
        }
        let mut journal = self.journal.borrow_mut();
        if journal.suspended() {
            return;
        }
        // Derive this layer's inverse. A read error (near-impossible on a
        // just-listed field) or an empty inverse records nothing for the layer;
        // dropping the layer on error matches the forward path.
        let Ok(edits) = inverse_diff(change) else {
            return;
        };
        if edits.is_empty() {
            return;
        }
        // Buffer against this transaction's id. Its layers commit consecutively
        // and ids increase, so the current bucket — if any — is the last one; a
        // new bucket captures the transaction's mapping once (all layers share it).
        let inverse = Inverse {
            layer,
            edits,
            footprint: Rc::default(),
        };
        match journal.in_flight.last_mut() {
            Some(bucket) if bucket.generation == change.generation => bucket.transaction.layers.push(inverse),
            _ => journal.in_flight.push(InFlight {
                generation: change.generation,
                transaction: Transaction {
                    mapping: change.mapping.cloned(),
                    layers: vec![inverse],
                },
            }),
        }
    }

    fn aborted(&self, generation: u64) {
        self.journal
            .borrow_mut()
            .in_flight
            .retain(|bucket| bucket.generation != generation);
    }

    fn committed(
        &self,
        _stage: &Stage,
        change: &CommittedChange<'_>,
        footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)],
    ) {
        let generation = change.generation;
        let mut journal = self.journal.borrow_mut();
        // An edit made elsewhere invalidates what it overlaps, while a revert
        // replays too.
        if !change.is_own() {
            journal.invalidate(footprints);
            return;
        }
        let at = journal
            .in_flight
            .iter()
            .position(|bucket| bucket.generation == generation);
        let bucket = at.map(|at| journal.in_flight.remove(at));
        if journal.suspended() {
            return;
        }
        // Seal this transaction's bucket if it captured anything. A
        // transaction that did not land drops its bucket through `aborted`.
        let Some(bucket) = bucket else {
            return;
        };
        let mut transaction = bucket.transaction;
        for inverse in &mut transaction.layers {
            let footprint = footprint_of(footprints, inverse.layer).expect("an observed commit carries its footprint");
            inverse.footprint = Rc::clone(footprint);
        }
        match journal.groups.last_mut() {
            Some(open) => open.push(transaction),
            None => journal.push_step(vec![transaction]),
        }
    }
}

/// A [`Stage`] that records the forward [`Diff`] of every edit it commits.
///
/// Derefs to the wrapped [`Stage`], so it authors and reads exactly like one;
/// each committed edit appends a diff to the log. [`diff`](Self::diff) returns
/// the recorded stream for replay through [`Stage::apply_diff`].
pub struct ReplayStage {
    capture: CaptureStage<Vec<Diff>>,
}

impl From<Stage> for ReplayStage {
    /// Wrap `stage` and begin recording. Installs the recorder; drop the
    /// wrapper with [`into_inner`](Self::into_inner) to stop.
    fn from(stage: Stage) -> Self {
        Self {
            capture: CaptureStage::new(stage, Vec::new(), |log| ReplayRecorder { log }),
        }
    }
}

impl ReplayStage {
    /// The forward diffs recorded so far, oldest first — one per committed edit
    /// that produced any operations. Replay them in order through
    /// [`Stage::apply_diff`] to reproduce the edits on a mirror. Non-draining:
    /// call [`clear`](Self::clear) to reset the log.
    pub fn diff(&self) -> Vec<Diff> {
        self.capture.log().borrow().clone()
    }

    /// Discard the recorded stream, keeping the scene. Recording continues for
    /// subsequent edits.
    pub fn clear(&self) {
        self.capture.log().borrow_mut().clear();
    }

    /// Stop recording and return the wrapped [`Stage`], removing the
    /// recorder.
    pub fn into_inner(self) -> Stage {
        self.capture.into_inner()
    }
}

impl Deref for ReplayStage {
    type Target = Stage;

    fn deref(&self) -> &Stage {
        &self.capture
    }
}

/// The observer a [`ReplayStage`] installs: it appends each committed edit's
/// forward diff to the shared log as the edit reconciles, while the layers
/// still hold its values.
struct ReplayRecorder {
    log: Rc<RefCell<Vec<Diff>>>,
}

impl TxnObserver for ReplayRecorder {
    fn committed(
        &self,
        stage: &Stage,
        change: &CommittedChange<'_>,
        _footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)],
    ) {
        // Only the stage's own edits are its to replay, as only they are its
        // to undo.
        if !change.is_own() {
            return;
        }
        // One forward diff per edited layer, read from that layer's committed
        // data. A layer that produced no operations (only child-name bookkeeping)
        // contributes nothing; an edit whose diff can't be derived (a field that
        // fails to read) is dropped: the observer has no caller to report to.
        if let Ok(diffs) = forward_diff(stage, change) {
            self.log.borrow_mut().extend(diffs);
        }
    }
}

/// A [`Stage`] with a recorder installed (a [`TxnObserver`]) and a shared log
/// of type `L` it writes: the shared plumbing behind [`UndoStage`] and
/// [`ReplayStage`].
///
/// The log is an `Rc<RefCell<L>>` shared between the recorder and the wrapper
/// handle, so a returned sub-view (a [`Prim`](super::Prim) authoring through
/// its own stage clone) still records through it. The recorder is removed
/// when this `CaptureStage` drops — whether through
/// [`into_inner`](Self::into_inner) or by going out of scope — so recording
/// always stops with the wrapper, even if a [`Stage`] clone outlives it.
struct CaptureStage<L> {
    stage: Stage,
    log: Rc<RefCell<L>>,
    /// The internal observer of transaction outcomes, for a log kept current
    /// as transactions reconcile.
    observer: Option<sdf::sink::Id<dyn TxnObserver>>,
}

impl<L> CaptureStage<L> {
    /// Wrap `stage` with a fresh `Rc<RefCell<log>>` and install the observer
    /// `make` builds over it, to hear each transaction outcome as it
    /// reconciles, until this `CaptureStage` drops.
    fn new<O: TxnObserver + 'static>(stage: Stage, log: L, make: impl FnOnce(Rc<RefCell<L>>) -> O) -> Self {
        let log = Rc::new(RefCell::new(log));
        let observer = Some(stage.add_observer(Rc::new(make(Rc::clone(&log)))));
        Self { stage, log, observer }
    }

    /// The shared log, for the wrapper's queries.
    fn log(&self) -> &RefCell<L> {
        &self.log
    }

    /// Return a handle to the wrapped stage; the recorders are removed as this
    /// `CaptureStage` drops at the end of the call.
    fn into_inner(self) -> Stage {
        // The `Drop` below removes the recorders, so the stage cannot be moved
        // out of `self`; return a clone (a cheap `Rc` bump onto the same stage)
        // and let the drop remove them.
        self.stage.clone()
    }
}

impl<L> Deref for CaptureStage<L> {
    type Target = Stage;

    fn deref(&self) -> &Stage {
        &self.stage
    }
}

impl<L> Drop for CaptureStage<L> {
    /// Remove the recorder, so recording stops when the wrapper goes away
    /// even if a [`Stage`] clone (or a returned sub-view) outlives it — otherwise
    /// later edits would keep writing into a now-unreachable log.
    fn drop(&mut self) {
        if let Some(observer) = self.observer.take() {
            self.stage.remove_observer(observer);
        }
    }
}

/// The footprint `footprints` holds for the layer `layer`.
fn footprint_of(footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)], layer: pcp::LayerId) -> Option<&Rc<sdf::Footprint>> {
    footprints
        .iter()
        .find(|(touched, _)| *touched == layer)
        .map(|(_, footprint)| footprint)
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::fs;
    use std::panic::{self, AssertUnwindSafe};

    use super::*;
    use crate::usd::stage::tests::recorder_counts;
    use crate::usd::{ApplyMode, EditTarget, ListPosition, StageSink};
    use crate::{Error, Result};
    use crate::{sdf, vt};

    fn in_memory_stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    /// Author a `def` Xform prim spec directly on a layer, for the direct-edit
    /// test.
    fn author_prim(layer: &mut sdf::LayerEdit<'_>, path: &str) -> Result<(), sdf::AuthoringError> {
        sdf::PrimSpec::new(layer.data_mut(), path, sdf::Specifier::Def, "Xform")?;
        Ok(())
    }

    /// Undo reverts the most recent transaction; repeated calls unwind the
    /// stack, each edit returning the scene to its prior state.
    #[test]
    fn undo_unwinds_stack() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/World")?.set_type_name("Xform")?;
        assert!(stage.prim("/World")?.is_valid()?);
        assert_eq!(stage.undo_depth(), 2);

        // The newest transaction is the type-name edit: undo restores its
        // absence, the prim survives.
        assert!(stage.undo()?);
        assert_eq!(stage.prim("/World")?.type_name()?.as_deref(), None);
        assert!(stage.prim("/World")?.is_valid()?);

        // Undo the define: the prim is gone, and the stack is empty.
        assert!(stage.undo()?);
        assert!(!stage.prim("/World")?.is_valid()?);
        assert!(!stage.can_undo());
        assert!(!stage.undo()?);
        Ok(())
    }

    /// Undo restores a field's prior value, not merely its absence.
    #[test]
    fn undo_restores_value() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/World")?;
        stage.create_attribute("/World.size", "double")?.set(1.0_f64)?;
        stage.attribute("/World.size")?.set(2.0_f64)?;
        assert_eq!(stage.attribute("/World.size")?.get::<f64>()?, Some(2.0));

        assert!(stage.undo()?);
        assert_eq!(stage.attribute("/World.size")?.get::<f64>()?, Some(1.0));
        Ok(())
    }

    /// Every spec created in one transaction undoes together as one step: an
    /// ancestor chain authored by a single `define_prim` is one step.
    #[test]
    fn undo_one_transaction() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/A/B/C")?;
        assert!(stage.prim("/A/B/C")?.is_valid()?);
        assert_eq!(stage.undo_depth(), 1);

        assert!(stage.undo()?);
        assert!(!stage.prim("/A")?.is_valid()?);
        assert!(!stage.prim("/A/B/C")?.is_valid()?);
        Ok(())
    }

    /// An edit made through a layer handle is not the stage's own, and records
    /// no undo step; the stage edit after it does.
    #[test]
    fn handle_edit_not_undoable() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        let root = stage.root_layer().identifier().to_string();
        stage
            .layer_handle(&root)
            .expect("root layer")
            .edit(|l| author_prim(l, "/Direct"))?;
        stage.define_prim("/Staged")?;
        assert_eq!(stage.undo_depth(), 1);

        assert!(stage.undo()?);
        assert!(!stage.prim("/Staged")?.is_valid()?);
        assert!(stage.prim("/Direct")?.is_valid()?, "the handle edit stays");
        assert!(!stage.can_undo());
        Ok(())
    }

    /// A stage sink that panics in `before_commit` after the undo recorder
    /// captured the edit aborts the transaction: the recorder drops its capture
    /// once the abort is delivered, and a later edit records and undoes alone.
    #[test]
    fn panicking_sink_aborts() -> Result<()> {
        struct Panics(Cell<bool>);
        impl StageSink for Panics {
            fn before_commit(&self, _: &Stage, _: &PendingChange<'_>) {
                if !self.0.replace(true) {
                    panic!("the sink panics");
                }
            }
        }

        let stage = UndoStage::from(in_memory_stage()?);
        stage.add_sink(Panics(Cell::new(false)));
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| stage.define_prim("/Lost")));
        assert!(unwound.is_err());
        assert!(!stage.prim("/Lost")?.is_valid()?, "the transaction rolled back");
        assert!(
            stage.capture.log().borrow().in_flight.is_empty(),
            "the delivered abort dropped the capture"
        );

        stage.define_prim("/Kept")?;
        assert_eq!(stage.undo_depth(), 1);
        assert!(stage.undo()?);
        assert!(!stage.prim("/Kept")?.is_valid()?);
        assert!(!stage.can_undo());
        Ok(())
    }

    /// An edit through [`Stage::edit_layer`] is the stage's own and undoable.
    #[test]
    fn undo_edit_layer() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        let root = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root, |l| author_prim(l, "/Direct"))?;
        assert!(stage.undo()?, "the layer edit is undone");
        assert!(!stage.prim("/Direct")?.is_valid()?);
        assert!(!stage.can_undo());
        Ok(())
    }

    /// Two stage edits a layer sink makes from its `after_commit` each record
    /// their own undo step, after the edit that fired the sink.
    #[test]
    fn nested_stage_edits_undo() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        let root = stage.root_layer().identifier().to_string();
        let layer = stage.layer_handle(&root).expect("root layer");
        let nested = (*stage).clone();
        let fired = Rc::new(Cell::new(false));
        let once = Rc::clone(&fired);
        let target = root.clone();
        let sink = layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            if !once.replace(true) {
                nested
                    .edit_layer(&target, |l| author_prim(l, "/First"))
                    .expect("first nested edit");
                nested
                    .edit_layer(&target, |l| author_prim(l, "/Second"))
                    .expect("second nested edit");
            }
        })?;
        stage.edit_layer(&root, |l| author_prim(l, "/Outer"))?;
        layer.remove_sink(sink)?;

        assert_eq!(stage.undo_depth(), 3);
        for path in ["/Second", "/First", "/Outer"] {
            assert!(stage.undo()?);
            assert!(!stage.prim(path)?.is_valid()?, "{path} is undone");
        }
        assert!(!stage.can_undo());
        Ok(())
    }

    /// `reset` discards the undo stack but leaves the scene untouched — the
    /// pay-only-when-you-undo path.
    #[test]
    fn reset_keeps_scene() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/World")?;
        stage.reset();
        assert!(stage.prim("/World")?.is_valid()?);
        assert!(!stage.can_undo());
        assert!(!stage.undo()?);
        Ok(())
    }

    /// A bounded stack drops the oldest step once full; the evicted edit becomes
    /// permanent (no longer undoable).
    #[test]
    fn capacity_eviction() -> Result<()> {
        let stage = UndoStage::with_capacity(in_memory_stage()?, 1);
        stage.define_prim("/A")?;
        stage.define_prim("/B")?;
        assert_eq!(stage.undo_depth(), 1);

        assert!(stage.undo()?);
        assert!(!stage.prim("/B")?.is_valid()?);
        assert!(stage.prim("/A")?.is_valid()?, "the evicted /A edit is permanent");
        assert!(!stage.undo()?);
        Ok(())
    }

    /// The transactions of a group are one step, undone together; edits
    /// outside a group stay one step each, and a group that commits nothing
    /// records no step.
    #[test]
    fn group_is_one_step() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/Loose")?.set_type_name("Scope")?;
        assert_eq!(stage.undo_depth(), 2);
        stage.group(|stage| {
            stage.define_prim("/World")?.set_type_name("Xform")?;
            Ok::<_, crate::Error>(())
        })?;
        assert_eq!(stage.undo_depth(), 3);
        stage.group(|_| Ok::<_, crate::Error>(()))?;
        assert_eq!(stage.undo_depth(), 3);

        assert!(stage.undo()?);
        assert!(!stage.prim("/World")?.is_valid()?);
        assert_eq!(stage.prim("/Loose")?.type_name()?.as_deref(), Some("Scope"));
        assert_eq!(stage.undo_depth(), 2);
        Ok(())
    }

    /// A transaction a stage sink's panic aborts reaches the stage's sinks
    /// before a later transaction that commits ahead of the next drain.
    #[test]
    fn abort_in_commit_order() -> Result<()> {
        struct Log {
            panicked: Cell<bool>,
            events: Rc<RefCell<Vec<(&'static str, u64)>>>,
        }
        impl StageSink for Log {
            fn before_commit(&self, _: &Stage, _: &PendingChange<'_>) {
                if !self.panicked.replace(true) {
                    panic!("the sink panics");
                }
            }
            fn aborted(&self, _: &Stage, generation: u64) {
                self.events.borrow_mut().push(("aborted", generation));
            }
            fn after_commit(&self, _: &Stage, change: &CommittedChange<'_>) {
                self.events.borrow_mut().push(("committed", change.generation));
            }
        }

        let stage = in_memory_stage()?;
        let events = Rc::new(RefCell::new(Vec::new()));
        stage.add_sink(Log {
            panicked: Cell::new(false),
            events: Rc::clone(&events),
        });
        let root = stage.root_layer().identifier().to_string();
        let layer = stage.layer_handle(&root).expect("root layer");
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| layer.edit(|l| author_prim(l, "/Lost"))));
        assert!(unwound.is_err());
        layer.edit(|l| author_prim(l, "/Kept"))?;
        stage.process_pending();

        let events = events.borrow();
        assert_eq!(
            events.iter().map(|&(kind, _)| kind).collect::<Vec<_>>(),
            ["aborted", "committed"]
        );
        assert!(events[0].1 < events[1].1, "{events:?}");
        Ok(())
    }

    /// A group run from inside a stage sink's `after_commit` that fails
    /// reverts what it committed, though its notices wait for the delivery it
    /// runs inside.
    #[test]
    fn group_in_sink_reverts() -> Result<()> {
        let undo = Rc::new(UndoStage::from(in_memory_stage()?));
        let weak = Rc::downgrade(&undo);
        let fired = Cell::new(false);
        let failed = Rc::new(Cell::new(false));
        let reported = Rc::clone(&failed);
        undo.add_sink(move |_: &Stage, _: &CommittedChange<'_>| {
            if fired.replace(true) {
                return;
            }
            let undo = weak.upgrade().expect("the undo stage is alive");
            let result = undo.group(|stage| -> Result<()> {
                stage.define_prim("/Inner")?;
                Err(Error::UnresolvedAsset("/Inner".to_owned()))
            });
            reported.set(result.is_err());
        });
        undo.define_prim("/Outer")?;
        assert!(failed.get(), "the group failed");
        assert!(undo.prim("/Outer")?.is_valid()?);
        assert!(!undo.prim("/Inner")?.is_valid()?, "the failed group reverted");
        Ok(())
    }

    /// A group whose edit fails reverts what it committed and records nothing;
    /// a failed group inside another reverts only its own transactions, and
    /// the outer group stays one step.
    #[test]
    fn failed_group_reverts() -> Result<()> {
        let undo = UndoStage::from(in_memory_stage()?);
        let fail = |stage: &Stage, path: &str| -> Result<()> {
            stage.define_prim(path)?.set_type_name("Xform")?;
            Err(crate::Error::UnresolvedAsset(path.to_owned()))
        };
        assert!(undo.group(|stage| fail(stage, "/Partial")).is_err());
        assert!(!undo.prim("/Partial")?.is_valid()?);
        assert!(!undo.can_undo());

        undo.group(|stage| {
            stage.define_prim("/Kept")?;
            assert!(stage.group(|stage| fail(stage, "/Dropped")).is_err());
            stage.define_prim("/Also")?;
            Ok::<_, crate::Error>(())
        })?;
        assert!(!undo.prim("/Dropped")?.is_valid()?);
        assert!(undo.prim("/Kept")?.is_valid()?);
        assert_eq!(undo.undo_depth(), 1);
        assert!(undo.undo()?);
        assert!(!undo.prim("/Kept")?.is_valid()?);
        assert!(!undo.prim("/Also")?.is_valid()?);
        Ok(())
    }

    /// A full stack evicts the oldest whole step, never part of a group.
    #[test]
    fn capacity_evicts_whole_steps() -> Result<()> {
        let stage = UndoStage::with_capacity(in_memory_stage()?, 2);
        stage.define_prim("/Old")?;
        stage.group(|stage| {
            stage.define_prim("/World")?.set_type_name("Xform")?;
            Ok::<_, crate::Error>(())
        })?;
        stage.define_prim("/New")?;
        assert_eq!(stage.undo_depth(), 2);

        assert!(stage.undo()?);
        assert!(!stage.prim("/New")?.is_valid()?);
        assert!(stage.undo()?);
        assert!(!stage.prim("/World")?.is_valid()?, "the group undoes whole");
        assert!(!stage.undo()?);
        assert!(stage.prim("/Old")?.is_valid()?, "the evicted step is permanent");
        Ok(())
    }

    /// A `reset` inside a nested group discards what every open group recorded
    /// before it, and a failure after it reverts only what came after.
    #[test]
    fn group_reset_nested() -> Result<()> {
        let undo = UndoStage::from(in_memory_stage()?);
        undo.group(|stage| {
            stage.define_prim("/Before")?;
            let failed = stage.group(|stage| {
                stage.define_prim("/Discarded")?;
                stage.reset();
                stage.define_prim("/Reverted")?;
                Err::<(), _>(crate::Error::UnresolvedAsset("/Reverted".to_owned()))
            });
            assert!(failed.is_err());
            stage.define_prim("/After")?;
            Ok::<_, crate::Error>(())
        })?;
        assert!(undo.prim("/Before")?.is_valid()?);
        assert!(undo.prim("/Discarded")?.is_valid()?);
        assert!(!undo.prim("/Reverted")?.is_valid()?);
        assert_eq!(undo.undo_depth(), 1);
        assert!(undo.undo()?);
        assert!(!undo.prim("/After")?.is_valid()?);
        assert!(undo.prim("/Before")?.is_valid()?, "reset made it permanent");
        Ok(())
    }

    /// A group whose edit panics after an edit through
    /// [`Stage::edit_layer`] still records that edit in its step, and one undo
    /// reverts the group whole.
    #[test]
    fn group_unwind_keeps_step() -> Result<()> {
        let undo = UndoStage::from(in_memory_stage()?);
        let root = undo.root_layer().identifier().to_string();
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| {
            undo.group(|stage| -> Result<()> {
                stage.define_prim("/Staged")?;
                stage.edit_layer(&root, |edit| author_prim(edit, "/Direct"))?;
                panic!("the edit panics after a direct layer edit")
            })
        }));
        assert!(unwound.is_err());
        assert_eq!(undo.undo_depth(), 1);
        assert!(undo.undo()?);
        assert!(!undo.prim("/Staged")?.is_valid()?);
        assert!(!undo.prim("/Direct")?.is_valid()?);
        assert!(!undo.can_undo());
        Ok(())
    }

    /// A group whose only transaction a layer sink vetoes, after the undo
    /// recorder captured it, records no step and evicts nothing.
    #[test]
    fn group_veto_no_step() -> Result<()> {
        struct Veto;
        impl sdf::LayerSink for Veto {
            fn before_commit(&self, _: &sdf::PendingLayerChange<'_>) -> Result<(), sdf::sink::Error> {
                Err(sdf::sink::Error::new("vetoed"))
            }
        }

        let undo = UndoStage::with_capacity(in_memory_stage()?, 1);
        undo.define_prim("/Kept")?;
        let root = undo.root_layer().identifier().to_string();
        let sink = undo.layer_handle(&root).expect("root layer").add_sink(Veto)?;
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| {
            undo.group(|stage| -> Result<()> {
                assert!(stage.define_prim("/Vetoed").is_err());
                panic!("the edit panics after a vetoed transaction")
            })
        }));
        assert!(unwound.is_err());
        undo.layer_handle(&root).expect("root layer").remove_sink(sink)?;

        assert_eq!(undo.undo_depth(), 1);
        assert!(undo.undo()?);
        assert!(!undo.prim("/Kept")?.is_valid()?);
        Ok(())
    }

    /// Inside an open group nothing is undone: the group's own edits are newer
    /// than every recorded step.
    #[test]
    fn undo_inside_group() -> Result<()> {
        let undo = UndoStage::from(in_memory_stage()?);
        undo.define_prim("/Old")?;
        undo.group(|stage| {
            stage.define_prim("/New")?;
            assert!(!stage.can_undo());
            assert!(!stage.undo()?);
            Ok::<_, crate::Error>(())
        })?;
        assert!(undo.prim("/Old")?.is_valid()?);
        assert_eq!(undo.undo_depth(), 2);
        Ok(())
    }

    /// `UndoStage::into_inner` removes the recorder and returns the wrapped
    /// stage, which then authors normally.
    #[test]
    fn undo_into_inner_returns_stage() -> Result<()> {
        let undo = UndoStage::from(in_memory_stage()?);
        undo.define_prim("/World")?;
        let stage = undo.into_inner();
        assert_eq!(recorder_counts(&stage), (0, 0), "into_inner removes the recorders");
        stage.define_prim("/Another")?;
        assert!(stage.prim("/World")?.is_valid()?);
        assert!(stage.prim("/Another")?.is_valid()?);
        Ok(())
    }

    /// An [`UndoStage`] records through one observer and installs no sink.
    /// Dropping it without `into_inner` still removes the observer, so
    /// recording stops even when a stage clone outlives it — nothing left
    /// writing into an unreachable log.
    #[test]
    fn undo_drop_removes_observer() -> Result<()> {
        let stage = in_memory_stage()?;
        assert_eq!(recorder_counts(&stage), (0, 0));
        {
            let undo = UndoStage::from(stage.clone());
            assert_eq!(recorder_counts(&stage), (0, 1), "one observer, no sink");
            undo.define_prim("/World")?;
        }
        assert_eq!(
            recorder_counts(&stage),
            (0, 0),
            "the recorder goes when the wrapper drops"
        );
        // The surviving clone still authors, no longer recording.
        stage.define_prim("/Another")?;
        assert!(stage.prim("/World")?.is_valid()?);
        assert!(stage.prim("/Another")?.is_valid()?);
        Ok(())
    }

    /// A `ReplayStage` records each edit's forward diff; replaying the stream
    /// onto a fresh stage reconstructs the edited subtree. Edits made through a
    /// returned `Prim` (which owns its own stage clone) are captured too — the
    /// capture rides the shared sink, not the wrapper.
    #[test]
    fn replay_onto_mirror() -> Result<()> {
        let source = ReplayStage::from(in_memory_stage()?);
        source.define_prim("/World")?.set_type_name("Xform")?;
        source.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        source.create_attribute("/World/Mesh.size", "double")?.set(2.0_f64)?;

        let mirror = in_memory_stage()?;
        for diff in source.diff() {
            mirror.apply_diff(&diff, ApplyMode::CurrentEditTarget)?;
        }
        assert_eq!(mirror.prim("/World")?.type_name()?.as_deref(), Some("Xform"));
        assert_eq!(mirror.prim("/World/Mesh")?.type_name()?.as_deref(), Some("Mesh"));
        assert_eq!(mirror.attribute("/World/Mesh.size")?.get::<f64>()?, Some(2.0));
        Ok(())
    }

    /// `clear` drops the recorded stream; `ReplayStage::into_inner` removes the
    /// sink and returns the wrapped stage, which then authors normally.
    #[test]
    fn clear_and_into_inner() -> Result<()> {
        let source = ReplayStage::from(in_memory_stage()?);
        source.define_prim("/World")?;
        assert!(!source.diff().is_empty());
        source.clear();
        assert!(source.diff().is_empty());

        let stage = source.into_inner();
        assert_eq!(recorder_counts(&stage), (0, 0), "into_inner removes the recorder");
        stage.define_prim("/Another")?;
        assert!(stage.prim("/Another")?.is_valid()?);
        Ok(())
    }

    /// A stage edit's replay holds its own value though a layer sink edits the
    /// same field again from `after_commit`: the edit reconciles before the
    /// layer's sinks run.
    #[test]
    fn replay_before_layer_sink() -> Result<()> {
        let source = ReplayStage::from(in_memory_stage()?);
        source.define_prim("/A")?;
        let x = source.create_attribute("/A.x", "double")?;
        let root = source.root_layer().identifier().to_string();
        let layer = source.layer_handle(&root).expect("root layer");
        let nested = layer.clone();
        let fired = Cell::new(false);
        let sink = layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            if !fired.replace(true) {
                nested
                    .edit(|e| {
                        let path = sdf::path("/A.x")?;
                        e.data_mut()
                            .set_field(&path, sdf::FieldKey::Default.as_str(), 2.0_f64.into());
                        Ok(())
                    })
                    .expect("the layer sink's edit");
            }
        })?;
        source.clear();
        x.set(1.0_f64)?;
        layer.remove_sink(sink)?;

        let mirror = in_memory_stage()?;
        mirror.define_prim("/A")?;
        mirror.create_attribute("/A.x", "double")?;
        for diff in source.diff() {
            mirror.apply_diff(&diff, ApplyMode::CurrentEditTarget)?;
        }
        assert_eq!(mirror.attribute("/A.x")?.get::<f64>()?, Some(1.0));
        Ok(())
    }

    /// A replay recorded through a variant edit target, with no stage sink
    /// installed, carries the target's mapping, which lifts it onto a
    /// mirror's own variant.
    #[test]
    fn replay_variant_target() -> Result<()> {
        let source = ReplayStage::from(in_memory_stage()?);
        source.define_prim("/Prim")?;
        let root = source.edit_target().layer_identifier().to_string();
        source.set_edit_target(EditTarget::for_local_direct_variant(
            root,
            sdf::path("/Prim{set=sel}")?,
        )?)?;
        source.clear();
        source.define_prim("/Prim/child")?;
        let diffs = source.diff();
        assert!(!diffs.is_empty());
        assert!(diffs.iter().all(|diff| diff.mapping.is_some()), "{diffs:?}");
        Ok(())
    }

    /// Two stage edits a sink makes from `after_commit` to one field replay as
    /// two steps, each with its own value, though their notices wait for the
    /// delivery they run inside.
    #[test]
    fn replay_nested_edits() -> Result<()> {
        let source = ReplayStage::from(in_memory_stage()?);
        source.define_prim("/A")?;
        source.create_attribute("/A.x", "double")?;
        let stage = (*source).clone();
        let fired = Cell::new(false);
        source.add_sink(move |_: &Stage, _: &CommittedChange<'_>| {
            if fired.replace(true) {
                return;
            }
            let x = stage.attribute("/A.x").expect("a valid path");
            let x = x.set(1.0_f64).expect("the first set");
            x.set(2.0_f64).expect("the second set");
        });
        source.define_prim("/Trigger")?;

        let mirror = in_memory_stage()?;
        let mut values = Vec::new();
        for diff in source.diff() {
            mirror.apply_diff(&diff, ApplyMode::CurrentEditTarget)?;
            let value = mirror.attribute("/A.x")?.get::<f64>()?;
            if values.last() != Some(&value) {
                values.push(value);
            }
        }
        assert_eq!(values, [None, Some(1.0), Some(2.0)]);
        Ok(())
    }

    /// Dropping a [`ReplayStage`] without `into_inner` removes its recorder.
    #[test]
    fn replay_drop_removes_recorder() -> Result<()> {
        let stage = in_memory_stage()?;
        {
            let source = ReplayStage::from(stage.clone());
            assert_eq!(recorder_counts(&stage), (0, 1));
            source.define_prim("/World")?;
        }
        assert_eq!(
            recorder_counts(&stage),
            (0, 0),
            "the recorder goes when the wrapper drops"
        );
        Ok(())
    }

    /// Two stages on one registry over `root.usda`, which holds `/P` with
    /// `double x = 0` and an empty `/Q`: the first wrapped for undo.
    fn shared_pair() -> Result<(tempfile::TempDir, UndoStage, Stage)> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("root.usda");
        fs::write(&path, "#usda 1.0\ndef \"P\" {\n    double x = 0\n}\ndef \"Q\" {}\n")?;
        let path = path.to_str().expect("utf-8 path");
        let registry = sdf::LayerRegistry::default();
        let a = Stage::builder().registry(registry.clone()).open(path)?;
        let b = Stage::builder().registry(registry).open(path)?;
        Ok((dir, UndoStage::from(a), b))
    }

    /// `/P.x` as `stage` composes it.
    fn x(stage: &Stage) -> Result<Option<f64>> {
        stage.attribute("/P.x")?.get::<f64>()
    }

    /// Another stage setting a field a step changed drops the step, and the
    /// other stage's value stays.
    #[test]
    fn foreign_set_drops_step() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.attribute("/P.x")?.set(1.0)?;
        assert!(a.can_undo());
        b.attribute("/P.x")?.set(2.0)?;
        assert!(!a.can_undo(), "the step would overwrite B's value");
        assert!(!a.undo()?);
        assert_eq!(x(&a)?, Some(2.0));
        Ok(())
    }

    /// Another stage erasing a field a step changed drops the step, and the
    /// field stays erased.
    #[test]
    fn foreign_erase_drops_step() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.attribute("/P.x")?.set(1.0)?;
        b.attribute("/P.x")?.clear_default()?;
        assert!(!a.can_undo());
        assert_eq!(x(&a)?, None);
        Ok(())
    }

    /// Another stage erasing the spec that holds a field a step changed drops
    /// the step.
    #[test]
    fn foreign_spec_erase_drops() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.attribute("/P.x")?.set(1.0)?;
        assert!(b.remove_prim("/P")?);
        assert!(!a.can_undo());
        assert!(!a.prim("/P")?.is_valid()?);
        Ok(())
    }

    /// A foreign edit that touches nothing a step would restore keeps the
    /// history, and the step still undoes.
    #[test]
    fn foreign_disjoint_keeps_step() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.attribute("/P.x")?.set(1.0)?;
        b.define_prim("/Q/Child")?;
        assert_eq!(a.undo_depth(), 1);
        assert!(a.undo()?);
        assert_eq!(x(&a)?, Some(0.0));
        assert!(b.prim("/Q/Child")?.is_valid()?, "B's edit stays");
        Ok(())
    }

    /// A foreign edit overlapping a grouped step drops it and every older
    /// step, and leaves newer ones.
    #[test]
    fn foreign_conflict_drops_older() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.define_prim("/Old")?;
        a.group(|a| {
            a.attribute("/P.x")?.set(1.0)?;
            a.define_prim("/Grouped")?;
            Ok::<_, Error>(())
        })?;
        a.define_prim("/Newer")?;
        assert_eq!(a.undo_depth(), 3);
        b.attribute("/P.x")?.set(2.0)?;
        assert_eq!(a.undo_depth(), 1, "only the step newer than the conflict stays");
        assert!(a.undo()?);
        assert!(!a.prim("/Newer")?.is_valid()?);
        assert!(a.prim("/Grouped")?.is_valid()?);
        Ok(())
    }

    /// A foreign edit overlapping what an open nested group recorded discards
    /// the open groups and the stack: the inner group's failure reverts
    /// nothing, and the outer records no step.
    #[test]
    fn foreign_conflict_open_groups() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.define_prim("/Before")?;
        let failed = a.group(|a| {
            a.define_prim("/Outer")?;
            a.group(|a| {
                a.attribute("/P.x")?.set(1.0)?;
                b.attribute("/P.x")?.set(2.0)?;
                Err::<(), _>(Error::from(StageAuthoringError::PrimNotValid {
                    path: sdf::path("/Failed")?,
                }))
            })
        });
        assert!(failed.is_err());
        assert_eq!(x(&a)?, Some(2.0), "the inner group reverted nothing");
        assert!(a.prim("/Outer")?.is_valid()?);
        assert_eq!(a.undo_depth(), 0, "the stale chain and the stack below it are gone");
        Ok(())
    }

    /// Inside one of A's sink callbacks, a foreign edit that overlaps A's step
    /// already drops it: `can_undo` is false and `undo` restores nothing.
    #[test]
    fn undo_inside_callback() -> Result<()> {
        struct Check {
            a: Rc<RefCell<Option<UndoStage>>>,
            b: Stage,
            seen: Rc<RefCell<Vec<(bool, bool)>>>,
        }
        impl StageSink for Check {
            fn after_commit(&self, _: &Stage, change: &CommittedChange<'_>) {
                if !change.is_own() {
                    return;
                }
                let a = self.a.borrow();
                let a = a.as_ref().expect("the wrapper is set");
                let Ok(attribute) = self.b.attribute("/P.x") else {
                    return;
                };
                if attribute.set(2.0).is_err() {
                    return;
                }
                let undone = a.undo().unwrap_or(true);
                self.seen.borrow_mut().push((a.can_undo(), undone));
            }
        }

        let (_dir, a, b) = shared_pair()?;
        let slot = Rc::new(RefCell::new(None));
        let seen = Rc::new(RefCell::new(Vec::new()));
        let sink = a.add_sink(Check {
            a: Rc::clone(&slot),
            b: b.clone(),
            seen: Rc::clone(&seen),
        });
        let stage = Stage::clone(&a);
        slot.replace(Some(a));
        stage.attribute("/P.x")?.set(1.0)?;
        stage.remove_sink(sink);
        assert_eq!(*seen.borrow(), [(false, false)]);
        assert_eq!(x(&stage)?, Some(2.0), "B's value stays");
        slot.take();
        Ok(())
    }

    /// An edit through a handle to a layer the stage holds is foreign to it,
    /// and drops a step it overlaps.
    #[test]
    fn handle_edit_drops_step() -> Result<()> {
        let (_dir, a, _b) = shared_pair()?;
        a.attribute("/P.x")?.set(1.0)?;
        let root = a.root_layer().identifier().to_string();
        a.layer_handle(&root).expect("root layer").edit(|e| {
            e.data_mut().set_field(
                &sdf::path("/P.x")?,
                sdf::FieldKey::Default.as_str(),
                vt::Value::Double(3.0),
            );
            Ok(())
        })?;
        assert!(!a.can_undo());
        assert_eq!(x(&a)?, Some(3.0));
        Ok(())
    }

    /// Two stages creating different siblings do not conflict: the parent's
    /// child list is bookkeeping, and undoing A's prim keeps B's.
    #[test]
    fn foreign_sibling_keeps_step() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.define_prim("/A")?;
        b.define_prim("/B")?;
        assert!(a.can_undo());
        assert!(a.undo()?);
        assert!(!a.prim("/A")?.is_valid()?);
        assert!(a.prim("/B")?.is_valid()?, "B's sibling stays");
        Ok(())
    }

    /// Another stage creating a child under a prim a step created drops the
    /// step, whose undo would erase the child.
    #[test]
    fn foreign_child_drops_step() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.define_prim("/N")?;
        b.define_prim("/N/Child")?;
        assert!(!a.can_undo());
        assert!(a.prim("/N/Child")?.is_valid()?);
        Ok(())
    }

    /// A foreign edit made while an undo replays, overlapping a transaction
    /// not yet replayed, ends the revert: that transaction is not replayed
    /// over the other stage's value.
    #[test]
    fn revert_stops_on_conflict() -> Result<()> {
        struct Arm {
            armed: Rc<Cell<bool>>,
            b: Stage,
        }
        impl StageSink for Arm {
            fn after_commit(&self, _: &Stage, change: &CommittedChange<'_>) {
                if change.is_own()
                    && self.armed.replace(false)
                    && let Ok(attribute) = self.b.attribute("/P.x")
                {
                    let _ = attribute.set(2.0);
                }
            }
        }

        let (_dir, a, b) = shared_pair()?;
        a.group(|a| {
            a.attribute("/P.x")?.set(1.0)?;
            a.define_prim("/G")?;
            Ok::<_, Error>(())
        })?;
        let armed = Rc::new(Cell::new(false));
        let sink = a.add_sink(Arm {
            armed: Rc::clone(&armed),
            b: b.clone(),
        });
        armed.set(true);
        assert!(a.undo()?);
        a.remove_sink(sink);
        assert!(!a.prim("/G")?.is_valid()?, "the newest transaction reverted");
        assert_eq!(x(&a)?, Some(2.0), "the stale one was not replayed");
        assert!(!a.can_undo());
        Ok(())
    }

    /// A foreign edit overlapping an older transaction of an open group keeps
    /// the group's newer ones, which a failed group still reverts.
    #[test]
    fn group_keeps_newer() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        let failed = a.group(|a| {
            a.attribute("/P.x")?.set(1.0)?;
            a.define_prim("/G")?;
            b.attribute("/P.x")?.set(2.0)?;
            Err::<(), _>(Error::from(StageAuthoringError::PrimNotValid {
                path: sdf::path("/Failed")?,
            }))
        });
        assert!(failed.is_err());
        assert!(!a.prim("/G")?.is_valid()?, "the newer transaction reverted");
        assert_eq!(x(&a)?, Some(2.0), "the stale one did not");
        Ok(())
    }

    /// A reset made while an undo replays leaves the undo to finish its step.
    #[test]
    fn reset_mid_undo() -> Result<()> {
        struct Reset {
            undo: Rc<RefCell<Option<UndoStage>>>,
            armed: Rc<Cell<bool>>,
        }
        impl StageSink for Reset {
            fn after_commit(&self, _: &Stage, _: &CommittedChange<'_>) {
                if self.armed.replace(false)
                    && let Some(undo) = self.undo.borrow().as_ref()
                {
                    undo.reset();
                }
            }
        }

        let undo = UndoStage::from(in_memory_stage()?);
        undo.group(|stage| {
            stage.define_prim("/A")?;
            stage.define_prim("/B")?;
            Ok::<_, Error>(())
        })?;
        let slot = Rc::new(RefCell::new(None));
        let armed = Rc::new(Cell::new(false));
        let sink = undo.add_sink(Reset {
            undo: Rc::clone(&slot),
            armed: Rc::clone(&armed),
        });
        let stage = Stage::clone(&undo);
        slot.replace(Some(undo));
        armed.set(true);
        let undone = slot.borrow().as_ref().expect("the wrapper is set").undo()?;
        assert!(undone);
        stage.remove_sink(sink);
        assert!(!stage.prim("/A")?.is_valid()?, "the whole step reverted");
        assert!(!stage.prim("/B")?.is_valid()?);
        slot.take();
        Ok(())
    }

    /// Another stage adding a variant to a set a step created drops the step,
    /// whose undo would erase the set the variant belongs to.
    #[test]
    fn foreign_variant_drops_step() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.prim("/Q")?
            .variant_set("v")
            .add_variant("a", ListPosition::BackOfPrepend)?;
        b.prim("/Q")?
            .variant_set("v")
            .add_variant("b", ListPosition::BackOfPrepend)?;
        assert!(!a.can_undo());
        Ok(())
    }
}
