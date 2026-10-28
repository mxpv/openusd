//! Recording stage wrappers: [`UndoStage`] and [`ReplayStage`].
//!
//! Both wrap a [`Stage`] and install a [`StageSink`] that captures a [`Diff`] of
//! every committed edit into a shared log:
//!
//! - [`UndoStage`] records the *inverse* of each transaction — the operations
//!   that restore the pre-edit state — onto an undo stack;
//!   [`undo`](UndoStage::undo) replays the newest to revert it.
//! - [`ReplayStage`] records the *forward* diff of each edit — a redo/replay log
//!   fed to [`Stage::apply_diff`] to reproduce the edits here or on a mirror.
//!
//! Recording is opt-in: a plain [`Stage`] captures nothing. The shared
//! `CaptureStage` plumbing installs the sink on construction and removes it when
//! the wrapper drops — through `into_inner` or by going out of scope — so
//! recording always stops with the wrapper, even if a [`Stage`] clone outlives
//! it.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::ops::Deref;
use std::rc::Rc;

use crate::Result;
use crate::pcp;

use super::diff::{apply_edits_verbatim, forward_diff, inverse_diff};
use super::sink::{CommittedChange, PendingChange, StageSink, StageSinkId};
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
/// The inverse is derived at the layer's commit seam, from
/// [`StageSink::before_commit`], the one moment the pre-edit values are still
/// readable — after the commit drains they are gone. Each layer's inverse is
/// buffered against its transaction id ([`PendingChange::generation`]) and
/// sealed into one entry when that transaction's
/// [`after_commit`](StageSink::after_commit) arrives; a transaction that rolls
/// back fires no `after_commit`, so its buffered captures are dropped when a
/// later transaction seals. The stack is bounded
/// ([`with_capacity`](Self::with_capacity)); once full, the oldest step is
/// dropped and becomes permanent.
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
            group: None,
            suspended: false,
            capacity: capacity.max(1),
        };
        Self {
            capture: CaptureStage::new(stage, journal, |journal| UndoRecorder { journal }),
        }
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
    pub fn group<T, E>(&self, edit: impl FnOnce(&Stage) -> Result<T, E>) -> Result<T, E>
    where
        E: From<StageAuthoringError>,
    {
        // An edit committed before the group, still pending, is not part of it.
        self.capture.process_pending();
        let (outermost, start) = {
            let mut journal = self.capture.log().borrow_mut();
            let outermost = journal.group.is_none();
            let open = journal.group.get_or_insert_with(Vec::new);
            (outermost, open.len())
        };
        // Closes the group when the outermost edit returns or unwinds,
        // recording what it committed as one step.
        let _close = CloseGroup {
            journal: self.capture.log(),
            outermost,
        };
        let result = edit(&self.capture);
        // A direct edit made inside the group seals into it.
        self.capture.process_pending();
        match result {
            Ok(value) => Ok(value),
            Err(error) => {
                let committed = {
                    let mut journal = self.capture.log().borrow_mut();
                    journal
                        .group
                        .as_mut()
                        .map(|open| open.split_off(start))
                        .unwrap_or_default()
                };
                // What could not be reverted stays in the group, still undoable.
                if let Err((revert, unreverted)) = self.revert(committed) {
                    if let Some(open) = self.capture.log().borrow_mut().group.as_mut() {
                        open.extend(unreverted);
                    }
                    return Err(revert.into());
                }
                Err(error)
            }
        }
    }

    /// Revert the most recent step, replaying the inverse of each of its
    /// transactions, newest first, onto the layers it touched. Returns whether
    /// anything was undone (`false` when the stack is empty). Repeated calls
    /// unwind further.
    ///
    /// The revert is itself an edit but is not recorded: capture is suspended
    /// for its duration, so an undone step leaves the stack shorter, not
    /// longer. Each transaction reverts atomically; one that fails leaves the
    /// transactions not yet reverted on the stack as the newest step.
    pub fn undo(&self) -> Result<bool, StageAuthoringError> {
        // A direct `layer_mut` edit does not drain on its own, so seal any edit
        // still pending into the stack before reading it — otherwise it is
        // invisible to the pop, and the replay's own drain below would then skip
        // its seal and lose it. Draining on a query is the stage's normal
        // drain-on-read.
        self.capture.process_pending();
        let Some(step) = self.capture.log().borrow_mut().stack.pop_back() else {
            return Ok(false);
        };
        match self.revert(step.transactions) {
            Ok(()) => Ok(true),
            Err((error, unreverted)) => {
                self.capture.log().borrow_mut().stack.push_back(Step::new(unreverted));
                Err(error)
            }
        }
    }

    /// Discard the recorded undo stack, keeping the current scene. Cheap — the
    /// captured inverse diffs are dropped without replaying. Recording continues
    /// for subsequent edits, a group still open included.
    pub fn reset(&self) {
        let mut journal = self.capture.log().borrow_mut();
        journal.stack.clear();
        journal.in_flight.clear();
        if let Some(open) = journal.group.as_mut() {
            open.clear();
        }
    }

    /// Discard up to `count` of the oldest steps, keeping the current scene,
    /// as eviction from a full stack does. Returns how many were discarded.
    /// Drains any pending edit into the stack first.
    pub fn discard_oldest(&self, count: usize) -> usize {
        self.capture.process_pending();
        let mut journal = self.capture.log().borrow_mut();
        let count = count.min(journal.stack.len());
        journal.stack.drain(..count);
        count
    }

    /// Keep only the steps `keep` accepts, oldest first, discarding the rest
    /// without replaying them. A step discarded below a kept one is
    /// permanent, as an evicted one is, so a caller drops only steps whose
    /// layers it no longer edits through this history, such as layers it
    /// reloaded. Drains any pending edit into the stack first.
    pub fn retain(&self, mut keep: impl FnMut(&UndoStep) -> bool) {
        self.capture.process_pending();
        self.capture.log().borrow_mut().stack.retain(|step| keep(&step.summary));
    }

    /// The steps on the undo stack, oldest first. Drains any pending edit into
    /// the stack first.
    pub fn steps(&self) -> Vec<UndoStep> {
        self.capture.process_pending();
        let journal = self.capture.log().borrow();
        journal.stack.iter().map(|step| step.summary.clone()).collect()
    }

    /// Run `edit` without recording what it commits, such as a layer reloaded
    /// from disk, which no undo should revert. Drains any pending edit into
    /// the stack first. Recording resumes as it was when `edit` returns or
    /// unwinds, so a call inside another keeps the outer one unrecorded.
    pub fn without_recording<T>(&self, edit: impl FnOnce(&Stage) -> T) -> T {
        self.capture.process_pending();
        let _suspend = Suspend::begin(self.capture.log());
        let result = edit(&self.capture);
        // A direct edit made inside commits while capture is still suspended.
        self.capture.process_pending();
        result
    }

    /// Whether there is a recorded step to [`undo`](Self::undo). Drains any
    /// pending edit into the stack first, so an undrained direct edit counts.
    pub fn can_undo(&self) -> bool {
        self.capture.process_pending();
        !self.capture.log().borrow().stack.is_empty()
    }

    /// The number of recorded steps on the undo stack. Drains any pending edit
    /// into the stack first, so an undrained direct edit is counted.
    pub fn undo_depth(&self) -> usize {
        self.capture.process_pending();
        self.capture.log().borrow().stack.len()
    }

    /// Stop recording and return the wrapped [`Stage`], removing the capture
    /// sink.
    pub fn into_inner(self) -> Stage {
        self.capture.into_inner()
    }

    /// Replay the inverse of each of `transactions`, newest first, with
    /// capture suspended. On a failure, returns the error with the
    /// transactions not yet reverted, the failed one included, oldest first.
    fn revert(&self, mut transactions: Vec<Transaction>) -> Result<(), (StageAuthoringError, Vec<Transaction>)> {
        // Restore capture even if a replay panics (a user sink could panic
        // mid-commit), so a panic can never leave capture suspended.
        let _suspend = Suspend::begin(self.capture.log());
        while let Some(transaction) = transactions.pop() {
            // A single-mapping replay is atomic, so a failure applied nothing.
            if let Err(error) = self.replay(&transaction) {
                transactions.push(transaction);
                return Err((error, transactions));
            }
        }
        Ok(())
    }

    /// Replay `transaction`'s per-layer inverse edits as one atomic
    /// [`author_layers_txn`] (all-or-nothing) through its shared edit-target
    /// mapping. A layer no longer in the stage is skipped.
    fn replay(&self, transaction: &Transaction) -> Result<(), StageAuthoringError> {
        // Resolve recorded identifiers to live layer ids under a short graph
        // borrow, pairing each with its inverse edits. The borrow is released
        // before `author_layers_txn` re-borrows the graph mutably.
        let batch: Vec<(pcp::LayerId, &[Edit])> = {
            let graph = self.capture.layers();
            transaction
                .layers
                .iter()
                .filter_map(|(identifier, edits)| graph.id_of(identifier).map(|id| (id, edits.as_slice())))
                .collect()
        };
        if batch.is_empty() {
            return Ok(());
        }
        let ids: Vec<pcp::LayerId> = batch.iter().map(|(id, _)| *id).collect();
        self.capture
            .author_layers_txn(&ids, transaction.mapping.as_ref(), true, |realized, edits| {
                for (edit, &id) in edits.iter_mut().zip(realized) {
                    if let Some((_, ops)) = batch.iter().find(|(batch_id, _)| *batch_id == id) {
                        apply_edits_verbatim(edit, ops).map_err(StageAuthoringError::from)?;
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

/// The recorded inverse of one atomic transaction: its per-layer inverse edits
/// (each keyed by layer identifier) and the one edit-target mapping they were
/// authored through — a transaction's layers share it, so it is stored once.
struct Transaction {
    mapping: Option<pcp::MapFunction>,
    layers: Vec<(String, Vec<Edit>)>,
}

/// One step of an [`UndoStage`]'s undo stack, as [`UndoStage::steps`] and
/// [`UndoStage::retain`] show it: what one [`undo`](UndoStage::undo) reverts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UndoStep {
    layers: Vec<String>,
}

impl UndoStep {
    /// The identifiers of the layers the step edits, in the order its
    /// transactions first edited them.
    pub fn layers(&self) -> &[String] {
        &self.layers
    }

    /// Whether the step edits the layer `identifier`.
    pub fn edits_layer(&self, identifier: &str) -> bool {
        self.layers.iter().any(|layer| layer == identifier)
    }
}

/// The recorded transactions of one step, oldest first, with the summary
/// [`UndoStep`] shows of them.
struct Step {
    transactions: Vec<Transaction>,
    summary: UndoStep,
}

impl Step {
    fn new(transactions: Vec<Transaction>) -> Self {
        let mut layers: Vec<String> = Vec::new();
        for (identifier, _) in transactions.iter().flat_map(|transaction| &transaction.layers) {
            if !layers.contains(identifier) {
                layers.push(identifier.clone());
            }
        }
        Self {
            transactions,
            summary: UndoStep { layers },
        }
    }
}

/// A transaction's captures buffered at `before_commit`, awaiting its sealing
/// `after_commit`, keyed by the transaction id ([`PendingChange::generation`]).
struct InFlight {
    generation: u64,
    mapping: Option<pcp::MapFunction>,
    layers: Vec<(String, Vec<Edit>)>,
}

/// An [`UndoStage`]'s recording state.
struct Journal {
    /// The undo stack, oldest at the front (the eviction end), newest at the
    /// back (the [`undo`](UndoStage::undo) end).
    stack: VecDeque<Step>,
    /// Per-transaction captures awaiting their sealing `after_commit`. Buckets
    /// open in id order; a bucket older than a sealing transaction that was never
    /// sealed belongs to a rolled-back transaction and is dropped.
    in_flight: Vec<InFlight>,
    /// The transactions sealed inside the open [`group`](UndoStage::group),
    /// oldest first, or `None` outside one.
    group: Option<Vec<Transaction>>,
    /// Set while [`undo`](UndoStage::undo) replays or
    /// [`without_recording`](UndoStage::without_recording) runs, so their
    /// commits are not recorded.
    suspended: bool,
    /// The maximum number of steps on [`stack`](Self::stack).
    capacity: usize,
}

impl Journal {
    /// Push `transactions` as the newest step, evicting the oldest past
    /// capacity.
    fn push_step(&mut self, transactions: Vec<Transaction>) {
        self.stack.push_back(Step::new(transactions));
        while self.stack.len() > self.capacity {
            self.stack.pop_front();
        }
    }
}

/// Suspends capture until dropped, then restores it as it was, so nested
/// suspensions and a panic mid-replay leave it as they found it.
struct Suspend<'a> {
    journal: &'a RefCell<Journal>,
    previous: bool,
}

impl<'a> Suspend<'a> {
    fn begin(journal: &'a RefCell<Journal>) -> Self {
        let previous = std::mem::replace(&mut journal.borrow_mut().suspended, true);
        Self { journal, previous }
    }
}

impl Drop for Suspend<'_> {
    fn drop(&mut self) {
        self.journal.borrow_mut().suspended = self.previous;
    }
}

/// Closes the outermost [`group`](UndoStage::group) when dropped, recording
/// what it committed as one step.
struct CloseGroup<'a> {
    journal: &'a RefCell<Journal>,
    outermost: bool,
}

impl Drop for CloseGroup<'_> {
    fn drop(&mut self) {
        if !self.outermost {
            return;
        }
        let mut journal = self.journal.borrow_mut();
        if let Some(open) = journal.group.take()
            && !open.is_empty()
        {
            journal.push_step(open);
        }
    }
}

/// The [`StageSink`] an [`UndoStage`] installs: it captures each layer's inverse
/// at `before_commit` and seals the transaction at `after_commit`.
struct UndoRecorder {
    journal: Rc<RefCell<Journal>>,
}

impl StageSink for UndoRecorder {
    fn before_commit(&self, _stage: &Stage, change: &PendingChange<'_>) {
        let mut journal = self.journal.borrow_mut();
        if journal.suspended {
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
        let layer = (change.layer_identifier.to_string(), edits);
        // Buffer against this transaction's id. Its layers commit consecutively
        // and ids increase, so the current bucket — if any — is the last one; a
        // new bucket captures the transaction's mapping once (all layers share it).
        match journal.in_flight.last_mut() {
            Some(bucket) if bucket.generation == change.generation => bucket.layers.push(layer),
            _ => journal.in_flight.push(InFlight {
                generation: change.generation,
                mapping: change.mapping.cloned(),
                layers: vec![layer],
            }),
        }
    }

    fn after_commit(&self, _stage: &Stage, change: &CommittedChange<'_>) {
        let mut journal = self.journal.borrow_mut();
        if journal.suspended {
            return;
        }
        let generation = change.generation;
        // Buckets open in id order and `after_commit`s arrive in id order, so any
        // bucket older than this transaction never sealed — it rolled back (no
        // `after_commit`). Drop those orphans off the front, then seal this
        // transaction's bucket if it captured anything.
        while journal
            .in_flight
            .first()
            .is_some_and(|bucket| bucket.generation < generation)
        {
            journal.in_flight.remove(0);
        }
        if journal.in_flight.first().map(|bucket| bucket.generation) != Some(generation) {
            return;
        }
        let bucket = journal.in_flight.remove(0);
        let transaction = Transaction {
            mapping: bucket.mapping,
            layers: bucket.layers,
        };
        match journal.group.as_mut() {
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
    /// Wrap `stage` and begin recording. Installs the capture sink; drop the
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

    /// Stop recording and return the wrapped [`Stage`], removing the capture
    /// sink.
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

/// The [`StageSink`] a [`ReplayStage`] installs: it appends each committed edit's
/// forward diff to the shared log.
struct ReplayRecorder {
    log: Rc<RefCell<Vec<Diff>>>,
}

impl StageSink for ReplayRecorder {
    fn after_commit(&self, stage: &Stage, change: &CommittedChange<'_>) {
        // One forward diff per edited layer, read from that layer's committed
        // data. A layer that produced no operations (only child-name bookkeeping)
        // contributes nothing; an edit whose diff can't be derived (a field that
        // fails to read) is dropped — an `after_commit` observer cannot surface an
        // error.
        if let Ok(diffs) = forward_diff(stage, change) {
            self.log.borrow_mut().extend(diffs);
        }
    }
}

/// A [`Stage`] with a recording [`StageSink`] installed and a shared log of type
/// `L` the sink writes — the shared plumbing behind [`UndoStage`] and
/// [`ReplayStage`].
///
/// The log is an `Rc<RefCell<L>>` shared between the installed sink and the
/// wrapper handle, so a returned sub-view (a [`Prim`](super::Prim) authoring
/// through its own stage clone) still records through the same sink. The sink is
/// removed when this `CaptureStage` drops — whether through
/// [`into_inner`](Self::into_inner) or by going out of scope — so recording
/// always stops with the wrapper, even if a [`Stage`] clone outlives it.
struct CaptureStage<L> {
    stage: Stage,
    log: Rc<RefCell<L>>,
    sink: StageSinkId,
}

impl<L> CaptureStage<L> {
    /// Wrap `stage` with a fresh `Rc<RefCell<log>>` and install the sink
    /// `make_sink` builds from a clone of it. `make_sink` receives the shared log
    /// so the sink writes what the wrapper reads.
    fn new<S: StageSink + 'static>(stage: Stage, log: L, make_sink: impl FnOnce(Rc<RefCell<L>>) -> S) -> Self {
        let log = Rc::new(RefCell::new(log));
        let sink = stage.add_sink(make_sink(log.clone()));
        Self { stage, log, sink }
    }

    /// The shared log, for the wrapper's queries.
    fn log(&self) -> &RefCell<L> {
        &self.log
    }

    /// Return a handle to the wrapped stage; the recording sink is removed as this
    /// `CaptureStage` drops at the end of the call.
    fn into_inner(self) -> Stage {
        // The `Drop` below removes the sink, so the stage cannot be moved out of
        // `self`; return a clone (a cheap `Rc` bump onto the same stage) and let
        // the drop uninstall the sink.
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
    /// Remove the recording sink, so recording stops when the wrapper goes away
    /// even if a [`Stage`] clone (or a returned sub-view) outlives it — otherwise
    /// later edits would keep writing into a now-unreachable log.
    fn drop(&mut self) {
        self.stage.remove_sink(self.sink);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Result;
    use crate::sdf;
    use crate::usd::{ApplyMode, EditTarget};

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
    /// ancestor chain authored by a single `define_prim` is one undo entry.
    #[test]
    fn undo_groups_transaction() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/A/B/C")?;
        assert!(stage.prim("/A/B/C")?.is_valid()?);
        assert_eq!(stage.undo_depth(), 1);

        assert!(stage.undo()?);
        assert!(!stage.prim("/A")?.is_valid()?);
        assert!(!stage.prim("/A/B/C")?.is_valid()?);
        Ok(())
    }

    /// A direct `layer_mut` edit left pending when a stage edit lands keeps its
    /// own undo entry — the two transactions do not coalesce, and neither
    /// inverse is discarded.
    #[test]
    fn undo_pending_direct_edit() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        // A direct layer edit, deliberately not followed by a composed read, so
        // it sits pending when the stage edit below commits.
        let root = stage.root_layer().identifier().to_string();
        {
            let mut layer = stage.layer_mut(&root).expect("root layer");
            layer.edit(|l| author_prim(l, "/Direct"))?;
        }
        stage.define_prim("/Staged")?;

        // Both transactions were recorded, newest first.
        assert!(stage.prim("/Direct")?.is_valid()?);
        assert!(stage.prim("/Staged")?.is_valid()?);
        assert_eq!(stage.undo_depth(), 2);

        assert!(stage.undo()?); // undo the staged edit
        assert!(!stage.prim("/Staged")?.is_valid()?);
        assert!(stage.prim("/Direct")?.is_valid()?, "the direct edit survives");

        assert!(stage.undo()?); // undo the direct edit
        assert!(!stage.prim("/Direct")?.is_valid()?);
        Ok(())
    }

    /// A direct `layer_mut` edit is undoable with no intervening composed read or
    /// stage edit: `undo` (and `can_undo`/`undo_depth`) drains the still-pending
    /// edit into the stack first, so it is neither invisible nor lost to the
    /// replay's own drain.
    #[test]
    fn undo_direct_edit_no_drain() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        let root = stage.root_layer().identifier().to_string();
        {
            let mut layer = stage.layer_mut(&root).expect("root layer");
            layer.edit(|l| author_prim(l, "/Direct"))?;
        }
        // No composed read or stage edit drains the pending edit before undo.
        assert!(stage.undo()?, "the pending direct edit is undone");
        assert!(!stage.prim("/Direct")?.is_valid()?);
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

    /// A bounded stack drops the oldest transaction once full; the evicted edit
    /// becomes permanent (no longer undoable).
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
            assert!(undo.group(|stage| fail(stage, "/Dropped")).is_err());
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
        let stage = UndoStage::with_capacity(in_memory_stage()?, 1);
        stage.group(|stage| {
            stage.define_prim("/World")?.set_type_name("Xform")?;
            Ok::<_, crate::Error>(())
        })?;
        assert_eq!(stage.undo_depth(), 1);
        assert!(stage.undo()?);
        assert!(!stage.prim("/World")?.is_valid()?);
        Ok(())
    }

    /// `discard_oldest` drops whole steps and keeps the scene; the newer
    /// steps stay undoable.
    #[test]
    fn discard_oldest_drops_steps() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.group(|stage| {
            stage.define_prim("/World")?.set_type_name("Xform")?;
            Ok::<_, crate::Error>(())
        })?;
        stage.define_prim("/World/Child")?;
        assert_eq!(stage.discard_oldest(0), 0);
        assert_eq!(stage.discard_oldest(1), 1);
        assert_eq!(stage.undo_depth(), 1);
        assert!(stage.undo()?);
        assert!(!stage.prim("/World/Child")?.is_valid()?);
        assert_eq!(stage.prim("/World")?.type_name()?.as_deref(), Some("Xform"));
        assert_eq!(stage.discard_oldest(usize::MAX), 0);
        Ok(())
    }

    /// What `without_recording` commits is not undone, a direct edit inside it
    /// included; a call inside another keeps the outer one unrecorded, and
    /// recording resumes after.
    #[test]
    fn without_recording_is_not_undone() -> Result<()> {
        let undo = UndoStage::from(in_memory_stage()?);
        let root = undo.root_layer().identifier().to_string();
        undo.without_recording(|stage| -> Result<()> {
            undo.without_recording(|stage| stage.define_prim("/Nested").map(drop))?;
            stage.define_prim("/AfterNested")?;
            let mut layer = stage.layer_mut(&root).expect("root layer");
            layer.edit(|edit| author_prim(edit, "/Direct"))?;
            Ok(())
        })?;
        assert!(!undo.can_undo());
        for path in ["/Nested", "/AfterNested", "/Direct"] {
            assert!(undo.prim(path)?.is_valid()?, "{path}");
        }
        undo.define_prim("/Recorded")?;
        assert_eq!(undo.undo_depth(), 1);
        Ok(())
    }

    /// Each step lists the layers it edits, and `retain` drops the steps a
    /// predicate refuses, keeping the scene and the other steps.
    #[test]
    fn retain_drops_steps_by_layer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let weak = dir.path().join("weak.usda");
        std::fs::write(&weak, "#usda 1.0\n")?;
        let root = dir.path().join("root.usda");
        std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@./weak.usda@]\n)\n")?;
        let stage = UndoStage::from(Stage::open(root.to_str().unwrap())?);
        let root = stage.root_layer().identifier().to_string();
        let weak = stage
            .layer_identifiers()
            .into_iter()
            .find(|identifier| *identifier != root)
            .expect("the sublayer is loaded");
        stage.define_prim("/Strong")?;
        stage.set_edit_target(EditTarget::for_layer(&weak))?;
        stage.define_prim("/Weak")?;
        let steps = stage.steps();
        assert_eq!(steps.len(), 2);
        assert_eq!(steps[0].layers(), std::slice::from_ref(&root));
        assert!(steps[1].edits_layer(&weak));

        stage.retain(|step| !step.edits_layer(&weak));
        assert_eq!(stage.steps().len(), 1);
        assert!(stage.prim("/Weak")?.is_valid()?);
        assert!(stage.undo()?);
        assert!(!stage.prim("/Strong")?.is_valid()?);
        assert!(stage.prim("/Weak")?.is_valid()?);
        Ok(())
    }

    /// `UndoStage::into_inner` removes the recording sink and returns the wrapped
    /// stage, which then authors normally.
    #[test]
    fn undo_into_inner_returns_stage() -> Result<()> {
        let undo = UndoStage::from(in_memory_stage()?);
        undo.define_prim("/World")?;
        let stage = undo.into_inner();
        assert_eq!(stage.sink_count(), 0, "into_inner removes the sink");
        stage.define_prim("/Another")?;
        assert!(stage.prim("/World")?.is_valid()?);
        assert!(stage.prim("/Another")?.is_valid()?);
        Ok(())
    }

    /// Dropping an [`UndoStage`] without `into_inner` still removes its recording
    /// sink, so recording stops even when a stage clone outlives it — no sink
    /// left writing into an unreachable log.
    #[test]
    fn undo_drop_removes_sink() -> Result<()> {
        let stage = in_memory_stage()?;
        assert_eq!(stage.sink_count(), 0);
        {
            let undo = UndoStage::from(stage.clone());
            assert_eq!(stage.sink_count(), 1);
            undo.define_prim("/World")?;
        }
        assert_eq!(stage.sink_count(), 0, "the sink is removed when the wrapper drops");
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
        assert_eq!(stage.sink_count(), 0, "into_inner removes the sink");
        stage.define_prim("/Another")?;
        assert!(stage.prim("/Another")?.is_valid()?);
        Ok(())
    }

    /// Dropping a [`ReplayStage`] without `into_inner` removes its recording sink.
    #[test]
    fn replay_drop_removes_sink() -> Result<()> {
        let stage = in_memory_stage()?;
        {
            let source = ReplayStage::from(stage.clone());
            assert_eq!(stage.sink_count(), 1);
            source.define_prim("/World")?;
        }
        assert_eq!(stage.sink_count(), 0, "the sink is removed when the wrapper drops");
        Ok(())
    }
}
