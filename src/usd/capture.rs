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

use crate::pcp;

use super::diff::{apply_edits_verbatim, forward_diff, inverse_diff};
use super::sink::{CommittedChange, PendingChange, StageSink, StageSinkId};
use super::stage::{Stage, StageAuthoringError};
use super::{Diff, Edit};

/// The default depth of an [`UndoStage`]'s undo stack.
const DEFAULT_CAPACITY: usize = 128;

/// A [`Stage`] that records the inverse of every edit it commits, for undo.
///
/// Derefs to the wrapped [`Stage`], so it authors and reads exactly like one;
/// each committed transaction pushes one entry onto the undo stack.
/// [`undo`](Self::undo) reverts the newest, [`reset`](Self::reset) discards the
/// stack, and [`into_inner`](Self::into_inner) stops recording.
///
/// The inverse is derived at the layer's commit seam, from
/// [`StageSink::before_commit`], the one moment the pre-edit values are still
/// readable — after the commit drains they are gone. Each layer's inverse is
/// buffered against its transaction id ([`PendingChange::generation`]) and
/// sealed into one entry when that transaction's
/// [`after_commit`](StageSink::after_commit) arrives; a transaction that rolls
/// back fires no `after_commit`, so its buffered captures are dropped when a
/// later transaction seals. The stack is bounded
/// ([`with_capacity`](Self::with_capacity)); once full, the oldest transaction is
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
    /// Wrap `stage` and begin recording, keeping at most `capacity` undo entries
    /// (at least one). Beyond that the oldest transaction is dropped and becomes
    /// permanent.
    pub fn with_capacity(stage: Stage, capacity: usize) -> Self {
        let journal = Journal {
            stack: VecDeque::new(),
            in_flight: Vec::new(),
            suspended: false,
            capacity: capacity.max(1),
        };
        Self {
            capture: CaptureStage::new(stage, journal, |journal| UndoRecorder { journal }),
        }
    }

    /// Revert the most recent recorded transaction, replaying its inverse onto
    /// the layers it touched. Returns whether anything was undone (`false` when
    /// the stack is empty). Repeated calls unwind further.
    ///
    /// The revert is itself an edit but is not recorded: capture is suspended
    /// for its duration, so an undone transaction leaves the stack shorter, not
    /// longer.
    pub fn undo(&self) -> Result<bool, StageAuthoringError> {
        // A direct `layer_mut` edit does not drain on its own, so seal any edit
        // still pending into the stack before reading it — otherwise it is
        // invisible to the pop, and the replay's own drain below would then skip
        // its seal and lose it. Draining on a query is the stage's normal
        // drain-on-read.
        self.capture.process_pending();
        // Pop under a short borrow and flag capture suspended, releasing the
        // borrow before the replay re-enters the sink.
        let transaction = {
            let mut journal = self.capture.log().borrow_mut();
            match journal.stack.pop_back() {
                Some(transaction) => {
                    journal.suspended = true;
                    transaction
                }
                None => return Ok(false),
            }
        };
        // Clear `suspended` even if the replay panics (a user sink could panic
        // mid-commit), so a panic can never leave capture permanently suspended.
        let result = {
            let _resume = ClearSuspend(self.capture.log());
            self.replay(&transaction)
        };
        match result {
            Ok(()) => Ok(true),
            // A single-mapping replay is atomic, so a failure applied nothing;
            // restore the entry so it stays undoable.
            Err(error) => {
                self.capture.log().borrow_mut().stack.push_back(transaction);
                Err(error)
            }
        }
    }

    /// Discard the recorded undo stack, keeping the current scene. Cheap — the
    /// captured inverse diffs are dropped without replaying. Recording continues
    /// for subsequent edits.
    pub fn reset(&self) {
        let mut journal = self.capture.log().borrow_mut();
        journal.stack.clear();
        journal.in_flight.clear();
    }

    /// Whether there is a recorded transaction to [`undo`](Self::undo). Drains any
    /// pending edit into the stack first, so an undrained direct edit counts.
    pub fn can_undo(&self) -> bool {
        self.capture.process_pending();
        !self.capture.log().borrow().stack.is_empty()
    }

    /// The number of recorded transactions on the undo stack. Drains any pending
    /// edit into the stack first, so an undrained direct edit is counted.
    pub fn undo_depth(&self) -> usize {
        self.capture.process_pending();
        self.capture.log().borrow().stack.len()
    }

    /// Stop recording and return the wrapped [`Stage`], removing the capture
    /// sink.
    pub fn into_inner(self) -> Stage {
        self.capture.into_inner()
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
    stack: VecDeque<Transaction>,
    /// Per-transaction captures awaiting their sealing `after_commit`. Buckets
    /// open in id order; a bucket older than a sealing transaction that was never
    /// sealed belongs to a rolled-back transaction and is dropped.
    in_flight: Vec<InFlight>,
    /// Set while [`undo`](UndoStage::undo) replays, so the revert's own commit is
    /// not recorded.
    suspended: bool,
    /// The maximum number of entries on [`stack`](Self::stack).
    capacity: usize,
}

/// Clears [`Journal::suspended`] on drop, so a panic during [`undo`](UndoStage::undo)'s
/// replay cannot leave capture permanently suspended.
struct ClearSuspend<'a>(&'a RefCell<Journal>);

impl Drop for ClearSuspend<'_> {
    fn drop(&mut self) {
        self.0.borrow_mut().suspended = false;
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
        journal.stack.push_back(Transaction {
            mapping: bucket.mapping,
            layers: bucket.layers,
        });
        while journal.stack.len() > journal.capacity {
            journal.stack.pop_front();
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
    use crate::sdf;
    use crate::usd::ApplyMode;
    use anyhow::Result;

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
        assert!(stage.prim("/World").is_valid()?);
        assert_eq!(stage.undo_depth(), 2);

        // The newest transaction is the type-name edit: undo restores its
        // absence, the prim survives.
        assert!(stage.undo()?);
        assert_eq!(stage.prim("/World").type_name()?.as_deref(), None);
        assert!(stage.prim("/World").is_valid()?);

        // Undo the define: the prim is gone, and the stack is empty.
        assert!(stage.undo()?);
        assert!(!stage.prim("/World").is_valid()?);
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
        stage.attribute("/World.size").set(2.0_f64)?;
        assert_eq!(stage.attribute("/World.size").get::<f64>()?, Some(2.0));

        assert!(stage.undo()?);
        assert_eq!(stage.attribute("/World.size").get::<f64>()?, Some(1.0));
        Ok(())
    }

    /// Every spec created in one transaction undoes together as one step: an
    /// ancestor chain authored by a single `define_prim` is one undo entry.
    #[test]
    fn undo_groups_transaction() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/A/B/C")?;
        assert!(stage.prim("/A/B/C").is_valid()?);
        assert_eq!(stage.undo_depth(), 1);

        assert!(stage.undo()?);
        assert!(!stage.prim("/A").is_valid()?);
        assert!(!stage.prim("/A/B/C").is_valid()?);
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
        assert!(stage.prim("/Direct").is_valid()?);
        assert!(stage.prim("/Staged").is_valid()?);
        assert_eq!(stage.undo_depth(), 2);

        assert!(stage.undo()?); // undo the staged edit
        assert!(!stage.prim("/Staged").is_valid()?);
        assert!(stage.prim("/Direct").is_valid()?, "the direct edit survives");

        assert!(stage.undo()?); // undo the direct edit
        assert!(!stage.prim("/Direct").is_valid()?);
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
        assert!(!stage.prim("/Direct").is_valid()?);
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
        assert!(stage.prim("/World").is_valid()?);
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
        assert!(!stage.prim("/B").is_valid()?);
        assert!(stage.prim("/A").is_valid()?, "the evicted /A edit is permanent");
        assert!(!stage.undo()?);
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
        assert!(stage.prim("/World").is_valid()?);
        assert!(stage.prim("/Another").is_valid()?);
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
        assert!(stage.prim("/World").is_valid()?);
        assert!(stage.prim("/Another").is_valid()?);
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
        assert_eq!(mirror.prim("/World").type_name()?.as_deref(), Some("Xform"));
        assert_eq!(mirror.prim("/World/Mesh").type_name()?.as_deref(), Some("Mesh"));
        assert_eq!(mirror.attribute("/World/Mesh.size").get::<f64>()?, Some(2.0));
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
        assert!(stage.prim("/Another").is_valid()?);
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
