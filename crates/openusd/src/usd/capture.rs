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
use std::collections::{HashSet, VecDeque};
use std::mem;
use std::ops::Deref;
use std::rc::Rc;

use crate::Result;
use crate::{pcp, sdf};

use super::diff::{apply_edits_verbatim, forward_diff, inverse_diff};
use super::sink::{CommittedChange, PendingChange, ReplayId, TxnObserver};
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
            frames: Vec::new(),
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
    /// reverted and no step is recorded, unless an own edit a sink makes
    /// during that rollback overlaps one not yet reverted ([`undo`](Self::undo)
    /// has the rule): that one and the older ones stay, recorded with the
    /// sink's edit as one step. A group run inside another joins it, its
    /// error reverting only what it committed itself.
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
        self.capture.log().borrow_mut().frames.push(Frame::Group(Vec::new()));
        let _close = CloseGroup(self.capture.log());
        let result = edit(self);
        // Reconcile what the group committed, which seals it into the group.
        self.capture.process_pending();
        let Err(error) = result else {
            return result;
        };
        let committed = match self.capture.log().borrow_mut().frames.last_mut() {
            Some(Frame::Group(transactions)) => mem::take(transactions),
            _ => unreachable!("a group is the innermost frame until its guard drops"),
        };
        // The rollback runs inside the still-open group: what it does not
        // revert goes back into the group, still undoable, and keeps the
        // layers it names.
        self.capture.holding_reclaims(|| match self.revert(committed) {
            Ok(()) => Err(error),
            Err(revert) => Err(revert.into()),
        })
    }

    /// Revert the most recent step, replaying the inverse of each of its
    /// transactions, newest first, onto the layers it touched. Returns whether
    /// anything was undone (`false` when the stack is empty). Repeated calls
    /// unwind further.
    ///
    /// The revert is itself an edit but is not recorded: its replays carry
    /// its identity, which this stage's recorder skips, so the undone step
    /// leaves the stack and no step of the replays joins it. Each transaction
    /// reverts atomically; one that fails leaves the transactions not yet
    /// reverted on the stack, the failed one to be retried first, beneath
    /// whatever a sink recorded during the undo. An
    /// edit made elsewhere while the step replays, overlapping one of its
    /// transactions not yet replayed, ends the revert before that one, so the
    /// step is undone in part and the other editor's work stays.
    ///
    /// An own edit a sink makes while the step replays is recorded as a newer
    /// step, a group a sink runs as one. The revert then stops before the
    /// newest of its transactions not yet replayed that the edit overlaps,
    /// and those stay on the stack beneath the sink's step, so undoing again
    /// reverts the sink's edit first. However the revert ends, a panic
    /// included, what it did not replay and what was recorded during it are
    /// back in the history in that order.
    ///
    /// Inside an open [`group`](Self::group), or while this stage's undo
    /// replays (from a sink), nothing is undone, and this returns `false`
    /// without changing the history: the group's own edits, or the step being
    /// reverted, are newer than every step on the stack.
    pub fn undo(&self) -> Result<bool, StageAuthoringError> {
        // Reconcile every committed edit before reading the stack. One still
        // queued (made from inside a sink's delivery) then seals before the
        // pop, not in the replay's own drain after it.
        self.capture.settle()?;
        let step = {
            let mut journal = self.capture.log().borrow_mut();
            if !journal.frames.is_empty() {
                return Ok(false);
            }
            journal.stack.pop_back()
        };
        let Some(step) = step else {
            return Ok(false);
        };
        // A replay takes its transaction out of the history before it runs,
        // so the hold keeps that transaction's layers through the replays'
        // reclaims, until what is not reverted is back on the stack.
        self.capture.holding_reclaims(|| self.revert(step).map(|()| true))
    }

    /// Discard the recorded undo stack, keeping the current scene. Cheap — the
    /// captured inverse diffs are dropped without replaying. Recording continues
    /// for subsequent edits, a group still open included. An undo in progress
    /// replays to its end, except the transactions a sink's edit protected
    /// ([`undo`](Self::undo)), and returns nothing to the stack.
    pub fn reset(&self) {
        self.capture.log().borrow_mut().discard();
        // The layers only the history held may leave.
        self.capture.end_edit();
    }

    /// Whether [`undo`](Self::undo) would revert a step: one is recorded, and
    /// neither a [`group`](Self::group) nor an undo is open. Every committed
    /// edit counts: this reconciles first.
    pub fn can_undo(&self) -> bool {
        self.capture.process_pending();
        let journal = self.capture.log().borrow();
        journal.frames.is_empty() && !journal.stack.is_empty()
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
        let stage = self.capture.into_inner();
        // The layers only the history held may leave.
        stage.end_edit();
        stage
    }

    /// Replay the inverse of each of `transactions`, oldest first in the
    /// list, newest first in time, as a revert frame ([`RevertFrame`]),
    /// which puts back what it did not replay, and the steps recorded during
    /// it, on every way out.
    ///
    /// Each round settles first, so a pending edit elsewhere drops what it
    /// made stale before the next transaction is chosen, and nothing drains
    /// between the choice and its commit. The revert ends when nothing
    /// unprotected is left ([`Journal::seal`]).
    fn revert(&self, transactions: Vec<Transaction>) -> Result<(), StageAuthoringError> {
        let journal = self.capture.log();
        let frame = RevertFrame::open(journal, transactions);
        loop {
            self.capture.settle()?;
            let selected = journal.borrow_mut().revert_mut(frame.id).and_then(Revert::select);
            let Some(transaction) = selected else {
                return Ok(());
            };
            self.replay(frame.id, &transaction)?;
        }
    }

    /// Replay `transaction`, the revert `id`'s replay in progress, as one
    /// atomic transaction (all-or-nothing) through its shared edit-target
    /// mapping, carrying `id`. It stops being in progress as its commit
    /// lands, before the commit is delivered: a panic before it lands (a
    /// `before_commit` sink) leaves it for the revert to put back, and one
    /// after (an `after_commit` sink) leaves it done.
    fn replay(&self, id: ReplayId, transaction: &Transaction) -> Result<(), StageAuthoringError> {
        let journal = self.capture.log();
        let ids: Vec<pcp::LayerId> = transaction.layers.iter().map(|inverse| inverse.layer).collect();
        let committed: Result<sdf::Committed, StageAuthoringError> =
            self.capture
                .commit_layers_txn(&ids, transaction.mapping.as_ref(), Some(id), |realized, edits| {
                    for (edit, &id) in edits.iter_mut().zip(realized) {
                        if let Some(inverse) = transaction.layers.iter().find(|inverse| inverse.layer == id) {
                            apply_edits_verbatim(edit, &inverse.edits).map_err(StageAuthoringError::from)?;
                        }
                    }
                    Ok(())
                });
        if committed.is_ok()
            && let Some(revert) = journal.borrow_mut().revert_mut(id)
        {
            revert.in_progress = None;
        }
        self.capture.deliver_edit(committed)?;
        Ok(())
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
    /// Whether edits that touched each layer in `footprints` with its
    /// footprint overlap what this transaction's inverse would restore. A
    /// layer may be listed with several footprints, all of which count.
    fn overlaps(&self, footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)]) -> bool {
        self.layers.iter().any(|inverse| {
            footprints
                .iter()
                .any(|(layer, footprint)| *layer == inverse.layer && inverse.footprint.overlaps(footprint))
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
    /// The open groups and reverts, the outermost first. The history runs,
    /// oldest to newest, through the stack's steps and then each frame in
    /// order: a group's transactions; a revert's transactions still to
    /// replay, its replay in progress, then the steps recorded inside it.
    frames: Vec<Frame>,
    /// The maximum number of steps on [`stack`](Self::stack).
    capacity: usize,
}

/// An open [`group`](UndoStage::group) or a revert in progress, in
/// [`Journal::frames`].
enum Frame {
    /// A group's sealed transactions, oldest first.
    Group(Vec<Transaction>),
    /// A revert in progress.
    Revert(Revert),
}

/// A revert in progress ([`UndoStage::revert`]).
struct Revert {
    /// The identity its replays carry.
    id: ReplayId,
    /// The transactions it has still to replay, newest last.
    remaining: Vec<Pending>,
    /// The transaction being replayed, taken out of
    /// [`remaining`](Self::remaining) until its commit lands: still undo
    /// work, and the newest of it. Shared with the replay, which reads its
    /// edits while the journal is free for the recorder.
    in_progress: Option<Rc<Transaction>>,
    /// The steps sealed while it runs, oldest first.
    recorded: Vec<Vec<Transaction>>,
    /// Whether a [`reset`](UndoStage::reset) discarded the history it
    /// reverts, so its remainder is dropped as it ends.
    discarded: bool,
}

/// A transaction a revert has still to replay.
struct Pending {
    transaction: Transaction,
    /// Whether an own edit made while the revert runs overlaps it, or a
    /// newer transaction of the revert: the revert never replays it.
    protected: bool,
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

    /// Whether `replay` names one of this journal's reverts, whose replays
    /// capture skips.
    fn is_replay(&self, replay: Option<ReplayId>) -> bool {
        replay.is_some_and(|replay| {
            self.frames
                .iter()
                .any(|frame| matches!(frame, Frame::Revert(revert) if revert.id == replay))
        })
    }

    /// The revert `id` names.
    fn revert_mut(&mut self, id: ReplayId) -> Option<&mut Revert> {
        self.frames.iter_mut().find_map(|frame| match frame {
            Frame::Revert(revert) if revert.id == id => Some(revert),
            _ => None,
        })
    }

    /// Add to `layers` the layers the recorded transactions name, through
    /// the whole history and the captures awaiting their reconciliation.
    fn hold(&self, layers: &mut HashSet<pcp::LayerId>) {
        let mut add = |transaction: &Transaction| layers.extend(transaction.layers.iter().map(|inverse| inverse.layer));
        self.stack.iter().flatten().for_each(&mut add);
        for frame in &self.frames {
            match frame {
                Frame::Group(transactions) => transactions.iter().for_each(&mut add),
                Frame::Revert(revert) => {
                    revert.work().for_each(&mut add);
                    revert.recorded.iter().flatten().for_each(&mut add);
                }
            }
        }
        self.in_flight
            .iter()
            .map(|flight| &flight.transaction)
            .for_each(&mut add);
    }

    /// Drop every recorded step and capture, the open groups' and the
    /// steps recorded inside a revert included, and mark each revert
    /// discarded: it replays to its end, never a protected transaction, and
    /// returns nothing to history.
    fn discard(&mut self) {
        self.in_flight.clear();
        self.stack.clear();
        for frame in &mut self.frames {
            match frame {
                Frame::Group(transactions) => transactions.clear(),
                Frame::Revert(revert) => {
                    revert.recorded.clear();
                    revert.discarded = true;
                }
            }
        }
    }

    /// Protect, in every revert, the newest transaction still to replay that
    /// an own edit, which touched each layer in `footprints` with its
    /// footprint, overlaps, and each older one, so no replay overwrites the
    /// edit; they stay undoable beneath it.
    fn protect(&mut self, footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)]) {
        for frame in &mut self.frames {
            if let Frame::Revert(revert) = frame
                && let Some(newest) = revert
                    .remaining
                    .iter()
                    .rposition(|pending| pending.transaction.overlaps(footprints))
            {
                for pending in &mut revert.remaining[..=newest] {
                    pending.protected = true;
                }
            }
        }
    }

    /// Seal `transaction`, an own edit, into the innermost frame: a group
    /// appends it, a revert records it as a step, and with none open it is
    /// the newest step.
    fn seal(&mut self, transaction: Transaction) {
        match self.frames.last_mut() {
            Some(Frame::Group(transactions)) => transactions.push(transaction),
            Some(Frame::Revert(revert)) => revert.recorded.push(vec![transaction]),
            None => self.push_step(vec![transaction]),
        }
    }

    /// Close the innermost frame, an open group: what it committed joins
    /// the enclosing group, is recorded as one step of the enclosing
    /// revert, or is the newest step.
    fn close_group(&mut self) {
        let Some(Frame::Group(own)) = self.frames.pop() else {
            unreachable!("a group closes as the innermost frame");
        };
        if own.is_empty() {
            return;
        }
        match self.frames.last_mut() {
            Some(Frame::Group(outer)) => outer.extend(own),
            Some(Frame::Revert(revert)) => revert.recorded.push(own),
            None => self.push_step(own),
        }
    }

    /// Close the revert `id`, the innermost frame. Its remainder — the
    /// transactions it did not replay, oldest first, ending with an unlanded
    /// replay in progress, which the next undo retries first — then the
    /// steps recorded inside it, join the enclosing group (a failed group's
    /// rollback), or the stack. A discarded revert returns no remainder.
    fn close_revert(&mut self, id: ReplayId) {
        let Some(Frame::Revert(revert)) = self.frames.pop() else {
            unreachable!("a revert closes as the innermost frame");
        };
        debug_assert!(revert.id == id, "the revert closing is the innermost one");
        let Revert {
            remaining,
            in_progress,
            recorded,
            discarded,
            ..
        } = revert;
        let mut remainder: Vec<Transaction> = Vec::new();
        if !discarded {
            remainder.extend(remaining.into_iter().map(|pending| pending.transaction));
            // The replay's own handle is gone by the time its frame closes.
            if let Some(transaction) = in_progress.and_then(Rc::into_inner) {
                remainder.push(transaction);
            }
        }
        match self.frames.last_mut() {
            Some(Frame::Group(group)) => {
                group.extend(remainder);
                group.extend(recorded.into_iter().flatten());
            }
            Some(Frame::Revert(_)) => unreachable!("a revert opens only inside a group or with no frame open"),
            None => {
                if !remainder.is_empty() {
                    self.push_step(remainder);
                }
                for step in recorded {
                    self.push_step(step);
                }
            }
        }
    }

    /// Drop what an edit elsewhere, which touched each layer in `footprints`
    /// with its footprint, made stale. Undo replays newest first, so the newest
    /// transaction it overlaps goes with every older one, and the newer ones
    /// stay, through the whole history ([`frames`](Self::frames)). A revert
    /// replays nothing it dropped. A capture still in flight is of an edit
    /// made after it, and stays.
    fn invalidate(&mut self, footprints: &[(pcp::LayerId, Rc<sdf::Footprint>)]) {
        // TODO(perf): every foreign commit scans every recorded transaction; a
        // per-layer index of the steps touching each layer would skip the
        // layers no step touched.
        self.drop_stale(|transaction| transaction.overlaps(footprints));
    }

    /// Drop the newest transaction `stale` holds with every older one,
    /// newest first through the frames' units ([`frame_units`](Self::frame_units))
    /// and then the stack's steps. A step is atomic and goes whole; a unit of
    /// frames, which closes into one step, loses its stale transaction and
    /// the older ones.
    fn drop_stale(&mut self, stale: impl Fn(&Transaction) -> bool) {
        let units = self.frame_units();
        for (at, &unit) in units.iter().enumerate() {
            if let Some(newest) = self.unit(unit).into_iter().rposition(&stale) {
                self.drop_unit(unit, Some(newest));
                for &older in &units[at + 1..] {
                    self.drop_unit(older, None);
                }
                self.stack.clear();
                return;
            }
        }
        if let Some(newest) = self.stack.iter().rposition(|step| step.iter().any(&stale)) {
            self.stack.drain(..=newest);
        }
    }

    /// Drop the history on the layers in `layers`, which left the stage or
    /// were reloaded: an edit to a layer that left no longer reaches the
    /// journal, and a reload set a new baseline the history was not recorded
    /// against, so history touching one cannot be kept valid. A step is
    /// atomic, so one touching such a layer goes whole, and a step only on
    /// other layers stays. Frames that close into one step go whole the same
    /// way, and a revert whose remaining work touches one replays nothing
    /// more.
    ///
    /// What a dropped unit authored on the other layers stays authored, as an
    /// edit made elsewhere would: the newest older transaction overlapping it
    /// goes, with every one older still, by [`drop_stale`](Self::drop_stale)'s
    /// rule.
    fn depart(&mut self, layers: &HashSet<pcp::LayerId>) {
        let touches =
            |transaction: &Transaction| transaction.layers.iter().any(|inverse| layers.contains(&inverse.layer));
        let mut units = self.frame_units();
        units.extend((0..self.stack.len()).rev().map(Unit::Step));
        // The footprints the dropped units leave on the other layers.
        let mut kept: Vec<(pcp::LayerId, Rc<sdf::Footprint>)> = Vec::new();
        // What goes of each unit, newest first: all of it, or through a
        // transaction; the units after a cut go whole.
        let mut drops: Vec<(Unit, Option<usize>)> = Vec::new();
        for (at, &unit) in units.iter().enumerate() {
            let transactions = self.unit(unit);
            if transactions.iter().any(|transaction| touches(transaction)) {
                let inverses = transactions.iter().flat_map(|transaction| &transaction.layers);
                let others = inverses.filter(|inverse| !layers.contains(&inverse.layer));
                kept.extend(others.map(|inverse| (inverse.layer, Rc::clone(&inverse.footprint))));
                drops.push((unit, None));
            } else if let Some(newest) = transactions.iter().rposition(|transaction| transaction.overlaps(&kept)) {
                drops.push((unit, Some(newest)));
                drops.extend(units[at + 1..].iter().map(|&older| (older, None)));
                break;
            }
        }
        for (unit, through) in drops {
            self.drop_unit(unit, through);
        }
    }

    /// The frames' units of history, newest first ([`Unit`]). Every frame
    /// closes into the outermost one, so with a group outermost the frames are
    /// one unit; with a revert outermost (an undo), the frames above it are
    /// one unit, closing into one step it records, then come its recorded
    /// steps and its remaining work.
    fn frame_units(&self) -> Vec<Unit> {
        match self.frames.first() {
            None => Vec::new(),
            Some(Frame::Group(_)) => vec![Unit::Frames(0)],
            Some(Frame::Revert(revert)) => {
                let above = (self.frames.len() > 1).then_some(Unit::Frames(1));
                let recorded = (0..revert.recorded.len()).rev().map(Unit::Recorded);
                above.into_iter().chain(recorded).chain([Unit::Remaining]).collect()
            }
        }
    }

    /// The transactions `unit` holds, oldest first.
    fn unit(&self, unit: Unit) -> Vec<&Transaction> {
        match unit {
            Unit::Step(step) => self.stack[step].iter().collect(),
            Unit::Recorded(step) => match &self.frames[0] {
                Frame::Revert(revert) => revert.recorded[step].iter().collect(),
                Frame::Group(_) => unreachable!("a recorded step belongs to the outermost revert"),
            },
            Unit::Remaining => match &self.frames[0] {
                Frame::Revert(revert) => revert.work().collect(),
                Frame::Group(_) => unreachable!("remaining work belongs to the outermost revert"),
            },
            Unit::Frames(from) => self.frames[from..]
                .iter()
                .flat_map(|frame| -> Vec<&Transaction> {
                    match frame {
                        Frame::Group(transactions) => transactions.iter().collect(),
                        Frame::Revert(revert) => revert.work().chain(revert.recorded.iter().flatten()).collect(),
                    }
                })
                .collect(),
        }
    }

    /// Drop `unit`'s transactions through the one at `through`, oldest first,
    /// or all of them with `None`; a step goes whole. Dropping runs newest
    /// first, so an index a later call names is still in place.
    fn drop_unit(&mut self, unit: Unit, through: Option<usize>) {
        let mut left = through.map_or(usize::MAX, |at| at + 1);
        match unit {
            Unit::Step(step) => {
                self.stack.remove(step);
            }
            Unit::Recorded(step) => {
                if let Frame::Revert(revert) = &mut self.frames[0] {
                    revert.recorded.remove(step);
                }
            }
            Unit::Remaining => {
                if let Frame::Revert(revert) = &mut self.frames[0] {
                    // The replay in progress is the newest of the work.
                    if left <= revert.remaining.len() {
                        revert.remaining.drain(..left);
                    } else {
                        revert.clear_remaining();
                    }
                }
            }
            Unit::Frames(from) => {
                for frame in &mut self.frames[from..] {
                    left -= match frame {
                        Frame::Group(transactions) => {
                            let gone = left.min(transactions.len());
                            transactions.drain(..gone);
                            gone
                        }
                        Frame::Revert(revert) => revert.drain_front(left),
                    };
                }
            }
        }
    }
}

impl Revert {
    /// Open a revert of `transactions`, oldest first.
    fn new(transactions: Vec<Transaction>) -> Self {
        Self {
            id: ReplayId::next(),
            remaining: transactions
                .into_iter()
                .map(|transaction| Pending {
                    transaction,
                    protected: false,
                })
                .collect(),
            in_progress: None,
            recorded: Vec::new(),
            discarded: false,
        }
    }

    /// The revert's remaining work, oldest first: the transactions still to
    /// replay, then the replay in progress.
    fn work(&self) -> impl Iterator<Item = &Transaction> {
        self.remaining
            .iter()
            .map(|pending| &pending.transaction)
            .chain(self.in_progress.as_deref())
    }

    /// Drop the remaining work, the replay in progress included.
    fn clear_remaining(&mut self) {
        self.remaining.clear();
        self.in_progress = None;
    }

    /// Drop the first `n` transactions of the work, then of the steps
    /// recorded inside the revert, oldest first, all of it when `n` reaches
    /// past; returns how many went.
    fn drain_front(&mut self, n: usize) -> usize {
        let work = self.remaining.len() + usize::from(self.in_progress.is_some());
        if n <= self.remaining.len() {
            self.remaining.drain(..n);
            return n;
        }
        self.clear_remaining();
        let mut left = n - work.min(n);
        let mut gone = work.min(n);
        while left > 0 && !self.recorded.is_empty() {
            let step = &mut self.recorded[0];
            let take = left.min(step.len());
            step.drain(..take);
            if step.is_empty() {
                self.recorded.remove(0);
            }
            left -= take;
            gone += take;
        }
        gone
    }

    /// Take the newest remaining transaction to replay, unless it is
    /// protected or none is left.
    fn select(&mut self) -> Option<Rc<Transaction>> {
        let pending = self.remaining.pop_if(|pending| !pending.protected)?;
        let transaction = Rc::new(pending.transaction);
        self.in_progress = Some(Rc::clone(&transaction));
        Some(transaction)
    }
}

/// A unit of history: what a step-atomic rule keeps or drops whole.
#[derive(Clone, Copy)]
enum Unit {
    /// A step on the stack, by index.
    Step(usize),
    /// A step the outermost frame, a revert, recorded, by index.
    Recorded(usize),
    /// The outermost frame's remaining work, that frame being a revert.
    Remaining,
    /// The frames from this one in, which close into one step.
    Frames(usize),
}

/// A revert in progress ([`Revert`]) until dropped, which closes it
/// ([`Journal::close_revert`]) on every way out of the revert, a panic
/// included, doing bookkeeping only.
struct RevertFrame<'a> {
    journal: &'a RefCell<Journal>,
    id: ReplayId,
}

impl<'a> RevertFrame<'a> {
    /// Open a revert of `transactions`, oldest first, as the innermost frame.
    fn open(journal: &'a RefCell<Journal>, transactions: Vec<Transaction>) -> Self {
        let revert = Revert::new(transactions);
        let id = revert.id;
        journal.borrow_mut().frames.push(Frame::Revert(revert));
        Self { journal, id }
    }
}

impl Drop for RevertFrame<'_> {
    fn drop(&mut self) {
        self.journal.borrow_mut().close_revert(self.id);
    }
}

/// Closes a [`group`](UndoStage::group) when dropped, as its edit returns or
/// unwinds ([`Journal::close_group`]).
struct CloseGroup<'a>(&'a RefCell<Journal>);

impl Drop for CloseGroup<'_> {
    fn drop(&mut self) {
        // Every transaction the group committed has reconciled: a stage edit
        // reconciles as its commit is delivered.
        self.0.borrow_mut().close_group();
    }
}

/// The observer an [`UndoStage`] installs: it captures each layer's inverse
/// as the layer commits, and seals, drops or invalidates as each transaction
/// reconciles.
struct UndoRecorder {
    journal: Rc<RefCell<Journal>>,
}

impl TxnObserver for UndoRecorder {
    fn held_layers(&self, layers: &mut HashSet<pcp::LayerId>) {
        self.journal.borrow().hold(layers);
    }

    fn capture(&self, _stage: &Stage, change: &PendingChange<'_>, layer: pcp::LayerId) {
        // Only the stage's own edits are undoable: another editor's edit to a
        // layer the stage holds, or one made through a layer handle, is not
        // this stage's to revert.
        if !change.is_own() {
            return;
        }
        let mut journal = self.journal.borrow_mut();
        // A replay of this journal's own revert is not recorded.
        if journal.is_replay(change.replay) {
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

    fn departed(&self, layers: &HashSet<pcp::LayerId>) {
        self.journal.borrow_mut().depart(layers);
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
        if journal.is_replay(change.replay) {
            return;
        }
        // An own edit protects what a revert still to replay overlaps, even
        // one whose inverse was not captured.
        journal.protect(footprints);
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
        journal.seal(transaction);
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
    use std::cell::{Cell, Ref};
    use std::fs;
    use std::panic::{self, AssertUnwindSafe};

    use super::*;
    use crate::usd::stage::tests::recorder_counts;
    use crate::usd::{ApplyMode, Diff, Edit, EditTarget, ListPosition, StageSink};
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

    /// A layer listing a prim's children in another order undoes to the order
    /// it replaced.
    #[test]
    fn undo_reorder_children() -> Result<()> {
        let stage = UndoStage::from(in_memory_stage()?);
        stage.define_prim("/W/a")?;
        stage.define_prim("/W/b")?;
        let root = stage.root_layer().identifier().to_string();
        let diff = Diff {
            edits: vec![Edit::SetField {
                path: sdf::path("/W")?,
                spec_type: sdf::SpecType::Prim,
                field: "primChildren".into(),
                value: vt::Value::TokenVec(vec!["b".into(), "a".into()]),
            }],
            mapping: None,
        };
        stage.apply_diff(&diff, ApplyMode::ExactLayer(&root))?;
        assert_eq!(stage.prim("/W")?.child_names()?, ["b", "a"]);

        assert!(stage.undo()?);
        assert_eq!(stage.prim("/W")?.child_names()?, ["a", "b"]);
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
        stage.add_sink(Panics(Cell::new(false)))?;
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
        })?;
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
        })?;
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
        })?;
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
    /// `double x = 0` and `/Q` with `double z = 0`: the first wrapped for
    /// undo.
    fn shared_pair() -> Result<(tempfile::TempDir, UndoStage, Stage)> {
        shared("def \"P\" {\n    double x = 0\n}\ndef \"Q\" {\n    double z = 0\n}\n")
    }

    /// An undo stage `A` and a plain stage `B` over one root layer holding
    /// `body`, on one registry, so B's edits reach A as edits made elsewhere.
    fn shared(body: &str) -> Result<(tempfile::TempDir, UndoStage, Stage)> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("root.usda");
        fs::write(&path, format!("#usda 1.0\n{body}"))?;
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
        })?;
        let stage = Stage::clone(&a);
        slot.replace(Some(a));
        stage.attribute("/P.x")?.set(1.0)?;
        stage.remove_sink(sink)?;
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
        })?;
        armed.set(true);
        assert!(a.undo()?);
        a.remove_sink(sink)?;
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
        })?;
        let stage = Stage::clone(&undo);
        slot.replace(Some(undo));
        armed.set(true);
        let undone = slot.borrow().as_ref().expect("the wrapper is set").undo()?;
        assert!(undone);
        stage.remove_sink(sink)?;
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

    /// An undo stage over `/A`, `/B`, `/C` and `/O`, each with `x = 0` (`/A`
    /// with `w = 0` too), recording from that state on.
    fn scene() -> Result<UndoStage> {
        scene_with(DEFAULT_CAPACITY)
    }

    /// [`scene`], keeping at most `capacity` undo steps.
    fn scene_with(capacity: usize) -> Result<UndoStage> {
        let undo = UndoStage::with_capacity(in_memory_stage()?, capacity);
        for prim in ["/A", "/B", "/C", "/O"] {
            undo.define_prim(prim)?;
            undo.create_attribute(format!("{prim}.x").as_str(), "double")?
                .set(0.0)?;
        }
        undo.create_attribute("/A.w", "double")?.set(0.0)?;
        undo.reset();
        Ok(undo)
    }

    /// The value of `attribute` as `stage` composes it.
    fn value(stage: &Stage, attribute: &str) -> Result<Option<f64>> {
        stage.attribute(attribute)?.get::<f64>()
    }

    /// Set `attribute` to `to` on `stage`.
    fn set(stage: &Stage, attribute: &str, to: f64) -> Result<()> {
        stage.attribute(attribute)?.set(to)?;
        Ok(())
    }

    /// One step of three transactions setting `/A.x`, `/B.x` and `/C.x` to 1,
    /// so an undo replays `/C.x` first and `/A.x` last.
    fn three_step(undo: &UndoStage) -> Result<()> {
        undo.group(|undo| {
            set(undo, "/A.x", 1.0)?;
            set(undo, "/B.x", 1.0)?;
            set(undo, "/C.x", 1.0)
        })
    }

    /// The undo stage a hook acts on. The test takes it back at the end,
    /// which breaks the cycle through the sink.
    type Slot = Rc<RefCell<Option<UndoStage>>>;

    /// Runs `act` with the undo stage in `slot` on the `nth` own commit the
    /// stage delivers once armed, counting from 1 (`countdown` arms it).
    struct OnCommit {
        slot: Slot,
        countdown: Rc<Cell<u32>>,
        act: Box<dyn Fn(&UndoStage)>,
    }

    impl StageSink for OnCommit {
        fn after_commit(&self, _: &Stage, change: &CommittedChange<'_>) {
            if !change.is_own() {
                return;
            }
            match self.countdown.get() {
                0 => {}
                1 => {
                    self.countdown.set(0);
                    if let Some(undo) = self.slot.borrow().as_ref() {
                        (self.act)(undo);
                    }
                }
                n => self.countdown.set(n - 1),
            }
        }
    }

    /// Installs `act` on `undo` ([`OnCommit`]), returning the slot holding
    /// `undo` and the countdown arming the act.
    fn hooked(undo: UndoStage, act: impl Fn(&UndoStage) + 'static) -> Result<(Slot, Rc<Cell<u32>>)> {
        let slot: Slot = Rc::default();
        let countdown = Rc::new(Cell::new(0));
        undo.add_sink(OnCommit {
            slot: Rc::clone(&slot),
            countdown: Rc::clone(&countdown),
            act: Box::new(act),
        })?;
        slot.replace(Some(undo));
        Ok((slot, countdown))
    }

    /// The undo stage in `slot`.
    fn held(slot: &Slot) -> Ref<'_, UndoStage> {
        Ref::map(slot.borrow(), |undo| undo.as_ref().expect("the slot holds the stage"))
    }

    /// Records the attribute each own commit changes, in order.
    struct Order(Rc<RefCell<Vec<String>>>);

    impl StageSink for Order {
        fn after_commit(&self, _: &Stage, change: &CommittedChange<'_>) {
            if change.is_own()
                && let Some(path) = change.changed_info_only.first()
            {
                self.0.borrow_mut().push(path.as_str().to_owned());
            }
        }
    }

    /// An own edit a sink makes while a step replays is recorded as a newer
    /// step and survives: the undo depth is what it was, one step gone and
    /// the sink's come, and undoing again reverts the sink's edit.
    #[test]
    fn sink_edit_recorded() -> Result<()> {
        let undo = scene()?;
        set(&undo, "/A.x", 1.0)?;
        let depth = undo.undo_depth();
        let (slot, countdown) = hooked(undo, |undo| set(undo, "/O.x", 9.0).expect("the sink's edit"))?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(0.0));
            assert_eq!(value(&undo, "/O.x")?, Some(9.0), "the sink's edit survives");
            assert_eq!(undo.undo_depth(), depth);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/O.x")?, Some(0.0), "and is undoable");
        }
        slot.take();
        Ok(())
    }

    /// A sink's edit overlapping a transaction not yet replayed stops the
    /// revert before it: the sink's value stays, undoing again reverts the
    /// sink's edit, and once more the rest of the step.
    #[test]
    fn sink_edit_stops_revert() -> Result<()> {
        let undo = scene()?;
        undo.group(|undo| {
            set(undo, "/A.x", 1.0)?;
            set(undo, "/B.x", 2.0)
        })?;
        let (slot, countdown) = hooked(undo, |undo| set(undo, "/A.x", 5.0).expect("the sink's edit"))?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/B.x")?, Some(0.0), "the newer transaction reverted");
            assert_eq!(
                value(&undo, "/A.x")?,
                Some(5.0),
                "the older one was not replayed over it"
            );
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(1.0), "the sink's edit reverted first");
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(0.0), "then the rest of the step");
            assert!(!undo.can_undo());
        }
        slot.take();
        Ok(())
    }

    /// A group a sink runs while a step replays is one step afterwards.
    #[test]
    fn callback_group_one_step() -> Result<()> {
        let undo = scene()?;
        set(&undo, "/A.x", 1.0)?;
        let (slot, countdown) = hooked(undo, |undo| {
            undo.group(|undo| {
                set(undo, "/B.x", 1.0)?;
                set(undo, "/C.x", 1.0)
            })
            .expect("the sink's group");
        })?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(undo.undo_depth(), 1, "the sink's group is one step");
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/B.x")?, Some(0.0));
            assert_eq!(value(&undo, "/C.x")?, Some(0.0));
        }
        slot.take();
        Ok(())
    }

    /// A failed group a sink runs while a step replays rolls back its own
    /// edits, and the undo finishes.
    #[test]
    fn callback_group_rolls_back() -> Result<()> {
        let undo = scene()?;
        set(&undo, "/A.x", 1.0)?;
        let (slot, countdown) = hooked(undo, |undo| {
            let failed = undo.group(|undo| -> Result<()> {
                set(undo, "/B.x", 1.0)?;
                Err(Error::UnresolvedAsset("/Rolled".to_owned()))
            });
            assert!(failed.is_err());
        })?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(0.0), "the undo finished");
            assert_eq!(value(&undo, "/B.x")?, Some(0.0), "the group rolled back");
            assert!(!undo.can_undo());
        }
        slot.take();
        Ok(())
    }

    /// A failed group a sink runs while a step replays, whose edit overlapped
    /// the revert's work not yet replayed, rolls its edit back, and the outer
    /// revert stopped before that work all the same: it stays undoable.
    #[test]
    fn nested_rollback_interrupts() -> Result<()> {
        let undo = scene()?;
        undo.group(|undo| {
            set(undo, "/A.x", 1.0)?;
            set(undo, "/B.x", 2.0)
        })?;
        let (slot, countdown) = hooked(undo, |undo| {
            let failed = undo.group(|undo| -> Result<()> {
                set(undo, "/A.x", 5.0)?;
                Err(Error::UnresolvedAsset("/Rolled".to_owned()))
            });
            assert!(failed.is_err());
        })?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/B.x")?, Some(0.0));
            assert_eq!(value(&undo, "/A.x")?, Some(1.0), "rolled back, and not replayed");
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(0.0), "the remainder is undoable");
        }
        slot.take();
        Ok(())
    }

    /// A foreign edit overlapping a sink's edit recorded during the same
    /// revert drops the sink's step, so no later undo overwrites it.
    #[test]
    fn foreign_drops_recorded() -> Result<()> {
        let (_dir, a, b) = shared_pair()?;
        a.attribute("/P.x")?.set(1.0)?;
        let (slot, countdown) = hooked(a, move |a| {
            set(a, "/Q.z", 3.0).expect("the sink's edit");
            set(&b, "/Q.z", 4.0).expect("the foreign edit");
        })?;
        countdown.set(1);
        {
            let a = held(&slot);
            assert!(a.undo()?);
            assert_eq!(x(&a)?, Some(0.0));
            assert_eq!(value(&a, "/Q.z")?, Some(4.0));
            assert!(!a.can_undo(), "the sink's step went stale");
        }
        slot.take();
        Ok(())
    }

    /// A sink that records an edit and then panics while a step replays
    /// leaves the edit undoable, no revert open, and recording working.
    #[test]
    fn panic_keeps_recorded() -> Result<()> {
        let undo = scene()?;
        set(&undo, "/A.x", 1.0)?;
        let (slot, countdown) = hooked(undo, |undo| {
            set(undo, "/O.x", 9.0).expect("the sink's edit");
            panic!("the sink failed");
        })?;
        countdown.set(1);
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| held(&slot).undo()));
        assert!(unwound.is_err());
        {
            let undo = held(&slot);
            assert_eq!(value(&undo, "/A.x")?, Some(0.0), "the replay landed");
            assert_eq!(undo.undo_depth(), 1, "the sink's edit is recorded");
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/O.x")?, Some(0.0));
            set(&undo, "/B.x", 1.0)?;
            assert!(undo.undo()?, "recording works");
        }
        slot.take();
        Ok(())
    }

    /// Panics in the `nth` own `before_commit` once armed.
    struct PanicBefore(Rc<Cell<u32>>);

    impl StageSink for PanicBefore {
        fn before_commit(&self, _: &Stage, change: &PendingChange<'_>) {
            if !change.is_own() {
                return;
            }
            match self.0.get() {
                0 => {}
                1 => {
                    self.0.set(0);
                    panic!("the sink failed before the commit");
                }
                n => self.0.set(n - 1),
            }
        }
    }

    /// A replay a `before_commit` panic stops never landed: it stays
    /// undoable, retried first.
    #[test]
    fn panic_before_commit() -> Result<()> {
        let undo = scene()?;
        three_step(&undo)?;
        let armed = Rc::new(Cell::new(0));
        undo.add_sink(PanicBefore(Rc::clone(&armed)))?;
        let order = Rc::new(RefCell::new(Vec::new()));
        undo.add_sink(Order(Rc::clone(&order)))?;
        armed.set(2);
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| undo.undo()));
        assert!(unwound.is_err());
        assert_eq!(value(&undo, "/C.x")?, Some(0.0), "the first replay landed");
        assert_eq!(value(&undo, "/B.x")?, Some(1.0), "the second did not");
        order.borrow_mut().clear();
        assert!(undo.undo()?);
        assert_eq!(*order.borrow(), ["/B.x", "/A.x"], "the panicked one first");
        assert!(!undo.can_undo());
        Ok(())
    }

    /// A replay an `after_commit` panic interrupts landed: it is done, and
    /// only the older work stays undoable.
    #[test]
    fn panic_after_commit() -> Result<()> {
        let undo = scene()?;
        three_step(&undo)?;
        let (slot, countdown) = hooked(undo, |_| panic!("the sink failed after the commit"))?;
        // The step's last replay, `/A.x`'s.
        countdown.set(3);
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| held(&slot).undo()));
        assert!(unwound.is_err());
        {
            let undo = held(&slot);
            assert_eq!(value(&undo, "/A.x")?, Some(0.0), "the last replay landed");
            assert_eq!(value(&undo, "/B.x")?, Some(0.0));
            assert_eq!(value(&undo, "/C.x")?, Some(0.0));
            assert!(!undo.can_undo(), "the landed replay does not return to history");
        }
        slot.take();
        Ok(())
    }

    /// Vetoes a commit touching `/B.x` while armed.
    struct VetoB(Rc<Cell<bool>>);

    impl sdf::LayerSink for VetoB {
        fn before_commit(&self, change: &sdf::PendingLayerChange<'_>) -> Result<(), sdf::sink::Error> {
            let touches = change
                .change_list
                .entries()
                .iter()
                .any(|(path, _)| path.as_str() == "/B.x");
            match self.0.get() && touches {
                true => Err(sdf::sink::Error::new("vetoed")),
                false => Ok(()),
            }
        }
    }

    /// A vetoed replay returns the error with the newer work reverted; the
    /// rest stays undoable oldest first, the vetoed one retried first, under
    /// what a sink recorded during the failed undo.
    #[test]
    fn veto_keeps_order() -> Result<()> {
        let undo = scene()?;
        three_step(&undo)?;
        let root = undo.root_layer().identifier().to_string();
        let veto = Rc::new(Cell::new(true));
        let vetoing = undo
            .layer_handle(&root)
            .expect("root layer")
            .add_sink(VetoB(Rc::clone(&veto)))?;
        let order = Rc::new(RefCell::new(Vec::new()));
        undo.add_sink(Order(Rc::clone(&order)))?;
        let (slot, countdown) = hooked(undo, |undo| set(undo, "/O.x", 9.0).expect("the sink's edit"))?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo().is_err());
            assert_eq!(value(&undo, "/C.x")?, Some(0.0));
            assert_eq!(value(&undo, "/B.x")?, Some(1.0), "vetoed");
            assert_eq!(undo.undo_depth(), 2);
            veto.set(false);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/O.x")?, Some(0.0), "the sink's step is newest");
            order.borrow_mut().clear();
            assert!(undo.undo()?);
            assert_eq!(*order.borrow(), ["/B.x", "/A.x"], "the vetoed one first");
            undo.layer_handle(&root).expect("root layer").remove_sink(vetoing)?;
        }
        slot.take();
        Ok(())
    }

    /// A foreign edit that drops a protected transaction leaves the newer,
    /// unprotected ones to replay.
    #[test]
    fn foreign_prefix_keeps_marks() -> Result<()> {
        let (_dir, a, b) = shared(
            "def \"A\" {\n    double x = 0\n    double w = 0\n}\ndef \"B\" {\n    double x = 0\n}\n\
             def \"C\" {\n    double x = 0\n}\n",
        )?;
        let root = a.root_layer().identifier().to_string();
        a.group(|a| {
            // One transaction setting `/A.x` and `/A.w`.
            a.edit_layer(&root, |e| {
                e.data_mut()
                    .set_field(&sdf::path("/A.x")?, "default", vt::Value::Double(1.0));
                e.data_mut()
                    .set_field(&sdf::path("/A.w")?, "default", vt::Value::Double(1.0));
                Ok(())
            })?;
            set(a, "/B.x", 1.0)?;
            set(a, "/C.x", 1.0)
        })?;
        let (slot, countdown) = hooked(a, move |a| {
            set(a, "/A.x", 5.0).expect("the sink's edit protects the oldest");
            set(&b, "/A.w", 7.0).expect("the foreign edit drops it");
        })?;
        countdown.set(1);
        {
            let a = held(&slot);
            assert!(a.undo()?);
            assert_eq!(value(&a, "/C.x")?, Some(0.0));
            assert_eq!(value(&a, "/B.x")?, Some(0.0), "the newer work still replayed");
            assert_eq!(value(&a, "/A.w")?, Some(7.0));
            assert_eq!(value(&a, "/A.x")?, Some(5.0));
        }
        slot.take();
        Ok(())
    }

    /// A foreign edit committed as one replay is delivered, overlapping the
    /// transaction about to be chosen, makes it stale before it is chosen:
    /// neither it nor anything older is replayed over the foreign value.
    #[test]
    fn pending_foreign_before_replay() -> Result<()> {
        let (_dir, a, b) = shared(
            "def \"A\" {\n    double x = 0\n}\ndef \"B\" {\n    double x = 0\n}\ndef \"C\" {\n    double x = 0\n}\n",
        )?;
        three_step(&a)?;
        let (slot, countdown) = hooked(a, move |_| {
            set(&b, "/B.x", 7.0).expect("the foreign edit");
        })?;
        countdown.set(1);
        {
            let a = held(&slot);
            assert!(a.undo()?);
            assert_eq!(value(&a, "/C.x")?, Some(0.0));
            assert_eq!(value(&a, "/B.x")?, Some(7.0), "the stale transaction was not replayed");
            assert_eq!(value(&a, "/A.x")?, Some(1.0), "nor anything older");
            assert!(!a.can_undo());
        }
        slot.take();
        Ok(())
    }

    /// A reset during a revert, after a sink's edit protected older work,
    /// replays nothing protected and returns nothing of the remainder.
    #[test]
    fn reset_keeps_boundary() -> Result<()> {
        let undo = scene()?;
        three_step(&undo)?;
        let (slot, countdown) = hooked(undo, |undo| {
            set(undo, "/A.x", 5.0).expect("the sink's edit");
            undo.reset();
        })?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/B.x")?, Some(0.0), "unprotected work replays to the end");
            assert_eq!(value(&undo, "/A.x")?, Some(5.0), "protected work is not replayed");
            assert!(!undo.can_undo(), "the reset discarded the remainder");
        }
        slot.take();
        Ok(())
    }

    /// Finalizing a remainder and two recorded steps keeps the newest ones
    /// the capacity allows.
    #[test]
    fn capacity_on_finalize() -> Result<()> {
        let undo = scene_with(2)?;
        three_step(&undo)?;
        let (slot, countdown) = hooked(undo, |undo| {
            set(undo, "/A.x", 5.0).expect("protects the oldest");
            set(undo, "/O.x", 9.0).expect("a second step");
        })?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(undo.undo_depth(), 2);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/O.x")?, Some(0.0));
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(1.0));
            assert!(!undo.can_undo(), "the remainder was evicted");
        }
        slot.take();
        Ok(())
    }

    /// A reset during a revert drops its remainder; an edit recorded after
    /// the reset is kept.
    #[test]
    fn reset_mid_undo_records() -> Result<()> {
        let undo = scene()?;
        undo.group(|undo| {
            set(undo, "/A.x", 1.0)?;
            set(undo, "/B.x", 1.0)
        })?;
        let (slot, countdown) = hooked(undo, |undo| {
            undo.reset();
            set(undo, "/A.x", 5.0).expect("the sink's edit after the reset");
        })?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(5.0));
            assert_eq!(undo.undo_depth(), 1, "only the edit after the reset");
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(1.0));
        }
        slot.take();
        Ok(())
    }

    /// An undo a sink asks for while a step replays is refused and changes
    /// nothing: the older step stays undoable after the outer undo.
    #[test]
    fn nested_undo_refused() -> Result<()> {
        let undo = scene()?;
        set(&undo, "/A.x", 1.0)?;
        set(&undo, "/B.x", 1.0)?;
        let refused = Rc::new(Cell::new(None));
        let seen = Rc::clone(&refused);
        let (slot, countdown) = hooked(undo, move |undo| seen.set(Some(undo.undo().expect("the nested undo"))))?;
        countdown.set(1);
        {
            let undo = held(&slot);
            assert!(undo.undo()?);
            assert_eq!(refused.get(), Some(false), "the nested undo was refused");
            assert_eq!(value(&undo, "/B.x")?, Some(0.0));
            assert_eq!(value(&undo, "/A.x")?, Some(1.0));
            assert!(undo.undo()?);
            assert_eq!(value(&undo, "/A.x")?, Some(0.0), "the older step was kept");
        }
        slot.take();
        Ok(())
    }

    /// Two undo stages on one stage: one's undo replays are own edits to the
    /// other, which records them, and neither suppresses the other's.
    #[test]
    fn two_recorders() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/A")?;
        stage.create_attribute("/A.x", "double")?.set(0.0)?;
        let a = UndoStage::from(stage.clone());
        let b = UndoStage::from(stage.clone());
        set(&a, "/A.x", 1.0)?;
        assert_eq!(b.undo_depth(), 1);
        assert!(a.undo()?);
        assert_eq!(value(&a, "/A.x")?, Some(0.0));
        assert_eq!(b.undo_depth(), 2, "the other recorder records the replay");
        assert!(b.undo()?);
        assert_eq!(value(&b, "/A.x")?, Some(1.0), "and can undo the undo");
        Ok(())
    }

    /// A replay stage still logs the replays an undo makes.
    #[test]
    fn replay_log_unchanged() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/A")?;
        stage.create_attribute("/A.x", "double")?.set(0.0)?;
        let replay = ReplayStage::from(stage.clone());
        let undo = UndoStage::from(stage);
        set(&undo, "/A.x", 1.0)?;
        assert!(undo.undo()?);
        assert_eq!(replay.diff().len(), 2, "the edit and its undo");
        Ok(())
    }
}
