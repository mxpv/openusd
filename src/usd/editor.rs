//! Stage-level namespace editing, the Rust port of C++ `UsdNamespaceEditor`
//! (`pxr/usd/usd/namespaceEditor.h`).
//!
//! [`NamespaceEditor`] renames, reparents, and deletes prims and properties on
//! a composed [`Stage`], fixing up everything that points at the moved or
//! deleted objects — relationship targets, attribute connections, and internal
//! references / inherits / specializes — and authoring relocates when an
//! object's opinions arrive across a reference or payload arc.
//!
//! Unlike C++, which applies one edit at a time, edits batch: each staging call
//! appends to an ordered queue and [`apply`](NamespaceEditor::apply) commits the
//! whole batch. The batch is sequential — a later edit sees the result of the
//! earlier ones, so `move /A → /B` then `delete /B/Child` resolves naturally.
//! This falls out of the atomic copy-on-write staging: structural ops stage in
//! each layer's overlay, whose reads already reflect the prior edits, and all
//! layers commit together once the batch authors cleanly.
//!
//! The current edit target selects one of two authoring shapes. An identity
//! target on the local root layer stack authors across the whole stack, as C++
//! does: it moves local specs directly and synthesizes `layerRelocates` for
//! content that arrives across a reference or payload arc. A variant or
//! cross-arc edit target authors into the single layer it writes to, in that
//! target's namespace — each edit path mapped through the target — and performs
//! only direct moves and deletes of content the target reaches: a variant move
//! lands at the `{set=sel}` paths, a cross-arc move edits the shared source
//! layer. A mapped target authors no relocates, so it edits only a source the
//! target layer solely contributes: a source that also composes from another
//! layer or a deeper arc would survive the single-layer edit and is rejected as
//! [`RequiresRelocate`](NamespaceEditError::RequiresRelocate), and a move onto a
//! destination already occupied on the composed stage collides
//! ([`DestinationExists`](NamespaceEditError::DestinationExists)) rather than
//! silently merging.
//!
//! In both shapes the structural move is [`copy_spec_within`](crate::sdf::copy_spec_within)
//! plus [`Layer::remove_spec`](crate::sdf::Layer::remove_spec), and the fixup
//! remaps embedded paths in place through
//! [`Value::filter_map_paths`](crate::sdf::Value::filter_map_paths), preserving
//! list-op structure rather than flattening opinions. The local-stack fixup
//! remaps in stage namespace; the mapped fixup lifts each path to stage
//! namespace, follows the batch's moves, then maps it back into the target
//! layer's namespace.

use std::collections::{HashMap, HashSet};

use super::{EditTarget, Prim, Stage, StageAuthoringError};
use crate::{pcp, sdf};

/// Batches namespace edits — prim/property renames, reparents, and deletes —
/// and applies them to a [`Stage`] with full target/connection/reference fixup.
/// Mirrors C++ `UsdNamespaceEditor`.
///
/// Stage an edit with one of the staging methods, then [`apply`](Self::apply)
/// (or check feasibility first with [`can_apply`](Self::can_apply)). A
/// successful [`apply`](Self::apply) clears the queue.
pub struct NamespaceEditor {
    stage: Stage,
    edits: Vec<NamespaceEdit>,
}

/// One staged namespace edit. Paths are in composed stage namespace and are
/// interpreted after the edits queued before them. `kind` is fixed by the
/// staging method (a prim or a property edit) and the paths are validated
/// against it, so a prim path passed to a property method is rejected.
enum NamespaceEdit {
    /// Remove the object (prim or property) at `path` and its namespace
    /// descendants.
    Delete { path: sdf::Path, kind: ObjectKind },
    /// Move the object at `src` (and its descendants) to `dst`.
    Move {
        src: sdf::Path,
        dst: sdf::Path,
        kind: ObjectKind,
    },
}

/// Whether a staged edit targets a prim or a property. The staging method fixes
/// this, and each edit path is checked to be of the matching kind.
#[derive(Clone, Copy, PartialEq)]
enum ObjectKind {
    Prim,
    Property,
}

impl ObjectKind {
    /// Whether `path` is of this kind — a property path for `Property`, a
    /// non-property (prim) path for `Prim`.
    fn matches(self, path: &sdf::Path) -> bool {
        path.is_property_path() == (self == ObjectKind::Property)
    }
}

impl NamespaceEdit {
    /// The path the edit reads from — the move source or the deletion target.
    fn source(&self) -> &sdf::Path {
        match self {
            NamespaceEdit::Delete { path, .. } => path,
            NamespaceEdit::Move { src, .. } => src,
        }
    }
}

/// Errors raised while staging, validating, or applying a namespace edit.
#[derive(Debug, thiserror::Error)]
pub enum NamespaceEditError {
    /// [`apply`](NamespaceEditor::apply) was called with no edits staged.
    #[error("no namespace edits staged")]
    NoEdits,

    /// A source path is not an absolute prim or property path.
    #[error("source path {0} is not an absolute prim or property path")]
    InvalidSource(sdf::Path),

    /// A destination path is not a valid absolute object path.
    #[error("destination path {0} is not a valid absolute object path")]
    InvalidDestination(sdf::Path),

    /// An edit targets the pseudo-root, which cannot be renamed or deleted.
    #[error("cannot namespace-edit the pseudo-root")]
    PseudoRoot,

    /// Nothing is composed at a source path (accounting for the edits queued
    /// before it).
    #[error("nothing composed at the source path {0}")]
    SourceNotFound(sdf::Path),

    /// An object already exists at a destination path.
    #[error("an object already exists at the destination {0}")]
    DestinationExists(sdf::Path),

    /// The batch cannot be expressed as a valid relocate set: deleting a
    /// cross-arc prim would orphan a descendant an earlier edit relocated out of
    /// it, or the synthesized relocates violate Pcp's structural/conflict rules.
    /// USD relocates cannot represent the requested namespace, so the batch is
    /// rejected rather than authored as relocates Pcp would silently drop.
    #[error("the requested edits cannot be represented as valid relocates (at {0})")]
    UnrepresentableRelocateBatch(sdf::Path),

    /// A destination is the source itself or a descendant of it, so the move
    /// would nest a subtree inside itself.
    #[error("destination {dst} is the source or a descendant of {src}")]
    DestinationUnderSource {
        /// The move's source path.
        src: sdf::Path,
        /// The move's destination path.
        dst: sdf::Path,
    },

    /// An edit path is the wrong namespace kind for the operation — a prim path
    /// passed to a property edit, or a property path to a prim edit.
    #[error("path is the wrong namespace kind for this edit (prim vs property)")]
    KindMismatch,

    /// An edit against a mapped (variant or cross-arc) edit target would need a
    /// relocate to express: the source composes on the stage but has no spec
    /// reachable through the target, so it arrives across a deeper arc and
    /// cannot be moved or deleted directly. A mapped target performs only direct
    /// moves and deletes in v1; synthesizing relocates through a mapped target
    /// is future work, and this is the seam it fills.
    #[error("the edit at {0} would need a relocate the current edit target cannot author")]
    RequiresRelocate(sdf::Path),

    /// A composed-stage query needed to validate or apply an edit failed.
    #[error(transparent)]
    Composition(#[from] anyhow::Error),

    /// Authoring the edit onto a layer failed.
    #[error(transparent)]
    Stage(#[from] StageAuthoringError),
}

impl From<sdf::sink::Error> for NamespaceEditError {
    fn from(error: sdf::sink::Error) -> Self {
        NamespaceEditError::Stage(StageAuthoringError::Rejected(error))
    }
}

impl NamespaceEditor {
    /// Create an editor with an empty edit queue targeting `stage`.
    pub fn new(stage: &Stage) -> Self {
        Self {
            stage: stage.clone(),
            edits: Vec::new(),
        }
    }

    /// Stage a move of the prim at `old` to `new`. Mirrors C++
    /// `MovePrimAtPath`.
    pub fn move_prim(&mut self, old: impl Into<sdf::Path>, new: impl Into<sdf::Path>) -> &mut Self {
        self.push_move(old, new, ObjectKind::Prim)
    }

    /// Stage a move of the property at `old` to `new`. Mirrors C++
    /// `MovePropertyAtPath`.
    pub fn move_property(&mut self, old: impl Into<sdf::Path>, new: impl Into<sdf::Path>) -> &mut Self {
        self.push_move(old, new, ObjectKind::Property)
    }

    /// Stage a deletion of the prim at `path`. Mirrors C++ `DeletePrimAtPath`.
    pub fn delete_prim(&mut self, path: impl Into<sdf::Path>) -> &mut Self {
        self.push_delete(path, ObjectKind::Prim)
    }

    /// Stage a deletion of the property at `path`. Mirrors C++
    /// `DeletePropertyAtPath`.
    pub fn delete_property(&mut self, path: impl Into<sdf::Path>) -> &mut Self {
        self.push_delete(path, ObjectKind::Property)
    }

    fn push_move(&mut self, old: impl Into<sdf::Path>, new: impl Into<sdf::Path>, kind: ObjectKind) -> &mut Self {
        self.edits.push(NamespaceEdit::Move {
            src: old.into(),
            dst: new.into(),
            kind,
        });
        self
    }

    fn push_delete(&mut self, path: impl Into<sdf::Path>, kind: ObjectKind) -> &mut Self {
        self.edits.push(NamespaceEdit::Delete {
            path: path.into(),
            kind,
        });
        self
    }

    /// Stage a rename of `prim` to the sibling name `new_name`. Mirrors C++
    /// `RenamePrim`.
    pub fn rename_prim(&mut self, prim: &Prim, new_name: &str) -> Result<&mut Self, NamespaceEditError> {
        let src = prim.path().clone();
        let parent = src.parent().ok_or(NamespaceEditError::PseudoRoot)?;
        let dst = parent
            .append_path(new_name)
            .map_err(|_| NamespaceEditError::InvalidDestination(src.clone()))?;
        Ok(self.move_prim(src, dst))
    }

    /// Stage a reparent of `prim` under `new_parent`, keeping its name. Mirrors
    /// C++ `ReparentPrim`.
    pub fn reparent_prim(&mut self, prim: &Prim, new_parent: &Prim) -> Result<&mut Self, NamespaceEditError> {
        let name = prim.path().name().ok_or(NamespaceEditError::PseudoRoot)?.to_owned();
        self.reparent_prim_with_name(prim, new_parent, &name)
    }

    /// Stage a reparent of `prim` under `new_parent`, renaming it to `new_name`.
    /// Mirrors C++ `ReparentPrim` with a new name.
    pub fn reparent_prim_with_name(
        &mut self,
        prim: &Prim,
        new_parent: &Prim,
        new_name: &str,
    ) -> Result<&mut Self, NamespaceEditError> {
        let src = prim.path().clone();
        let dst = new_parent
            .path()
            .append_path(new_name)
            .map_err(|_| NamespaceEditError::InvalidDestination(src.clone()))?;
        Ok(self.move_prim(src, dst))
    }

    /// Check whether [`apply`](Self::apply) would succeed, without changing the
    /// stage. Mirrors C++ `CanApplyEdits`. This runs the same path as
    /// [`apply`](Self::apply) but always rolls the transactions back, so any
    /// error surfaces here exactly as it would there.
    pub fn can_apply(&self) -> Result<(), NamespaceEditError> {
        self.execute(false)
    }

    /// Apply every staged edit to the stage's local layer stack, fixing up
    /// targets / connections / internal references and authoring relocates for
    /// objects composed across an arc. On success the edit queue is cleared.
    /// Mirrors C++ `ApplyEdits`.
    ///
    /// The whole batch is atomic: the edits stage into every affected layer's
    /// overlay in order, and the layers commit together only once every one has
    /// authored cleanly. An authoring error rolls every layer back, so a failed
    /// apply leaves the stage exactly as it was. This atomicity is only against
    /// authoring errors,
    /// not a database-style guarantee: a layer's backing
    /// [`AbstractData`](sdf::AbstractData) can be any implementation (an
    /// in-memory store, `CrateData`, a custom backend), and committing a staged
    /// edit into it is not assumed to itself be atomic or recoverable.
    ///
    /// When the batch touches more than one layer, the single
    /// [`CommittedChange`](super::CommittedChange) delivered to sinks merges the
    /// per-layer change records and attributes them to the strongest edited
    /// layer. Composed-path reporting is exact, but a sink that reads the raw
    /// change list per layer — notably [`Stage::extract_diff`](super::Stage::extract_diff) —
    /// cannot recover which layer each record landed in, so diff replication of a
    /// multi-layer namespace edit is not supported yet.
    pub fn apply(&mut self) -> Result<(), NamespaceEditError> {
        self.execute(true)?;
        self.edits.clear();
        Ok(())
    }

    /// Stage the batch onto the local layer stack as one atomic multi-layer edit.
    /// Runs in two phases. First a [`NamespaceProjection`] replays the batch over
    /// the composed pre-batch namespace to settle the cross-arc facts the staged
    /// overlays cannot see — whether each source/destination resolves to content
    /// realized by a relocate — and to build the relocate plan; this must finish
    /// before the layer graph is borrowed mutably, since composition queries and
    /// layer mutation cannot borrow the stage at once. Then each edit stages in
    /// order against every affected layer, combining its projected facts with the
    /// staged overlays (which reflect the prior edits), embedded paths are
    /// remapped, and the relocates authored. The layers either commit together
    /// (driving one composition-invalidation cycle) or — when `commit` is false —
    /// roll back for a dry run. The shared path behind
    /// [`can_apply`](Self::can_apply) and [`apply`](Self::apply).
    ///
    /// Any failure — an invalid edit or an authoring error — rolls every layer
    /// back, so a failed batch leaves the stage untouched and the cache valid. A
    /// dry run runs this same path, so [`can_apply`](Self::can_apply) reports an
    /// error exactly as
    /// [`apply`](Self::apply) would hit it.
    fn execute(&self, commit: bool) -> Result<(), NamespaceEditError> {
        if self.edits.is_empty() {
            return Err(NamespaceEditError::NoEdits);
        }
        match self.plan()? {
            BatchPlan::LocalStack {
                layer_ids,
                seeds,
                relocates,
                per_edit,
            } => self.execute_local_stack(commit, layer_ids, seeds, relocates, per_edit),
            BatchPlan::Mapped {
                layer_id,
                target,
                per_edit,
            } => self.execute_mapped(commit, layer_id, &target, &per_edit),
        }
    }

    /// Stage the batch into the local root layer stack: direct structural moves
    /// and deletes at the composed (stage == spec) paths across every local
    /// layer, embedded-path fixup, and synthesized relocates for content that
    /// arrives across an arc. The identity-target authoring shape behind
    /// [`execute`](Self::execute).
    fn execute_local_stack(
        &self,
        commit: bool,
        layer_ids: Vec<pcp::LayerId>,
        seeds: HashMap<pcp::LayerId, sdf::RelocateList>,
        relocate_plan: RelocateStackPlan,
        plan: Vec<EditPlan>,
    ) -> Result<(), NamespaceEditError> {
        let resolved = relocate_plan.resolve(seeds)?;

        // Stage the structural edits atomically across the layer
        // stack. The whole batch commits through `edit_layers`: every layer's
        // sinks veto first, then all commit, so a multi-layer namespace edit is
        // all-or-nothing even under a rejecting sink, and each commit feeds the
        // stage's aggregator for the recompose below. A dry run (`dry_run_layers`)
        // stages the same way to prove the batch applies, then discards it. The
        // batch assumes its layers carry no uncommitted direct edits — a discard
        // drops the whole overlay.
        {
            let mut graph = self.stage.layers_mut();
            let mut layers: Vec<(pcp::LayerId, &mut sdf::Layer)> = graph.layers_mut(&layer_ids).into_iter().collect();
            let ids: Vec<pcp::LayerId> = layers.iter().map(|(id, _)| *id).collect();
            let mut batch: Vec<&mut sdf::Layer> = layers.iter_mut().map(|(_, layer)| &mut **layer).collect();
            let stage_edits = |edits: &mut [sdf::LayerEdit<'_>]| -> Result<(), NamespaceEditError> {
                {
                    let mut refs: Vec<&mut sdf::LayerEdit<'_>> = edits.iter_mut().collect();
                    for (edit, plan) in self.edits.iter().zip(&plan) {
                        apply_edit(&mut refs, edit, plan)?;
                    }
                }
                for (id, layer) in ids.iter().zip(edits.iter_mut()) {
                    fixup_embedded_paths(layer, &self.edits)?;
                    // The plan is the sole authority for relocates; the generic
                    // fixup above leaves them alone.
                    if let Some(next) = resolved.change_for(*id) {
                        layer.set_relocates(next).map_err(StageAuthoringError::Layer)?;
                    }
                }
                Ok(())
            };
            if commit {
                sdf::edit_layers(&mut batch, stage_edits)?;
            } else {
                // Dry run: stage to prove the batch applies cleanly, then discard.
                // No sink sees a dry run.
                return sdf::dry_run_layers(&mut batch, stage_edits);
            }
        }
        self.stage.process_pending();
        Ok(())
    }

    /// Stage the batch into the single layer a variant or cross-arc edit target
    /// writes to, in that target's namespace. Each edit's paths are mapped
    /// through the target ([`MappedEdit`]); the structural moves and deletes
    /// author directly into the one layer, and embedded paths are fixed up
    /// through the lift-then-map chain. The mapped authoring shape behind
    /// [`execute`](Self::execute).
    ///
    /// A mapped target reaches its content directly, so this performs only
    /// direct moves and deletes — no relocate synthesis. An edit whose source
    /// composes only across a deeper arc is rejected
    /// ([`RequiresRelocate`](NamespaceEditError::RequiresRelocate)) rather than
    /// authored as a relocate the target's layer stack would not carry.
    fn execute_mapped(
        &self,
        commit: bool,
        layer_id: pcp::LayerId,
        target: &EditTarget,
        per_edit: &[MappedEdit],
    ) -> Result<(), NamespaceEditError> {
        self.stage
            .author_layer_txn(layer_id, Some(target.map_function()), commit, |layer| {
                for mapped in per_edit {
                    apply_mapped_edit(layer, mapped)?;
                }
                fixup_mapped_paths(layer, target, &self.edits)
            })
    }

    /// Resolve the current edit target into a [`BatchPlan`], the read-only first
    /// half of [`execute`](Self::execute) shared with
    /// [`layers_to_edit`](Self::layers_to_edit). An identity local-stack target
    /// plans direct authoring plus relocate synthesis
    /// ([`plan_local_stack`](Self::plan_local_stack)); a variant or cross-arc
    /// target plans direct mapped authoring ([`plan_mapped`](Self::plan_mapped)).
    /// Runs before the layer graph is borrowed mutably for staging: composition
    /// queries and layer mutation cannot borrow the stage at once.
    fn plan(&self) -> Result<BatchPlan, NamespaceEditError> {
        let edit_target = self.stage.edit_target_layer_id()?;
        let layer_ids = self.stage.root_stack_layer_ids();
        let target = self.stage.edit_target();
        // An identity mapping into a local-stack layer authors at the composed
        // (stage == spec) paths verbatim, so the batch can move local specs
        // directly and synthesize relocates for cross-arc content. Any other
        // target is single-layer and mapped: every path goes through the target
        // and only directly reachable content is edited.
        if layer_ids.contains(&edit_target) && target.map_function().is_identity() {
            self.plan_local_stack(layer_ids, edit_target)
        } else {
            self.plan_mapped(edit_target, target)
        }
    }

    /// Plan the identity local-stack authoring shape: seed every local-stack
    /// layer's relocates and evolve them through the edits, deciding per edit
    /// whether its source and destination resolve to cross-arc content.
    fn plan_local_stack(
        &self,
        layer_ids: Vec<pcp::LayerId>,
        edit_target: pcp::LayerId,
    ) -> Result<BatchPlan, NamespaceEditError> {
        // `seeds` (per layer) is the baseline each layer's final list is compared
        // against; the plan tracks per-occurrence freshness so validation blames
        // only the pairs this batch created or changed.
        let seeds = {
            let layers = self.stage.layers();
            let mut seeds: HashMap<pcp::LayerId, sdf::RelocateList> = HashMap::new();
            for id in &layer_ids {
                if let Some(node) = layers.get(*id) {
                    let pairs = node.layer.relocates();
                    if !pairs.is_empty() {
                        seeds.insert(*id, pairs);
                    }
                }
            }
            seeds
        };
        let projection = NamespaceProjection::new(&self.stage);
        let mut relocates = RelocateStackPlan::new(&layer_ids, &seeds, edit_target);
        let mut per_edit: Vec<EditPlan> = Vec::with_capacity(self.edits.len());
        // TODO(perf): each edit replays the growing `earlier` prefix through
        // `cross_arc_facts`/`occupied` (premove/project over all prior edits),
        // making the projection work O(edits^2); a forward cumulative path
        // projection would make it linear if batches ever grow large.
        for (i, edit) in self.edits.iter().enumerate() {
            validate_edit_shape(edit)?;
            let earlier = &self.edits[..i];
            let entry = match edit {
                NamespaceEdit::Move { src, dst, .. } => {
                    let occupied = projection.occupied(dst, earlier)?;
                    let (present, masks) = projection.cross_arc_facts(src, earlier)?;
                    if present && masks {
                        return Err(NamespaceEditError::UnrepresentableRelocateBatch(src.clone()));
                    }
                    relocates.record_move(src, dst, present)?;
                    EditPlan { present, occupied }
                }
                NamespaceEdit::Delete { path, .. } => {
                    let (present, masks) = projection.cross_arc_facts(path, earlier)?;
                    if present && masks {
                        return Err(NamespaceEditError::UnrepresentableRelocateBatch(path.clone()));
                    }
                    relocates.record_delete(path, present)?;
                    EditPlan {
                        present,
                        occupied: false,
                    }
                }
            };
            per_edit.push(entry);
        }
        Ok(BatchPlan::LocalStack {
            layer_ids,
            seeds,
            relocates,
            per_edit,
        })
    }

    /// Plan the mapped authoring shape for a variant or cross-arc `target`:
    /// translate each edit's paths into the target layer's namespace, rejecting a
    /// move endpoint the target cannot express
    /// ([`StageAuthoringError::OutsideEditTarget`]), and record whether each
    /// source composes and whether each destination is occupied on the composed
    /// stage. No relocate analysis runs: a mapped target edits only directly
    /// reachable content.
    ///
    /// A mapped target authors a direct single-layer edit, so it can represent a
    /// move or delete only when the target layer is the source's sole contributor.
    /// A source that also composes from another layer or a deeper arc would
    /// survive the edit in those other contributors, so it is rejected here as
    /// [`RequiresRelocate`](NamespaceEditError::RequiresRelocate) rather than
    /// authored as a partial edit that leaves the prim composed. The
    /// multi-contributor test is conservative at node granularity (see
    /// [`NamespaceProjection::multi_contributor`]).
    fn plan_mapped(&self, layer_id: pcp::LayerId, target: EditTarget) -> Result<BatchPlan, NamespaceEditError> {
        let map = |path: &sdf::Path| {
            target
                .map_to_spec_path(path)
                .ok_or_else(|| NamespaceEditError::Stage(StageAuthoringError::OutsideEditTarget { path: path.clone() }))
        };
        let projection = NamespaceProjection::new(&self.stage);
        let mut per_edit: Vec<MappedEdit> = Vec::with_capacity(self.edits.len());
        for (i, edit) in self.edits.iter().enumerate() {
            validate_edit_shape(edit)?;
            let earlier = &self.edits[..i];
            let stage_src = edit.source().clone();
            let src = map(&stage_src)?;
            let composed = self.stage.has_spec(&stage_src)?;
            // A composed source the target layer does not solely own cannot be
            // moved or deleted as a single-layer edit; expressing it needs a
            // relocate the mapped target does not author.
            if composed && projection.multi_contributor(&stage_src, earlier)? {
                return Err(NamespaceEditError::RequiresRelocate(stage_src));
            }
            let (dst, occupied) = match edit {
                NamespaceEdit::Move { dst, .. } => (Some(map(dst)?), projection.occupied(dst, earlier)?),
                NamespaceEdit::Delete { .. } => (None, false),
            };
            per_edit.push(MappedEdit {
                stage_src,
                src,
                dst,
                composed,
                occupied,
            });
        }
        Ok(BatchPlan::Mapped {
            layer_id,
            target,
            per_edit,
        })
    }

    /// The identifiers of the local-stack layers a successful apply would write:
    /// a layer holding a spec at a source path (the structural move or delete) or
    /// one whose `layerRelocates` the batch would change — including a sublayer
    /// whose relocate follows a moved or deleted prim. Mirrors C++
    /// `GetLayersToEdit`.
    pub fn layers_to_edit(&self) -> Result<Vec<String>, NamespaceEditError> {
        if self.edits.is_empty() {
            return Ok(Vec::new());
        }
        // TODO(perf): this preflight runs the full `plan()` — composed-index
        // builds and relocate analysis per edit — because the evolved relocates
        // decide which layers' `layerRelocates` change. A future fast path could
        // skip the composition projection when no edit is cross-arc and no layer
        // authors relocates, leaving only the cheap per-layer spec scan.
        match self.plan()? {
            BatchPlan::LocalStack {
                layer_ids,
                seeds,
                relocates,
                ..
            } => {
                let resolved = relocates.resolve(seeds)?;
                let layers = self.stage.layers();
                let mut result = Vec::new();
                // TODO(perf): each layer is independent — the spec scan and the
                // relocate comparison for the layers in `layer_ids` can run in parallel.
                for id in &layer_ids {
                    let Some(node) = layers.get(*id) else { continue };
                    let touches_spec = self.edits.iter().any(|edit| node.layer.data().has_spec(edit.source()));
                    if touches_spec || resolved.change_for(*id).is_some() {
                        result.push(layers.identifier(*id).to_string());
                    }
                }
                Ok(result)
            }
            // A mapped target authors into exactly the one layer it writes to.
            BatchPlan::Mapped { layer_id, .. } => Ok(vec![self.stage.layers().identifier(layer_id).to_string()]),
        }
    }
}

/// The read-only result of [`NamespaceEditor::plan`], one variant per authoring
/// shape. Consumed by `execute` to validate and stage, and by `layers_to_edit`
/// to report which layers a successful apply would write.
enum BatchPlan {
    /// An identity local-stack target: the local-stack layer ids, each layer's
    /// seed relocates, the evolved relocate stack plan, and the per-edit
    /// cross-arc facts.
    LocalStack {
        layer_ids: Vec<pcp::LayerId>,
        seeds: HashMap<pcp::LayerId, sdf::RelocateList>,
        relocates: RelocateStackPlan,
        per_edit: Vec<EditPlan>,
    },
    /// A variant or cross-arc target: the single layer it writes to, that target
    /// (carrying the namespace mapping), and the batch edits translated into the
    /// target layer's namespace.
    Mapped {
        layer_id: pcp::LayerId,
        target: EditTarget,
        per_edit: Vec<MappedEdit>,
    },
}

/// One batch edit translated into a mapped target layer's namespace. A move
/// copies the source spec subtree to the destination and removes the source; a
/// delete (`dst` is `None`) removes the source spec.
struct MappedEdit {
    /// The edit's source path in composed stage namespace, for error reporting.
    stage_src: sdf::Path,
    /// The source spec path in the target layer's namespace — a move source or
    /// a deletion target.
    src: sdf::Path,
    /// The destination spec path for a move, `None` for a delete.
    dst: Option<sdf::Path>,
    /// Whether the source composes on the stage before the batch, separating a
    /// source that arrives across a deeper arc (and would need a relocate) from
    /// one that is simply absent.
    composed: bool,
    /// Whether a composed object already occupies the move destination on the
    /// stage (a referenced or otherwise cross-arc occupant the target layer's
    /// overlay alone cannot see). Always `false` for a delete.
    occupied: bool,
}

impl MappedEdit {
    /// The error for a source the structural op could not author directly: a
    /// composed source reachable only across a deeper arc would need a relocate
    /// ([`RequiresRelocate`](NamespaceEditError::RequiresRelocate)); an uncomposed
    /// one is simply missing ([`SourceNotFound`](NamespaceEditError::SourceNotFound)).
    fn unreachable_source(&self) -> NamespaceEditError {
        if self.composed {
            NamespaceEditError::RequiresRelocate(self.stage_src.clone())
        } else {
            NamespaceEditError::SourceNotFound(self.stage_src.clone())
        }
    }
}

/// Answers composed-namespace questions the staged layer overlays cannot.
///
/// A referenced or payload prim has no local spec, and relocates take effect
/// only on recomposition — which does not happen between the edits of a batch —
/// so the overlays alone cannot tell whether a source composes or a destination
/// is occupied after the earlier edits. Each query replays the edit prefix
/// against the pre-batch `stage`, mapping a path back to its pre-batch location
/// and confirming the content still lands there.
struct NamespaceProjection<'a> {
    stage: &'a Stage,
}

impl<'a> NamespaceProjection<'a> {
    fn new(stage: &'a Stage) -> Self {
        Self { stage }
    }

    /// The cross-arc facts for a move or delete of `path` after the `earlier`
    /// edits, read from one composed-index build.
    ///
    /// `realized` is whether the edit must be realized by a relocate: its opinion
    /// arrives across an arc rooted away from `path`, so it has no local spec of
    /// its own to move. `masks` is whether `path` is a relocate target that also
    /// masks its own direct ancestral content — content composed directly at
    /// `path` (through a plain arc) that a relocate happens to shadow. Moving or
    /// deleting such a path would reveal the masked content, leaving `path` still
    /// composed, so the edit cannot be expressed as a single relocate and the
    /// batch is rejected. In the composed index the relocated-in content sits
    /// under a `Relocate` arc while the masked content reaches `path` through a
    /// plain arc; both kinds present means a masking relocate target. Property
    /// paths are never realized by a relocate.
    fn cross_arc_facts(&self, path: &sdf::Path, earlier: &[NamespaceEdit]) -> Result<(bool, bool), NamespaceEditError> {
        if path.is_property_path() {
            return Ok((false, false));
        }
        let Some(origin) = projected_origin(path, earlier) else {
            return Ok((false, false));
        };
        let index = self.stage.prim(origin.clone()).prim_index().graph()?;
        let mut realized = false;
        let mut via_relocate = false;
        let mut direct_ancestral = false;
        for (id, node) in index.nodes_with_ids() {
            if !node.has_specs() {
                continue;
            }
            let introduced_away = node
                .map_to_root()
                .map_source_to_target(&node.path_at_introduction())
                .is_some_and(|intro| intro != origin);
            if node.arc() != pcp::ArcType::Root && introduced_away {
                realized = true;
            }
            if node_under_relocate(&index, id) {
                via_relocate = true;
            } else if introduced_away {
                direct_ancestral = true;
            }
        }
        Ok((realized, via_relocate && direct_ancestral))
    }

    /// Whether a composed object (prim or property) occupies `path` after the
    /// `earlier` edits and so blocks a move onto it. A destination an earlier
    /// edit vacated round-trips to a different path and is free. Catches
    /// composed-only occupants the staged per-layer check cannot see, including a
    /// property arriving across a reference.
    fn occupied(&self, path: &sdf::Path, earlier: &[NamespaceEdit]) -> Result<bool, NamespaceEditError> {
        let Some(origin) = projected_origin(path, earlier) else {
            return Ok(false);
        };
        Ok(self.stage.has_spec(&origin)?)
    }

    /// Whether the object at `path`, after the `earlier` edits, draws spec
    /// opinions from more than one node of its prim's composition graph — so the
    /// single layer a mapped target writes cannot be the sole contributor, and a
    /// direct move or delete would leave the prim composed by the others.
    ///
    /// The count is at composition-node granularity: a node bundles its whole
    /// site layer stack, so a source whose only contributing node spans several
    /// sublayers (only one of which the target writes) reads as single and is not
    /// caught here. Authoring relocates to suppress such within-stack residue is
    /// future work; a single-node source is the common variant / cross-arc case.
    fn multi_contributor(&self, path: &sdf::Path, earlier: &[NamespaceEdit]) -> Result<bool, NamespaceEditError> {
        let Some(origin) = projected_origin(path, earlier) else {
            return Ok(false);
        };
        let index = self.stage.prim(origin.prim_path()).prim_index().graph()?;
        Ok(index.nodes_with_ids().filter(|(_, node)| node.has_specs()).count() > 1)
    }
}

/// Whether `node` (or any ancestor in the composed index) was introduced by a
/// `Relocate` arc, so its content reaches the prim through a relocate rather
/// than directly.
fn node_under_relocate(index: &pcp::PrimIndex, node: pcp::NodeId) -> bool {
    let mut current = Some(node);
    while let Some(id) = current {
        if index.node(id).arc() == pcp::ArcType::Relocate {
            return true;
        }
        current = index.parent(id);
    }
    false
}

/// One relocate pair as the batch evolves it, tagged with the layer that owns
/// it. `source` is the path Pcp sees as the relocate source — in the current,
/// possibly already-relocated, parent namespace — and `target` the live composed
/// destination, or empty for a deletion.
struct RelocatedEntry {
    source: sdf::Path,
    target: sdf::Path,
    layer: pcp::LayerId,
    /// The pair as it was seeded from the layer, or `None` when the batch
    /// synthesized this occurrence. An occurrence is fresh — created or changed
    /// by the batch — when this is `None` or differs from the current pair, even
    /// if the current pair's value happens to coincide with another layer's
    /// pre-existing one. Validation blames fresh occurrences by identity, not by
    /// value.
    original: Option<sdf::Relocate>,
    /// Whether Pcp dropped this seed when classifying the pre-batch relocate set,
    /// for any reason — structurally invalid, duplicate source, or conflict. An
    /// immutable before-snapshot, used only to reject a batch that would make a
    /// previously-dropped pair live again; it is never consulted to decide how a
    /// pair evolves (that uses the live classification of the current pairs).
    ///
    /// Frozen at seed time, not recomputed at validation: a pair's seed-time
    /// status depends on the whole initial set, including pairs the batch later
    /// deletes (duplicate-source and conflict groups drop together), so it cannot
    /// be reconstructed from the surviving entries alone. This bool is the minimal
    /// record of the "before" half of the resurrection check; the live analysis
    /// over the current pairs supplies the "after" half.
    dropped_at_seed: bool,
}

impl RelocatedEntry {
    /// Whether the batch created or changed this occurrence, so validation may
    /// blame it for being invalid or conflicting.
    fn is_fresh(&self) -> bool {
        self.original
            .as_ref()
            .is_none_or(|(s, t)| s != &self.source || t != &self.target)
    }

    /// Whether the batch collapsed a created or non-identity seed pair to an
    /// identity relocate omitted from authored metadata.
    fn drops_as_identity(&self) -> bool {
        self.source == self.target
            && match &self.original {
                None => true,
                Some((source, target)) => source != target,
            }
    }
}

/// The evolving `layerRelocates` of the whole local root stack.
///
/// Pcp validates relocates over the combined layer stack, not the edit target
/// alone, so the plan owns every local-stack layer's pairs (tagged by owning
/// layer) and evolves them through each edit: a move reprojects endpoints, a
/// delete empties a target or drops a source, and a cross-arc move or delete
/// synthesizes a new pair — always on the edit target, the only layer the editor
/// authors into. Authoring writes each layer's evolved list back to that layer;
/// validation runs over the combined set. Tracking every layer (not just the
/// edit target) lets a later edit recognize a relocate target an earlier edit
/// moved, and lets a delete reject an orphaned cross-layer relocate.
struct RelocateStackPlan {
    entries: Vec<RelocatedEntry>,
    edit_target: pcp::LayerId,
    layer_rank: HashMap<pcp::LayerId, usize>,
}

impl RelocateStackPlan {
    /// Seed the plan with each local-stack layer's existing relocates, tagged by
    /// owning layer. New pairs synthesized by the batch land on `edit_target`.
    fn new(
        layer_ids: &[pcp::LayerId],
        seeds: &HashMap<pcp::LayerId, sdf::RelocateList>,
        edit_target: pcp::LayerId,
    ) -> Self {
        let mut seen_layers: HashSet<pcp::LayerId> = HashSet::new();
        let ordered_layers: Vec<pcp::LayerId> = layer_ids
            .iter()
            .copied()
            .filter(|layer| seen_layers.insert(*layer))
            .collect();
        let layer_rank: HashMap<pcp::LayerId, usize> = ordered_layers
            .iter()
            .enumerate()
            .map(|(rank, layer)| (*layer, rank))
            .collect();
        let seeded: Vec<(pcp::LayerId, sdf::Relocate)> = ordered_layers
            .iter()
            .filter_map(|layer| seeds.get(layer).map(|pairs| (*layer, pairs)))
            .flat_map(|(layer, pairs)| pairs.iter().map(move |pair| (layer, (pair.0.clone(), pair.1.clone()))))
            .collect();
        let pairs: sdf::RelocateList = seeded.iter().map(|(_, pair)| pair.clone()).collect();
        let status = pcp::analyze_relocate_occurrences(&pairs);
        let entries = seeded
            .into_iter()
            .zip(status)
            .map(|((layer, pair), status)| RelocatedEntry {
                source: pair.0.clone(),
                target: pair.1.clone(),
                layer,
                // Pcp did not apply this seed over the initial stack: the
                // before-snapshot for the resurrection check.
                dropped_at_seed: !status.is_active(),
                original: Some(pair),
            })
            .collect();
        Self {
            entries,
            edit_target,
            layer_rank,
        }
    }

    /// Record a move `src -> dst`. Always follows the moved subtree through every
    /// entry, so a relocate on any layer whose endpoint sits under `src` tracks
    /// the edit. When `cross_arc`, the move is realized by a relocate, so a fresh
    /// pair is appended on the edit target unless `src` is already a live target
    /// (then [`reproject`](Self::reproject) just retargets it, chain-free).
    // TODO(perf): this recomputes the active classification several times for one
    // edit — `continuation_source` and `prohibiting_source` each call
    // `active_relocates` -> `active_flags`, and `reproject` calls `active_flags`
    // again — all O(n^2) over an entry set that does not change until the
    // reproject. Compute `active_flags()` once here and thread the mask into
    // those helpers.
    fn record_move(&mut self, src: &sdf::Path, dst: &sdf::Path, cross_arc: bool) -> Result<(), NamespaceEditError> {
        let continues_source = self.continuation_source(src);
        if let Some(source) = self.prohibiting_source(dst) {
            if continues_source.as_ref() != Some(&source) || dst != &source {
                return Err(NamespaceEditError::UnrepresentableRelocateBatch(source));
            }
        }
        let continues = continues_source.is_some();
        self.reproject(src, dst);
        if cross_arc && !continues {
            self.insert_edit_target_entry(RelocatedEntry {
                source: src.clone(),
                target: dst.clone(),
                layer: self.edit_target,
                original: None,
                dropped_at_seed: false,
            });
        }
        Ok(())
    }

    /// Record a delete of `path`. Evolves every entry against the live
    /// classification: an active relocate wholly inside the deleted subtree
    /// (sourced under `path`) is removed with it, and an active relocate whose
    /// target is under `path` collapses to a deletion. Inert (dropped) pairs are
    /// left exactly as authored — they place no content, so deleting a directly
    /// composed prim must not rewrite them. When `cross_arc`, a deletion pair is
    /// appended on the edit target unless an active pair already targets `path`.
    /// Rejected as
    /// [`UnrepresentableRelocateBatch`](NamespaceEditError::UnrepresentableRelocateBatch)
    /// when an active relocate was sourced under `path` but targets outside it: a
    /// descendant relocated out of the deleted subtree would lose its source, and
    /// no valid relocate set keeps the moved child while deleting its parent.
    fn record_delete(&mut self, path: &sdf::Path, cross_arc: bool) -> Result<(), NamespaceEditError> {
        let active = self.active_flags();
        let orphans_child = self.entries.iter().zip(&active).any(|(e, &a)| {
            a && &e.source != path && e.source.has_prefix(path) && !e.target.is_empty() && !e.target.has_prefix(path)
        });
        if orphans_child {
            return Err(NamespaceEditError::UnrepresentableRelocateBatch(path.clone()));
        }
        let mut continues = false;
        let kept: Vec<RelocatedEntry> = std::mem::take(&mut self.entries)
            .into_iter()
            .zip(active)
            .filter_map(|(mut e, a)| {
                if a && &e.source != path && e.source.has_prefix(path) {
                    return None;
                }
                if a && &e.target == path {
                    continues = true;
                }
                if a && !e.target.is_empty() && e.target.has_prefix(path) {
                    e.target = sdf::Path::default();
                }
                Some(e)
            })
            .collect();
        self.entries = kept;
        if cross_arc && !continues {
            self.insert_edit_target_entry(RelocatedEntry {
                source: path.clone(),
                target: sdf::Path::default(),
                layer: self.edit_target,
                original: None,
                dropped_at_seed: false,
            });
        }
        Ok(())
    }

    /// Insert a synthesized edit-target pair at the edit target's layer-stack
    /// strength, after any earlier pairs from the same layer.
    fn insert_edit_target_entry(&mut self, entry: RelocatedEntry) {
        debug_assert_eq!(entry.layer, self.edit_target);
        let edit_rank = self.layer_rank[&self.edit_target];
        let insert_at = self
            .entries
            .iter()
            .position(|e| self.layer_rank[&e.layer] > edit_rank)
            .unwrap_or(self.entries.len());
        self.entries.insert(insert_at, entry);
    }

    /// The live Pcp classification of the current entries, index-aligned: whether
    /// each occurrence is active over the current `(source, target)` set. Derived
    /// on demand from the current values — not cached — so it stays correct as the
    /// batch evolves the entries.
    // TODO(perf): re-analyzes the whole set (O(n^2)) on each call; n is small and
    // this is a cold authoring path, but a cached-and-invalidated mask would help.
    fn active_flags(&self) -> Vec<bool> {
        let pairs: sdf::RelocateList = self
            .entries
            .iter()
            .map(|e| (e.source.clone(), e.target.clone()))
            .collect();
        pcp::analyze_relocate_occurrences(&pairs)
            .into_iter()
            .map(|status| status.is_active())
            .collect()
    }

    fn active_relocates(&self) -> sdf::RelocateList {
        self.entries
            .iter()
            .zip(self.active_flags())
            .filter(|(_, active)| *active)
            .map(|(e, _)| (e.source.clone(), e.target.clone()))
            .collect()
    }

    fn continuation_source(&self, path: &sdf::Path) -> Option<sdf::Path> {
        self.active_relocates()
            .into_iter()
            .find_map(|(source, target)| (!target.is_empty() && target == *path).then_some(source))
    }

    /// The active relocate source that prohibits authoring at `path`, if any.
    fn prohibiting_source(&self, path: &sdf::Path) -> Option<sdf::Path> {
        self.active_relocates()
            .into_iter()
            .filter_map(|(source, _)| path.has_prefix(&source).then_some(source))
            .max_by_key(|source| source.element_count())
    }

    /// Follow a subtree moved from `old` to `new` through every entry. A target
    /// strictly under `old` is inside a renamed subtree and follows regardless of
    /// whether the pair is active. A target exactly equal to `old` follows only
    /// for the active relocate that actually places content there — an inert
    /// (dropped) pair that merely names `old` does not place the moved prim, so
    /// re-rooting it would manufacture a spurious conflict. A source strictly
    /// under `old` (a child already relocated out) follows; the pair whose source
    /// is exactly `old` keeps it (the pre-relocation location).
    fn reproject(&mut self, old: &sdf::Path, new: &sdf::Path) {
        let active = self.active_flags();
        for (e, is_active) in self.entries.iter_mut().zip(active) {
            if !e.target.is_empty() {
                if e.target == *old {
                    if is_active {
                        e.target = new.clone();
                    }
                } else {
                    e.target = rebased(&e.target, old, new);
                }
            }
            if &e.source != old {
                e.source = rebased(&e.source, old, new);
            }
        }
    }

    /// Every current pair across the stack, tagged with its freshness and
    /// dropped-seed provenance and with no-op `source == target` pairs dropped,
    /// for the combined Pcp-equivalent validation.
    fn combined(&self) -> Vec<pcp::BatchRelocate> {
        self.entries
            .iter()
            .filter(|e| e.source != e.target)
            .map(|e| pcp::BatchRelocate {
                pair: (e.source.clone(), e.target.clone()),
                fresh: e.is_fresh(),
                dropped_seed: e.dropped_at_seed,
            })
            .collect()
    }

    /// Validate the relocates Pcp will see: the combined set across the whole
    /// local stack. Pcp validates the layer stack as a whole, not the edit target
    /// alone, and a cross-layer conflict only appears in the combined list. Fresh
    /// occurrences are blamed for being dropped; seed occurrences that Pcp dropped
    /// before the batch are rejected if the edit would make them active.
    fn validate(&self) -> Result<(), NamespaceEditError> {
        let combined = self.combined();
        let pairs: sdf::RelocateList = combined.iter().map(|r| r.pair.clone()).collect();
        let status = pcp::analyze_relocate_occurrences(&pairs);
        if let Some(path) = pcp::first_unrepresentable_relocate(&combined, &status) {
            return Err(NamespaceEditError::UnrepresentableRelocateBatch(path));
        }
        if let Some((r, _)) = combined
            .iter()
            .zip(&status)
            .find(|(r, s)| r.dropped_seed && s.is_active())
        {
            return Err(NamespaceEditError::UnrepresentableRelocateBatch(r.pair.0.clone()));
        }
        Ok(())
    }

    /// The final relocate list per owning layer. A no-op `source == target` the
    /// batch produced (a pair folded to identity) is dropped, but one the batch
    /// left untouched is preserved as authored — an unrelated edit must not
    /// rewrite a layer's existing metadata away. A layer that had relocates but
    /// is absent from the result has had all its pairs removed and must be
    /// cleared by the caller.
    fn into_by_layer(self) -> HashMap<pcp::LayerId, sdf::RelocateList> {
        let mut by_layer: HashMap<pcp::LayerId, sdf::RelocateList> = HashMap::new();
        for e in self.entries {
            if e.drops_as_identity() {
                continue;
            }
            by_layer.entry(e.layer).or_default().push((e.source, e.target));
        }
        by_layer
    }

    /// Validate the combined stack and resolve each layer's final
    /// `layerRelocates` against the `seeds` baseline. The shared back half of
    /// [`execute`](NamespaceEditor::execute) and
    /// [`layers_to_edit`](NamespaceEditor::layers_to_edit): both validate, fold
    /// the plan to per-layer lists, and compare against the seeds to touch a
    /// layer only when its relocates change.
    fn resolve(self, seeds: HashMap<pcp::LayerId, sdf::RelocateList>) -> Result<ResolvedRelocates, NamespaceEditError> {
        self.validate()?;
        Ok(ResolvedRelocates {
            seeds,
            final_by_layer: self.into_by_layer(),
        })
    }
}

/// Per-layer relocate authoring resolved from a validated [`RelocateStackPlan`]:
/// the final `layerRelocates` each layer should hold and the seed baseline to
/// compare against.
struct ResolvedRelocates {
    seeds: HashMap<pcp::LayerId, sdf::RelocateList>,
    final_by_layer: HashMap<pcp::LayerId, sdf::RelocateList>,
}

impl ResolvedRelocates {
    /// The relocate list `id` should hold after the batch when it differs from
    /// the layer's seed baseline, or `None` when unchanged. Authoring on a change
    /// covers clearing pairs the batch folded away, while skipping an unchanged
    /// layer leaves a pre-existing (possibly invalid) pair exactly as authored.
    fn change_for(&self, id: pcp::LayerId) -> Option<sdf::RelocateList> {
        let next = self.final_by_layer.get(&id).cloned().unwrap_or_default();
        let prev = self.seeds.get(&id).cloned().unwrap_or_default();
        (next != prev).then_some(next)
    }
}

/// The cross-arc facts the [`NamespaceProjection`] settles for one edit, read
/// during staging: whether the source resolves to composed content realized by
/// a relocate (so it has no local spec yet counts as present), and whether the
/// destination is occupied by such content. Both account for the earlier edits.
struct EditPlan {
    present: bool,
    occupied: bool,
}

/// Validate `edit` against the staged state and its [`EditPlan`], then stage it
/// into every layer. The staged overlays already reflect the earlier edits, so
/// local-spec checks read precise data: a destination collision is a local spec
/// at `dst` (or a composed cross-arc occupant from `plan`), and a missing source
/// is an edit that moves or removes nothing in any layer and is not realized by
/// a relocate (`plan.present`).
fn apply_edit(
    layers: &mut [&mut sdf::LayerEdit<'_>],
    edit: &NamespaceEdit,
    plan: &EditPlan,
) -> Result<(), NamespaceEditError> {
    validate_edit_shape(edit)?;
    match edit {
        NamespaceEdit::Move { src, dst, .. } => {
            // A composed cross-arc occupant (`plan.occupied`) or a local spec
            // staged by an earlier edit in this batch blocks the move.
            if plan.occupied || layers.iter().any(|layer| layer.data().has_spec(dst)) {
                return Err(NamespaceEditError::DestinationExists(dst.clone()));
            }
            stage_across_layers(layers, src, plan.present, |layer| move_spec(layer, src, dst))?;
        }
        NamespaceEdit::Delete { path, .. } => {
            stage_across_layers(layers, path, plan.present, |layer| layer.remove_spec(path))?;
        }
    }
    Ok(())
}

fn validate_edit_shape(edit: &NamespaceEdit) -> Result<(), NamespaceEditError> {
    match edit {
        NamespaceEdit::Move { src, dst, kind } => {
            check_editable(src, *kind, NamespaceEditError::InvalidSource)?;
            check_editable(dst, *kind, NamespaceEditError::InvalidDestination)?;
            if dst.has_prefix(src) {
                return Err(NamespaceEditError::DestinationUnderSource {
                    src: src.clone(),
                    dst: dst.clone(),
                });
            }
        }
        NamespaceEdit::Delete { path, kind } => {
            check_editable(path, *kind, NamespaceEditError::InvalidSource)?;
        }
    }
    Ok(())
}

/// Stage `op` into every layer, tracking whether any layer authored a change.
/// Errors with [`SourceNotFound`](NamespaceEditError::SourceNotFound) when no
/// layer did and the source is not realized through a relocate (`present`).
fn stage_across_layers(
    layers: &mut [&mut sdf::LayerEdit<'_>],
    path: &sdf::Path,
    present: bool,
    mut op: impl FnMut(&mut sdf::LayerEdit<'_>) -> Result<bool, sdf::AuthoringError>,
) -> Result<(), NamespaceEditError> {
    let mut authored = false;
    for layer in layers.iter_mut() {
        if op(layer).map_err(StageAuthoringError::Layer)? {
            authored = true;
        }
    }
    if !authored && !present {
        return Err(NamespaceEditError::SourceNotFound(path.clone()));
    }
    Ok(())
}

/// Author one translated batch edit on the single mapped target layer: a move
/// copies the source spec subtree to the destination and removes the source, a
/// delete removes the source spec. A destination is blocked by a composed
/// occupant settled in the plan ([`MappedEdit::occupied`]) or a spec an earlier
/// batch edit staged into the layer overlay, and a source the structural op
/// could not author is reported through
/// [`unreachable_source`](MappedEdit::unreachable_source).
fn apply_mapped_edit(layer: &mut sdf::LayerEdit<'_>, edit: &MappedEdit) -> Result<(), NamespaceEditError> {
    let authored = match &edit.dst {
        Some(dst) => {
            // A composed cross-arc occupant (`edit.occupied`) or a spec staged by
            // an earlier edit in this batch blocks the move.
            if edit.occupied || layer.data().has_spec(dst) {
                return Err(NamespaceEditError::DestinationExists(dst.clone()));
            }
            move_spec(layer, &edit.src, dst).map_err(StageAuthoringError::Layer)?
        }
        None => layer.remove_spec(&edit.src).map_err(StageAuthoringError::Layer)?,
    };
    if !authored {
        return Err(edit.unreachable_source());
    }
    Ok(())
}

/// Move the spec subtree at `src` to `dst` within one layer: copy it then remove
/// the source, returning whether a spec was present to move. The structural move
/// shared by the local-stack and mapped authoring paths.
fn move_spec(layer: &mut sdf::LayerEdit<'_>, src: &sdf::Path, dst: &sdf::Path) -> Result<bool, sdf::AuthoringError> {
    let moved = sdf::copy_spec_within(layer.data_mut(), src, dst)?;
    if moved {
        layer.remove_spec(src)?;
    }
    Ok(moved)
}

/// Rewrite every embedded namespace path in `layer` for an identity local-stack
/// edit: a path under a move source re-roots onto the destination, one under a
/// deletion source drops out of its list op.
fn fixup_embedded_paths(layer: &mut sdf::LayerEdit<'_>, edits: &[NamespaceEdit]) -> Result<(), NamespaceEditError> {
    rewrite_embedded_paths(layer, |p| Ok(project_path(p, edits)))
}

/// Rewrite every embedded namespace path in `layer` for a mapped edit, through
/// the lift-then-map chain ([`remap_embedded_path`]): lift the layer-namespace
/// path to stage namespace, follow the batch's moves, then map it back into the
/// target layer's namespace.
fn fixup_mapped_paths(
    layer: &mut sdf::LayerEdit<'_>,
    target: &EditTarget,
    edits: &[NamespaceEdit],
) -> Result<(), NamespaceEditError> {
    rewrite_embedded_paths(layer, |p| remap_embedded_path(p, target, edits))
}

/// Rewrite every embedded namespace path in `layer` through `rewrite`,
/// preserving list-op structure. `rewrite` maps one path to its replacement,
/// `Ok(None)` to drop it from its list op, or an error to fail the batch.
///
/// `layerRelocates` is skipped: a layer-level relocate's source and target carry
/// different meaning, and a deleted target becomes the empty sentinel rather than
/// dropping out, so it is owned by [`RelocateStackPlan`] for a local-stack edit
/// and not modeled for a mapped target. Spec-level `relocates` are ordinary
/// embedded paths and are rewritten here.
//
// TODO(perf): scans every spec and field in the layer. A path-keyed index of
// specs carrying target/connection/reference opinions would bound this to the
// opinions that can actually reference a moved object.
fn rewrite_embedded_paths(
    layer: &mut sdf::LayerEdit<'_>,
    rewrite: impl Fn(&sdf::Path) -> Result<Option<sdf::Path>, NamespaceEditError>,
) -> Result<(), NamespaceEditError> {
    // `filter_map_paths` takes a `Fn` that cannot itself fail, so a rejected
    // path is parked here and surfaced after the rewrite.
    let failed: std::cell::Cell<Option<NamespaceEditError>> = std::cell::Cell::new(None);
    for path in layer.data().spec_paths() {
        let fields = layer.data().list_fields(&path).unwrap_or_default();
        for field in &fields {
            if field == sdf::FieldKey::LayerRelocates.as_str() {
                continue;
            }
            let Some(value) = layer
                .data()
                .try_field(&path, field)
                .map_err(|e| StageAuthoringError::Layer(e.into()))?
            else {
                continue;
            };
            if !value.has_embedded_paths() {
                continue;
            }
            let value = value.into_owned();
            let rewritten = value.filter_map_paths(|p| match rewrite(p) {
                Ok(mapped) => mapped,
                Err(error) => {
                    failed.set(Some(error));
                    Some(p.clone())
                }
            });
            if let Some(error) = failed.take() {
                return Err(error);
            }
            if rewritten != value {
                layer.data_mut().set_field(&path, field, rewritten);
            }
        }
    }
    Ok(())
}

/// Rewrite one embedded namespace path for a mapped edit: lift it to composed
/// stage namespace through the target's mapping, follow the batch's moves with
/// [`project_path`], then map it back into the target layer's namespace.
/// `Ok(None)` drops a path whose target a deletion removed; an `Err` rejects a
/// projected target the arc cannot express
/// ([`StageAuthoringError::OutsideEditTarget`]). A path the mapping cannot lift
/// names nothing in the arc's stage projection, so no stage-namespace move can
/// affect it and it is left as authored.
fn remap_embedded_path(
    path: &sdf::Path,
    target: &EditTarget,
    edits: &[NamespaceEdit],
) -> Result<Option<sdf::Path>, NamespaceEditError> {
    let Some(scene) = target.map_function().map_source_to_target(path) else {
        return Ok(Some(path.clone()));
    };
    match project_path(&scene, edits) {
        None => Ok(None),
        Some(projected) => target
            .map_to_spec_target_path(&projected)
            .map(Some)
            .ok_or_else(|| NamespaceEditError::Stage(StageAuthoringError::OutsideEditTarget { path: projected })),
    }
}

/// `path` with prefix `from` rewritten to `to`, or `path` unchanged when it does
/// not start with `from`.
fn rebased(path: &sdf::Path, from: &sdf::Path, to: &sdf::Path) -> sdf::Path {
    path.replace_prefix(from, to).unwrap_or_else(|| path.clone())
}

/// Apply the batch in order to one path, returning its post-batch path or
/// `None` if a deletion removed it.
fn project_path(path: &sdf::Path, edits: &[NamespaceEdit]) -> Option<sdf::Path> {
    let mut current = path.clone();
    for edit in edits {
        match edit {
            NamespaceEdit::Delete { path: removed, .. } => {
                if current.has_prefix(removed) {
                    return None;
                }
            }
            NamespaceEdit::Move { src, dst, .. } => {
                current = rebased(&current, src, dst);
            }
        }
    }
    Some(current)
}

/// Map `path` back through `earlier` moves, in reverse, to the namespace it
/// occupied before those edits ran. The inverse of [`project_path`] over the
/// move subsequence: each earlier move `src -> dst` is undone by rewriting the
/// `dst` prefix back to `src`, so a path that an earlier move landed under a
/// relocated subtree resolves to its pre-batch location (where its cross-arc
/// opinions can be looked up).
fn premove_path(path: &sdf::Path, earlier: &[NamespaceEdit]) -> sdf::Path {
    let mut original = path.clone();
    for edit in earlier.iter().rev() {
        if let NamespaceEdit::Move { src, dst, .. } = edit {
            original = rebased(&original, dst, src);
        }
    }
    original
}

/// The pre-batch origin a composed query at `path` should read, or `None` when
/// `path` is not where that origin lands after the `earlier` edits — an earlier
/// delete removed it, or it round-trips elsewhere — so the query has nothing to
/// read there. The shared guard the composed-namespace projections key on.
fn projected_origin(path: &sdf::Path, earlier: &[NamespaceEdit]) -> Option<sdf::Path> {
    let origin = premove_path(path, earlier);
    (project_path(&origin, earlier).as_ref() == Some(path)).then_some(origin)
}

/// Validate that `path` is an absolute, non-pseudo-root object path of the
/// edit's `kind`. A non-absolute path maps through `invalid` to the caller's
/// source or destination error variant; a path of the wrong kind (a prim path
/// for a property edit, or vice versa) is a [`KindMismatch`](NamespaceEditError::KindMismatch).
fn check_editable(
    path: &sdf::Path,
    kind: ObjectKind,
    invalid: fn(sdf::Path) -> NamespaceEditError,
) -> Result<(), NamespaceEditError> {
    if path.is_abs_root() {
        return Err(NamespaceEditError::PseudoRoot);
    }
    if !path.is_abs() {
        return Err(invalid(path.clone()));
    }
    if !kind.matches(path) {
        return Err(NamespaceEditError::KindMismatch);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;
    use crate::sdf::{self, path, FieldKey, LayerOffset, Specifier, Variability};
    use crate::usd::{EditTarget, EditTargetArc, Stage};

    /// Author into `layer` and commit, for building a test layer before it joins a
    /// stage.
    fn edit_layer(layer: &mut sdf::Layer, f: impl FnOnce(&mut sdf::LayerEdit<'_>)) {
        layer
            .edit(|e| {
                f(e);
                Ok(())
            })
            .expect("authored");
    }

    /// A stage with `/A` (Xform) → `/A/Child`, a relationship `/Other.rel`
    /// targeting `[/A, /Keep]`, and an attribute `/Other.con` connected to
    /// `/A.out`, all authored in one anonymous root layer.
    fn sample() -> Stage {
        let stage = Stage::builder().in_memory("root.usda").unwrap();
        stage.define_prim("/A").unwrap().set_type_name("Xform").unwrap();
        stage.define_prim("/A/Child").unwrap();
        stage.create_attribute("/A.out", "double").unwrap();
        stage.define_prim("/Keep").unwrap();
        stage.define_prim("/Other").unwrap();
        stage
            .create_relationship("/Other.rel")
            .unwrap()
            .set_targets([path("/A").unwrap(), path("/Keep").unwrap()])
            .unwrap();
        stage
            .create_attribute("/Other.con", "double")
            .unwrap()
            .set_connections([path("/A.out").unwrap()])
            .unwrap();
        stage
    }

    fn valid(stage: &Stage, p: &str) -> bool {
        stage.prim(path(p).unwrap()).is_valid().unwrap()
    }

    fn rel_targets(stage: &Stage, p: &str) -> Vec<String> {
        stage
            .relationship(path(p).unwrap())
            .targets()
            .unwrap()
            .iter()
            .map(|t| t.as_str().to_owned())
            .collect()
    }

    fn connections(stage: &Stage, p: &str) -> Vec<String> {
        stage
            .attribute(path(p).unwrap())
            .connections()
            .unwrap()
            .iter()
            .map(|t| t.as_str().to_owned())
            .collect()
    }

    #[test]
    fn rename_subtree_targets() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .rename_prim(&stage.prim(path("/A").unwrap()), "B")
            .unwrap()
            .apply()
            .unwrap();

        // The subtree moves, and every external opinion that named the prim — a
        // relationship target and an attribute connection — follows it.
        assert!(valid(&stage, "/B"));
        assert!(valid(&stage, "/B/Child"));
        assert!(!valid(&stage, "/A"));
        assert_eq!(rel_targets(&stage, "/Other.rel"), vec!["/B", "/Keep"]);
        assert_eq!(connections(&stage, "/Other.con"), vec!["/B.out"]);
    }

    #[test]
    fn reparent_under_parent() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .reparent_prim(&stage.prim(path("/A").unwrap()), &stage.prim(path("/Keep").unwrap()))
            .unwrap();
        editor.apply().unwrap();

        assert!(valid(&stage, "/Keep/A"));
        assert!(valid(&stage, "/Keep/A/Child"));
        assert!(!valid(&stage, "/A"));
    }

    #[test]
    fn delete_subtree_targets() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/A").unwrap());
        editor.apply().unwrap();

        // The subtree is removed, and every external opinion that named the prim
        // is cleared: the relationship target drops, the connection empties.
        assert!(!valid(&stage, "/A"));
        assert!(!valid(&stage, "/A/Child"));
        assert_eq!(rel_targets(&stage, "/Other.rel"), vec!["/Keep"]);
        assert!(connections(&stage, "/Other.con").is_empty());
    }

    #[test]
    fn rename_fixes_internal_ref() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Other", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Other").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    prim_path: path("/A").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());

        NamespaceEditor::new(&stage)
            .rename_prim(&stage.prim(path("/A").unwrap()), "B")
            .unwrap()
            .apply()
            .unwrap();

        let references = stage
            .root_layer()
            .data()
            .try_field(&path("/Other").unwrap(), FieldKey::References.as_str())
            .unwrap()
            .unwrap()
            .into_owned()
            .try_as_reference_list_op()
            .unwrap();
        assert_eq!(references.prepended_items[0].prim_path.as_str(), "/B");
    }

    #[test]
    fn rename_preserves_listop() {
        // A prepended (not explicit) target survives the fixup as prepended.
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Other", Specifier::Def, "").unwrap();
            sdf::RelationshipSpec::new(e.data_mut(), "/Other.rel", Variability::Varying, false).unwrap();
            e.data_mut().set_field(
                &path("/Other.rel").unwrap(),
                FieldKey::TargetPaths.as_str(),
                sdf::Value::PathListOp(sdf::PathListOp::prepended([path("/A").unwrap()])),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());

        NamespaceEditor::new(&stage)
            .rename_prim(&stage.prim(path("/A").unwrap()), "B")
            .unwrap()
            .apply()
            .unwrap();

        let op = stage
            .root_layer()
            .data()
            .try_field(&path("/Other.rel").unwrap(), FieldKey::TargetPaths.as_str())
            .unwrap()
            .unwrap()
            .into_owned()
            .try_as_path_list_op()
            .unwrap();
        assert!(op.explicit_items.is_empty());
        assert_eq!(op.prepended_items, vec![path("/B").unwrap()]);
    }

    #[test]
    fn move_property_renames() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .move_property(path("/A.out").unwrap(), path("/A.renamed").unwrap())
            .apply()
            .unwrap();

        assert!(stage.has_spec(&path("/A.renamed").unwrap()).unwrap());
        assert!(!stage.has_spec(&path("/A.out").unwrap()).unwrap());
    }

    #[test]
    fn delete_property_works() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .delete_property(path("/A.out").unwrap())
            .apply()
            .unwrap();

        assert!(!stage.has_spec(&path("/A.out").unwrap()).unwrap());
    }

    #[test]
    fn batched_two_moves() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/A").unwrap(), path("/B").unwrap())
            .move_prim(path("/Keep").unwrap(), path("/Kept").unwrap());
        editor.apply().unwrap();

        assert!(valid(&stage, "/B") && valid(&stage, "/Kept"));
        assert!(!valid(&stage, "/A") && !valid(&stage, "/Keep"));
    }

    #[test]
    fn batched_delete_then_move_onto() {
        // Deleting an object then moving another onto its vacated path succeeds:
        // the destination occupancy reflects the earlier delete, not just the
        // pre-batch state.
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .delete_prim(path("/Keep").unwrap())
            .move_prim(path("/A").unwrap(), path("/Keep").unwrap());
        editor.apply().unwrap();

        assert!(valid(&stage, "/Keep") && valid(&stage, "/Keep/Child"));
        assert!(!valid(&stage, "/A"));
    }

    #[test]
    fn batched_move_then_delete() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/A").unwrap(), path("/B").unwrap())
            .delete_prim(path("/B/Child").unwrap());
        editor.apply().unwrap();

        assert!(valid(&stage, "/B"));
        assert!(!valid(&stage, "/B/Child"));
    }

    #[test]
    fn local_child_no_relocate() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .move_prim(path("/A/Child").unwrap(), path("/B").unwrap())
            .apply()
            .unwrap();

        assert!(valid(&stage, "/B"));
        assert!(!valid(&stage, "/A/Child"));
        assert!(
            stage.root_layer().relocates().is_empty(),
            "local spec move should not author relocates: {:?}",
            stage.root_layer().relocates()
        );
    }

    #[test]
    fn chained_move_then_move() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/A").unwrap(), path("/B").unwrap())
            .move_prim(path("/B").unwrap(), path("/C").unwrap());
        editor.apply().unwrap();

        assert!(valid(&stage, "/C") && valid(&stage, "/C/Child"));
        assert!(!valid(&stage, "/A") && !valid(&stage, "/B"));
        // A chained move drags the external target through both hops.
        assert_eq!(rel_targets(&stage, "/Other.rel"), vec!["/C", "/Keep"]);
    }

    #[test]
    fn fixup_across_sublayers() {
        let stage = Stage::builder().in_memory("root.usda").unwrap();
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "Xform").unwrap();
        });
        let root_id = stage.root_layer().identifier().to_string();
        stage.insert_layer(&root_id, 0, sub, LayerOffset::IDENTITY).unwrap();
        stage.define_prim("/Other").unwrap();
        stage
            .create_relationship("/Other.rel")
            .unwrap()
            .set_targets([path("/A").unwrap()])
            .unwrap();

        NamespaceEditor::new(&stage)
            .rename_prim(&stage.prim(path("/A").unwrap()), "B")
            .unwrap()
            .apply()
            .unwrap();

        assert!(valid(&stage, "/B"));
        assert!(!valid(&stage, "/A"));
        assert_eq!(rel_targets(&stage, "/Other.rel"), vec!["/B"]);
    }

    /// A root referencing `model.usda` so `/Ref/Geom` composes across the arc
    /// with no local spec — the case that needs a relocate to edit.
    fn referenced_stage() -> Stage {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
        });
        Stage::builder().make_stage(vec![root, model], 0, Vec::new())
    }

    #[test]
    fn relocate_moves_cross_arc() {
        let stage = referenced_stage();
        assert!(valid(&stage, "/Ref/Geom"));
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap())
            .apply()
            .unwrap();

        // The relocate is authored on the local layer stack...
        let relocates = stage.root_layer().relocates();
        assert!(relocates
            .iter()
            .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t == &path("/Ref/Renamed").unwrap()));
        // ...and the composed prim moves to the relocate target.
        assert!(valid(&stage, "/Ref/Renamed"));
        assert!(!valid(&stage, "/Ref/Geom"));
    }

    #[test]
    fn relocate_deletes_cross_arc() {
        let stage = referenced_stage();
        NamespaceEditor::new(&stage)
            .delete_prim(path("/Ref/Geom").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.root_layer().relocates();
        assert!(relocates
            .iter()
            .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t.is_empty()));
        assert!(!valid(&stage, "/Ref/Geom"));
    }

    #[test]
    fn rejects_composed_only_dst() {
        // `/Ref/Geom` composes across the reference with no local spec; a move
        // onto it must still collide rather than silently overlay it.
        let stage = referenced_stage();
        stage.define_prim("/Src").unwrap();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Src").unwrap(), path("/Ref/Geom").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationExists(_))
        ));
    }

    #[test]
    fn can_apply_dry_run() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/A").unwrap(), path("/B").unwrap());
        // A feasible batch checks out, and the dry run leaves the stage untouched.
        editor.can_apply().unwrap();
        assert!(valid(&stage, "/A"));
        assert!(!valid(&stage, "/B"));
        // The same editor still applies for real afterward.
        editor.apply().unwrap();
        assert!(valid(&stage, "/B"));
        assert!(!valid(&stage, "/A"));
    }

    #[test]
    fn rejects_no_edits() {
        let stage = sample();
        assert!(matches!(
            NamespaceEditor::new(&stage).can_apply(),
            Err(NamespaceEditError::NoEdits)
        ));
    }

    #[test]
    fn rejects_missing_source() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Nope").unwrap(), path("/B").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::SourceNotFound(_))));
    }

    #[test]
    fn rejects_collision() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/A").unwrap(), path("/Keep").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationExists(_))
        ));
    }

    #[test]
    fn rejects_self_descendant() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/A").unwrap(), path("/A/Inside").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationUnderSource { .. })
        ));
    }

    #[test]
    fn rejects_cross_arc_descendant() {
        let stage = referenced_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Geom/Sub").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationUnderSource { .. })
        ));
    }

    #[test]
    fn rejects_kind_mismatch() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/A").unwrap(), path("/Other.con").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::KindMismatch)));
    }

    #[test]
    fn rejects_prim_path_in_property_edit() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        // A prim path handed to a property method is rejected, not silently
        // moved as a prim subtree.
        editor.move_property(path("/A").unwrap(), path("/B").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::KindMismatch)));
    }

    #[test]
    fn rejects_property_path_in_prim_edit() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/A.out").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::KindMismatch)));
    }

    /// A stage whose root layer holds `/Prim`, and inside its `{set=sel}` variant
    /// a child `/Prim/child` (with an attribute connected to `/Prim/other.in`)
    /// and a sibling `/Prim/sibling`. The edit target is left on the variant, so
    /// a namespace edit authors at `{set=sel}` paths.
    fn variant_stage() -> Stage {
        let stage = Stage::builder().in_memory("root.usda").unwrap();
        stage.define_prim("/Prim").unwrap();
        let root = stage.root_layer().identifier().to_string();
        stage
            .set_edit_target(EditTarget::for_local_direct_variant(
                root,
                path("/Prim{set=sel}").unwrap(),
            ))
            .unwrap();
        stage.define_prim("/Prim/child").unwrap();
        stage
            .create_attribute("/Prim/child.out", "double")
            .unwrap()
            .set_connections([path("/Prim/other.in").unwrap()])
            .unwrap();
        stage.define_prim("/Prim/sibling").unwrap();
        stage
    }

    /// A variant-target rename authors at the `{set=sel}` paths: the child spec
    /// and its attribute move inside the variant, the connection target stays
    /// free of variant selections, and the variant sibling is untouched.
    #[test]
    fn variant_rename() {
        let stage = variant_stage();
        NamespaceEditor::new(&stage)
            .move_prim(path("/Prim/child").unwrap(), path("/Prim/renamed").unwrap())
            .apply()
            .unwrap();

        let layer = stage.root_layer();
        let data = layer.data();
        assert_eq!(
            data.spec_type(&path("/Prim{set=sel}renamed").unwrap()),
            Some(sdf::SpecType::Prim)
        );
        assert_eq!(
            data.spec_type(&path("/Prim{set=sel}renamed.out").unwrap()),
            Some(sdf::SpecType::Attribute)
        );
        assert!(!data.has_spec(&path("/Prim{set=sel}child").unwrap()));
        // The sibling inside the variant is left alone.
        assert_eq!(
            data.spec_type(&path("/Prim{set=sel}sibling").unwrap()),
            Some(sdf::SpecType::Prim)
        );
        // The connection target never carries a variant selection.
        let connections = data
            .try_field(
                &path("/Prim{set=sel}renamed.out").unwrap(),
                FieldKey::ConnectionPaths.as_str(),
            )
            .unwrap()
            .expect("connections authored")
            .into_owned()
            .try_as_path_list_op()
            .expect("connections are a path list op");
        assert_eq!(connections.explicit_items, vec![path("/Prim/other.in").unwrap()]);
    }

    /// A variant-target reparent moves the child subtree under another variant
    /// prim, landing at the `{set=sel}` destination.
    #[test]
    fn variant_reparent() {
        let stage = variant_stage();
        NamespaceEditor::new(&stage)
            .move_prim(path("/Prim/child").unwrap(), path("/Prim/sibling/child").unwrap())
            .apply()
            .unwrap();

        let layer = stage.root_layer();
        let data = layer.data();
        assert_eq!(
            data.spec_type(&path("/Prim{set=sel}sibling/child").unwrap()),
            Some(sdf::SpecType::Prim)
        );
        assert!(!data.has_spec(&path("/Prim{set=sel}child").unwrap()));
    }

    /// A variant-target delete removes the child spec inside the variant.
    #[test]
    fn variant_delete() {
        let stage = variant_stage();
        NamespaceEditor::new(&stage)
            .delete_prim(path("/Prim/child").unwrap())
            .apply()
            .unwrap();

        let layer = stage.root_layer();
        let data = layer.data();
        assert!(!data.has_spec(&path("/Prim{set=sel}child").unwrap()));
        assert!(!data.has_spec(&path("/Prim{set=sel}child.out").unwrap()));
        assert_eq!(
            data.spec_type(&path("/Prim{set=sel}sibling").unwrap()),
            Some(sdf::SpecType::Prim)
        );
    }

    /// A stage where `/Ref` references `model.usda`'s `/Model`, bringing in two
    /// children `/Ref/A` and `/Ref/B` with no local specs. The edit target is
    /// left on the reference arc, so a namespace edit authors into `model.usda`
    /// in the `/Model` namespace.
    fn arc_target_stage() -> Stage {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/A", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/B", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        let target = stage
            .edit_target_for_node(&path("/Ref").unwrap(), EditTargetArc::Reference)
            .unwrap();
        stage.set_edit_target(target).unwrap();
        stage
    }

    /// A cross-arc move authors the structural move into the arc source layer
    /// (not the root), and the prim composes back through the arc.
    #[test]
    fn arc_move_child() {
        let stage = arc_target_stage();
        assert!(valid(&stage, "/Ref/A"));
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/A").unwrap(), path("/Ref/Renamed").unwrap())
            .apply()
            .unwrap();

        let model = stage.layer("model.usda").expect("model layer");
        assert_eq!(
            model.data().spec_type(&path("/Model/Renamed").unwrap()),
            Some(sdf::SpecType::Prim)
        );
        assert!(!model.data().has_spec(&path("/Model/A").unwrap()));
        // The edit landed in the source layer, not the root.
        assert!(!stage.root_layer().data().has_spec(&path("/Ref/Renamed").unwrap()));
        assert!(valid(&stage, "/Ref/Renamed"));
        assert!(!valid(&stage, "/Ref/A"));
        // No relocate is authored: the move is a direct edit of the source.
        assert!(stage.root_layer().relocates().is_empty());
    }

    /// A cross-arc delete removes the spec from the arc source layer, so the prim
    /// stops composing.
    #[test]
    fn arc_delete_child() {
        let stage = arc_target_stage();
        NamespaceEditor::new(&stage)
            .delete_prim(path("/Ref/A").unwrap())
            .apply()
            .unwrap();

        let model = stage.layer("model.usda").expect("model layer");
        assert!(!model.data().has_spec(&path("/Model/A").unwrap()));
        assert!(!valid(&stage, "/Ref/A"));
        assert!(valid(&stage, "/Ref/B"));
    }

    /// A cross-arc move follows an external relationship target authored in the
    /// arc source layer: a sibling relationship to the moved prim is rewritten in
    /// the source's namespace and composes back through the arc.
    #[test]
    fn arc_move_fixes_target() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/A", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/B", Specifier::Def, "").unwrap();
            sdf::RelationshipSpec::new(e.data_mut(), "/Model/B.rel", Variability::Varying, false).unwrap();
            e.data_mut().set_field(
                &path("/Model/B.rel").unwrap(),
                FieldKey::TargetPaths.as_str(),
                sdf::Value::PathListOp(sdf::PathListOp::explicit([path("/Model/A").unwrap()])),
            );
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        let target = stage
            .edit_target_for_node(&path("/Ref").unwrap(), EditTargetArc::Reference)
            .unwrap();
        stage.set_edit_target(target).unwrap();

        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/A").unwrap(), path("/Ref/Renamed").unwrap())
            .apply()
            .unwrap();

        // The sibling relationship target follows the move, in the source layer's
        // namespace, and composes back through the arc.
        let model = stage.layer("model.usda").expect("model layer");
        let op = model
            .data()
            .try_field(&path("/Model/B.rel").unwrap(), FieldKey::TargetPaths.as_str())
            .unwrap()
            .expect("targets authored")
            .into_owned()
            .try_as_path_list_op()
            .expect("targets are a path list op");
        assert_eq!(op.explicit_items, vec![path("/Model/Renamed").unwrap()]);
        assert_eq!(rel_targets(&stage, "/Ref/B.rel"), vec!["/Ref/Renamed"]);
    }

    /// A move onto a destination occupied by another referenced child collides,
    /// detected against the arc source layer's overlay.
    #[test]
    fn arc_dest_occupied() {
        let stage = arc_target_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/A").unwrap(), path("/Ref/B").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationExists(_))
        ));
    }

    /// A move endpoint outside the arc's reach is rejected up front: the
    /// destination cannot be mapped into the arc source layer.
    #[test]
    fn mapped_outside_arc() {
        let stage = arc_target_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/A").unwrap(), path("/Elsewhere").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::Stage(StageAuthoringError::OutsideEditTarget { .. }))
        ));
    }

    /// An edit whose source composes only across a deeper arc into the source
    /// layer has no spec the mapped target can move directly, so it is rejected
    /// as needing a relocate rather than silently dropped.
    #[test]
    fn mapped_requires_relocate() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            // /Model brings in its own children across a deeper reference, so
            // they have no spec in this layer.
            e.data_mut().set_field(
                &path("/Model").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "deep.usda".into(),
                    prim_path: path("/Deep").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut deep = sdf::Layer::new_in_memory("deep.usda");
        edit_layer(&mut deep, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Deep", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Deep/Inner", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model, deep], 0, Vec::new());
        assert!(valid(&stage, "/Ref/Inner"));
        let target = stage
            .edit_target_for_node(&path("/Ref").unwrap(), EditTargetArc::Reference)
            .unwrap();
        stage.set_edit_target(target).unwrap();

        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/Inner").unwrap(), path("/Ref/Moved").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::RequiresRelocate(_))
        ));
    }

    /// A failed mapped batch leaves the arc source layer and the cache untouched:
    /// a feasible move followed by an infeasible one rolls the whole batch back.
    #[test]
    fn mapped_atomic() {
        let stage = arc_target_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/A").unwrap(), path("/Ref/Moved").unwrap())
            .move_prim(path("/Ref/Missing").unwrap(), path("/Ref/X").unwrap());
        assert!(editor.apply().is_err());

        let model = stage.layer("model.usda").expect("model layer");
        assert!(model.data().has_spec(&path("/Model/A").unwrap()));
        assert!(!model.data().has_spec(&path("/Model/Moved").unwrap()));
        assert!(valid(&stage, "/Ref/A"));
        assert!(!valid(&stage, "/Ref/Moved"));
    }

    /// A mapped batch with no edits staged is rejected the same as a local one.
    #[test]
    fn mapped_no_source() {
        let stage = arc_target_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/Missing").unwrap(), path("/Ref/X").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::SourceNotFound(_))));
    }

    /// `layers_to_edit` for a mapped target names exactly the layer it writes to.
    #[test]
    fn mapped_layers_to_edit() {
        let stage = arc_target_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/A").unwrap(), path("/Ref/Renamed").unwrap());
        assert_eq!(editor.layers_to_edit().unwrap(), vec!["model.usda".to_string()]);
    }

    /// A `/Ref` referencing `model.usda`'s `/Model`, with the root layer also
    /// authoring local overrides for the prims named in `overrides` (so each
    /// composes from both the root and the arc). The edit target is left on the
    /// reference arc, writing into `model.usda`.
    fn arc_overridden_stage(overrides: &[&str]) -> Stage {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            for name in overrides {
                sdf::PrimSpec::over(e.data_mut(), format!("/Ref/{name}").as_str()).unwrap();
            }
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/A", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        let target = stage
            .edit_target_for_node(&path("/Ref").unwrap(), EditTargetArc::Reference)
            .unwrap();
        stage.set_edit_target(target).unwrap();
        stage
    }

    /// A mapped move onto a destination occupied only by content composed from
    /// another layer (not the target's overlay) is rejected: authoring the move
    /// into the arc source would merge with the root-layer override at the
    /// destination rather than collide.
    #[test]
    fn mapped_dest_composed_elsewhere() {
        let stage = arc_overridden_stage(&["B"]);
        assert!(valid(&stage, "/Ref/B"));
        // The target layer holds no `/Model/B` spec, so only the composed-stage
        // occupancy check catches the collision.
        assert!(!stage
            .layer("model.usda")
            .unwrap()
            .data()
            .has_spec(&path("/Model/B").unwrap()));
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/A").unwrap(), path("/Ref/B").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationExists(_))
        ));
    }

    /// A mapped move of a source that composes from both the root layer and the
    /// arc is rejected: editing the arc source alone would leave the root-layer
    /// opinion behind, so a relocate would be needed to express it.
    #[test]
    fn mapped_source_multi_layer() {
        let stage = arc_overridden_stage(&["A"]);
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/A").unwrap(), path("/Ref/Renamed").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::RequiresRelocate(_))
        ));
    }

    /// A mapped delete of a source that composes from both the root layer and the
    /// arc is rejected for the same reason: deleting the arc source spec alone
    /// would leave the prim composed from the root override.
    #[test]
    fn mapped_delete_multi_layer() {
        let stage = arc_overridden_stage(&["A"]);
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/Ref/A").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::RequiresRelocate(_))
        ));
    }

    #[test]
    fn rejects_relative_path() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(sdf::Path::from("A"), path("/B").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::InvalidSource(_))));
    }

    #[test]
    fn invalid_batch_atomic() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        // A feasible move followed by an infeasible one: the batch is rejected
        // before anything is authored, so the first move never lands.
        editor
            .move_prim(path("/A").unwrap(), path("/B").unwrap())
            .move_prim(path("/Nope").unwrap(), path("/X").unwrap());
        assert!(editor.apply().is_err());
        assert!(valid(&stage, "/A"));
        assert!(!valid(&stage, "/B"));
    }

    #[test]
    fn rejects_pseudo_root() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(sdf::Path::abs_root());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::PseudoRoot)));
    }

    #[test]
    fn layers_to_edit_lists() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/A").unwrap());
        let layers = editor.layers_to_edit().unwrap();
        assert_eq!(layers, vec![stage.root_layer().identifier().to_string()]);
    }

    #[test]
    fn layers_to_edit_rejects() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/B", Specifier::Def, "").unwrap();
            e.set_relocates(vec![
                (path("/A/X").unwrap(), path("/B/Y").unwrap()),
                (path("/C/Y").unwrap(), path("/D/Y").unwrap()),
            ])
            .unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/B").unwrap(), path("/D").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
        assert!(matches!(
            editor.layers_to_edit(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }

    /// A pre-existing `(/Ref/Orig, /Ref/Geom)` relocate brings referenced content
    /// to `/Ref/Geom`; moving `/Ref/Geom -> /Ref/Final` retargets that live pair
    /// to `(/Ref/Orig, /Ref/Final)` rather than chaining, preserving the original
    /// source `/Ref/Orig`.
    #[test]
    fn relocate_fold_existing() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            // Pre-existing relocate bringing the referenced /Ref/Orig to /Ref/Geom.
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Orig", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());

        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Final").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.root_layer().relocates();
        // Moving the live target /Ref/Geom retargets the existing pair to
        // (/Ref/Orig, /Ref/Final); the original source /Ref/Orig is preserved and
        // no transient (/Ref/Geom, /Ref/Final) pair is authored.
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Orig").unwrap() && t == &path("/Ref/Final").unwrap()),
            "expected (/Ref/Orig, /Ref/Final) in {relocates:?}"
        );
        assert!(
            !relocates.iter().any(|(s, _)| s == &path("/Ref/Geom").unwrap()),
            "transient /Ref/Geom source must be dropped: {relocates:?}"
        );
        let targets: Vec<_> = relocates
            .iter()
            .filter(|(_, t)| !t.is_empty())
            .map(|(_, t)| t)
            .collect();
        assert_eq!(
            targets.len(),
            targets.iter().collect::<HashSet<_>>().len(),
            "duplicate destinations: {relocates:?}"
        );
    }

    /// A pre-existing relocate whose destination is a child of a deleted cross-arc
    /// prim collapses to the delete sentinel — its target re-roots onto the empty
    /// path rather than becoming a truncated path like `/Sub`.
    #[test]
    fn fold_delete_child() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            // Pre-existing relocate with a child of /Ref/Geom as its destination.
            e.set_relocates(vec![(path("/Ref/B").unwrap(), path("/Ref/Geom/Sub").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom/Sub", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());

        NamespaceEditor::new(&stage)
            .delete_prim(path("/Ref/Geom").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.root_layer().relocates();
        // Deleting /Ref/Geom re-roots (/Ref/B, /Ref/Geom/Sub) onto the sentinel.
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/B").unwrap() && t.is_empty()),
            "expected (/Ref/B, '') in {relocates:?}"
        );
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t.is_empty()),
            "expected (/Ref/Geom, '') in {relocates:?}"
        );
    }

    /// Move a cross-arc prim then delete it in the same batch: the second edit
    /// must also produce a relocate.
    #[test]
    fn chain_move_delete() {
        let stage = referenced_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap())
            .delete_prim(path("/Ref/Renamed").unwrap());
        editor.apply().unwrap();

        let relocates = stage.root_layer().relocates();
        // The chain collapses to a single delete on the original cross-arc
        // source: (/Ref/Geom, '').
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t.is_empty()),
            "expected (/Ref/Geom, '') in {relocates:?}"
        );
        assert!(!valid(&stage, "/Ref/Geom"));
        assert!(!valid(&stage, "/Ref/Renamed"));
    }

    /// Move a cross-arc prim, then move the result again in the same batch:
    /// both edits must produce relocates, and the first must be folded through
    /// the second so the list contains no chain.
    #[test]
    fn chain_two_moves() {
        let stage = referenced_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap())
            .move_prim(path("/Ref/Renamed").unwrap(), path("/Ref/Final").unwrap());
        editor.apply().unwrap();

        let relocates = stage.root_layer().relocates();
        // The two-hop chain collapses into a single pair targeting the final
        // destination: (/Ref/Geom, /Ref/Final).
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t == &path("/Ref/Final").unwrap()),
            "expected (/Ref/Geom, /Ref/Final) in {relocates:?}"
        );
        // No path appears as both a source and a target (no chains).
        let sources: HashSet<_> = relocates.iter().map(|(s, _)| s).collect();
        let targets: HashSet<_> = relocates.iter().map(|(_, t)| t).collect();
        assert!(
            sources.intersection(&targets).next().is_none(),
            "chain found in {relocates:?}"
        );
        assert!(valid(&stage, "/Ref/Final"));
        assert!(!valid(&stage, "/Ref/Geom"));
        assert!(!valid(&stage, "/Ref/Renamed"));
    }

    /// A delete that targets a path only produced by a *later* edit in the
    /// same batch is rejected: the earlier edit must not be validated against
    /// a path that does not yet exist when it runs.
    #[test]
    fn rejects_premature_delete() {
        // edit 0: Delete(/Ref/Renamed) — /Ref/Renamed does not exist yet
        // edit 1: Move(/Ref/Geom → /Ref/Renamed) — would have created it
        let stage = referenced_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .delete_prim(path("/Ref/Renamed").unwrap())
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::SourceNotFound(_))));
    }

    /// Two separate applies form a chain across an already-authored relocate:
    /// move `/Ref/Geom → /Ref/Renamed`, commit, then move `/Ref/Renamed →
    /// /Ref/Final`. The second batch must fold through the committed pair onto
    /// the genuine origin `/Ref/Geom`, not keep the transient `/Ref/Renamed`
    /// source, so the prim ends up composed at `/Ref/Final`.
    #[test]
    fn relocate_fold_sequential() {
        let stage = referenced_stage();
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap())
            .apply()
            .unwrap();
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Renamed").unwrap(), path("/Ref/Final").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.root_layer().relocates();
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t == &path("/Ref/Final").unwrap()),
            "expected (/Ref/Geom, /Ref/Final) in {relocates:?}"
        );
        assert!(
            !relocates.iter().any(|(s, _)| s == &path("/Ref/Renamed").unwrap()),
            "transient /Ref/Renamed source must be dropped: {relocates:?}"
        );
        assert!(valid(&stage, "/Ref/Final"));
        assert!(!valid(&stage, "/Ref/Geom"));
        assert!(!valid(&stage, "/Ref/Renamed"));
    }

    /// Move a cross-arc prim, then in the same batch move a descendant that
    /// only exists under the relocated subtree: the descendant has no local
    /// spec, so it must be recognized as cross-arc and earn its own relocate
    /// authored in the relocated parent's namespace.
    #[test]
    fn chain_move_descendant() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom/Sub", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());

        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap())
            .move_prim(path("/Ref/Renamed/Sub").unwrap(), path("/Ref/Renamed/Sub2").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.root_layer().relocates();
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Renamed/Sub").unwrap() && t == &path("/Ref/Renamed/Sub2").unwrap()),
            "expected (/Ref/Renamed/Sub, /Ref/Renamed/Sub2) in {relocates:?}"
        );
        assert!(valid(&stage, "/Ref/Renamed/Sub2"));
        assert!(!valid(&stage, "/Ref/Renamed/Sub"));
        assert!(!valid(&stage, "/Ref/Geom"));
    }

    /// A later move whose source descends from a moved cross-arc root but names
    /// no real prim (a typo under the relocated subtree) is rejected as
    /// `SourceNotFound` rather than gaining a phantom relocate.
    #[test]
    fn rejects_missing_descendant() {
        let stage = referenced_stage(); // /Ref/Geom has no children
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap())
            .move_prim(
                path("/Ref/Renamed/Missing").unwrap(),
                path("/Ref/Renamed/Other").unwrap(),
            );
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::SourceNotFound(_))));
    }

    /// A property under a moved cross-arc root cannot be relocated (relocates
    /// are prim-only), so a cross-arc property move is rejected and authors no
    /// relocate.
    #[test]
    fn rejects_property_descendant() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
            sdf::AttributeSpec::new(e.data_mut(), "/Model/Geom.attr", "double", Variability::Varying, false).unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Renamed").unwrap())
            .move_property(path("/Ref/Renamed.attr").unwrap(), path("/Ref/Renamed.attr2").unwrap());
        assert!(matches!(editor.can_apply(), Err(NamespaceEditError::SourceNotFound(_))));
        assert!(
            !stage.root_layer().relocates().iter().any(|(s, _)| s.is_property_path()),
            "no property relocate must be authored"
        );
    }

    fn nested_ref_stage(children: &[&str]) -> Stage {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
            for c in children {
                sdf::PrimSpec::new(e.data_mut(), format!("/Model/Geom/{c}").as_str(), Specifier::Def, "").unwrap();
            }
        });
        Stage::builder().make_stage(vec![root, model], 0, Vec::new())
    }

    /// Moving a descendant onto a destination occupied by a referenced sibling
    /// inside a relocated subtree collides: `/A/Other` composes from the moved
    /// `/Ref/Geom/Other`, so the second move must report `DestinationExists`.
    #[test]
    fn occupied_in_relocated() {
        let stage = nested_ref_stage(&["Sub", "Other"]);
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/A").unwrap())
            .move_prim(path("/A/Sub").unwrap(), path("/A/Other").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationExists(_))
        ));
    }

    /// After a child is relocated out of a cross-arc subtree, moving the parent
    /// root again must carry the child's relocate source with it: move
    /// `/Ref/Geom -> /A`, `/A/Sub -> /B`, then `/A -> /C` leaves the child pair
    /// sourced at `/C/Sub`, so `/B` is still created.
    #[test]
    fn child_source_follows_parent() {
        let stage = nested_ref_stage(&["Sub"]);
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/A").unwrap())
            .move_prim(path("/A/Sub").unwrap(), path("/B").unwrap())
            .move_prim(path("/A").unwrap(), path("/C").unwrap());
        editor.apply().unwrap();

        let relocates = stage.root_layer().relocates();
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/C/Sub").unwrap() && t == &path("/B").unwrap()),
            "expected (/C/Sub, /B) in {relocates:?}"
        );
        assert!(valid(&stage, "/C"));
        assert!(valid(&stage, "/B"));
        assert!(!valid(&stage, "/A"));
        assert!(!valid(&stage, "/C/Sub"));
    }

    /// Deleting a cross-arc parent after a descendant was relocated out of it
    /// cannot be represented: preserving `/B` would need a child relocate source
    /// under the deleted parent source, which Pcp rejects. The batch must fail
    /// explicitly rather than author a dead `(/A/Sub, /B)` pair that silently
    /// drops `/B`.
    #[test]
    fn delete_orphans_moved_child() {
        let stage = nested_ref_stage(&["Sub"]);
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/A").unwrap())
            .move_prim(path("/A/Sub").unwrap(), path("/B").unwrap())
            .delete_prim(path("/A").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }

    /// A destination vacated by earlier moves is free for a later move. With
    /// `move /Ref/A -> /Ref/B`, `move /Ref/B -> /Ref/C`, then `move /Ref/X ->
    /// /Ref/B`, the slot `/Ref/B` is transient (its occupant moved on to
    /// `/Ref/C`), so the third move must succeed rather than report
    /// `DestinationExists` just because `/Ref/B` held composed content earlier in
    /// the batch. The relocates collapse to the chain-free `(/Ref/A, /Ref/C)` and
    /// `(/Ref/X, /Ref/B)`.
    #[test]
    fn move_into_vacated_dst() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/A", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/X", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());

        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/A").unwrap(), path("/Ref/B").unwrap())
            .move_prim(path("/Ref/B").unwrap(), path("/Ref/C").unwrap())
            .move_prim(path("/Ref/X").unwrap(), path("/Ref/B").unwrap());
        editor.apply().unwrap();

        assert!(valid(&stage, "/Ref/C"));
        assert!(valid(&stage, "/Ref/B"));
        assert!(!valid(&stage, "/Ref/A"));
        assert!(!valid(&stage, "/Ref/X"));
    }

    /// Renaming a prim that carries its own reference moves the local spec (which
    /// carries the arc); the reference is rooted at the prim itself, not an
    /// ancestor, so no relocate is needed and the rename is not rejected.
    #[test]
    fn rename_referenced_prim() {
        let stage = referenced_stage();
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref").unwrap(), path("/Ref2").unwrap())
            .apply()
            .unwrap();
        assert!(valid(&stage, "/Ref2/Geom"));
        assert!(!valid(&stage, "/Ref"));
        assert!(
            stage.root_layer().relocates().is_empty(),
            "rename should author no relocate"
        );
    }

    /// Moving a property onto a destination occupied only by a referenced
    /// composed property collides: `/Ref.attr` composes from `/Model.attr`, so
    /// the move must report `DestinationExists` rather than overlay it.
    #[test]
    fn move_onto_composed_property() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Src", Specifier::Def, "").unwrap();
            sdf::AttributeSpec::new(e.data_mut(), "/Src.attr", "double", Variability::Varying, false).unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::AttributeSpec::new(e.data_mut(), "/Model.attr", "double", Variability::Varying, false).unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        // /Ref.attr composes from the referenced /Model.attr (no local spec).
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_property(path("/Src.attr").unwrap(), path("/Ref.attr").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::DestinationExists(_))
        ));
    }

    /// Moving an already-relocated prim back to its original source folds the
    /// relocate to a no-op; the edit-target metadata must be cleared rather than
    /// left holding the stale pair.
    #[test]
    fn fold_relocate_to_empty() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Orig", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        assert!(valid(&stage, "/Ref/Geom"));
        // Move the relocated prim back to its original source: the relocate folds
        // to a no-op and the metadata must be cleared.
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Orig").unwrap())
            .apply()
            .unwrap();
        let relocates = stage.root_layer().relocates();
        assert!(relocates.is_empty(), "stale relocate left authored: {relocates:?}");
        assert!(valid(&stage, "/Ref/Orig"), "prim should be back at /Ref/Orig");
        assert!(!valid(&stage, "/Ref/Geom"), "prim should no longer be at /Ref/Geom");
    }

    /// A purely local move of a prim that hosts a relocate target carries the
    /// relocate with it: with `(/Ref/Geom, /Local/Geom)` authored, moving the
    /// local `/Local` to `/Moved` retargets the relocate to `(/Ref/Geom,
    /// /Moved/Geom)` so the relocated prim follows the namespace edit.
    #[test]
    fn local_retarget_relocate() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Local", Specifier::Def, "").unwrap();
            // /Ref/Geom is relocated under the local prim /Local.
            e.set_relocates(vec![(path("/Ref/Geom").unwrap(), path("/Local/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        assert!(valid(&stage, "/Local/Geom"));
        // A purely local move of /Local must carry the relocate target with it.
        NamespaceEditor::new(&stage)
            .move_prim(path("/Local").unwrap(), path("/Moved").unwrap())
            .apply()
            .unwrap();
        let relocates = stage.root_layer().relocates();
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t == &path("/Moved/Geom").unwrap()),
            "relocate target should follow the local move: {relocates:?}"
        );
        assert!(
            valid(&stage, "/Moved/Geom"),
            "relocated prim should follow to /Moved/Geom"
        );
        assert!(!valid(&stage, "/Local/Geom"));
    }

    /// A purely local rename that neither creates nor changes a relocate must
    /// succeed even when the layer already holds a structurally-invalid relocate
    /// that Pcp drops as a recoverable error; the batch is not blamed for the
    /// pre-existing pair.
    #[test]
    fn local_keeps_invalid() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Local", Specifier::Def, "").unwrap();
            // A pre-existing structurally-invalid relocate (root-prim source) that
            // Pcp drops as a recoverable error. The batch below does not touch it.
            e.set_relocates(vec![(path("/B").unwrap(), path("/C").unwrap())])
                .unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        NamespaceEditor::new(&stage)
            .move_prim(path("/Local").unwrap(), path("/Moved").unwrap())
            .apply()
            .unwrap();
        assert!(valid(&stage, "/Moved"));
        assert!(!valid(&stage, "/Local"));
    }

    #[test]
    fn invalid_seed_resurrection() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/A/X", Specifier::Def, "").unwrap();
            e.set_relocates(vec![(path("/A/X").unwrap(), path("/A").unwrap())])
                .unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/A").unwrap(), path("/C").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
        assert!(valid(&stage, "/A"));
        assert!(!valid(&stage, "/C"));
        assert_eq!(
            stage.root_layer().relocates(),
            vec![(path("/A/X").unwrap(), path("/A").unwrap())]
        );
    }

    /// A relocate authored on a sublayer (not the edit target) folds with a move
    /// of the relocated prim: moving `/Ref/Geom` to `/Ref/Final` lets fixup
    /// remap the sublayer pair to `(/Ref/Orig, /Ref/Final)` and authors no
    /// conflicting duplicate on the root, so the prim ends up at `/Ref/Final`.
    #[test]
    fn relocate_in_sublayer_folds() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.data_mut().set_field(
                &sdf::Path::abs_root(),
                FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".into()]),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            // The relocate lives on the sublayer, not the edit target (root).
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Orig", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, sub, model], 0, Vec::new());
        assert!(valid(&stage, "/Ref/Geom"), "sublayer relocate should compose");
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Final").unwrap())
            .apply()
            .unwrap();
        assert!(valid(&stage, "/Ref/Final"), "relocated prim should move to /Ref/Final");
        assert!(!valid(&stage, "/Ref/Geom"));
        // No conflicting duplicate authored on the root edit target.
        assert!(
            stage.root_layer().relocates().is_empty(),
            "root should author no relocate: {:?}",
            stage.root_layer().relocates()
        );
    }

    /// The synthesized relocate must be validated against the whole local stack,
    /// not the edit target alone: a sublayer pair `(/Ref/C, /Ref/D)` makes the
    /// new root pair `(/Ref/X, /Ref/C)` a target-is-source chain that Pcp drops,
    /// so the batch is rejected rather than silently failing to compose.
    #[test]
    fn rejects_cross_layer_conflict() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.data_mut().set_field(
                &sdf::Path::abs_root(),
                FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".into()]),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            e.set_relocates(vec![(path("/Ref/C").unwrap(), path("/Ref/D").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/X", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, sub, model], 0, Vec::new());
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/X").unwrap(), path("/Ref/C").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }

    /// A structurally-invalid pre-existing relocate is dropped by Pcp before
    /// conflict detection, so it must not block a newly synthesized pair: with an
    /// invalid `(/B, /C)` authored, moving referenced `/Ref/X` to `/B` (whose
    /// target coincides with the invalid pair's source) still succeeds.
    #[test]
    fn new_ignores_invalid() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            // Invalid: a root prim cannot be a relocate source. Pcp drops it.
            e.set_relocates(vec![(path("/B").unwrap(), path("/C").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/X", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/X").unwrap(), path("/B").unwrap())
            .apply()
            .unwrap();
        assert!(valid(&stage, "/B"));
        assert!(!valid(&stage, "/Ref/X"));
    }

    /// A structurally-invalid seed relocate is metadata only: Pcp ignores it, so
    /// the namespace editor must not evolve it as a live relocate even when its
    /// target overlaps the edited path. Moving the referenced `/Ref/Geom` authors
    /// a new valid pair and leaves the invalid old pair unchanged.
    #[test]
    fn invalid_seed_stays_inert() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            e.set_relocates(vec![(path("/A").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Final").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.root_layer().relocates();
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/A").unwrap() && t == &path("/Ref/Geom").unwrap()),
            "invalid old pair should remain unchanged: {relocates:?}"
        );
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t == &path("/Final").unwrap()),
            "valid move pair should be authored: {relocates:?}"
        );
        assert!(valid(&stage, "/Final"));
        assert!(!valid(&stage, "/Ref/Geom"));
    }

    /// A pre-existing relocate dropped only by a conflict must follow namespace
    /// moves with the conflicting pair. If it stayed at the old target while the
    /// conflicting pair moved away, Pcp would start applying it and hide
    /// `/Other/X`.
    #[test]
    fn inactive_conflict_reprojects() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/World", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Other", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Other/X", Specifier::Def, "").unwrap();
            e.set_relocates(vec![
                (path("/World/A").unwrap(), path("/World/C").unwrap()),
                (path("/Other/X").unwrap(), path("/World/A/B").unwrap()),
            ])
            .unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        assert!(valid(&stage, "/Other/X"));

        NamespaceEditor::new(&stage)
            .move_prim(path("/World").unwrap(), path("/Scene").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.root_layer().relocates();
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Scene/A").unwrap() && t == &path("/Scene/C").unwrap()),
            "conflicting pair target should follow /World -> /Scene: {relocates:?}"
        );
        assert!(
            relocates
                .iter()
                .any(|(s, t)| s == &path("/Other/X").unwrap() && t == &path("/Scene/A/B").unwrap()),
            "dropped pair target should follow /World -> /Scene: {relocates:?}"
        );
        assert!(valid(&stage, "/Other/X"));
    }

    /// A weaker duplicate-source relocate is ignored by Pcp extraction. Its
    /// target must not make a cross-arc move look like a continuation of a live
    /// relocate; the move still needs its own pair.
    #[test]
    fn duplicate_source_inert() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.data_mut().set_field(
                &sdf::Path::abs_root(),
                FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".into()]),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Strong").unwrap())])
                .unwrap();
        });
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Orig", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, sub, model], 0, Vec::new());
        assert!(valid(&stage, "/Ref/Strong"));
        assert!(valid(&stage, "/Ref/Geom"));

        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref/Geom").unwrap(), path("/Final").unwrap())
            .apply()
            .unwrap();

        let root_relocates = stage.root_layer().relocates();
        assert!(
            root_relocates
                .iter()
                .any(|(s, t)| s == &path("/Ref/Geom").unwrap() && t == &path("/Final").unwrap()),
            "move pair should be authored: {root_relocates:?}"
        );
        assert!(valid(&stage, "/Final"));
        assert!(!valid(&stage, "/Ref/Geom"));
    }

    /// Fresh relocates authored on a stronger edit target must validate at that
    /// layer's strength, ahead of weaker sublayer pairs with the same source.
    #[test]
    fn edit_target_strength() {
        let root = pcp::LayerId::from_raw(0);
        let sub = pcp::LayerId::from_raw(1);
        let source = path("/Ref/X").unwrap();
        let weak_target = path("/Ref/T").unwrap();
        let move_target = path("/Final").unwrap();
        let mut seeds = HashMap::new();
        seeds.insert(sub, vec![(source.clone(), weak_target.clone())]);

        let mut move_plan = RelocateStackPlan::new(&[root, sub], &seeds, root);
        move_plan.record_move(&source, &move_target, true).unwrap();
        let combined = move_plan.combined();
        assert_eq!(combined[0].pair, (source.clone(), move_target));
        assert!(combined[0].fresh);
        let pairs: sdf::RelocateList = combined.iter().map(|r| r.pair.clone()).collect();
        let status = pcp::analyze_relocate_occurrences(&pairs);
        assert_eq!(pcp::first_unrepresentable_relocate(&combined, &status), None);

        let mut delete_plan = RelocateStackPlan::new(&[root, sub], &seeds, root);
        delete_plan.record_delete(&source, true).unwrap();
        let combined = delete_plan.combined();
        assert_eq!(combined[0].pair, (source, sdf::Path::default()));
        assert!(combined[0].fresh);
        let pairs: sdf::RelocateList = combined.iter().map(|r| r.pair.clone()).collect();
        let status = pcp::analyze_relocate_occurrences(&pairs);
        assert_eq!(pcp::first_unrepresentable_relocate(&combined, &status), None);
    }

    #[test]
    fn rejects_deleted_source() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Local", Specifier::Def, "").unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom/Sub", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());

        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/A").unwrap())
            .delete_prim(path("/A/Sub").unwrap())
            .move_prim(path("/Local").unwrap(), path("/A/Sub").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
        assert!(valid(&stage, "/Local"));
        assert!(!valid(&stage, "/A"));
    }

    /// Deleting a prim relocated by a sublayer empties that sublayer pair (its
    /// target collapses to the delete sentinel) so the prim stops composing,
    /// rather than leaving the pair pointing at a now-deleted path.
    #[test]
    fn delete_sublayer_relocate_target() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.data_mut().set_field(
                &sdf::Path::abs_root(),
                FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".into()]),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Orig", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, sub, model], 0, Vec::new());
        assert!(valid(&stage, "/Ref/Geom"));
        NamespaceEditor::new(&stage)
            .delete_prim(path("/Ref/Geom").unwrap())
            .apply()
            .unwrap();
        assert!(
            !valid(&stage, "/Ref/Geom"),
            "deleted relocated prim should no longer compose"
        );
    }

    fn sublayer_relocate_stage(relocate: (&str, &str), model_children: &[&str]) -> Stage {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.data_mut().set_field(
                &sdf::Path::abs_root(),
                FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".into()]),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Local", Specifier::Def, "").unwrap();
        });
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            e.set_relocates(vec![(path(relocate.0).unwrap(), path(relocate.1).unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            for c in model_children {
                sdf::PrimSpec::new(e.data_mut(), format!("/Model/{c}").as_str(), Specifier::Def, "").unwrap();
            }
        });
        Stage::builder().make_stage(vec![root, sub, model], 0, Vec::new())
    }

    /// Deleting a prim whose relocated child (described by a sublayer pair) was
    /// moved out of the deleted subtree earlier in the batch is rejected, like
    /// the edit-target orphan case: no valid relocate set keeps the moved child
    /// while deleting its parent.
    #[test]
    fn delete_orphans_sublayer_child() {
        let stage = sublayer_relocate_stage(("/Ref/Orig", "/Ref/Geom"), &["Orig"]);
        assert!(valid(&stage, "/Ref/Geom"));
        let mut editor = NamespaceEditor::new(&stage);
        editor
            .move_prim(path("/Ref/Geom").unwrap(), path("/B").unwrap())
            .delete_prim(path("/Ref").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }

    /// A relocate target on a sublayer that an earlier edit moved is recognized
    /// by a later edit: moving local `/Local -> /Moved` carries the sublayer pair
    /// `(/Ref/Orig, /Local/Geom)` to `/Moved/Geom`, and the subsequent move of
    /// `/Moved/Geom -> /Final` retargets that same pair instead of synthesizing a
    /// conflicting duplicate.
    #[test]
    fn sublayer_target_reprojects() {
        let stage = sublayer_relocate_stage(("/Ref/Orig", "/Local/Geom"), &["Orig"]);
        assert!(valid(&stage, "/Local/Geom"));
        NamespaceEditor::new(&stage)
            .move_prim(path("/Local").unwrap(), path("/Moved").unwrap())
            .move_prim(path("/Moved/Geom").unwrap(), path("/Final").unwrap())
            .apply()
            .unwrap();
        assert!(valid(&stage, "/Final"));
        assert!(!valid(&stage, "/Moved/Geom"));
    }

    /// Renaming a prim that owns a subroot reference (`@model@</Model/Geom>`)
    /// moves the local spec that carries the reference; the arc is authored at
    /// the prim itself, so no relocate is needed and the rename is not rejected.
    #[test]
    fn rename_subroot_referenced_prim() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model/Geom").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "Xform").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        NamespaceEditor::new(&stage)
            .move_prim(path("/Ref").unwrap(), path("/Ref2").unwrap())
            .apply()
            .unwrap();
        assert!(valid(&stage, "/Ref2"));
        assert!(!valid(&stage, "/Ref"));
        assert!(
            stage.root_layer().relocates().is_empty(),
            "rename should author no relocate"
        );
    }

    /// Spec-level `relocates` metadata is ordinary embedded-path data (it is not
    /// owned by the relocate stack plan, which handles only layer-level
    /// `layerRelocates`), so moving the prim that holds it reprojects its paths
    /// like any other field.
    #[test]
    fn move_reprojects_spec_relocates() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/A").unwrap(),
                FieldKey::Relocates.as_str(),
                sdf::Value::Relocates(vec![(path("/A/X").unwrap(), path("/A/Y").unwrap())]),
            );
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        NamespaceEditor::new(&stage)
            .move_prim(path("/A").unwrap(), path("/Moved").unwrap())
            .apply()
            .unwrap();

        let value = stage
            .root_layer()
            .data()
            .try_field(&path("/Moved").unwrap(), FieldKey::Relocates.as_str())
            .unwrap()
            .expect("spec-level relocates should move with the prim")
            .into_owned();
        let relocates = value.try_as_relocates().expect("relocates value");
        assert_eq!(
            relocates,
            vec![(path("/Moved/X").unwrap(), path("/Moved/Y").unwrap())],
            "spec-level relocate paths should reproject onto the moved prim"
        );
    }

    /// A pre-existing relocate the batch does not touch is left as authored, even
    /// a structurally-invalid no-op `source == target`: an unrelated local move
    /// must not rewrite a layer's existing relocate metadata away.
    #[test]
    fn untouched_noop_relocate_preserved() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "").unwrap();
            e.set_relocates(vec![(path("/X/Keep").unwrap(), path("/X/Keep").unwrap())])
                .unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        NamespaceEditor::new(&stage)
            .move_prim(path("/A").unwrap(), path("/Moved").unwrap())
            .apply()
            .unwrap();
        assert!(
            stage
                .root_layer()
                .relocates()
                .iter()
                .any(|(s, t)| s == &path("/X/Keep").unwrap() && t == &path("/X/Keep").unwrap()),
            "untouched no-op relocate must be preserved: {:?}",
            stage.root_layer().relocates()
        );
    }

    #[test]
    fn moved_noop_preserved() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/A/X", Specifier::Def, "").unwrap();
            e.set_relocates(vec![(path("/A/X").unwrap(), path("/A/X").unwrap())])
                .unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        NamespaceEditor::new(&stage)
            .move_prim(path("/A").unwrap(), path("/B").unwrap())
            .apply()
            .unwrap();
        assert_eq!(
            stage.root_layer().relocates(),
            vec![(path("/B/X").unwrap(), path("/B/X").unwrap())],
            "moved no-op relocate metadata follows the namespace edit"
        );
    }

    /// A layer included more than once in the root stack has one authored
    /// relocate list. Seeding the relocate plan must not duplicate that layer's
    /// entries and write doubled metadata during an unrelated edit.
    #[test]
    fn duplicate_sublayer_seed() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.data_mut().set_field(
                &sdf::Path::abs_root(),
                FieldKey::SubLayers.as_str(),
                sdf::Value::StringVec(vec!["sub.usda".into(), "sub.usda".into()]),
            );
            sdf::PrimSpec::new(e.data_mut(), "/A", Specifier::Def, "").unwrap();
        });
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, sub], 0, Vec::new());

        NamespaceEditor::new(&stage)
            .move_prim(path("/A").unwrap(), path("/Moved").unwrap())
            .apply()
            .unwrap();

        let relocates = stage.layer("sub.usda").expect("sub layer").relocates();
        assert_eq!(
            relocates,
            vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())],
            "unrelated edit must not duplicate repeated sublayer relocates"
        );
    }

    /// `layers_to_edit` reports a sublayer whose relocate the batch would rewrite:
    /// moving a prim relocated by `sub.usda` mutates that sublayer, even though no
    /// source spec lives there, so the preflight must name it.
    #[test]
    fn layers_to_edit_relocates() {
        let stage = sublayer_relocate_stage(("/Ref/Orig", "/Ref/Geom"), &["Orig"]);
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/Geom").unwrap(), path("/Ref/Final").unwrap());
        let layers = editor.layers_to_edit().unwrap();
        assert!(
            layers.iter().any(|id| id == "sub.usda"),
            "sublayer whose relocate is rewritten should be reported: {layers:?}"
        );
    }

    fn relocate_target_masking_stage() -> Stage {
        // /Ref references a model with BOTH Orig and Geom; a relocate
        // /Ref/Orig -> /Ref/Geom puts Orig's content at /Ref/Geom, masking the
        // referenced /Ref/Geom.
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            e.set_relocates(vec![(path("/Ref/Orig").unwrap(), path("/Ref/Geom").unwrap())])
                .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Orig", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
        });
        Stage::builder().make_stage(vec![root, model], 0, Vec::new())
    }

    /// Moving a relocate target that masks its own referenced content is
    /// rejected: retargeting the relocate would reveal the masked `/Ref/Geom`,
    /// so the move cannot be cleanly expressed and must not silently leave both
    /// `/Final` and `/Ref/Geom` composed.
    #[test]
    fn rejects_masking_move() {
        let stage = relocate_target_masking_stage();
        assert!(valid(&stage, "/Ref/Geom"));
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/Geom").unwrap(), path("/Final").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }

    /// Deleting a relocate target that masks its own referenced content is
    /// rejected for the same reason: emptying the relocate would reveal the
    /// masked `/Ref/Geom` rather than removing it.
    #[test]
    fn rejects_masking_delete() {
        let stage = relocate_target_masking_stage();
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/Ref/Geom").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }

    /// /Ref references a model with Geom, A, B; the root authors two relocates
    /// onto the same target (/Ref/A -> /Ref/Geom, /Ref/B -> /Ref/Geom), so both
    /// are conflict-dropped and /Ref/Geom composes directly from the reference.
    /// Moving /Ref/Geom would author /Ref/Geom -> /Dst, whose source is the target
    /// of those dropped relocates; Pcp would drop the fresh pair too, so the batch
    /// is rejected.
    #[test]
    fn rejects_dropped_conflict() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            e.set_relocates(vec![
                (path("/Ref/A").unwrap(), path("/Ref/Geom").unwrap()),
                (path("/Ref/B").unwrap(), path("/Ref/Geom").unwrap()),
            ])
            .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/A", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/B", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        assert!(valid(&stage, "/Ref/Geom"));
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/Ref/Geom").unwrap(), path("/Dst").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }

    /// The root authors a target-is-source chain (/Ref/X -> /Ref/Geom, /Ref/Geom
    /// -> /Ref/Y); both are conflict-dropped and /Ref/Geom composes directly.
    /// Deleting /Ref/Geom cannot be represented: the deletion pair (/Ref/Geom,'')
    /// is a duplicate source of the inert (/Ref/Geom,/Ref/Y) and source-is-target
    /// with (/Ref/X,/Ref/Geom), so it would be dropped — the batch is rejected
    /// rather than silently leaving /Ref/Geom composed.
    #[test]
    fn delete_over_dropped_chain() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &path("/Ref").unwrap(),
                FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "model.usda".into(),
                    prim_path: path("/Model").unwrap(),
                    ..Default::default()
                }])),
            );
            e.set_relocates(vec![
                (path("/Ref/X").unwrap(), path("/Ref/Geom").unwrap()),
                (path("/Ref/Geom").unwrap(), path("/Ref/Y").unwrap()),
            ])
            .unwrap();
        });
        let mut model = sdf::Layer::new_in_memory("model.usda");
        edit_layer(&mut model, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/Model/X", Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, model], 0, Vec::new());
        assert!(valid(&stage, "/Ref/Geom"));
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/Ref/Geom").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::UnrepresentableRelocateBatch(_))
        ));
    }
}
