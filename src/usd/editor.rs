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
//! This falls out of the atomic copy-on-write
//! [`Transaction`](crate::sdf::Transaction): structural ops stage in an overlay
//! whose reads already reflect the prior edits.
//!
//! Edits author across the whole local layer stack of the current edit target,
//! as C++ does. The structural move is [`copy_spec_within`](crate::sdf::copy_spec_within)
//! plus [`Layer::remove_spec`](crate::sdf::Layer::remove_spec); the fixup remaps
//! embedded paths in place through [`Value::filter_map_paths`](crate::sdf::Value::filter_map_paths),
//! preserving list-op structure rather than flattening opinions.

use std::collections::HashSet;

use super::{Prim, Stage, StageAuthoringError};
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

    /// The current edit target is not a local (root layer stack) layer with an
    /// identity mapping. Namespace editing authors verbatim into the local layer
    /// stack, so a variant or cross-arc edit target is not supported.
    #[error("namespace editing requires a local edit target (variant and cross-arc targets are unsupported)")]
    NonLocalEditTarget,

    /// A composed-stage query needed to validate or apply an edit failed.
    #[error(transparent)]
    Composition(#[from] anyhow::Error),

    /// Authoring the edit onto a layer failed.
    #[error(transparent)]
    Stage(#[from] StageAuthoringError),
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
    /// The whole batch is transactional: a [`Transaction`](sdf::Transaction)
    /// opens on each affected layer, the edits stage into all of them in order,
    /// and the transactions commit only once every layer has authored cleanly.
    /// An authoring error rolls every layer back, so a failed apply leaves the
    /// stage exactly as it was. This atomicity is only against authoring errors,
    /// not a database-style guarantee: a layer's backing
    /// [`AbstractData`](sdf::AbstractData) can be any implementation (an
    /// in-memory store, `CrateData`, a custom backend), and committing a staged
    /// edit into it is not assumed to itself be atomic or recoverable.
    ///
    /// When the batch touches more than one layer, the single
    /// [`ObjectsChanged`](super::Notice::ObjectsChanged) notice merges the
    /// per-layer change records and attributes them to the strongest edited
    /// layer. Composed-path reporting is exact, but a listener that reads the raw
    /// change list per layer — notably [`Stage::extract_diff`](super::Stage::extract_diff) —
    /// cannot recover which layer each record landed in, so diff replication of a
    /// multi-layer namespace edit is not supported yet.
    pub fn apply(&mut self) -> Result<(), NamespaceEditError> {
        self.execute(true)?;
        self.edits.clear();
        Ok(())
    }

    /// Stage the batch onto the local layer stack in one atomic multi-layer
    /// transaction. Open a [`Transaction`](sdf::Transaction) on each layer, then
    /// apply the edits in order: each is validated against the staged state the
    /// prior edits produced — the transactions already reflect them, so a
    /// collision or missing source is read from the precise staged data, not a
    /// simulated projection — and staged into every layer. After the structural
    /// edits, embedded paths are remapped and relocates authored. Then the
    /// transactions either commit together (driving one composition-invalidation
    /// cycle) or — when `commit` is false — roll back for a dry run. The shared
    /// path behind [`can_apply`](Self::can_apply) and [`apply`](Self::apply).
    ///
    /// Any failure — an invalid edit or an authoring error — returns, dropping the
    /// still-open transactions and rolling every layer back, so a failed batch
    /// leaves the stage untouched and the cache valid. A dry run runs this same
    /// path, so [`can_apply`](Self::can_apply) reports an error exactly as
    /// [`apply`](Self::apply) would hit it.
    fn execute(&self, commit: bool) -> Result<(), NamespaceEditError> {
        if self.edits.is_empty() {
            return Err(NamespaceEditError::NoEdits);
        }
        let edit_target = self.stage.edit_target_layer_id()?;
        let layer_ids = self.stage.root_stack_layer_ids();
        // Namespace editing authors verbatim into the local layer stack, so it
        // requires the current edit target to be one of those layers with an
        // identity mapping. A variant or cross-arc target would need every edit
        // path (and the relocates) mapped through it, which v1 does not do.
        if !layer_ids.contains(&edit_target) || !self.stage.edit_target().map_function().is_identity() {
            return Err(NamespaceEditError::NonLocalEditTarget);
        }
        let relocates = self.relocate_plan(&self.stage)?;
        // The sources whose opinions arrive across an arc: they have no local
        // spec to move, so an edit on one counts as present even when no layer
        // authors it (the move/delete is realized by a relocate instead).
        //
        // TODO(namespace-edit): `relocates`/`cross_arc` are computed once from
        // the pre-batch stage, so a later edit on a path produced by an earlier
        // *cross-arc* move (e.g. move referenced /Ref/Geom→/Ref/Renamed then
        // delete /Ref/Renamed) is not recognized. Direct-spec edits chain (their
        // staged specs are visible); cross-arc chaining within one batch is not
        // yet supported.
        let cross_arc: HashSet<sdf::Path> = relocates.iter().map(|(src, _)| src.clone()).collect();
        // Destinations occupied by a composed object that has no local spec in the
        // root stack — a referenced/payload prim the staged per-layer check inside
        // the transaction cannot see, and which no earlier local edit in the batch
        // can vacate. A destination that has a local spec, or is produced by an
        // earlier edit, is left to that staged check, which reflects prior edits.
        let mut occupied_dsts: HashSet<sdf::Path> = HashSet::new();
        for edit in &self.edits {
            let NamespaceEdit::Move { dst, .. } = edit else {
                continue;
            };
            if !dst.is_abs() || dst.is_abs_root() {
                continue;
            }
            let has_local_spec = {
                let graph = self.stage.layers();
                layer_ids
                    .iter()
                    .any(|id| graph.get(*id).is_some_and(|node| node.layer.data().has_spec(dst)))
            };
            if !has_local_spec && self.stage.has_spec(dst.clone())? {
                occupied_dsts.insert(dst.clone());
            }
        }
        let collected: Vec<(pcp::LayerId, sdf::ChangeList)> = {
            let mut graph = self.stage.layers_mut();
            let mut txs: Vec<(pcp::LayerId, sdf::Transaction<'_>)> = graph
                .layers_mut(&layer_ids)
                .into_iter()
                .map(|(id, layer)| (id, sdf::Transaction::new(layer)))
                .collect();
            for edit in &self.edits {
                apply_edit(&mut txs, edit, &cross_arc, &occupied_dsts)?;
            }
            // After every structural edit, remap embedded paths against the whole
            // batch and author relocates on the edit-target layer (guaranteed to
            // be in the local stack by the check above).
            //
            // TODO(namespace-edit): the appended relocates are not folded through
            // ones already authored. Editing a prim that is itself the target of
            // an existing relocate (e.g. `/B -> /A` then moving `/A`) can leave
            // two pairs with the same target, which Pcp rejects as invalid.
            for (id, tx) in txs.iter_mut() {
                fixup_embedded_paths(tx, &self.edits).map_err(StageAuthoringError::Layer)?;
                if *id == edit_target && !relocates.is_empty() {
                    let mut authored = tx.relocates();
                    authored.extend(relocates.iter().cloned());
                    tx.set_relocates(authored).map_err(StageAuthoringError::Layer)?;
                }
            }
            if !commit {
                // Dry run: drop the transactions to roll every layer back, having
                // proven the batch applies cleanly.
                return Ok(());
            }
            txs.into_iter()
                .filter_map(|(id, tx)| {
                    let changes = tx.commit();
                    (!changes.is_empty()).then_some((id, changes))
                })
                .collect()
        };
        if !collected.is_empty() {
            let refs: Vec<(pcp::LayerId, &sdf::ChangeList)> = collected.iter().map(|(id, c)| (*id, c)).collect();
            self.stage.apply_change_sets(&refs, None);
        }
        Ok(())
    }

    /// The identifiers of the local-stack layers a successful apply would
    /// author into: every layer holding a spec at a source path. Mirrors C++
    /// `GetLayersToEdit`.
    pub fn layers_to_edit(&self) -> Result<Vec<String>, NamespaceEditError> {
        let layers = self.stage.layers();
        let mut result = Vec::new();
        for id in self.stage.root_stack_layer_ids() {
            let Some(node) = layers.get(id) else { continue };
            let touches = self.edits.iter().any(|edit| node.layer.data().has_spec(edit.source()));
            if touches {
                result.push(layers.identifier(id).to_string());
            }
        }
        Ok(result)
    }

    /// The relocates to author so objects composed across an arc move or delete:
    /// a prim with any opinion arriving across a reference/payload gets a
    /// `(source, destination)` pair (or `(source, empty)` for a deletion).
    fn relocate_plan(&self, stage: &Stage) -> Result<Vec<(sdf::Path, sdf::Path)>, NamespaceEditError> {
        let mut plan = Vec::new();
        for edit in &self.edits {
            let path = edit.source();
            if path.is_property_path() || !crosses_arc(stage, path)? {
                continue;
            }
            match edit {
                NamespaceEdit::Move { src, dst, .. } => plan.push((src.clone(), dst.clone())),
                NamespaceEdit::Delete { path, .. } => plan.push((path.clone(), sdf::Path::default())),
            }
        }
        Ok(plan)
    }
}

/// Validate `edit` against the staged state, then stage it into every layer.
/// The transactions already reflect the edits applied before this one, so the
/// checks read the precise staged data rather than a simulated projection: a
/// destination collision is an existing spec at `dst`, and a missing source is
/// an edit that moves or removes nothing in any layer. `cross_arc` names the
/// sources whose opinions arrive across an arc — they have no local spec to
/// move, so an edit on one is realized by a relocate and counts as present even
/// when no layer authors it.
fn apply_edit(
    txs: &mut [(pcp::LayerId, sdf::Transaction<'_>)],
    edit: &NamespaceEdit,
    cross_arc: &HashSet<sdf::Path>,
    occupied_dsts: &HashSet<sdf::Path>,
) -> Result<(), NamespaceEditError> {
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
            // A pre-existing composed object (occupied_dsts) or one staged by an
            // earlier edit in this batch (the per-layer check) blocks the move.
            if occupied_dsts.contains(dst) || txs.iter().any(|(_, tx)| tx.data().has_spec(dst)) {
                return Err(NamespaceEditError::DestinationExists(dst.clone()));
            }
            stage_across_layers(txs, src, cross_arc, |tx| {
                let moved = sdf::copy_spec_within(tx.data_mut(), src, dst)?;
                if moved {
                    tx.remove_spec(src)?;
                }
                Ok(moved)
            })?;
        }
        NamespaceEdit::Delete { path, kind } => {
            check_editable(path, *kind, NamespaceEditError::InvalidSource)?;
            stage_across_layers(txs, path, cross_arc, |tx| tx.remove_spec(path))?;
        }
    }
    Ok(())
}

/// Stage `op` into every layer, tracking whether any layer authored a change.
/// Errors with [`SourceNotFound`](NamespaceEditError::SourceNotFound) when no
/// layer did and `path` is not realized through a relocate (`cross_arc`).
fn stage_across_layers(
    txs: &mut [(pcp::LayerId, sdf::Transaction<'_>)],
    path: &sdf::Path,
    cross_arc: &HashSet<sdf::Path>,
    mut op: impl FnMut(&mut sdf::Transaction<'_>) -> Result<bool, sdf::AuthoringError>,
) -> Result<(), NamespaceEditError> {
    let mut authored = false;
    for (_, tx) in txs.iter_mut() {
        if op(tx).map_err(StageAuthoringError::Layer)? {
            authored = true;
        }
    }
    if !authored && !cross_arc.contains(path) {
        return Err(NamespaceEditError::SourceNotFound(path.clone()));
    }
    Ok(())
}

/// Rewrite every embedded namespace path in the layer through the batch: a
/// path under a move source re-roots onto the destination, and one under a
/// deletion source drops out of its list op. Preserves list-op structure.
//
// TODO(perf): scans every spec and field in the layer. A path-keyed index of
// specs carrying target/connection/reference opinions would bound this to the
// opinions that can actually reference a moved object.
fn fixup_embedded_paths(layer: &mut sdf::Layer, edits: &[NamespaceEdit]) -> Result<(), sdf::AuthoringError> {
    for path in layer.data().spec_paths() {
        let fields = layer.data().list_fields(&path).unwrap_or_default();
        for field in &fields {
            let Some(value) = layer.data().try_field(&path, field)? else {
                continue;
            };
            if !value.has_embedded_paths() {
                continue;
            }
            let value = value.into_owned();
            let rewritten = value.filter_map_paths(|p| project_path(p, edits));
            if rewritten != value {
                layer.data_mut().set_field(&path, field, rewritten);
            }
        }
    }
    Ok(())
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
                if let Some(moved) = current.replace_prefix(src, dst) {
                    current = moved;
                }
            }
        }
    }
    Some(current)
}

/// Whether the composed prim at `path` has any opinion arriving across a
/// reference or payload arc, so moving or deleting it needs a relocate. Such a
/// site contributes a spec at a path other than the composed one.
fn crosses_arc(stage: &Stage, path: &sdf::Path) -> anyhow::Result<bool> {
    Ok(stage
        .prim(path.clone())
        .prim_stack()?
        .iter()
        .any(|(_, spec)| spec != path))
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
    use super::*;
    use crate::sdf::{self, path, FieldKey, LayerOffset, Specifier, Variability};
    use crate::usd::Stage;

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
    fn rename_moves_subtree() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .rename_prim(&stage.prim(path("/A").unwrap()), "B")
            .unwrap()
            .apply()
            .unwrap();

        assert!(valid(&stage, "/B"));
        assert!(valid(&stage, "/B/Child"));
        assert!(!valid(&stage, "/A"));
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
    fn delete_prim_subtree() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/A").unwrap());
        editor.apply().unwrap();

        assert!(!valid(&stage, "/A"));
        assert!(!valid(&stage, "/A/Child"));
    }

    #[test]
    fn rename_fixes_targets() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .rename_prim(&stage.prim(path("/A").unwrap()), "B")
            .unwrap()
            .apply()
            .unwrap();

        assert_eq!(rel_targets(&stage, "/Other.rel"), vec!["/B", "/Keep"]);
    }

    #[test]
    fn rename_fixes_connections() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .rename_prim(&stage.prim(path("/A").unwrap()), "B")
            .unwrap()
            .apply()
            .unwrap();

        assert_eq!(connections(&stage, "/Other.con"), vec!["/B.out"]);
    }

    #[test]
    fn delete_drops_targets() {
        let stage = sample();
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_prim(path("/A").unwrap());
        editor.apply().unwrap();

        assert_eq!(rel_targets(&stage, "/Other.rel"), vec!["/Keep"]);
        assert!(connections(&stage, "/Other.con").is_empty());
    }

    #[test]
    fn rename_fixes_internal_ref() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        sdf::PrimSpec::new(root.data_mut(), "/A", Specifier::Def, "Xform").unwrap();
        sdf::PrimSpec::new(root.data_mut(), "/Other", Specifier::Def, "").unwrap();
        root.data_mut().set_field(
            &path("/Other").unwrap(),
            FieldKey::References.as_str(),
            sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                prim_path: path("/A").unwrap(),
                ..Default::default()
            }])),
        );
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
        sdf::PrimSpec::new(root.data_mut(), "/A", Specifier::Def, "").unwrap();
        sdf::PrimSpec::new(root.data_mut(), "/Other", Specifier::Def, "").unwrap();
        sdf::RelationshipSpec::new(root.data_mut(), "/Other.rel", Variability::Varying, false).unwrap();
        root.data_mut().set_field(
            &path("/Other.rel").unwrap(),
            FieldKey::TargetPaths.as_str(),
            sdf::Value::PathListOp(sdf::PathListOp::prepended([path("/A").unwrap()])),
        );
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

        assert!(stage.has_spec(path("/A.renamed").unwrap()).unwrap());
        assert!(!stage.has_spec(path("/A.out").unwrap()).unwrap());
    }

    #[test]
    fn delete_property_works() {
        let stage = sample();
        NamespaceEditor::new(&stage)
            .delete_property(path("/A.out").unwrap())
            .apply()
            .unwrap();

        assert!(!stage.has_spec(path("/A.out").unwrap()).unwrap());
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
        sdf::PrimSpec::new(sub.data_mut(), "/A", Specifier::Def, "Xform").unwrap();
        let root_id = stage.root_layer().identifier().to_string();
        stage.insert_sub_layer(&root_id, 0, sub, LayerOffset::IDENTITY).unwrap();
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
        sdf::PrimSpec::new(root.data_mut(), "/Ref", Specifier::Def, "").unwrap();
        root.data_mut().set_field(
            &path("/Ref").unwrap(),
            FieldKey::References.as_str(),
            sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                asset_path: "model.usda".into(),
                prim_path: path("/Model").unwrap(),
                ..Default::default()
            }])),
        );
        let mut model = sdf::Layer::new_in_memory("model.usda");
        sdf::PrimSpec::new(model.data_mut(), "/Model", Specifier::Def, "Xform").unwrap();
        sdf::PrimSpec::new(model.data_mut(), "/Model/Geom", Specifier::Def, "").unwrap();
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

    #[test]
    fn rejects_non_local_edit_target() {
        let stage = sample();
        let root = stage.root_layer().identifier().to_string();
        // A variant edit target has a non-identity mapping; namespace editing
        // authors verbatim into the local stack and does not support it.
        stage
            .set_edit_target(crate::usd::EditTarget::for_local_direct_variant(
                root,
                path("/A{v=s}").unwrap(),
            ))
            .unwrap();
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_prim(path("/A").unwrap(), path("/B").unwrap());
        assert!(matches!(
            editor.can_apply(),
            Err(NamespaceEditError::NonLocalEditTarget)
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
}
