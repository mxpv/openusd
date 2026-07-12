//! Transferable edits: a stage edit captured as a value diff and replayed on a
//! stage.
//!
//! A [`Diff`] is an ordered list of [`Edit`] operations (a spec created with its
//! fields, a field set or erased, a spec removed) plus the namespace mapping of
//! the edit target the edit was authored through. Everything in it is plain
//! value data, so a diff can cross a process or machine boundary and be rebuilt
//! on the other side.
//!
//! A diff is produced by observing a [`Stage`]'s commits:
//! [`ReplayStage`](super::ReplayStage) records the forward diff of each
//! committed edit — its new authored values — for replay or cross-stage
//! mirroring, and [`UndoStage`](super::UndoStage) records the inverse — the
//! old values, for undo. Both are [`StageSink`](super::StageSink) clients; the
//! derivation of a forward or inverse diff from a committed edit lives here
//! ([`forward_diff`], [`inverse_diff`]).
//!
//! [`Stage::apply_diff`] is the consume half. [`ApplyMode`] names the two
//! replication flavors:
//!
//! - [`ExactLayer`](ApplyMode::ExactLayer) replays the operations
//!   verbatim, at their recorded layer-namespace paths, onto an explicitly
//!   named layer of the consuming stage — the same-asset mirror. Undo/redo
//!   replays a recorded diff back onto the layer it came from this way.
//! - [`CurrentEditTarget`](ApplyMode::CurrentEditTarget) retargets the
//!   edit semantically: each operation path is lifted to composed stage
//!   namespace through the diff's own mapping, then mapped into the consuming
//!   stage's current edit target, so one diff can replay into a variant or
//!   across a reference arc. Embedded path values and time-sample keys are
//!   translated through the same mappings.
//!
//! # Example
//!
//! ```
//! use openusd::usd::{ApplyMode, ReplayStage, Stage};
//!
//! # fn main() -> anyhow::Result<()> {
//! // Producer: record every committed edit as a transferable diff.
//! let producer = ReplayStage::from(Stage::builder().in_memory("producer.usda")?);
//! producer.define_prim("/World")?.set_type_name("Xform")?;
//!
//! // Consumer: replay each recorded diff through its own edit target.
//! let mirror = Stage::builder().in_memory("mirror.usda")?;
//! for diff in producer.diff() {
//!     mirror.apply_diff(&diff, ApplyMode::CurrentEditTarget)?;
//! }
//! assert_eq!(mirror.prim("/World").type_name()?.as_deref(), Some("Xform"));
//! # Ok(())
//! # }
//! ```
use std::borrow::Cow;

use anyhow::Result;

use crate::{pcp, sdf, tf};

use super::sink::{CommittedChange, PendingChange};
use super::stage::{EditTarget, Stage, StageAuthoringError};

/// A transferable diff of one stage edit, produced by a diff recorder
/// ([`ReplayStage`](super::ReplayStage), [`UndoStage`](super::UndoStage)) and
/// replayed by [`Stage::apply_diff`].
///
/// `edits` is the operation list describing the edit — paths, field names, and
/// field values inline — and `mapping` ties the operation paths back to
/// composed stage namespace. Everything is plain value data with nothing
/// process-local.
#[derive(Debug, Clone, PartialEq)]
pub struct Diff {
    /// The operations describing the edit, in the change record's order. This
    /// is what a replay interprets: only paths listed here are authored at
    /// the destination. Namespace scaffolding (ancestor `over`s, variant
    /// chains) never appears — the destination materializes its own as the
    /// operations are applied — which is how an authored bare `over` survives
    /// a retargeting replay while a look-alike scaffolding ancestor does not
    /// exist to be replayed at all.
    pub edits: Vec<Edit>,
    /// Namespace mapping (edited layer source to composed stage target) of the
    /// edit target the diff was extracted through, or `None` when the edit used
    /// an identity target and the diff's paths are already composed stage
    /// paths. [`Stage::apply_diff`] lifts the diff's layer-namespace paths to
    /// stage namespace through it before re-mapping them into the consuming
    /// stage's own edit target. Plain value data like the other fields — path
    /// pairs, the root-identity flag, and a time offset.
    pub mapping: Option<pcp::MapFunction>,
}

/// One operation of a [`Diff`], in the edited layer's namespace.
#[derive(Debug, Clone, PartialEq)]
pub enum Edit {
    /// The edit created the spec at `path`; `fields` is its whole authored
    /// state, so a replay materializes the spec wholesale.
    Create {
        /// The created spec's path.
        path: sdf::Path,
        /// The kind of spec to create.
        spec_type: sdf::SpecType,
        /// Every authored field of the new spec, with its value.
        fields: Vec<FieldValue>,
    },
    /// The edit authored one field of a pre-existing spec. A replay onto a
    /// destination that already holds the spec writes just this field, leaving
    /// its unrelated opinions intact.
    SetField {
        /// The owning spec's path.
        path: sdf::Path,
        /// The kind of spec the field belongs to, letting a replay materialize
        /// the spec when the destination does not hold it. Materializing an
        /// attribute requires its `typeName`, which a single field edit does
        /// not carry, so an attribute `SetField` replays only onto a
        /// destination that holds the spec (or whose field is the `typeName`
        /// itself); otherwise the replay fails.
        spec_type: sdf::SpecType,
        /// The field's name.
        field: tf::Token,
        /// The authored value.
        value: sdf::Value,
    },
    /// The edit erased one field while its spec survives (e.g. clearing an
    /// attribute's connections); a replay applies it with
    /// [`sdf::AbstractData::erase_field`].
    EraseField {
        /// The owning spec's path.
        path: sdf::Path,
        /// The erased field's name.
        field: tf::Token,
    },
    /// The edit removed the whole prim or property spec; a replay applies it
    /// with [`sdf::LayerEdit::remove_spec`].
    RemoveSpec {
        /// The removed spec's path.
        path: sdf::Path,
    },
}

impl Edit {
    /// The spec path this edit applies to.
    pub fn path(&self) -> &sdf::Path {
        match self {
            Edit::Create { path, .. }
            | Edit::SetField { path, .. }
            | Edit::EraseField { path, .. }
            | Edit::RemoveSpec { path } => path,
        }
    }
}

/// A field and its authored value, as carried by [`Edit::Create`].
#[derive(Debug, Clone, PartialEq)]
pub struct FieldValue {
    /// The field's name.
    pub field: tf::Token,
    /// The authored value.
    pub value: sdf::Value,
}

/// How [`Stage::apply_diff`] interprets a [`Diff`]'s paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ApplyMode<'a> {
    /// Replicate the edit exactly: every operation is applied verbatim, at its
    /// recorded path in the producing layer's namespace (variant paths
    /// included), onto the stage layer named by this identifier. The current
    /// edit target plays no part; naming a layer not in the stage fails with
    /// [`StageAuthoringError::LayerNotFound`].
    ///
    /// The mode presumes the consuming stage composes the named layer the way
    /// the producing stage did — the same-asset mirror. The diff's
    /// [`mapping`](Diff::mapping) translates the resulting change
    /// notice's paths to stage namespace under that assumption; a consumer
    /// whose composition reaches the layer differently sees notice paths in
    /// the producer's namespace, not its own.
    ExactLayer(&'a str),
    /// Retarget the edit through the stage's current edit target: every
    /// operation path is lifted to composed stage namespace through the
    /// diff's own [`Diff::mapping`], then mapped into the target layer's
    /// namespace through [`EditTarget::map_to_spec_path`], so the same diff
    /// replays into a variant or across a composition arc. Replays just the
    /// edit: on a spec the destination already holds, only the fields the
    /// edit touched are written, leaving the destination's unrelated opinions
    /// intact.
    CurrentEditTarget,
}

/// Derive the forward diffs of the committed edit `objects` — the operations
/// that reproduce it — by reading the new authored values out of each edited
/// layer. Used by [`ReplayStage`](super::ReplayStage) from
/// [`StageSink::after_commit`](super::StageSink::after_commit), where the layers
/// hold the committed state.
///
/// One [`Diff`] per edited layer ([`layer_changes`](CommittedChange::layer_changes)):
/// a multi-layer transaction (a batch or namespace edit) records one change list
/// per layer, and each yields its own diff read from that layer's data, so a spec
/// authored only in a weaker layer is captured from the right layer rather than
/// looked up in — and dropped by — the strongest one. A layer no longer in the
/// stage is skipped.
///
/// Each diff is in its layer's namespace: for an edit authored through an arc or
/// variant edit target the operations carry the arc source layer's paths (e.g. a
/// `{set=sel}` variant segment), not the composed stage paths. [`Diff::mapping`]
/// carries that edit target's namespace mapping so [`Stage::apply_diff`] can lift
/// the paths back to stage namespace when replaying through a different target.
pub(super) fn forward_diff(stage: &Stage, objects: &CommittedChange<'_>) -> Result<Vec<Diff>> {
    let mapping = objects.provenance.mapping();
    let layers = stage.layers();
    let mut diffs = Vec::new();
    for (layer_identifier, change_list) in objects.layer_changes {
        let Some(layer_id) = layers.id_of(layer_identifier) else {
            continue;
        };
        let edits = forward_edits(layers.layer(layer_id).data(), change_list)?;
        if !edits.is_empty() {
            diffs.push(Diff {
                edits,
                mapping: mapping.cloned(),
            });
        }
    }
    Ok(diffs)
}

/// The forward edits for one layer: the operations reproducing every
/// genuinely-touched spec, read from `src` (the committed layer data).
///
/// Turns each entry of `change_list` into [`Edit`] operations. List-valued field
/// edits (reference / target / apiSchema removals included) ride along as their
/// authored list-op values.
///
/// A spec whose change entry records only child-name bookkeeping — the
/// `primChildren` / `propertyChildren` / variant-chain registration a descendant
/// edit stamps on its ancestors — yields no edit: its own opinions did not
/// change, and the descendant's spec re-registers itself on replay. Only specs
/// the edit genuinely touched land in the edit list.
fn forward_edits(src: &dyn sdf::AbstractData, change_list: &sdf::ChangeList) -> Result<Vec<Edit>> {
    let mut edits = Vec::new();
    for (path, entry) in change_list.entries() {
        // A spec's presence in `src` is the source of truth: one still there
        // (added, modified, or removed-then-re-added within the edit) is
        // captured with its current authored state; one gone with a removal
        // flag is a whole-spec removal.
        if let Some(spec_type) = src.spec_type(path) {
            // An entry that only records child-name bookkeeping marks an
            // ancestor of a descendant edit; capturing the spec would only
            // restate its unchanged opinions.
            if entry.is_child_bookkeeping() {
                continue;
            }
            // A spec the edit created is owned by the edit wholesale, so its
            // whole authored state is captured; a pre-existing one is owned only
            // at its touched fields — each either set (still authored) or erased
            // (absent). Child-name lists are namespace bookkeeping the
            // destination rebuilds, never captured.
            if entry.flags.intersects(sdf::ChangeFlags::ADD) {
                edits.push(spec_create_edit(src, path, spec_type)?);
            } else {
                for field in entry.authored_fields() {
                    edits.push(field_op(src, path, spec_type, field)?);
                }
            }
        } else if entry.flags.intersects(sdf::ChangeFlags::REMOVE) {
            edits.push(Edit::RemoveSpec { path: path.clone() });
        }
    }
    Ok(edits)
}

/// Derive the inverse of the staged edit `change` — the diff that, replayed onto
/// the same layer, restores it to the state its [`base`](PendingChange::base)
/// holds. Used by [`UndoStage`](super::UndoStage) from
/// [`StageSink::before_commit`](super::StageSink::before_commit), the one moment
/// the pre-edit values are still readable.
///
/// The undo counterpart of [`forward_diff`]: where the forward diff captures the
/// edit's new values, this reads the old values off the pre-edit base. A field
/// the edit set inverts to its base value (or an erase when the base lacked it);
/// a spec the edit created inverts to a removal; a spec the edit removed or
/// replaced inverts to a re-creation of its whole base state.
///
/// Returns the inverse edits for one layer, ordered by path; a read error
/// propagates (like [`forward_diff`]) rather than silently dropping a spec or
/// field, so a partial — and therefore unsafe — inverse is never recorded. The
/// caller attaches the transaction's mapping once (all its layers share one).
pub(super) fn inverse_diff(change: &PendingChange<'_>) -> Result<Vec<Edit>> {
    let base = change.base;
    let mut edits = Vec::new();
    for (path, entry) in change.change_list.entries() {
        if entry.is_child_bookkeeping() {
            continue;
        }
        let base_type = base.spec_type(path);
        if entry.flags.intersects(sdf::ChangeFlags::ADD) {
            // The edit created (or replaced) the spec here: restore the base
            // spec wholesale when one existed, else remove the fresh creation.
            match base_type {
                Some(spec_type) => edits.push(spec_create_edit(base, path, spec_type)?),
                None => edits.push(Edit::RemoveSpec { path: path.clone() }),
            }
        } else if entry.flags.intersects(sdf::ChangeFlags::REMOVE) {
            // The edit removed the spec: re-create it from its base state.
            if let Some(spec_type) = base_type {
                edits.push(spec_create_edit(base, path, spec_type)?);
            }
        } else if let Some(spec_type) = base_type {
            // Field-level edits on a surviving spec: restore each touched field
            // to its base value, or erase it when the base did not hold it.
            for field in entry.authored_fields() {
                edits.push(field_op(base, path, spec_type, field)?);
            }
        }
    }
    // Order by path so a re-created ancestor precedes its descendants, and a
    // removed ancestor is removed before them; operations on one spec keep their
    // recorded order (the sort is stable). Removals still apply after the
    // authoring operations through [`apply_edits_verbatim`]'s partition.
    edits.sort_by(|a, b| a.path().cmp(b.path()));
    Ok(edits)
}

/// An [`Edit::Create`] capturing the whole authored state of the spec at `path`
/// in `data` — every field except the child-name lists, with its value. The
/// building block both directions use to reproduce (`forward_diff`, reading the
/// committed layer) or restore (`inverse_diff`, reading the pre-edit base) a spec
/// wholesale.
fn spec_create_edit(data: &dyn sdf::AbstractData, path: &sdf::Path, spec_type: sdf::SpecType) -> Result<Edit> {
    let mut fields = Vec::new();
    for field in data.list_fields(path).unwrap_or_default() {
        if sdf::is_children_field(&field) {
            continue;
        }
        if let Some(value) = data.try_field(path, &field)? {
            fields.push(FieldValue {
                field: tf::Token::from(field),
                value: value.into_owned(),
            });
        }
    }
    Ok(Edit::Create {
        path: path.clone(),
        spec_type,
        fields,
    })
}

/// The [`Edit`] restoring or reproducing one authored `field` of the spec at
/// `path`: a [`SetField`](Edit::SetField) with the value `data` holds, or an
/// [`EraseField`](Edit::EraseField) when `data` does not hold it. Shared by both
/// diff directions over their respective `data` (committed layer or pre-edit base).
fn field_op(
    data: &dyn sdf::AbstractData,
    path: &sdf::Path,
    spec_type: sdf::SpecType,
    field: &tf::Token,
) -> Result<Edit> {
    Ok(match data.try_field(path, field.as_str())? {
        Some(value) => Edit::SetField {
            path: path.clone(),
            spec_type,
            field: field.clone(),
            value: value.into_owned(),
        },
        None => Edit::EraseField {
            path: path.clone(),
            field: field.clone(),
        },
    })
}

impl Stage {
    /// Replay a [`Diff`] onto this stage in one transaction, the consume
    /// half of the diff producers ([`ReplayStage`](super::ReplayStage) and
    /// [`UndoStage`](super::UndoStage)): each [`Edit`] is
    /// interpreted — creations and set fields authoring their recorded values,
    /// removals and erasures applied destructively. The whole
    /// replay drains as a single edit, delivering one
    /// [`CommittedChange`](super::CommittedChange) to the stage's sinks and
    /// invalidating composition for every path it touched.
    ///
    /// `mode` selects where and in which namespace the diff lands — exact
    /// layer replication or retargeting through the current edit target; see
    /// [`ApplyMode`]. Under
    /// [`CurrentEditTarget`](ApplyMode::CurrentEditTarget), embedded path
    /// values — relationship targets, attribute connections, `inheritPaths`,
    /// `specializes`, relocates, internal reference and payload prim paths —
    /// are translated through the same mappings as the spec paths, and
    /// time-sample keys are re-keyed through the producing and consuming
    /// targets' time offsets. A diff path, spec or embedded value alike, that
    /// the target cannot express fails with
    /// [`StageAuthoringError::OutsideEditTarget`].
    ///
    /// The replay is atomic: every operation stages in the destination layer's
    /// copy-on-write overlay, and the whole batch commits only once all have
    /// applied. An operation that fails mid-batch rolls the overlay back, so the
    /// live layer — and any cached composition state — is left untouched.
    ///
    /// `apply_diff` fires this stage's own [`CommittedChange`](super::CommittedChange).
    /// A bidirectional mirror that feeds those changes back to the origin must
    /// tag or suppress the echo itself — that is an application-level concern
    /// this method does not arbitrate.
    pub fn apply_diff(&self, diff: &Diff, mode: ApplyMode<'_>) -> Result<(), StageAuthoringError> {
        match mode {
            ApplyMode::ExactLayer(identifier) => {
                let layer_id = self
                    .layers()
                    .id_of(identifier)
                    .ok_or_else(|| StageAuthoringError::LayerNotFound {
                        layer: identifier.to_string(),
                    })?;
                // The replay authors at the diff's layer-namespace paths, so
                // the diff's own mapping is what carries the resulting notice
                // paths back to composed stage namespace — e.g. a
                // variant-produced diff resyncs `/Prim/child`, not
                // `/Prim{set=sel}child`.
                self.author_on_layer(layer_id, diff.mapping.as_ref(), |layer| {
                    apply_edits_verbatim(layer, &diff.edits)
                })
            }
            ApplyMode::CurrentEditTarget => {
                let layer_id = self.edit_target_layer_id()?;
                let target = self.edit_target();
                let translated = translate_diff(diff, &target)?;
                self.author_on_layer(layer_id, Some(target.map_function()), |layer| {
                    apply_translated_diff(layer, diff, &target, &translated)
                })
            }
        }
    }
}

/// Apply `edits` to `layer` verbatim, at their recorded layer-namespace paths.
/// The mutating core of the [`ApplyMode::ExactLayer`] replay, and the primitive
/// [`UndoStage`](super::UndoStage) replays a transaction's per-layer edits
/// through inside one [`batch_edit`](Stage::batch_edit)-style transaction.
///
/// Removals apply after the authoring operations, the same ordering the
/// translated replay uses; a captured edit never authors and removes the
/// same path (the change record collapses per path), so the partition
/// preserves the diff's semantics.
pub(super) fn apply_edits_verbatim(layer: &mut sdf::LayerEdit<'_>, edits: &[Edit]) -> Result<(), sdf::AuthoringError> {
    for edit in edits {
        if !matches!(edit, Edit::RemoveSpec { .. }) {
            apply_edit(layer, edit.path(), edit, &sdf::Value::clone)?;
        }
    }
    for edit in edits {
        if matches!(edit, Edit::RemoveSpec { .. }) {
            apply_edit(layer, edit.path(), edit, &sdf::Value::clone)?;
        }
    }
    Ok(())
}

/// Apply one [`Edit`] at `dst`, with every written value produced by
/// `translate` from the recorded one.
///
/// A [`Create`](Edit::Create) materializes the spec with exactly its recorded
/// fields: a same-kind destination spec's other authored opinions are cleared
/// first, since the recorded fields are the created spec's whole state. A
/// [`SetField`](Edit::SetField) writes onto the existing spec, or materializes
/// it first when the destination does not hold it (or holds a different spec
/// kind), so a replay never writes a field without its spec — both through
/// [`sdf::author_spec`]'s upsert.
fn apply_edit(
    layer: &mut sdf::LayerEdit<'_>,
    dst: &sdf::Path,
    edit: &Edit,
    translate: &impl Fn(&sdf::Value) -> sdf::Value,
) -> Result<(), sdf::AuthoringError> {
    match edit {
        Edit::Create { spec_type, fields, .. } => {
            // Prim and variant specs hold the same prim-level fields and
            // author onto each other (the chain builder derives the created
            // kind from the destination path), so the correspondence counts
            // as a kind match here.
            let kind_matches = |existing: sdf::SpecType| {
                let prim_like = |kind: sdf::SpecType| matches!(kind, sdf::SpecType::Prim | sdf::SpecType::Variant);
                existing == *spec_type || (prim_like(existing) && prim_like(*spec_type))
            };
            match layer.data().spec_type(dst) {
                // The recorded fields are the created spec's whole state:
                // clear the other opinions a matching destination spec
                // already holds so the replay reproduces that state.
                Some(existing) if kind_matches(existing) => {
                    for field in layer.data().list_fields(dst).unwrap_or_default() {
                        let recorded = fields.iter().any(|f| f.field == field.as_str());
                        if !recorded && !sdf::is_children_field(&field) {
                            layer.data_mut().erase_field(dst, &field);
                        }
                    }
                }
                // A property spec of the other kind cannot be authored over
                // (the typed constructors reject it); the producer's create
                // replaces it.
                Some(sdf::SpecType::Attribute | sdf::SpecType::Relationship) => {
                    layer.remove_spec(dst)?;
                }
                _ => {}
            }
            sdf::author_spec(
                layer.data_mut(),
                dst,
                *spec_type,
                fields.iter().map(|f| (f.field.as_str(), translate(&f.value))),
            )?;
        }
        Edit::SetField {
            spec_type,
            field,
            value,
            ..
        } => {
            sdf::author_spec(layer.data_mut(), dst, *spec_type, [(field.as_str(), translate(value))])?;
        }
        Edit::EraseField { field, .. } => layer.data_mut().erase_field(dst, field.as_str()),
        Edit::RemoveSpec { .. } => remove_or_clear(layer, dst)?,
    }
    Ok(())
}

/// Remove the spec at `path` from `layer`, clearing its authored opinions
/// instead when the spec is of a kind [`sdf::LayerEdit::remove_spec`] cannot
/// erase. A removal routed onto variant scaffolding — e.g. a prim removal
/// translated through a variant edit target lands on the variant spec — must
/// still drop the opinions the producer deleted; the scaffolding spec itself
/// stays.
fn remove_or_clear(layer: &mut sdf::LayerEdit<'_>, path: &sdf::Path) -> Result<(), sdf::AuthoringError> {
    if layer.remove_spec(path)? || layer.data().spec_type(path).is_none() {
        return Ok(());
    }
    for field in layer.data().list_fields(path).unwrap_or_default() {
        if !sdf::is_children_field(&field) {
            layer.data_mut().erase_field(path, &field);
        }
    }
    Ok(())
}

/// A [`Diff`] re-keyed into an edit target's layer namespace: which diff
/// operation to apply where, and the time retiming. Built by
/// [`translate_diff`] as a pure pre-pass, so every path is validated before
/// [`apply_translated_diff`] mutates the target layer.
struct TranslatedDiff<'a> {
    /// The authoring operations as `(destination path, edit)` pairs, ordered
    /// by destination path (parents before children).
    edits: Vec<(sdf::Path, &'a Edit)>,
    /// The whole-spec removals, with their paths in the target layer's
    /// namespace, applied after the authoring operations in the edit list's
    /// order.
    removed: Vec<sdf::Path>,
    /// Retiming from the diff's time frame to the target layer's: the
    /// producing mapping's offset lifts a sample key to stage time, the
    /// consuming target's inverse offset keys it in the target layer (the same
    /// retiming as [`EditTarget::map_to_spec_time`]).
    time_offset: sdf::LayerOffset,
}

/// Lift `path` to composed stage namespace through the diff's producing
/// `mapping`, or `None` when the mapping cannot express it. A diff with no
/// mapping already carries stage paths, so the lift passes `path` through
/// unchanged (borrowed).
fn lift_path<'a>(mapping: Option<&pcp::MapFunction>, path: &'a sdf::Path) -> Option<Cow<'a, sdf::Path>> {
    match mapping {
        Some(m) => m.map_source_to_target(path).map(Cow::Owned),
        None => Some(Cow::Borrowed(path)),
    }
}

/// Translate every edit in `diff` into `target`'s layer namespace: lift the
/// diff's layer-namespace path to composed stage namespace through the diff's
/// own [`Diff::mapping`], then map it through the target. Pure — nothing
/// is authored — so a diff path the target cannot express fails here, before
/// any mutation, with [`StageAuthoringError::OutsideEditTarget`]. Embedded
/// value paths are validated the same way: a relationship target, connection,
/// or internal reference path the mappings cannot express fails rather than
/// authoring an untranslated path that could alias an unrelated spec through
/// the arc.
///
/// Only the [`Diff::edits`] list is translated; the namespace scaffolding
/// around it stays behind, because the destination rebuilds its own and the
/// scaffolding's paths (the pseudo-root, ancestors outside an arc's subtree)
/// need not be expressible through the target at all. Variant specs and prim
/// specs both translate — a variant's prim-level opinions lift to its owning
/// prim's stage path, and a prim's opinions can land on a variant spec when
/// the target routes them into one.
fn translate_diff<'a>(diff: &'a Diff, target: &EditTarget) -> Result<TranslatedDiff<'a>, StageAuthoringError> {
    let translate = |path: &sdf::Path| -> Result<sdf::Path, StageAuthoringError> {
        lift_path(diff.mapping.as_ref(), path)
            .and_then(|scene| target.map_to_spec_path(&scene))
            .ok_or_else(|| StageAuthoringError::OutsideEditTarget { path: path.clone() })
    };
    let mut edits = Vec::new();
    let mut removed = Vec::new();
    for edit in &diff.edits {
        let dst = translate(edit.path())?;
        match edit {
            Edit::RemoveSpec { .. } => {
                removed.push(dst);
                continue;
            }
            Edit::Create { fields, .. } => {
                for field in fields {
                    validate_value(diff, target, &field.value)?;
                }
            }
            Edit::SetField { value, .. } => validate_value(diff, target, value)?,
            Edit::EraseField { .. } => {}
        }
        edits.push((dst, edit));
    }
    // A variant spec and its owning prim can translate onto the same
    // destination; the variant's opinions are the weaker of the two, so they
    // apply first and the direct — stronger — opinions land last. The sort is
    // stable, so operations sharing a destination keep their recorded order.
    edits.sort_by(|(dst_a, edit_a), (dst_b, edit_b)| {
        let direct = |edit: &Edit| !edit.path().contains_prim_variant_selection();
        dst_a.cmp(dst_b).then_with(|| direct(edit_a).cmp(&direct(edit_b)))
    });
    let lift_offset = diff
        .mapping
        .as_ref()
        .map_or(sdf::LayerOffset::IDENTITY, |m| m.time_offset());
    let time_offset = target.map_function().time_offset().inverse().concatenate(&lift_offset);
    Ok(TranslatedDiff {
        edits,
        removed,
        time_offset,
    })
}

/// Apply a [`TranslatedDiff`] onto `layer`: each authoring operation at its
/// translated destination with values run through [`translate_value`], then
/// the translated removals. The mutating core of the
/// [`ApplyMode::CurrentEditTarget`] replay.
fn apply_translated_diff(
    layer: &mut sdf::LayerEdit<'_>,
    diff: &Diff,
    target: &EditTarget,
    translated: &TranslatedDiff<'_>,
) -> Result<(), sdf::AuthoringError> {
    let translate = |value: &sdf::Value| {
        translate_value(value, diff, target, translated.time_offset).unwrap_or_else(|| value.clone())
    };
    for (dst, edit) in &translated.edits {
        apply_edit(layer, dst, edit, &translate)?;
    }
    for path in &translated.removed {
        remove_or_clear(layer, path)?;
    }
    Ok(())
}

/// Check that every embedded path in `value` — time-sampled values included —
/// is expressible through the diff and target mappings, failing with
/// [`StageAuthoringError::OutsideEditTarget`] on the first path that is not.
/// The pure validation half of [`translate_value`], run by [`translate_diff`]
/// before any mutation.
fn validate_value(diff: &Diff, target: &EditTarget, value: &sdf::Value) -> Result<(), StageAuthoringError> {
    if let sdf::Value::TimeSamples(samples) = value {
        for (_, sample) in samples {
            validate_value(diff, target, sample)?;
        }
        return Ok(());
    }
    if !value.has_embedded_paths() {
        return Ok(());
    }
    let failed: std::cell::Cell<Option<sdf::Path>> = std::cell::Cell::new(None);
    value.remap_paths(|path| {
        if translate_value_path(diff, target, path).is_none() {
            failed.set(Some(path.clone()));
        }
        path.clone()
    });
    match failed.take() {
        Some(path) => Err(StageAuthoringError::OutsideEditTarget { path }),
        None => Ok(()),
    }
}

/// Translate one embedded value path — a relationship target, connection,
/// inherit, specialize, relocate endpoint, or internal reference prim path —
/// from the diff's namespace into the target layer's, or `None` when the
/// mappings cannot express it (which [`translate_diff`] rejects up front).
//
// TODO: both hops use the bare prefix maps; composition translates target
// paths through the bijection-checked `MapFunction::translate_to_target`,
// which additionally refuses shadowed results. Adopting that rule here needs
// a check that tolerates edit-target mappings first — a pair plus root
// identity shadows paths the bare map translates fine.
fn translate_value_path(diff: &Diff, target: &EditTarget, path: &sdf::Path) -> Option<sdf::Path> {
    lift_path(diff.mapping.as_ref(), path).and_then(|scene| target.map_to_spec_target_path(&scene))
}

/// Translate one field value for the retargeting replay, or `None` when the
/// value is correct as-is.
///
/// Embedded namespace paths are rewritten through [`translate_value_path`];
/// time-sample keys are re-keyed through `time_offset` so a diff replayed
/// across a composition arc with a layer offset keeps its samples at the same
/// composed stage times, and sampled values translate like any other value.
fn translate_value(
    value: &sdf::Value,
    diff: &Diff,
    target: &EditTarget,
    time_offset: sdf::LayerOffset,
) -> Option<sdf::Value> {
    if let sdf::Value::TimeSamples(samples) = value {
        let retime = !time_offset.is_identity();
        if !retime && !samples.iter().any(|(_, sample)| sample.has_embedded_paths()) {
            return None;
        }
        return Some(sdf::Value::TimeSamples(
            samples
                .iter()
                .map(|(time, sample)| {
                    let time = if retime { time_offset.apply(*time) } else { *time };
                    let sample = translate_value(sample, diff, target, time_offset).unwrap_or_else(|| sample.clone());
                    (time, sample)
                })
                .collect(),
        ));
    }
    if !value.has_embedded_paths() {
        return None;
    }
    Some(value.remap_paths(|path| translate_value_path(diff, target, path).unwrap_or_else(|| path.clone())))
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;

    use anyhow::Result;

    use super::super::sink::Provenance;
    use super::*;
    use crate::usd::{EditTargetArc, TimeCode};

    fn in_memory_stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    fn fixture_path(relative: &str) -> String {
        format!("{}/fixtures/{relative}", env!("CARGO_MANIFEST_DIR"))
    }

    /// `forward_diff` turns a whole-spec removal into a `RemoveSpec` operation.
    /// Driven with a synthetic committed change to unit-test the routing in
    /// isolation; the end-to-end `remove_prim` / `apply_diff` path is covered
    /// below.
    #[test]
    fn forward_removal() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/World")?;
        stage.create_attribute("/World.size", "double")?;
        let size = sdf::path("/World.size")?;
        let root = stage.root_layer().identifier().to_string();
        // Remove the spec, as a real removal edit would, so it is gone from the
        // layer when the synthetic change is processed.
        stage.remove_property(size.clone())?;
        let mut change_list = sdf::ChangeList::new();
        change_list.entry_mut(&size).flags |= sdf::ChangeFlags::REMOVE_PROPERTY;
        let provenance = Provenance::LocalStack;
        let layer_changes = [(root.clone(), change_list.clone())];
        let change = CommittedChange {
            resynced: &[],
            changed_info_only: std::slice::from_ref(&size),
            layer_identifier: &root,
            change_list: &change_list,
            layer_changes: &layer_changes,
            provenance: &provenance,
            generation: 0,
        };
        let diffs = forward_diff(&stage, &change)?;
        assert_eq!(diffs.len(), 1);
        assert_eq!(diffs[0].edits, vec![Edit::RemoveSpec { path: size.clone() }]);
        Ok(())
    }

    /// `forward_diff` from a sink captures the authored value inline: setting an
    /// attribute default yields a `SetField` operation carrying it — the source
    /// half of mirroring an edit.
    #[test]
    fn forward_set_value() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/World")?;
        let attr = stage.create_attribute("/World.size", "double")?;
        let value: Rc<RefCell<Option<f64>>> = Rc::new(RefCell::new(None));
        let _id = {
            let value = value.clone();
            let size = sdf::Path::new("/World.size")?;
            stage.add_sink(move |stage: &Stage, change: &CommittedChange<'_>| {
                let diffs = forward_diff(stage, change).expect("forward diff");
                value.replace(diffs.iter().flat_map(|d| &d.edits).find_map(|e| match e {
                    Edit::SetField { path, field, value, .. }
                        if *path == size && field == sdf::FieldKey::Default.as_str() =>
                    {
                        value.clone().try_as_double()
                    }
                    _ => None,
                }));
            })
        };
        attr.set(2.0_f64)?;
        assert_eq!(*value.borrow(), Some(2.0));
        Ok(())
    }

    /// Clearing an attribute's connections erases the connectionPaths field; the
    /// diff reports it as an `EraseField` operation so a mirror can drop its
    /// stale opinion.
    #[test]
    fn forward_field_erasure() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/World")?;
        stage.create_attribute("/World.target", "double")?;
        let attr = stage.create_attribute("/World.size", "double")?;
        let attr = attr.set_connections([sdf::Path::new("/World.target")?])?;
        // Field name erased on /World.size, captured from the diff's edits.
        let erased: Rc<RefCell<Vec<String>>> = Rc::new(RefCell::new(Vec::new()));
        let _id = {
            let erased = erased.clone();
            stage.add_sink(move |stage: &Stage, change: &CommittedChange<'_>| {
                let diffs = forward_diff(stage, change).expect("forward diff");
                let size = sdf::Path::new("/World.size").unwrap();
                erased
                    .borrow_mut()
                    .extend(diffs.iter().flat_map(|d| &d.edits).filter_map(|e| match e {
                        Edit::EraseField { path, field } if *path == size => Some(field.as_str().to_string()),
                        _ => None,
                    }));
            })
        };
        attr.clear_connections()?;
        assert!(erased.borrow().iter().any(|f| f == "connectionPaths"));
        Ok(())
    }

    /// Install a sink on `stage` that derives a forward [`Diff`] from every
    /// committed edit, collecting them for a mirror to replay. The sink stays
    /// installed for the stage's lifetime (the returned
    /// [`StageSinkId`](super::StageSinkId) is unused).
    fn capture_diffs(stage: &Stage) -> Rc<RefCell<Vec<Diff>>> {
        let diffs: Rc<RefCell<Vec<Diff>>> = Rc::new(RefCell::new(Vec::new()));
        {
            let diffs = diffs.clone();
            stage.add_sink(move |stage: &Stage, change: &CommittedChange<'_>| {
                diffs
                    .borrow_mut()
                    .extend(forward_diff(stage, change).expect("forward diff"));
            });
        }
        diffs
    }

    /// Replaying every diff a listener captures from stage A onto stage B
    /// reconstructs A's edited subtree — the round trip through
    /// `forward_diff` / `apply_diff`.
    #[test]
    fn apply_diff_roundtrip() -> Result<()> {
        let a = in_memory_stage()?;
        let diffs = capture_diffs(&a);
        a.define_prim("/World")?.set_type_name("Xform")?;
        a.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        a.create_attribute("/World/Mesh.size", "double")?.set(2.0_f64)?;

        let b = in_memory_stage()?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        assert_eq!(b.prim("/World").child_names()?, vec![tf::Token::new("Mesh")]);
        assert_eq!(b.prim("/World").type_name()?.as_deref(), Some("Xform"));
        assert_eq!(b.attribute("/World/Mesh.size").get::<f64>()?, Some(2.0));
        Ok(())
    }

    /// A diff carries deletions as `RemoveSpec` and `EraseField` operations —
    /// and `apply_diff` replays them so stage B drops the prim and the
    /// connections, matching A.
    #[test]
    fn apply_diff_removal() -> Result<()> {
        let a = in_memory_stage()?;
        let diffs = capture_diffs(&a);
        a.define_prim("/World")?;
        a.define_prim("/World/Doomed")?;
        a.define_prim("/World/Target")?;
        let attr = a.create_attribute("/World.size", "double")?;
        let attr = attr.set_connections([sdf::Path::new("/World/Target.size")?])?;
        assert!(a.remove_prim("/World/Doomed")?);
        attr.clear_connections()?;

        // The deletions surface in the captured diffs as removal and erasure
        // operations.
        let edits: Vec<Edit> = diffs.borrow().iter().flat_map(|d| d.edits.clone()).collect();
        let doomed = sdf::path("/World/Doomed")?;
        assert!(edits.iter().any(|e| *e == Edit::RemoveSpec { path: doomed.clone() }));
        let size = sdf::path("/World.size")?;
        assert!(edits
            .iter()
            .any(|e| matches!(e, Edit::EraseField { path, .. } if *path == size)));

        let b = in_memory_stage()?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        assert!(!b.prim("/World/Doomed").is_valid()?);
        assert!(b.prim("/World/Target").is_valid()?);
        assert!(b.attribute(&sdf::path("/World.size")?).connections()?.is_empty());
        Ok(())
    }

    /// A stage-namespace diff replayed through a variant edit target lands inside
    /// the variant: child specs gain the `{set=sel}` segment, the variant-owning
    /// prim's own opinions land on the variant spec, and connection paths stay
    /// free of variant selections.
    #[test]
    fn apply_diff_into_variant() -> Result<()> {
        let a = in_memory_stage()?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim")?.set_type_name("Xform")?;
        a.define_prim("/Prim/child")?;
        a.create_attribute("/Prim/child.out", "double")?
            .set_connections([sdf::path("/Prim/other.in")?])?;

        let b = in_memory_stage()?;
        let root = b.edit_target().layer_identifier().to_string();
        b.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }

        let layer = b.root_layer();
        let data = layer.data();
        assert_eq!(
            data.spec_type(&sdf::path("/Prim{set=sel}child")?),
            Some(sdf::SpecType::Prim)
        );
        assert_eq!(
            data.spec_type(&sdf::path("/Prim{set=sel}child.out")?),
            Some(sdf::SpecType::Attribute)
        );
        assert!(!data.has_spec(&sdf::path("/Prim/child")?));
        // The variant-owning prim's own opinion routed onto the variant spec.
        let type_name = data
            .try_field(&sdf::path("/Prim{set=sel}")?, sdf::FieldKey::TypeName.as_str())?
            .expect("typeName authored on the variant spec")
            .into_owned()
            .try_as_token()
            .expect("typeName is a token");
        assert_eq!(type_name.as_str(), "Xform");
        // Connection target paths never carry variant selections.
        let connections = data
            .try_field(
                &sdf::path("/Prim{set=sel}child.out")?,
                sdf::FieldKey::ConnectionPaths.as_str(),
            )?
            .expect("connections authored")
            .into_owned()
            .try_as_path_list_op()
            .expect("connections are a path list op");
        assert_eq!(connections.explicit_items, vec![sdf::path("/Prim/other.in")?]);
        Ok(())
    }

    /// A stage-namespace diff replayed through a reference arc target lands in the
    /// referenced layer's namespace — and composes back through the arc — with
    /// embedded connection paths translated into the arc source.
    #[test]
    fn apply_diff_into_reference_arc() -> Result<()> {
        let a = Stage::open(&fixture_path("ref_external.usda"))?;
        let diffs = capture_diffs(&a);
        a.define_prim("/World/MyPrim/added")?;
        a.create_attribute("/World/MyPrim/added.out", "double")?
            .set_connections([sdf::path("/World/MyPrim/Child.in")?])?;

        let b = Stage::open(&fixture_path("ref_external.usda"))?;
        let target = b.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
        let _ctx = b.edit_context(target)?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }

        // The specs landed at the arc-source paths in the referenced layer, not in
        // the root layer, and compose back through the reference.
        assert!(!b.root_layer().data().has_spec(&sdf::path("/World/MyPrim/added")?));
        assert!(b.prim("/World/MyPrim/added").is_valid()?);
        assert_eq!(
            b.attribute(&sdf::path("/World/MyPrim/added.out")?).connections()?,
            vec![sdf::path("/World/MyPrim/Child.in")?]
        );
        Ok(())
    }

    /// A diff authored through a variant edit target carries that target's
    /// mapping; replaying it through a different variant target lifts the paths
    /// out of the producer's variant and lands them in the consumer's.
    #[test]
    fn apply_diff_lifts_variant_diff() -> Result<()> {
        let a = in_memory_stage()?;
        a.define_prim("/Prim")?;
        let root_a = a.edit_target().layer_identifier().to_string();
        a.set_edit_target(EditTarget::for_local_direct_variant(
            root_a,
            sdf::path("/Prim{set=sel}")?,
        ))?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim/child")?.set_type_name("Scope")?;

        let b = in_memory_stage()?;
        let root_b = b.edit_target().layer_identifier().to_string();
        b.set_edit_target(EditTarget::for_local_direct_variant(
            root_b,
            sdf::path("/Prim{mirror=m}")?,
        ))?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }

        let layer = b.root_layer();
        let data = layer.data();
        assert_eq!(
            data.spec_type(&sdf::path("/Prim{mirror=m}child")?),
            Some(sdf::SpecType::Prim)
        );
        assert!(!data.has_spec(&sdf::path("/Prim{set=sel}child")?));
        let type_name = data
            .try_field(&sdf::path("/Prim{mirror=m}child")?, sdf::FieldKey::TypeName.as_str())?
            .expect("typeName carried into the consumer's variant")
            .into_owned()
            .try_as_token()
            .expect("typeName is a token");
        assert_eq!(type_name.as_str(), "Scope");
        Ok(())
    }

    /// A diff survives transfer between processes: the operations decompose
    /// into plain paths, tokens, and values, and the mapping into its path
    /// pairs, root-identity flag, and time offset — the rebuilt diff replays
    /// identically on the consumer.
    #[test]
    fn apply_diff_transferred() -> Result<()> {
        let a = in_memory_stage()?;
        a.define_prim("/Prim")?;
        let root_a = a.edit_target().layer_identifier().to_string();
        a.set_edit_target(EditTarget::for_local_direct_variant(
            root_a,
            sdf::path("/Prim{set=sel}")?,
        ))?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim/child")?.set_type_name("Scope")?;

        // Encode: nothing in the diff is process-local. Paths and field names
        // are strings, the mapping decomposes into path pairs, the
        // root-identity flag, and a time offset; the field values are cloned
        // in place of a wire codec.
        let mut wire = Vec::new();
        for diff in diffs.borrow().iter() {
            let mapping = diff.mapping.as_ref().map(|m| {
                let pairs: Vec<(String, String)> = m
                    .path_pairs()
                    .iter()
                    .map(|(s, t)| (s.as_str().to_owned(), t.as_str().to_owned()))
                    .collect();
                (pairs, m.has_root_identity(), m.time_offset())
            });
            wire.push((diff.edits.clone(), mapping));
        }

        // Decode on the "remote" side and replay through its own edit target.
        let b = in_memory_stage()?;
        let root_b = b.edit_target().layer_identifier().to_string();
        b.set_edit_target(EditTarget::for_local_direct_variant(
            root_b,
            sdf::path("/Prim{mirror=m}")?,
        ))?;
        for (edits, mapping) in &wire {
            let mapping = match mapping {
                Some((pairs, root_identity, offset)) => {
                    let pairs = pairs
                        .iter()
                        .map(|(s, t)| Ok((sdf::path(s)?, sdf::path(t)?)))
                        .collect::<Result<Vec<_>>>()?;
                    let mut mapping = pcp::MapFunction::new(pairs);
                    if *root_identity {
                        mapping = mapping.with_root_identity();
                    }
                    Some(mapping.with_time_offset(*offset))
                }
                None => None,
            };
            b.apply_diff(
                &Diff {
                    edits: edits.clone(),
                    mapping,
                },
                ApplyMode::CurrentEditTarget,
            )?;
        }

        let data_b = b.root_layer();
        assert_eq!(
            data_b.data().spec_type(&sdf::path("/Prim{mirror=m}child")?),
            Some(sdf::SpecType::Prim)
        );
        Ok(())
    }

    /// `ExactLayer` mode replicates a variant-produced diff verbatim onto the
    /// named layer — the exact same-layer mirror, variant scaffolding included —
    /// regardless of the consuming stage's edit target.
    #[test]
    fn apply_diff_exact_layer() -> Result<()> {
        let a = in_memory_stage()?;
        a.define_prim("/Prim")?;
        let root = a.edit_target().layer_identifier().to_string();
        a.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim/child")?;

        let b = in_memory_stage()?;
        let root_b = b.root_layer().identifier().to_string();
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::ExactLayer(&root_b))?;
        }
        assert_eq!(
            b.root_layer().data().spec_type(&sdf::path("/Prim{set=sel}child")?),
            Some(sdf::SpecType::Prim)
        );
        // A layer the stage does not hold is refused, not silently substituted.
        assert!(matches!(
            b.apply_diff(&diffs.borrow()[0], ApplyMode::ExactLayer("not-a-layer.usda")),
            Err(StageAuthoringError::LayerNotFound { .. })
        ));
        Ok(())
    }

    /// A diff path the consuming arc target cannot reach refuses up front, before
    /// any spec is authored.
    #[test]
    fn apply_diff_outside_arc() -> Result<()> {
        let a = Stage::open(&fixture_path("ref_external.usda"))?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Elsewhere")?;

        let b = Stage::open(&fixture_path("ref_external.usda"))?;
        let target = b.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
        let _ctx = b.edit_context(target)?;
        assert!(matches!(
            b.apply_diff(&diffs.borrow()[0], ApplyMode::CurrentEditTarget),
            Err(StageAuthoringError::OutsideEditTarget { .. })
        ));
        assert!(!b.prim("/Elsewhere").is_valid()?);
        Ok(())
    }

    /// An authored bare `over` prim survives a translated replay: the diff
    /// records it as a `Create` operation, while namespace scaffolding never
    /// enters the edit list at all.
    #[test]
    fn apply_diff_keeps_bare_over() -> Result<()> {
        let a = Stage::open(&fixture_path("ref_external.usda"))?;
        let diffs = capture_diffs(&a);
        a.override_prim("/World/MyPrim/bare")?;

        let b = Stage::open(&fixture_path("ref_external.usda"))?;
        let target = b.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
        let _ctx = b.edit_context(target)?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        // The over landed at the arc-source path and composes back.
        assert!(!b.root_layer().data().has_spec(&sdf::path("/World/MyPrim/bare")?));
        assert!(b.prim("/World/MyPrim/bare").is_valid()?);
        Ok(())
    }

    /// Time-sample keys replayed through an arc target with a layer offset are
    /// re-keyed into the arc source's time frame, so they read back at the
    /// original stage times once composition re-applies the offset.
    #[test]
    fn apply_diff_retimes_samples() -> Result<()> {
        // `/Prim` references `/Source` with a (offset = 10) layer offset, so a
        // source-layer time `t` composes to stage time `t + 10`.
        let reference_stage = || -> Result<Stage> {
            let stage = in_memory_stage()?;
            stage.define_prim("/Source")?.create_attribute("x", "double")?;
            stage.define_prim("/Prim")?.set_metadata(
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    prim_path: sdf::path("/Source")?,
                    layer_offset: sdf::LayerOffset::new(10.0, 1.0),
                    ..Default::default()
                }])),
            )?;
            Ok(stage)
        };

        // The producer authors a sample at stage time 15 through its own arc
        // target, so the diff carries `/Source.x` keyed at source time 5 plus the
        // arc mapping with its offset.
        let a = reference_stage()?;
        let diffs = capture_diffs(&a);
        {
            let target = a.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Reference)?;
            let _ctx = a.edit_context(target)?;
            a.attribute("/Prim.x")
                .set_at(sdf::Value::Double(42.0), TimeCode::new(15.0))?;
        }

        // An identity consumer lifts the key through the producer's offset:
        // the sample lands on the local `/Prim.x` override, back at stage
        // time 15. The local attribute must exist — a field edit cannot
        // materialize an attribute spec.
        let b = reference_stage()?;
        b.create_attribute("/Prim.x", "double")?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        let local = b.attribute("/Prim.x").time_samples()?.expect("samples");
        assert_eq!(local, vec![(15.0, sdf::Value::Double(42.0))]);

        // An arc consumer maps it back into the source's time frame: keyed at
        // source time 5, reading back at stage time 15 through the offset.
        let c = reference_stage()?;
        {
            let target = c.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Reference)?;
            let _ctx = c.edit_context(target)?;
            for diff in diffs.borrow().iter() {
                c.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
            }
        }
        let source = c.attribute("/Source.x").time_samples()?.expect("samples");
        assert_eq!(source, vec![(5.0, sdf::Value::Double(42.0))]);
        assert_eq!(c.attribute("/Prim.x").get_at::<f64>(TimeCode::new(15.0))?, Some(42.0));
        Ok(())
    }

    /// A diff that fails mid-replay leaves the stage's layer untouched: the
    /// replay dry-runs against a scratch copy before touching the live layer.
    #[test]
    fn apply_diff_atomic() -> Result<()> {
        let stage = in_memory_stage()?;
        // A prim spec at a property path is unauthorable, and it sorts after
        // `/A`, so a non-atomic replay would author `/A` before failing on it.
        let diff = Diff {
            edits: vec![
                Edit::Create {
                    path: sdf::path("/A")?,
                    spec_type: sdf::SpecType::Prim,
                    fields: Vec::new(),
                },
                Edit::Create {
                    path: sdf::path("/B.x")?,
                    spec_type: sdf::SpecType::Prim,
                    fields: Vec::new(),
                },
            ],
            mapping: None,
        };
        assert!(matches!(
            stage.apply_diff(&diff, ApplyMode::CurrentEditTarget),
            Err(StageAuthoringError::Layer(_))
        ));
        assert!(!stage.root_layer().data().has_spec(&sdf::path("/A")?));
        Ok(())
    }

    /// A `SetField` cannot materialize an attribute spec the destination
    /// lacks — an attribute without a `typeName` is not valid scene
    /// description — so the replay fails atomically instead of authoring an
    /// unexportable spec.
    #[test]
    fn apply_diff_attr_needs_type() -> Result<()> {
        let a = in_memory_stage()?;
        a.create_attribute("/Prim.x", "double")?;
        let diffs = capture_diffs(&a);
        a.attribute("/Prim.x").set(2.0_f64)?;

        let b = in_memory_stage()?;
        assert!(matches!(
            b.apply_diff(&diffs.borrow()[0], ApplyMode::CurrentEditTarget),
            Err(StageAuthoringError::Layer(_))
        ));
        assert!(!b.root_layer().data().has_spec(&sdf::path("/Prim.x")?));
        Ok(())
    }

    /// A removal routed onto a variant spec cannot erase the scaffolding spec,
    /// so the replay clears its authored opinions instead of silently keeping
    /// what the producer deleted.
    #[test]
    fn apply_diff_removes_variant_opinions() -> Result<()> {
        let a = in_memory_stage()?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim")?.set_type_name("Xform")?;
        a.define_prim("/Prim/child")?;

        let b = in_memory_stage()?;
        let root = b.edit_target().layer_identifier().to_string();
        b.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        let variant = sdf::path("/Prim{set=sel}")?;
        let type_name = sdf::FieldKey::TypeName.as_str();
        assert!(b.root_layer().data().try_field(&variant, type_name)?.is_some());

        let replayed = diffs.borrow().len();
        a.remove_prim("/Prim")?;
        for diff in diffs.borrow().iter().skip(replayed) {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        // The variant spec survives as scaffolding, but the deleted prim's
        // opinions and children are gone.
        let layer = b.root_layer();
        let data = layer.data();
        assert!(data.try_field(&variant, type_name)?.is_none());
        assert!(!data.has_spec(&sdf::path("/Prim{set=sel}child")?));
        Ok(())
    }

    /// An embedded value path the consuming arc target cannot express fails
    /// up front instead of authoring an untranslated path into the arc's
    /// layer, where composition could map it onto an unrelated prim.
    #[test]
    fn apply_diff_value_outside_arc() -> Result<()> {
        let a = Stage::open(&fixture_path("ref_external.usda"))?;
        let diffs = capture_diffs(&a);
        a.create_attribute("/World/MyPrim/added.out", "double")?
            .set_connections([sdf::path("/Elsewhere.in")?])?;

        let b = Stage::open(&fixture_path("ref_external.usda"))?;
        let target = b.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
        let _ctx = b.edit_context(target)?;
        let replay = diffs
            .borrow()
            .iter()
            .try_for_each(|diff| b.apply_diff(diff, ApplyMode::CurrentEditTarget));
        assert!(matches!(replay, Err(StageAuthoringError::OutsideEditTarget { .. })));
        Ok(())
    }

    /// Replaying a `Create` reproduces the created spec's whole authored
    /// state: opinions the destination already held that the producer's spec
    /// lacks are cleared rather than merged.
    #[test]
    fn apply_diff_create_replaces() -> Result<()> {
        let a = in_memory_stage()?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim")?;

        let b = in_memory_stage()?;
        b.define_prim("/Prim")?.set_kind("component")?;
        let root = b.root_layer().identifier().to_string();
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::ExactLayer(&root))?;
        }
        assert_eq!(b.prim("/Prim").kind()?, None);
        Ok(())
    }

    /// A retargeted `Create` landing on the corresponding variant spec
    /// replaces its prim-level opinions: prim and variant specs hold the same
    /// fields, so the correspondence counts as a kind match for whole-state
    /// replication.
    #[test]
    fn apply_diff_create_replaces_variant() -> Result<()> {
        // The first mirror window routes a kind opinion onto the variant spec.
        let a = in_memory_stage()?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim")?.set_kind("component")?;

        let b = in_memory_stage()?;
        let root = b.edit_target().layer_identifier().to_string();
        b.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        let variant = sdf::path("/Prim{set=sel}")?;
        let kind = sdf::FieldKey::Kind.as_str();
        assert!(b.root_layer().data().try_field(&variant, kind)?.is_some());

        // A fresh producer's create of `/Prim` carries no kind; its whole
        // state replaces the variant spec's prim-level opinions on replay.
        let fresh = in_memory_stage()?;
        let fresh_diffs = capture_diffs(&fresh);
        fresh.define_prim("/Prim")?;
        for diff in fresh_diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        assert!(b.root_layer().data().try_field(&variant, kind)?.is_none());
        Ok(())
    }

    /// A `Create` landing on a property spec of the other kind replaces it:
    /// the destination's relationship gives way to the producer's attribute.
    #[test]
    fn apply_diff_create_replaces_kind() -> Result<()> {
        let a = in_memory_stage()?;
        a.define_prim("/Prim")?;
        let diffs = capture_diffs(&a);
        a.create_attribute("/Prim.x", "double")?;

        let b = in_memory_stage()?;
        b.define_prim("/Prim")?;
        b.create_relationship("/Prim.x")?;
        let root = b.root_layer().identifier().to_string();
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::ExactLayer(&root))?;
        }
        assert_eq!(
            b.root_layer().data().spec_type(&sdf::path("/Prim.x")?),
            Some(sdf::SpecType::Attribute)
        );
        Ok(())
    }

    /// A replay writes only the fields the edit touched: a consumer's
    /// unrelated opinions on the same spec survive, in both apply modes.
    #[test]
    fn apply_diff_merges_fields() -> Result<()> {
        let a = in_memory_stage()?;
        a.define_prim("/Prim")?.set_type_name("Xform")?;
        let diffs = capture_diffs(&a);
        a.prim("/Prim").set_kind("component")?;

        // The consumer holds its own typeName opinion; replaying the kind-only
        // edit must not overwrite it.
        let b = in_memory_stage()?;
        b.define_prim("/Prim")?.set_type_name("Scope")?;
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::CurrentEditTarget)?;
        }
        assert_eq!(b.prim("/Prim").kind()?.as_deref(), Some("component"));
        assert_eq!(b.prim("/Prim").type_name()?.as_deref(), Some("Scope"));

        let c = in_memory_stage()?;
        c.define_prim("/Prim")?.set_type_name("Scope")?;
        let root_c = c.root_layer().identifier().to_string();
        for diff in diffs.borrow().iter() {
            c.apply_diff(diff, ApplyMode::ExactLayer(&root_c))?;
        }
        assert_eq!(c.prim("/Prim").kind()?.as_deref(), Some("component"));
        assert_eq!(c.prim("/Prim").type_name()?.as_deref(), Some("Scope"));
        Ok(())
    }

    /// An exact replay of a variant-produced diff reports composed stage paths
    /// in its own change notice — the diff's mapping translates the authored
    /// layer paths back — so a chained mirror sees the right namespace.
    #[test]
    fn apply_diff_exact_notice_paths() -> Result<()> {
        let a = in_memory_stage()?;
        a.define_prim("/Prim")?;
        let root_a = a.edit_target().layer_identifier().to_string();
        a.set_edit_target(EditTarget::for_local_direct_variant(
            root_a,
            sdf::path("/Prim{set=sel}")?,
        ))?;
        let diffs = capture_diffs(&a);
        a.define_prim("/Prim/child")?;

        let b = in_memory_stage()?;
        let root_b = b.root_layer().identifier().to_string();
        let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
        let _id = {
            let resynced = resynced.clone();
            b.add_sink(move |_: &Stage, change: &CommittedChange<'_>| {
                resynced.borrow_mut().extend(change.resynced.iter().cloned());
            })
        };
        for diff in diffs.borrow().iter() {
            b.apply_diff(diff, ApplyMode::ExactLayer(&root_b))?;
        }
        let resynced = resynced.borrow();
        assert!(resynced.contains(&sdf::path("/Prim/child")?));
        assert!(!resynced.contains(&sdf::path("/Prim{set=sel}child")?));
        Ok(())
    }

    /// An operation that cannot be authored surfaces as a layer-authoring
    /// error, not a composition error: the replay is a `Layer`-tier operation,
    /// so its failure lands in `StageAuthoringError::Layer`.
    #[test]
    fn apply_diff_author_error() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.root_layer().identifier().to_string();
        // A prim spec at the absolute root is not authorable: the replay
        // rejects the root path when materializing the prim chain.
        let diff = Diff {
            edits: vec![Edit::Create {
                path: sdf::Path::abs_root(),
                spec_type: sdf::SpecType::Prim,
                fields: Vec::new(),
            }],
            mapping: None,
        };
        assert!(matches!(
            stage.apply_diff(&diff, ApplyMode::ExactLayer(&root)),
            Err(StageAuthoringError::Layer(_))
        ));
        Ok(())
    }
}
