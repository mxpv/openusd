//! The shared machinery behind stage-tier property authoring: where a spec
//! comes from when the edit target holds none, which fields the generic
//! metadata calls may not touch, and the closures that edit a typed spec.
//!
//! Creating or editing a property on the edit target follows C++
//! `UsdStage::_CreatePropertySpecForEditing` in two phases. The read phase,
//! [`plan_property_spec`], runs before any transaction and is the only place
//! composition is consulted: it resolves an [`EnsurePlan`] in C++ precedence
//! order — the edit target's own spec, the schema declaration, the strongest
//! authored spec of any kind, then the caller's fallback. The write phase,
//! [`apply_plan`], runs inside the single transaction and only rechecks the
//! local spec and stamps the resolved declaration. Splitting them keeps
//! composed queries out of the transaction closure, which holds the layer
//! graph mutably, and lets a caller stamp the spec and perform its own
//! mutation as one atomic edit. Holding the read phase of several
//! properties open before the write is what a [`StageEdit`] does, so a
//! batch of them commits together.

use std::cell::RefCell;
use std::fmt;
use std::sync::Arc;

use crate::{pcp, sdf, tf};

use super::attribute::AttributeAuthoringPlan;
use super::{
    Attribute, AttributeBuilder, EditTarget, Prim, PrimTypeInfo, Relationship, RelationshipBuilder, SpecSite, Stage,
    StageAuthoringError,
};

/// The properties queued for one stage transaction.
///
/// What [`Stage::edit`] hands its closure. The authoring entry points here
/// mirror the stage's own — [`prim`](Self::prim) for a prim to author on, and
/// the property builders for a path — but the builders they hand out queue
/// their property instead of committing it, so where a builder came from is
/// what puts it in the transaction. The queue is stamped and written when the
/// closure returns, as one edit of the target layer; any error — from the
/// closure, from a plan, from a [`sdf::LayerSink`] veto — leaves every property
/// unchanged.
///
/// Reads inside the closure see the stage as it stands, not what the batch has
/// queued: a queued property reaches the stage only when the batch commits.
///
/// The batch is tied to the edit target it opened on. Each queued property
/// resolved its spec path, its value and its sample time against that target,
/// so moving the target while the batch is open would write them somewhere
/// else; the batch reports
/// [`StageAuthoringError::EditTargetMoved`] rather than commit them through a
/// target they were not planned for.
pub struct StageEdit {
    stage: Stage,
    /// The edit target every queued property was planned against.
    target: EditTarget,
    queued: RefCell<Vec<PlannedProperty>>,
}

impl fmt::Debug for StageEdit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StageEdit").field("queued", &self.queued).finish()
    }
}

impl StageEdit {
    pub(super) fn new(stage: &Stage) -> Self {
        StageEdit {
            stage: stage.clone(),
            target: stage.edit_target(),
            queued: RefCell::new(Vec::new()),
        }
    }

    /// A prim to author on inside the transaction: [`Stage::prim`], whose
    /// property builders queue rather than commit.
    pub fn prim(&self, path: impl sdf::IntoPath) -> Result<PrimEdit<'_>, sdf::PathParseError> {
        Ok(PrimEdit {
            batch: self,
            prim: self.stage.prim(path)?,
        })
    }

    /// An attribute at a property path, queued rather than committed:
    /// [`Stage::attribute_builder`] inside the transaction.
    pub fn attribute_builder(
        &self,
        path: impl sdf::IntoPath,
        type_name: impl Into<sdf::ValueTypeName>,
    ) -> AttributeBuilder<'_> {
        self.stage.attribute_builder(path, type_name).in_batch(self)
    }

    /// A relationship at a property path, queued rather than committed:
    /// [`Stage::relationship_builder`] inside the transaction.
    pub fn relationship_builder(&self, path: impl sdf::IntoPath) -> RelationshipBuilder<'_> {
        self.stage.relationship_builder(path).in_batch(self)
    }

    /// Queues an already-planned property, and hands back where it will be
    /// authored for the builder to make its handle from.
    ///
    /// Returns [`StageAuthoringError::DuplicateProperty`] where the batch
    /// already holds that path — two plans for one property each resolve
    /// against a stage the other has not changed yet, so neither accounts for
    /// what the other declares.
    pub(super) fn queue(&self, planned: PlannedProperty) -> Result<(Stage, sdf::Path), StageAuthoringError> {
        let mut queued = self.queued.borrow_mut();
        if queued.iter().any(|other| other.path == planned.path) {
            return Err(StageAuthoringError::DuplicateProperty { path: planned.path });
        }
        let site = (planned.stage.clone(), planned.path.clone());
        queued.push(planned);
        Ok(site)
    }

    /// That the stage still has the edit target the batch planned against,
    /// checked before a builder plans against it and again before the queue is
    /// written.
    ///
    /// A property's spec path, its value and its sample time are all resolved
    /// through the target that was current when it was queued, so a target the
    /// batch did not plan for would put the write somewhere else.
    pub(super) fn holds_target(&self) -> Result<(), StageAuthoringError> {
        match self.stage.holds_edit_target(&self.target) {
            true => Ok(()),
            false => Err(StageAuthoringError::EditTargetMoved),
        }
    }

    /// Stamps and writes every queued property as one transaction.
    pub(super) fn commit(self) -> Result<(), StageAuthoringError> {
        if self.queued.borrow().is_empty() {
            return Ok(());
        }
        self.holds_target()?;

        let (paths, writes): (Vec<sdf::Path>, Vec<PropertyWrite>) = self
            .queued
            .into_inner()
            .into_iter()
            .map(|property| (property.path, property.write))
            .unzip();
        self.stage
            .with_target_layer_at_each(&paths, move |layer, spec_paths| {
                for (write, spec_path) in writes.into_iter().zip(spec_paths) {
                    write.apply(layer.data_mut(), &spec_path)?;
                }
                Ok(())
            })
            .map(|_| ())
    }
}

/// A prim to author on inside a [`StageEdit`]'s transaction.
///
/// The transaction-bound counterpart of [`Prim`]: the same property builders,
/// each queued into the batch rather than committed on its own. Reads go
/// through [`prim`](Self::prim), and see the stage as it stands rather than
/// what the batch has queued.
#[derive(Debug)]
pub struct PrimEdit<'a> {
    batch: &'a StageEdit,
    prim: Prim,
}

impl<'a> PrimEdit<'a> {
    /// The prim itself, for reading it.
    ///
    /// It is an ordinary [`Prim`], so its own authoring methods author on their
    /// own: only the builders below queue into the transaction.
    pub fn prim(&self) -> &Prim {
        &self.prim
    }

    /// An attribute on the prim, queued rather than committed:
    /// [`Prim::attribute_builder`] inside the transaction.
    pub fn attribute_builder(
        &self,
        name: impl Into<tf::Token>,
        type_name: impl Into<sdf::ValueTypeName>,
    ) -> AttributeBuilder<'a> {
        self.prim.attribute_builder(name, type_name).in_batch(self.batch)
    }

    /// A relationship on the prim, queued rather than committed:
    /// [`Prim::relationship_builder`] inside the transaction.
    pub fn relationship_builder(&self, name: impl Into<tf::Token>) -> RelationshipBuilder<'a> {
        self.prim.relationship_builder(name).in_batch(self.batch)
    }
}

/// A property resolved against composed state, waiting for the transaction
/// that writes it.
///
/// What a builder produces: the composed reads the write depends on are already
/// done, so applying it needs nothing but the edit target's layer. That is what
/// lets several properties share one transaction: the read phase a single
/// property's write already runs first, held open long enough to collect more
/// of them.
#[derive(Debug)]
pub(super) struct PlannedProperty {
    stage: Stage,
    path: sdf::Path,
    write: PropertyWrite,
}

/// The write phase of one property, run against the edit target's own spec path
/// for it: all a [`PlannedProperty`] has left to do once the transaction opens.
#[derive(Debug)]
pub(super) enum PropertyWrite {
    /// An attribute declared, and left at whatever value it has.
    Attribute(EnsurePlan),
    /// An attribute declared and given the value planned for it.
    AttributeValue(AttributeAuthoringPlan),
    /// A relationship declared, and its targets replaced where the caller gave
    /// some.
    Relationship {
        ensure: EnsurePlan,
        targets: Option<Vec<sdf::Path>>,
    },
}

impl PlannedProperty {
    pub(super) fn new(stage: Stage, path: sdf::Path, write: PropertyWrite) -> Self {
        PlannedProperty { stage, path, write }
    }

    /// Writes the property on its own, as one transaction, and hands back where
    /// it was authored for the caller to build its handle from.
    pub(super) fn commit(self) -> Result<(Stage, sdf::Path), StageAuthoringError> {
        let PlannedProperty { stage, path, write } = self;
        stage.with_target_layer_at(&path, move |layer, spec_path| write.apply(layer.data_mut(), &spec_path))?;
        Ok((stage, path))
    }
}

impl PropertyWrite {
    fn apply(self, data: &mut dyn sdf::AbstractData, path: &sdf::Path) -> Result<(), StageAuthoringError> {
        match self {
            Self::Attribute(ensure) => apply_plan(data, path, Attribute::KIND, &ensure),
            Self::AttributeValue(plan) => plan.write(data, path),
            Self::Relationship { ensure, targets } => {
                apply_plan(data, path, Relationship::KIND, &ensure)?;
                let Some(targets) = targets else {
                    return Ok(());
                };
                edit_spec(data, path.clone(), Relationship::KIND, Relationship::view, |spec| {
                    Ok(spec.set_target_paths(targets)?)
                })
            }
        }
    }
}

/// A property kind, as the authoring operations below work on it: what its
/// specs are, and how one is opened for editing.
///
/// Implemented on the stage-tier handles, so an operation names the thing being
/// authored: `author::<Attribute>`.
pub(super) trait PropertySpecKind {
    /// What a spec of this kind answers to, for the checks that a path holds
    /// the kind the caller meant.
    const KIND: sdf::SpecType;

    /// A mutable view of one, borrowed from the layer that holds it.
    type View<'a>;

    /// Opens the spec at `path`, or `None` where the layer holds none.
    fn view(data: &mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self::View<'_>>;
}

impl PropertySpecKind for Attribute {
    const KIND: sdf::SpecType = sdf::SpecType::Attribute;

    type View<'a> = sdf::AttributeSpecMut<'a>;

    fn view(data: &mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self::View<'_>> {
        sdf::AttributeSpecMut::get(data, path)
    }
}

impl PropertySpecKind for Relationship {
    const KIND: sdf::SpecType = sdf::SpecType::Relationship;

    type View<'a> = sdf::RelationshipSpecMut<'a>;

    fn view(data: &mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self::View<'_>> {
        sdf::RelationshipSpecMut::get(data, path)
    }
}

/// Stamps the spec `path` needs on the edit target and runs `edit` on it, as
/// one transaction.
///
/// The phase order lives here: the read that resolves where the spec comes
/// from, then the transaction that stamps it and mutates it. A caller supplies
/// the mutation alone, typed to the spec its kind opens.
pub(super) fn author<P: PropertySpecKind>(
    stage: &Stage,
    path: &sdf::Path,
    edit: impl FnOnce(&mut P::View<'_>) -> Result<(), StageAuthoringError>,
) -> Result<(), StageAuthoringError> {
    let plan = plan_property_spec(stage, path, P::KIND, None)?;
    stage
        .with_target_layer_at(path, |layer, spec_path| {
            apply_plan(layer.data_mut(), &spec_path, P::KIND, &plan)?;
            edit_spec(layer.data_mut(), spec_path, P::KIND, P::view, edit)
        })
        .map(|_| ())
}

/// Runs `edit` on the spec `path` already has on the edit target, and does
/// nothing where it has none.
///
/// The path every clear takes. Removing an opinion never stamps a spec to
/// remove it from, so a layer that says nothing about the property goes on
/// saying nothing — which is what parts this from [`author`], and why the two
/// are separate operations rather than one asked to skip a phase.
pub(super) fn edit_existing<P: PropertySpecKind>(
    stage: &Stage,
    path: &sdf::Path,
    edit: impl FnOnce(&mut P::View<'_>) -> Result<(), StageAuthoringError>,
) -> Result<(), StageAuthoringError> {
    stage
        .with_target_layer_at(path, |layer, spec_path| {
            edit_existing_spec(layer.data_mut(), spec_path, P::KIND, P::view, edit)
        })
        .map(|_| ())
}

/// What a property spec stamped on the edit target declares: the fields C++
/// `_StampNewPropertySpec` copies from the declaration it found.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum PropertyDeclaration {
    Attribute {
        type_name: sdf::ValueTypeName,
        variability: sdf::Variability,
        custom: bool,
    },
    Relationship {
        variability: sdf::Variability,
        custom: bool,
    },
}

impl PropertyDeclaration {
    pub fn kind(&self) -> sdf::SpecType {
        match self {
            Self::Attribute { .. } => sdf::SpecType::Attribute,
            Self::Relationship { .. } => sdf::SpecType::Relationship,
        }
    }
}

/// The read phase's answer for a property about to be authored.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum EnsurePlan {
    /// The edit target already holds a spec of the wanted kind, which is left
    /// as it is.
    Existing,
    /// The edit target holds no spec; this declaration is stamped first.
    Stamp(PropertyDeclaration),
}

impl EnsurePlan {
    /// The value type this plan would declare an attribute with, or `None`
    /// when it stamps nothing — a target that already holds the spec says
    /// nothing about the type — or stamps a relationship.
    pub fn attribute_type(&self) -> Option<&sdf::ValueTypeName> {
        match self {
            Self::Stamp(PropertyDeclaration::Attribute { type_name, .. }) => Some(type_name),
            // A target that already holds the spec says nothing about its
            // type, and a relationship plan never reaches a value write.
            Self::Existing | Self::Stamp(PropertyDeclaration::Relationship { .. }) => None,
        }
    }
}

/// The read phase of authoring the property at `path` as a `kind` spec.
///
/// In C++ precedence order: a spec of that kind already on the edit target is
/// [`EnsurePlan::Existing`]; otherwise the schema declaration, then the
/// strongest authored spec of any kind, supplies the declaration to stamp; only
/// when nothing declares the property does `fallback` apply (`None` for an
/// edit, the supplied declaration for a creation). A declaration of the other
/// kind found at any of those sources is
/// [`SpecKindMismatch`](StageAuthoringError::SpecKindMismatch), never skipped
/// in favour of a weaker one. A declaration taken from a layer is read with
/// the fallible readers, so a malformed strongest spec is an error; the
/// fallback is checked only when it is stamped.
pub(super) fn plan_property_spec(
    stage: &Stage,
    path: &sdf::Path,
    kind: sdf::SpecType,
    fallback: Option<PropertyDeclaration>,
) -> Result<EnsurePlan, StageAuthoringError> {
    if let Some(found) = stage.local_spec_type(path)? {
        return if found == kind {
            Ok(EnsurePlan::Existing)
        } else {
            Err(kind_mismatch(path, kind, found))
        };
    }
    let Some((info, name)) = schema_definition(stage, path)? else {
        return Err(sdf::AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "property authoring needs a property path",
        }
        .into());
    };

    if let Some(property) = info.prim_definition().property(&name) {
        let found = property.spec_type();
        if found != kind {
            return Err(kind_mismatch(path, kind, found));
        }
        let declaration = if kind == sdf::SpecType::Attribute {
            PropertyDeclaration::Attribute {
                type_name: property
                    .type_name_token()
                    .map(sdf::ValueTypeName::from)
                    .ok_or(sdf::ValueTypeError::Empty)?,
                variability: property.variability(),
                custom: false,
            }
        } else {
            PropertyDeclaration::Relationship {
                variability: property.variability(),
                custom: false,
            }
        };
        return Ok(EnsurePlan::Stamp(declaration));
    }

    let strongest = stage
        .masked(path, |graph, cache| cache.property_stack(graph, path, None))?
        .into_iter()
        .next();
    if let Some(site) = strongest {
        let declaration = declaration_at(stage, &site, kind)?;
        if declaration.kind() != kind {
            return Err(kind_mismatch(path, kind, declaration.kind()));
        }
        return Ok(EnsurePlan::Stamp(declaration));
    }

    fallback.map(EnsurePlan::Stamp).ok_or_else(|| missing_spec(path, kind))
}

/// The write phase: inside the transaction, recheck the edit target's spec
/// at `path` and stamp the plan's declaration when it holds none.
pub(super) fn apply_plan(
    data: &mut dyn sdf::AbstractData,
    path: &sdf::Path,
    kind: sdf::SpecType,
    plan: &EnsurePlan,
) -> Result<(), StageAuthoringError> {
    match data.spec_type(path) {
        Some(found) if found == kind => Ok(()),
        Some(found) => Err(kind_mismatch(path, kind, found)),
        None => match plan {
            EnsurePlan::Existing => Err(missing_spec(path, kind)),
            EnsurePlan::Stamp(declaration) => stamp(data, path, declaration),
        },
    }
}

/// The schema of the prim the property at `path` hangs off, with the
/// property's own name: the pair every schema-declaration lookup starts from
/// (C++ `UsdStage::_GetSchemaProperty`). `None` when `path` is not a property
/// path.
pub(super) fn schema_definition(
    stage: &Stage,
    path: &sdf::Path,
) -> Result<Option<(Arc<PrimTypeInfo>, tf::Token)>, pcp::QueryError> {
    let Some((prim, name)) = path.split_property() else {
        return Ok(None);
    };
    Ok(Some((stage.prim_type_info_composed(prim)?, tf::Token::from(name))))
}

/// Run `f` on the `kind` spec at `path` on the edit-target layer, or return
/// [`sdf::AuthoringError::InvalidPath`] when no such spec exists. `get` is the
/// spec view's constructor (e.g. `sdf::PrimSpecMut::get`). The shared body of
/// the `usd`-tier authoring closures.
pub(super) fn edit_spec<'a, S>(
    data: &'a mut dyn sdf::AbstractData,
    path: sdf::Path,
    kind: sdf::SpecType,
    get: impl FnOnce(&'a mut dyn sdf::AbstractData, sdf::Path) -> Option<S>,
    f: impl FnOnce(&mut S) -> Result<(), StageAuthoringError>,
) -> Result<(), StageAuthoringError> {
    match get(data, path.clone()) {
        Some(mut spec) => f(&mut spec),
        None => Err(missing_spec(&path, kind)),
    }
}

/// The non-creating counterpart of [`edit_spec`]: run `f` on the `kind` spec
/// at `path` when the edit-target layer holds one, do nothing when it holds
/// none, and report a spec of the other kind. The clear operations use it, so
/// removing an opinion never stamps a spec to remove it from.
pub(super) fn edit_existing_spec<'a, S>(
    data: &'a mut dyn sdf::AbstractData,
    path: sdf::Path,
    kind: sdf::SpecType,
    get: impl FnOnce(&'a mut dyn sdf::AbstractData, sdf::Path) -> Option<S>,
    f: impl FnOnce(&mut S) -> Result<(), StageAuthoringError>,
) -> Result<(), StageAuthoringError> {
    match data.spec_type(&path) {
        None => Ok(()),
        Some(found) if found == kind => {
            let mut spec = get(data, path).expect("the kind was checked");
            f(&mut spec)
        }
        Some(found) => Err(kind_mismatch(&path, kind, found)),
    }
}

/// Rejects `key` when a `kind` spec authors it only through a dedicated,
/// validated setter, so the generic metadata calls cannot bypass the
/// invariants those setters keep. This is this crate's authoring
/// restriction, not a fact about the field: C++ `_IsPrivateFieldKey` is a
/// read-side classifier of value, arc and clip fields that does not police
/// `SetMetadata`, and a state only the raw field reaches — a whole-field
/// `timeSamples` block, an empty sample map — is authored on the layer
/// through [`sdf::Layer::edit`].
// TODO: the reserved fields belong in a per-spec-type field definition, the
// counterpart of C++ `SdfSchema::SpecDefinition`, which would also own the
// required-field knowledge `usda::parser::KNOWN_PROPS` keeps. Until then a
// prim's `typeName`, `active`, `hidden`, `kind` and `instanceable` have
// dedicated setters but stay reachable here, since gating them needs the
// matching clear operations first; `spline` joins the attribute list once
// splines are authored.
pub(super) fn check_reserved(kind: sdf::SpecType, key: &'static str) -> Result<(), StageAuthoringError> {
    let reserved: &[sdf::FieldKey] = match kind {
        sdf::SpecType::Attribute => &[
            sdf::FieldKey::Default,
            sdf::FieldKey::TimeSamples,
            sdf::FieldKey::TypeName,
            sdf::FieldKey::ConnectionPaths,
            sdf::FieldKey::Variability,
            sdf::FieldKey::Custom,
        ],
        sdf::SpecType::Relationship => &[
            sdf::FieldKey::TargetPaths,
            sdf::FieldKey::Variability,
            sdf::FieldKey::Custom,
        ],
        _ => &[],
    };
    if reserved.iter().any(|field| field.as_str() == key) {
        return Err(StageAuthoringError::ReservedField { field: key });
    }
    Ok(())
}

/// The declaration the spec at `site` carries, read from that layer with the
/// fallible readers; `wanted` names the kind being authored for the error
/// when the site holds none.
fn declaration_at(
    stage: &Stage,
    site: &SpecSite,
    wanted: sdf::SpecType,
) -> Result<PropertyDeclaration, StageAuthoringError> {
    let layer = stage
        .layer(&site.layer)
        .ok_or_else(|| StageAuthoringError::LayerNotFound {
            layer: site.layer.clone(),
        })?;
    declaration_of(layer.data(), &site.path, wanted)
}

/// The declaration a layer's property spec at `path` carries. An attribute
/// without a `typeName` is [`sdf::ValueTypeError::Empty`], a field holding
/// the wrong variant [`sdf::SpecError::FieldType`], and a decode failure a
/// [`sdf::DataError`]: a malformed declaration is never silently repaired.
fn declaration_of(
    data: &dyn sdf::AbstractData,
    path: &sdf::Path,
    wanted: sdf::SpecType,
) -> Result<PropertyDeclaration, StageAuthoringError> {
    match data.spec_type(path) {
        Some(sdf::SpecType::Attribute) => {
            let spec = sdf::AttributeSpecRef::get(data, path.clone()).expect("the kind was checked");
            Ok(PropertyDeclaration::Attribute {
                type_name: spec.declared_type()?.ok_or(sdf::ValueTypeError::Empty)?,
                variability: spec
                    .typed_field(sdf::FieldKey::Variability, "Variability")?
                    .unwrap_or_default(),
                custom: spec.typed_field(sdf::FieldKey::Custom, "Bool")?.unwrap_or(false),
            })
        }
        Some(sdf::SpecType::Relationship) => {
            let spec = sdf::RelationshipSpecRef::get(data, path.clone()).expect("the kind was checked");
            Ok(PropertyDeclaration::Relationship {
                variability: spec
                    .typed_field(sdf::FieldKey::Variability, "Variability")?
                    .unwrap_or_default(),
                custom: spec.typed_field(sdf::FieldKey::Custom, "Bool")?.unwrap_or(false),
            })
        }
        Some(found) => Err(kind_mismatch(path, wanted, found)),
        None => Err(missing_spec(path, wanted)),
    }
}

fn stamp(
    data: &mut dyn sdf::AbstractData,
    path: &sdf::Path,
    declaration: &PropertyDeclaration,
) -> Result<(), StageAuthoringError> {
    match declaration {
        PropertyDeclaration::Attribute {
            type_name,
            variability,
            custom,
        } => {
            sdf::AttributeSpec::new(data, path.clone(), type_name.clone(), *variability, *custom)?;
        }
        PropertyDeclaration::Relationship { variability, custom } => {
            sdf::RelationshipSpec::new(data, path.clone(), *variability, *custom)?;
        }
    }
    Ok(())
}

fn kind_mismatch(path: &sdf::Path, expected: sdf::SpecType, found: sdf::SpecType) -> StageAuthoringError {
    StageAuthoringError::SpecKindMismatch {
        path: path.clone(),
        expected,
        found,
    }
}

/// The error for a `kind` spec the edit target was expected to hold at
/// `path` and does not.
pub(super) fn missing_spec(path: &sdf::Path, kind: sdf::SpecType) -> StageAuthoringError {
    let reason = match kind {
        sdf::SpecType::Prim => "no prim spec at path on the edit target layer",
        sdf::SpecType::Attribute => "no attribute spec at path on the edit target layer",
        sdf::SpecType::Relationship => "no relationship spec at path on the edit target layer",
        _ => "no spec at path on the edit target layer",
    };
    sdf::AuthoringError::InvalidPath {
        path: path.clone(),
        reason,
    }
    .into()
}

#[cfg(test)]
mod tests {
    use crate::Result;
    use crate::sdf;
    use crate::usd::{EditTarget, Stage, StageAuthoringError, TimeCode};

    fn stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    /// An edit target on the same layer that maps `/World` into a variant, so
    /// a property planned against the stage's own target would land elsewhere
    /// through this one.
    fn variant_target(stage: &Stage) -> Result<EditTarget, sdf::PathParseError> {
        let root = stage.edit_target().layer_identifier().to_string();
        EditTarget::for_local_direct_variant(root, "/World{set=sel}")
    }

    /// Attributes and relationships share the one batch, and the closure's own
    /// value comes back once they commit.
    #[test]
    fn batch_authors_together() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/World")?;
        let (height, proxy) = stage.edit(|edit| {
            let world = edit.prim("/World")?;
            let height = world.attribute_builder("height", "double").set(2.0).build()?;
            let proxy = world
                .relationship_builder("proxy")
                .custom(false)
                .set_targets(["/World"])
                .build()?;
            Ok((height, proxy))
        })?;

        assert_eq!(height.get::<f64>()?, Some(2.0));
        assert_eq!(proxy.targets()?, vec![sdf::Path::new("/World")?]);
        assert!(!proxy.is_custom()?);
        Ok(())
    }

    /// A property path reaches the batch without naming its prim first.
    #[test]
    fn batch_takes_property_paths() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/World")?;
        let height = stage.edit(|edit| edit.attribute_builder("/World.height", "double").set(2.0).build())?;

        assert_eq!(height.get::<f64>()?, Some(2.0));
        Ok(())
    }

    /// Where a builder came from is what puts it in the transaction: one taken
    /// from the prim itself commits on its own, batch or no batch.
    #[test]
    fn prim_builder_commits_now() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        let failed = stage.edit(|edit| {
            prim.attribute_builder("height", "double").set(2.0).build()?;
            edit.prim("/World")?
                .attribute_builder("radius", "double")
                .set(1.0)
                .build()?;
            Err::<(), _>(StageAuthoringError::OutsideEditTarget {
                path: sdf::Path::new("/World.radius")?,
            })
        });

        assert!(failed.is_err());
        // The queued property is rolled back with the batch; the one that
        // committed on its own is already on the stage.
        assert!(prim.attribute("height").is_defined()?);
        assert!(!prim.attribute("radius").is_defined()?);
        Ok(())
    }

    /// A closure that gives up leaves the stage as it was, however much it
    /// queued first.
    #[test]
    fn batch_error_authors_none() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        let failed = stage.edit(|edit| {
            edit.prim("/World")?
                .attribute_builder("height", "double")
                .set(2.0)
                .build()?;
            Err::<(), _>(StageAuthoringError::OutsideEditTarget {
                path: sdf::Path::new("/World.height")?,
            })
        });

        assert!(matches!(failed, Err(StageAuthoringError::OutsideEditTarget { .. })));
        assert!(!prim.attribute("height").is_defined()?);
        Ok(())
    }

    /// Two plans for one property would each resolve against a stage the other
    /// has not changed, so the batch refuses the second.
    #[test]
    fn duplicate_property_rejected() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        let failed = stage.edit(|edit| {
            let world = edit.prim("/World")?;
            world.attribute_builder("height", "double").set(2.0).build()?;
            world.attribute_builder("height", "double").set(3.0).build()
        });

        assert!(matches!(failed, Err(StageAuthoringError::DuplicateProperty { .. })));
        assert!(!prim.attribute("height").is_defined()?);
        Ok(())
    }

    /// A queued property was planned against one edit target — its spec path,
    /// its value and its sample time all mapped through that target — so the
    /// batch refuses to write it through another.
    #[test]
    fn target_move_rejected() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        let variant = variant_target(&stage)?;

        let failed = stage.edit(|edit| {
            edit.prim("/World")?
                .attribute_builder("height", "double")
                .set_at(2.0, TimeCode::new(15.0))
                .build()?;
            stage.set_edit_target(variant.clone())?;
            Ok(())
        });

        assert!(matches!(failed, Err(StageAuthoringError::EditTargetMoved)));
        assert!(!prim.attribute("height").is_defined()?);
        Ok(())
    }

    /// The same move caught as it happens, rather than at the commit that
    /// would have written through the wrong target.
    #[test]
    fn target_move_rejects_queue() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/World")?;
        let variant = variant_target(&stage)?;

        let failed = stage.edit(|edit| {
            stage.set_edit_target(variant.clone())?;
            edit.prim("/World")?
                .attribute_builder("height", "double")
                .set(2.0)
                .build()
        });

        assert!(matches!(failed, Err(StageAuthoringError::EditTargetMoved)));
        Ok(())
    }

    /// An empty batch is a no-op that still hands back the closure's value.
    #[test]
    fn empty_batch_authors_nothing() -> Result<()> {
        let stage = stage()?;
        assert_eq!(stage.edit(|_| Ok(7))?, 7);
        Ok(())
    }
}
