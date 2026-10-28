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

use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::{fmt, mem};

use crate::{pcp, sdf, tf};

use super::attribute::AttributeAuthoringPlan;
use super::{
    Attribute, AttributeBuilder, EditTarget, Prim, PrimTypeId, PrimTypeInfo, Relationship, RelationshipBuilder,
    SpecSite, Stage, StageAuthoringError,
};

/// The prims and properties queued for one stage transaction.
///
/// What [`Stage::edit`] hands its closure. The authoring entry points here
/// mirror the stage's own: [`define_prim`](Self::define_prim),
/// [`define_typed_prim`](Self::define_typed_prim) and
/// [`override_prim`](Self::override_prim) for prims,
/// [`prim`](Self::prim) for a prim to author on, and the property builders
/// for a path. Each queues its operation instead of committing it, so where a
/// builder came from is what puts it in the transaction. The queue is written
/// when the closure returns, as one edit of the target layer; any error —
/// from the closure, from a plan, from a [`sdf::LayerSink`] veto — leaves
/// every prim and property unchanged.
///
/// Every operation is planned before anything is written. A plan reads the
/// stage as it stands with the prim opinions the batch has queued so far
/// composed in: a property queued after a prim is defined plans against the
/// type that definition leaves, on that prim and on every prim that composes
/// it. Values and properties the batch has queued are not read back. For
/// every batch it accepts, the commit authors what the same calls made one
/// after another would author. C++ recomposes between those calls, and a
/// batch cannot, so it refuses the sequences whose result it cannot show
/// beforehand:
///
/// - [`PlannedTypeChanged`](StageAuthoringError::PlannedTypeChanged): a prim
///   operation would change the schema a queued property was planned against;
/// - [`PlannedEffectUnknown`](StageAuthoringError::PlannedEffectUnknown): a
///   queued spec would revive a culled arc target, an index only a rebuild
///   composes, in a prim the batch has planned against or reads afterwards;
/// - [`PlanStale`](StageAuthoringError::PlanStale): a change made outside the
///   batch while it was open — a commit, a muting or load-rule change —
///   moved a prim it read. Any such change that moves the population or a
///   schema opinion counts, wherever it is on the stage.
///
/// The batch is tied to the edit target it opened on. Each queued operation
/// resolved its spec path, its value and its sample time against that target,
/// so moving the target while the batch is open would write them somewhere
/// else; the batch reports
/// [`StageAuthoringError::EditTargetMoved`] rather than commit them through a
/// target they were not planned for.
pub struct StageEdit {
    stage: Stage,
    /// The edit target every queued operation was planned against.
    target: EditTarget,
    plan: RefCell<PlanState>,
}

impl fmt::Debug for StageEdit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StageEdit").field("plan", &self.plan).finish()
    }
}

impl StageEdit {
    pub(super) fn new(stage: &Stage) -> Self {
        StageEdit {
            stage: stage.clone(),
            target: stage.edit_target(),
            plan: RefCell::new(PlanState::new(stage)),
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

    /// A `def` prim spec at `path`, queued rather than committed:
    /// [`Stage::define_prim`] inside the transaction.
    pub fn define_prim(&self, path: impl sdf::IntoPath) -> Result<PrimEdit<'_>, StageAuthoringError> {
        self.define_typed_prim(path, "")
    }

    /// A `def` prim spec typed `type_name` at `path`, queued rather than
    /// committed: [`Stage::define_typed_prim`] inside the transaction, decided
    /// against the prims the batch has already queued.
    pub fn define_typed_prim(
        &self,
        path: impl sdf::IntoPath,
        type_name: impl Into<String>,
    ) -> Result<PrimEdit<'_>, StageAuthoringError> {
        let type_name = tf::Token::from(type_name.into());
        self.queue_prim(path, PrimOp::Define { type_name })
    }

    /// A prim spec at `path` where the stage holds no prim there, queued
    /// rather than committed: [`Stage::override_prim`] inside the transaction.
    /// A prim the batch has already defined is held, so nothing more is
    /// queued for it.
    pub fn override_prim(&self, path: impl sdf::IntoPath) -> Result<PrimEdit<'_>, StageAuthoringError> {
        self.queue_prim(path, PrimOp::Override)
    }

    /// An attribute at a property path, queued rather than committed:
    /// [`Stage::attribute_builder`] inside the transaction.
    pub fn attribute_builder(
        &self,
        path: impl sdf::IntoPath,
        type_name: impl Into<sdf::ValueTypeName>,
    ) -> AttributeBuilder<'_> {
        self.stage.attribute_builder(path, type_name).in_edit(self)
    }

    /// A relationship at a property path, queued rather than committed:
    /// [`Stage::relationship_builder`] inside the transaction.
    pub fn relationship_builder(&self, path: impl sdf::IntoPath) -> RelationshipBuilder<'_> {
        self.stage.relationship_builder(path).in_edit(self)
    }

    /// Queues several operations as one: all of what `f` queues joins the
    /// transaction, or none of it does.
    ///
    /// `f` receives a batch of its own, on the edit target this one planned
    /// against, which plans against what this batch has queued so far. When
    /// `f` succeeds its operations join this batch in order, each admitted
    /// again against what this batch holds by then: `f` may have written
    /// through this batch while its own was open. When `f` fails, or one of
    /// its operations is refused, none of them joins, so an operation made of
    /// several writes leaves no part of itself queued behind an error the
    /// caller goes on from.
    ///
    /// Nothing is written until the outermost batch commits.
    pub fn group<T, E>(&self, f: impl FnOnce(&StageEdit) -> Result<T, E>) -> Result<T, E>
    where
        E: From<StageAuthoringError>,
    {
        let group = StageEdit {
            stage: self.stage.clone(),
            target: self.target.clone(),
            plan: RefCell::new(self.plan.borrow().fork()),
        };
        let value = f(&group)?;
        self.absorb(group.plan.into_inner())?;
        Ok(value)
    }

    /// Admits `group`'s operations into this batch, in order, on a copy of
    /// what it holds, and keeps the copy only when every one is admitted.
    ///
    /// The group forked this plan, so its stamps cover every prim this plan
    /// had read by then; the commit checks the ones this plan read since.
    // TODO(perf): the group and the copy are each a full fork of the plan, so
    // a batch made of many groups copies its state once per group.
    fn absorb(&self, group: PlanState) -> Result<(), StageAuthoringError> {
        group.check_fresh(&self.stage)?;
        let mut merged = self.plan.borrow().fork();
        for write in group.writes {
            merged.admit(&self.stage, write.into_operation())?;
        }
        let mut plan = self.plan.borrow_mut();
        let mut writes = mem::take(&mut plan.writes);
        writes.append(&mut merged.writes);
        *plan = PlanState { writes, ..merged };
        Ok(())
    }

    /// Queues the prim operation `op` at `path`, and hands back the prim to
    /// author on.
    fn queue_prim(&self, path: impl sdf::IntoPath, op: PrimOp) -> Result<PrimEdit<'_>, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
        self.admit(Operation::Prim { path: path.clone(), op })?;
        Ok(PrimEdit {
            batch: self,
            prim: Prim::new(&self.stage, path),
        })
    }

    /// Queues an already-planned property, and hands back where it will be
    /// authored for the builder to make its handle from.
    ///
    /// Returns [`StageAuthoringError::EditOfAnotherStage`] for a property
    /// planned on another stage, which this batch has no layer to write to,
    /// and [`StageAuthoringError::DuplicateProperty`] where the batch
    /// already holds that path — two plans for one property each resolve
    /// against a stage the other has not changed yet, so neither accounts for
    /// what the other declares.
    pub(super) fn queue(&self, planned: PlannedProperty) -> Result<(Stage, sdf::Path), StageAuthoringError> {
        if planned.stage != self.stage {
            return Err(StageAuthoringError::EditOfAnotherStage { path: planned.path });
        }
        let site = (planned.stage.clone(), planned.path.clone());
        self.admit(Operation::Property(planned))?;
        Ok(site)
    }

    /// Admits `operation` into the batch, on the edit target it planned
    /// against.
    fn admit(&self, operation: Operation) -> Result<(), StageAuthoringError> {
        self.holds_target()?;
        self.plan.borrow_mut().admit(&self.stage, operation)
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

    /// Writes every queued operation as one transaction.
    pub(super) fn commit(self) -> Result<(), StageAuthoringError> {
        if self.plan.borrow().writes.is_empty() {
            return Ok(());
        }
        self.holds_target()?;
        self.plan.into_inner().commit(&self.stage)
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
    /// own: only the builders and setters below queue into the transaction.
    pub fn prim(&self) -> &Prim {
        &self.prim
    }

    /// The prim's `typeName` on the edit target, queued rather than
    /// committed: [`Prim::set_type_name`] inside the transaction. The prim
    /// must be one the stage holds once the batch's queued prims are written,
    /// and properties queued under it afterwards plan against the type. An
    /// empty name erases the edit target's `typeName`.
    pub fn set_type_name(&self, name: impl Into<String>) -> Result<&Self, StageAuthoringError> {
        let type_name = tf::Token::from(name.into());
        self.batch.admit(Operation::Prim {
            path: self.prim.path().clone(),
            op: PrimOp::SetType { type_name },
        })?;
        Ok(self)
    }

    /// An attribute on the prim, queued rather than committed:
    /// [`Prim::attribute_builder`] inside the transaction, on a prim the
    /// stage holds once the batch's queued prims are written.
    pub fn attribute_builder(
        &self,
        name: impl Into<tf::Token>,
        type_name: impl Into<sdf::ValueTypeName>,
    ) -> AttributeBuilder<'a> {
        AttributeBuilder::new(self.property_site(name.into()), type_name.into()).in_edit(self.batch)
    }

    /// A relationship on the prim, queued rather than committed:
    /// [`Prim::relationship_builder`] inside the transaction, on a prim the
    /// stage holds once the batch's queued prims are written.
    pub fn relationship_builder(&self, name: impl Into<tf::Token>) -> RelationshipBuilder<'a> {
        RelationshipBuilder::new(self.property_site(name.into())).in_edit(self.batch)
    }

    /// Where a property named `name` on the prim is authored, or what naming
    /// it hit: [`PrimNotValid`](StageAuthoringError::PrimNotValid) for a prim
    /// the stage would not hold with the batch's queued prims written, as a
    /// prim handle refuses one the stage does not hold.
    // TODO(perf): the builder's plan and the batch's admission compose the
    // prim's schema again; the fields read here could be handed on.
    fn property_site(&self, name: tf::Token) -> Result<(Stage, sdf::Path), StageAuthoringError> {
        let path = self.prim.path().append_property(&name)?;
        if !held(&self.batch.stage, self.prim.path(), &self.batch.plan.borrow().overlay)? {
            return Err(StageAuthoringError::PrimNotValid {
                path: self.prim.path().clone(),
            });
        }
        Ok((self.batch.stage.clone(), path))
    }

    /// Queues several of the prim's operations as one: [`StageEdit::group`],
    /// with `f` handed this prim inside the group.
    pub fn group<T, E>(&self, f: impl FnOnce(&PrimEdit<'_>) -> Result<T, E>) -> Result<T, E>
    where
        E: From<StageAuthoringError>,
    {
        self.batch.group(|batch| {
            f(&PrimEdit {
                batch,
                prim: self.prim.clone(),
            })
        })
    }
}

/// Everything a batch has planned: its queued operations in order, the prim
/// opinions they write, and what each plan read.
///
/// The one owner of a batch's planning state. An operation enters only
/// through [`admit`](Self::admit), which checks it against everything
/// planned so far and records it whole or not at all.
#[derive(Debug)]
pub(super) struct PlanState {
    /// Every queued operation, in order.
    writes: Vec<PlannedWrite>,
    /// The prim opinions the queued operations write, composed into every
    /// read the plan makes.
    overlay: pcp::Overlay,
    /// Each prim the plan has read.
    prims: HashMap<sdf::Path, PrimPlan>,
    /// The queued property paths.
    properties: HashSet<sdf::Path>,
    /// The schema each prim resolves to under the current overlay, with the
    /// stage's edit epoch it was read at: read once for every property planned
    /// under the prim until a prim operation changes the overlay or a change
    /// outside the batch moves the epoch.
    schemas: HashMap<sdf::Path, (u64, Arc<PrimTypeInfo>)>,
    /// The stage's edit epoch when the plan opened, while it holds nothing
    /// has changed what the stage composes and every read is current; `None`
    /// for a plan committed as soon as it is made, which records no stamps.
    epoch: Option<u64>,
}

/// What a plan records about a prim it read.
#[derive(Debug, Clone)]
struct PrimPlan {
    /// The prim's stamp when the plan first read it, `None` in a plan that
    /// records none.
    stamp: Option<PlanStamp>,
    /// The schema the properties queued under the prim were planned against,
    /// once one has been.
    assumed: Option<PrimTypeId>,
}

/// What a plan rechecks a prim it read against.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(super) struct PlanStamp {
    /// The prim's composition revision, `None` where no index was cached for
    /// it: the plan read nothing an index answers.
    pub(super) revision: Option<pcp::PrimRevision>,
    /// The stage's population epoch.
    pub(super) population: u64,
    /// The stage's type-opinion epoch.
    pub(super) type_opinions: u64,
}

/// An operation asking to join a plan.
#[derive(Debug)]
pub(super) enum Operation {
    /// The prim operation `op` at `path`, decided when it is admitted.
    Prim { path: sdf::Path, op: PrimOp },
    /// A property, planned.
    Property(PlannedProperty),
}

/// One queued operation, as admitted.
#[derive(Debug)]
enum PlannedWrite {
    /// A prim operation and the specs it was decided to write.
    Prim {
        path: sdf::Path,
        op: PrimOp,
        /// Each spec written, at its scene path, in order.
        specs: Vec<(sdf::Path, SpecWrite)>,
    },
    /// A property, planned.
    Property(PlannedProperty),
}

/// What a prim operation asks for.
#[derive(Debug, Clone)]
pub(super) enum PrimOp {
    /// [`Stage::define_typed_prim`]; an empty type leaves the type alone.
    Define { type_name: tf::Token },
    /// [`Stage::override_prim`].
    Override,
    /// [`Prim::set_type_name`]; an empty type erases the edit target's.
    SetType { type_name: tf::Token },
}

/// A prim spec a prim operation writes on the edit target: created as `over`
/// where the layer holds none, then given the specifier and type set here.
#[derive(Debug, Clone, Default)]
struct SpecWrite {
    specifier: Option<sdf::Specifier>,
    type_name: Option<tf::Token>,
}

/// The specs a prim operation is deciding to write, recorded in a copy of
/// the plan's overlay so each later read of the decision sees the earlier
/// writes.
struct Decision {
    overlay: pcp::Overlay,
    specs: Vec<(sdf::Path, SpecWrite)>,
    /// The prims the decision read.
    read: Vec<sdf::Path>,
}

/// One write of a committing plan, at the spec path its scene path maps to.
enum Step {
    /// A prim spec.
    Spec(SpecWrite),
    /// Nothing written; the path is only validated.
    Validate,
    /// A property's write.
    Property(PropertyWrite),
}

impl PlannedWrite {
    /// The operation this was admitted from, for a group replay to admit
    /// again: a prim operation's request, its decision left behind.
    fn into_operation(self) -> Operation {
        match self {
            Self::Prim { path, op, .. } => Operation::Prim { path, op },
            Self::Property(property) => Operation::Property(property),
        }
    }
}

impl Decision {
    /// Records `spec` for the prim at `path`.
    fn write(&mut self, stage: &Stage, path: &sdf::Path, spec: SpecWrite) -> Result<(), StageAuthoringError> {
        write_spec(stage, &mut self.overlay, path, &spec)?;
        self.specs.push((path.clone(), spec));
        Ok(())
    }

    /// The prim at `path` as the decision's writes so far leave it.
    fn read(
        &mut self,
        stage: &Stage,
        path: &sdf::Path,
        with_type: bool,
    ) -> Result<Option<pcp::PrimFields>, StageAuthoringError> {
        self.read.push(path.clone());
        planned_prim(stage, path, &self.overlay, with_type)
    }

    /// [`Stage::define_typed_prim`]: each ancestor not defined gets a `def`,
    /// root-most first, then the prim gets one where it is not defined or has
    /// another type (C++ `_DefinePrim`, which defines the parent before the
    /// prim). With its parent defined, a prim is defined by its own specifier.
    // TODO(perf): each ancestor's read composes its own ancestors again under
    // a non-empty overlay; the walk down the path could carry whether the
    // parent is populated.
    fn define(&mut self, stage: &Stage, path: &sdf::Path, type_name: &tf::Token) -> Result<(), StageAuthoringError> {
        let def = SpecWrite {
            specifier: Some(sdf::Specifier::Def),
            type_name: None,
        };
        let mut ancestors: Vec<sdf::Path> = path.strict_ancestors_below_root().collect();
        ancestors.reverse();
        for ancestor in ancestors {
            if !self
                .read(stage, &ancestor, false)?
                .is_some_and(|fields| fields.defining)
            {
                self.write(stage, &ancestor, def.clone())?;
            }
        }
        let typed = (!type_name.as_str().is_empty()).then(|| type_name.clone());
        let fields = self.read(stage, path, typed.is_some())?;
        let retype = typed.is_some() && fields.as_ref().and_then(|fields| fields.type_name.clone()) != typed;
        if retype || !fields.is_some_and(|fields| fields.defining) {
            self.write(
                stage,
                path,
                SpecWrite {
                    type_name: typed,
                    ..def
                },
            )?;
        }
        Ok(())
    }
}

impl PlanState {
    pub(super) fn new(stage: &Stage) -> Self {
        PlanState {
            epoch: Some(stage.edit_epoch()),
            ..Self::untracked()
        }
    }

    /// A plan committed as soon as it is made, which records no stamps: what
    /// a standalone prim authoring call decides in.
    pub(super) fn untracked() -> Self {
        PlanState {
            writes: Vec::new(),
            overlay: pcp::Overlay::default(),
            prims: HashMap::new(),
            properties: HashSet::new(),
            schemas: HashMap::new(),
            epoch: None,
        }
    }

    /// A copy of everything this plan has planned, without its operations,
    /// which stay with this plan: what a group plans in, and what absorbing
    /// one admits into.
    fn fork(&self) -> Self {
        PlanState {
            writes: Vec::new(),
            overlay: self.overlay.clone(),
            prims: self.prims.clone(),
            properties: self.properties.clone(),
            schemas: self.schemas.clone(),
            epoch: self.epoch,
        }
    }

    /// Admits `operation` into the plan: decides a prim operation against
    /// what is planned so far, checks a property against the schema it was
    /// planned against, and records either whole or not at all.
    pub(super) fn admit(&mut self, stage: &Stage, operation: Operation) -> Result<(), StageAuthoringError> {
        let write = match operation {
            Operation::Prim { path, op } => {
                let specs = self.admit_prim(stage, &path, &op)?;
                PlannedWrite::Prim { path, op, specs }
            }
            Operation::Property(property) => PlannedWrite::Property(self.admit_property(stage, property)?),
        };
        self.writes.push(write);
        Ok(())
    }

    /// Decides which specs the prim operation `op` at `path` writes, against
    /// the prim opinions the plan has queued, as the standalone call decides
    /// against committed state, and records them. Refused where the path is
    /// one no prim can be authored at (C++ `_IsValidPathForCreatingPrim`), or
    /// where the specs would change the schema a queued property was planned
    /// against, or make it impossible to tell.
    fn admit_prim(
        &mut self,
        stage: &Stage,
        path: &sdf::Path,
        op: &PrimOp,
    ) -> Result<Vec<(sdf::Path, SpecWrite)>, StageAuthoringError> {
        stage.validate_target_prim(path)?;
        // TODO(perf): the overlay is copied for every prim operation so a
        // refused one leaves it as it was; an undo log of the sites written
        // would copy nothing.
        let mut decision = Decision {
            overlay: self.overlay.clone(),
            specs: Vec::new(),
            read: Vec::new(),
        };
        match op {
            PrimOp::Define { type_name } => decision.define(stage, path, type_name)?,
            // The stage holds a prim where one composes there with a spec
            // (C++ `GetPrimAtPath`), and then nothing is authored.
            PrimOp::Override => {
                if !decision.read(stage, path, false)?.is_some_and(|fields| fields.has_spec) {
                    decision.write(stage, path, SpecWrite::default())?;
                }
            }
            // A prim-handle write: the prim must be one the stage holds.
            PrimOp::SetType { type_name } => {
                if !decision.read(stage, path, false)?.is_some_and(|fields| fields.has_spec) {
                    return Err(StageAuthoringError::PrimNotValid { path: path.clone() });
                }
                let spec = SpecWrite {
                    specifier: None,
                    type_name: Some(type_name.clone()),
                };
                decision.write(stage, path, spec)?;
            }
        }
        if !decision.specs.is_empty() {
            self.revalidate(stage, &decision.overlay)?;
            self.schemas.clear();
        }
        if self.epoch.is_some() {
            for prim in decision.read {
                self.stamp(stage, prim);
            }
        }
        self.overlay = decision.overlay;
        Ok(decision.specs)
    }

    /// Checks `property` against the schema its prim resolves to now, and
    /// records the schema as what properties under the prim assume.
    ///
    /// A property's spec brings the prim specs above it into being where the
    /// edit target holds none, as [`sdf::AttributeSpec::new`] does; the plan
    /// records them, so later operations see the prim, and refuses them where
    /// they would move a queued property's schema.
    fn admit_property(
        &mut self,
        stage: &Stage,
        property: PlannedProperty,
    ) -> Result<PlannedProperty, StageAuthoringError> {
        if self.properties.contains(&property.path) {
            return Err(StageAuthoringError::DuplicateProperty { path: property.path });
        }
        let prim = property.path.prim_path();
        if *self.schema(stage, &prim)?.id() != property.schema {
            return Err(StageAuthoringError::PlannedTypeChanged { path: prim });
        }
        let (layer, spec_path) = stage.target_site(&prim)?;
        if !self.overlay.holds_spec(&stage.layers(), layer, &spec_path) {
            let mut overlay = self.overlay.clone();
            write_spec(stage, &mut overlay, &prim, &SpecWrite::default())?;
            self.revalidate(stage, &overlay)?;
            self.overlay = overlay;
            self.schemas.clear();
        }
        self.stamp(stage, prim).assumed = Some(property.schema.clone());
        self.properties.insert(property.path.clone());
        Ok(property)
    }

    /// The schema the prim at `prim` resolves to under the plan's overlay,
    /// read once until the overlay changes or a change outside the batch
    /// moves what the stage composes, when it is read again.
    pub(super) fn schema(&mut self, stage: &Stage, prim: &sdf::Path) -> Result<Arc<PrimTypeInfo>, StageAuthoringError> {
        let epoch = stage.edit_epoch();
        if let Some((read_at, schema)) = self.schemas.get(prim)
            && *read_at == epoch
        {
            return Ok(schema.clone());
        }
        let schema = planned_schema(stage, prim, &self.overlay)?;
        self.schemas.insert(prim.clone(), (epoch, schema.clone()));
        Ok(schema)
    }

    /// Refuses `overlay` where it changes, or leaves unknowable, the schema a
    /// queued property was planned against. The written site can reach any
    /// prim that composes it, so every assumption is checked, in path order so
    /// the prim reported is the same from run to run.
    // TODO(perf): every assumed prim is composed again. The prims whose
    // indices hold the written sites (C++ `PcpCache::FindSiteDependencies`)
    // are the only ones that can change.
    fn revalidate(&self, stage: &Stage, overlay: &pcp::Overlay) -> Result<(), StageAuthoringError> {
        let mut assumed: Vec<(&sdf::Path, &PrimTypeId)> = self
            .prims
            .iter()
            .filter_map(|(prim, plan)| Some((prim, plan.assumed.as_ref()?)))
            .collect();
        assumed.sort_by(|a, b| a.0.cmp(b.0));
        for (prim, schema) in assumed {
            if planned_schema(stage, prim, overlay)?.id() != schema {
                return Err(StageAuthoringError::PlannedTypeChanged { path: prim.clone() });
            }
        }
        Ok(())
    }

    /// The record of `prim`, stamped the first time the plan reads it.
    fn stamp(&mut self, stage: &Stage, prim: sdf::Path) -> &mut PrimPlan {
        let tracked = self.epoch.is_some();
        self.prims.entry(prim).or_insert_with_key(|prim| PrimPlan {
            stamp: tracked.then(|| stage.plan_stamp(prim)),
            assumed: None,
        })
    }

    /// [`PlanStale`](StageAuthoringError::PlanStale) where a change since the
    /// plan opened moved a prim it read; the first such prim in path order is
    /// the one reported.
    fn check_fresh(&self, stage: &Stage) -> Result<(), StageAuthoringError> {
        let Some(epoch) = self.epoch else {
            return Ok(());
        };
        if stage.edit_epoch() == epoch {
            return Ok(());
        }
        let moved = self
            .prims
            .iter()
            .filter(|(prim, plan)| plan.stamp.is_some_and(|stamp| stamp.moved(&stage.plan_stamp(prim))))
            .map(|(prim, _)| prim)
            .min();
        match moved {
            Some(prim) => Err(StageAuthoringError::PlanStale { path: prim.clone() }),
            None => Ok(()),
        }
    }

    /// Writes every queued operation, in order, as one transaction of the
    /// edit target's layer, unless a change since the plan opened moved what
    /// it planned against.
    pub(super) fn commit(self, stage: &Stage) -> Result<(), StageAuthoringError> {
        self.check_fresh(stage)?;
        let mut paths = Vec::new();
        let mut steps = Vec::new();
        for write in self.writes {
            match write {
                PlannedWrite::Prim { path, specs, .. } => {
                    for (spec_path, spec) in specs {
                        paths.push(spec_path);
                        steps.push(Step::Spec(spec));
                    }
                    // The prim's path goes along whether or not it is written:
                    // the transaction validates every path it is given (C++
                    // `_IsValidPathForCreatingPrim`), a prototype or proxy path
                    // among them whatever is authored there.
                    paths.push(path);
                    steps.push(Step::Validate);
                }
                PlannedWrite::Property(property) => {
                    paths.push(property.path);
                    steps.push(Step::Property(property.write));
                }
            }
        }
        stage
            .with_target_layer_at_each(&paths, move |layer, spec_paths| {
                for (step, spec_path) in steps.into_iter().zip(spec_paths) {
                    match step {
                        // Each spec is created as `over`, then given its
                        // specifier and type (C++ `SdfCreatePrimInLayer` and
                        // `SetSpecifier`), so a path a variant edit target maps
                        // to `/Prim{set=sel}` writes the variant spec.
                        Step::Spec(SpecWrite { specifier, type_name }) => {
                            let mut spec = sdf::PrimSpec::over(layer.data_mut(), spec_path)?;
                            if let Some(specifier) = specifier {
                                spec.set_specifier(specifier);
                            }
                            if let Some(type_name) = type_name {
                                spec.set_type_name(type_name);
                            }
                        }
                        Step::Validate => {}
                        Step::Property(write) => write.apply(layer.data_mut(), &spec_path)?,
                    }
                }
                Ok(())
            })
            .map(|_| ())
    }
}

impl PlanStamp {
    /// Whether `now` shows the prim moved since this stamp: either epoch
    /// advanced, or the prim's index was rebuilt or restaled. A stamp taken
    /// with no index cached recorded nothing an index answers, so building
    /// one later is not a move.
    fn moved(&self, now: &PlanStamp) -> bool {
        self.population != now.population
            || self.type_opinions != now.type_opinions
            || self.revision.is_some() && self.revision != now.revision
    }
}

/// The prim at `path` as the queued opinions in `overlay` compose it, or
/// `None` where the stage would not hold it: outside the population mask, or
/// below an ancestor that is not populated
/// ([`pcp::IndexCache::compose_planned`]). Its `typeName` is read where
/// `with_type` asks for it.
///
/// [`PlannedEffectUnknown`](StageAuthoringError::PlannedEffectUnknown) where a
/// spec `overlay` creates revives an arc only a rebuild composes.
fn planned_prim(
    stage: &Stage,
    path: &sdf::Path,
    overlay: &pcp::Overlay,
    with_type: bool,
) -> Result<Option<pcp::PrimFields>, StageAuthoringError> {
    stage.resolve_prototype_path(&path.prim_path())?;
    match stage.with_cache(|graph, cache| cache.compose_planned(graph, path, overlay, with_type))? {
        pcp::Planned::Reached(fields) => Ok(Some(fields)),
        pcp::Planned::Unreached => Ok(None),
        pcp::Planned::Unknown => Err(StageAuthoringError::PlannedEffectUnknown { path: path.clone() }),
    }
}

/// Whether the stage holds a prim at `path` with `overlay` written: one its
/// population reaches and that composes a spec (C++ `GetPrimAtPath`, the
/// validity a prim handle requires).
fn held(stage: &Stage, path: &sdf::Path, overlay: &pcp::Overlay) -> Result<bool, StageAuthoringError> {
    Ok(planned_prim(stage, path, overlay, false)?.is_some_and(|fields| fields.has_spec))
}

/// The schema the prim at `prim` resolves to with `overlay` composed in: its
/// type as [`planned_prim`] composes it, with its composed applied API
/// schemas, which no queued operation changes. With nothing queued, the
/// stage's own memoized answer.
fn planned_schema(
    stage: &Stage,
    prim: &sdf::Path,
    overlay: &pcp::Overlay,
) -> Result<Arc<PrimTypeInfo>, StageAuthoringError> {
    if overlay.is_empty() {
        return Ok(stage.prim_type_info_composed(prim)?);
    }
    let type_name = planned_prim(stage, prim, overlay, true)?.and_then(|fields| fields.type_name);
    let applied = Prim::new(stage, prim.clone()).authored_api_schemas_composed()?;
    Ok(stage.prim_type_info_for(type_name, applied)?)
}

/// The schema a property builder plans against: the one `batch` resolves the
/// owning prim to with its queued prims composed in, where the builder joins
/// a batch, and the committed one otherwise.
pub(super) fn property_schema(
    stage: &Stage,
    batch: Option<&StageEdit>,
    prim: sdf::Path,
) -> Result<Arc<PrimTypeInfo>, StageAuthoringError> {
    match batch {
        Some(batch) => batch.plan.borrow_mut().schema(&batch.stage, &prim),
        None => Ok(stage.prim_type_info_composed(prim)?),
    }
}

/// Records in `overlay` the prim spec `spec` a prim operation writes for the
/// prim at `path` on the edit target, with the specs above it that creating
/// it brings into being where the layer holds none: an `over` for a prim, a
/// variant with no specifier, as [`sdf::PrimSpec::over`] creates them.
fn write_spec(
    stage: &Stage,
    overlay: &mut pcp::Overlay,
    path: &sdf::Path,
    spec: &SpecWrite,
) -> Result<(), StageAuthoringError> {
    let (layer, spec_path) = stage.target_site(path)?;
    let graph = stage.layers();
    // Leaf first: a spec the layer or the overlay already holds has every
    // spec above it.
    for (site, kind) in sdf::prim_chain(&spec_path)?.rev() {
        if kind == sdf::SpecType::VariantSet {
            continue;
        }
        if overlay.holds_spec(&graph, layer, &site) {
            break;
        }
        let fields = overlay.entry(layer, site);
        fields.creates_spec = true;
        if kind == sdf::SpecType::Prim {
            fields.specifier = Some(sdf::Specifier::Over);
        }
    }
    let fields = overlay.entry(layer, spec_path);
    if let Some(specifier) = spec.specifier {
        fields.specifier = Some(specifier);
    }
    if let Some(type_name) = &spec.type_name {
        fields.type_name = Some(type_name.clone());
    }
    Ok(())
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
    /// The schema of the owning prim the plan resolved against.
    schema: PrimTypeId,
}

/// The write phase of one property, run against the edit target's own spec path
/// for it: all a [`PlannedProperty`] has left to do once the transaction opens.
#[derive(Debug)]
pub(super) enum PropertyWrite {
    /// An attribute declared, with the value opinion and the metadata fields
    /// planned for it.
    Attribute {
        value: AttributeWrite,
        metadata: Vec<(&'static str, sdf::Value)>,
    },
    /// A relationship declared, and its targets replaced where the caller gave
    /// some.
    Relationship {
        ensure: EnsurePlan,
        targets: Option<Vec<sdf::Path>>,
    },
}

/// What an attribute's write does to its value.
#[derive(Debug)]
pub(super) enum AttributeWrite {
    /// Declares the attribute, and leaves it at whatever value it has.
    Declare(EnsurePlan),
    /// Gives it the value planned for it.
    Set(Box<AttributeAuthoringPlan>),
    /// Blocks every weaker value opinion.
    Block(Box<AttributeAuthoringPlan>),
}

impl PlannedProperty {
    pub(super) fn new(stage: Stage, path: sdf::Path, write: PropertyWrite, schema: PrimTypeId) -> Self {
        PlannedProperty {
            stage,
            path,
            write,
            schema,
        }
    }

    /// Writes the property on its own, as one transaction, and hands back where
    /// it was authored for the caller to build its handle from.
    pub(super) fn commit(self) -> Result<(Stage, sdf::Path), StageAuthoringError> {
        let PlannedProperty { stage, path, write, .. } = self;
        stage.with_target_layer_at(&path, move |layer, spec_path| write.apply(layer.data_mut(), &spec_path))?;
        Ok((stage, path))
    }
}

impl PropertyWrite {
    fn apply(self, data: &mut dyn sdf::AbstractData, path: &sdf::Path) -> Result<(), StageAuthoringError> {
        match self {
            Self::Attribute { value, metadata } => {
                match value {
                    AttributeWrite::Declare(ensure) => apply_plan(data, path, Attribute::KIND, &ensure)?,
                    AttributeWrite::Set(plan) => plan.write(data, path)?,
                    AttributeWrite::Block(plan) => plan.block(data, path)?,
                }
                if metadata.is_empty() {
                    return Ok(());
                }
                edit_spec(data, path.clone(), Attribute::KIND, Attribute::view, |spec| {
                    for (key, value) in metadata {
                        spec.set(key, value);
                    }
                    Ok(())
                })
            }
            Self::Relationship { ensure, targets } => {
                apply_plan(data, path, Relationship::KIND, &ensure)?;
                let Some(targets) = targets else {
                    return Ok(());
                };
                edit_spec(data, path.clone(), Relationship::KIND, Relationship::view, |spec| {
                    Ok(spec.edit_targets().set(targets)?)
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

/// Rewrites with `f` the edit target's own opinion of the metadata field
/// `key` on the property of kind `P` at `path`, as
/// [`Attribute::update_metadata`] describes; a value `f` leaves as it was
/// is not written again.
pub(super) fn update_metadata<P: PropertySpecKind>(
    stage: &Stage,
    path: &sdf::Path,
    key: &'static str,
    f: impl FnOnce(Option<sdf::Value>) -> Option<sdf::Value>,
) -> Result<(), StageAuthoringError> {
    check_reserved(P::KIND, key)?;
    // Resolved before the transaction, consulted only when there is a value
    // to author: an erase never stamps a spec.
    let ensure = stage
        .prim_type_info_composed(path.prim_path())
        .map_err(StageAuthoringError::from)
        .and_then(|schema| plan_property_spec(stage, path, P::KIND, None, &schema));
    stage.with_target_layer_at(path, |layer, path| {
        let data = layer.data_mut();
        let local = data.try_field(&path, key)?.map(Cow::into_owned);
        let held = local.clone();
        let value = f(local);
        if value == held {
            return Ok(());
        }
        match (data.spec_type(&path), value) {
            (None, None) => Ok(()),
            (Some(found), _) if found != P::KIND => Err(kind_mismatch(&path, P::KIND, found)),
            (Some(_), None) => {
                data.erase_field(&path, key);
                Ok(())
            }
            (_, Some(value)) => {
                apply_plan(data, &path, P::KIND, &ensure?)?;
                data.set_field(&path, key, value);
                Ok(())
            }
        }
    })?;
    Ok(())
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
    let schema = stage.prim_type_info_composed(path.prim_path())?;
    let plan = plan_property_spec(stage, path, P::KIND, None, &schema)?;
    stage
        .with_target_layer_at(path, |layer, spec_path| {
            apply_plan(layer.data_mut(), &spec_path, P::KIND, &plan)?;
            edit_spec(layer.data_mut(), spec_path, P::KIND, P::view, edit)
        })
        .map(|_| ())
}

/// Runs `edit` on the spec `path` already has on the edit target, and does
/// nothing where it has none. A property of a prim the stage does not hold is
/// [`PrimNotValid`](StageAuthoringError::PrimNotValid).
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
    stage.require_included(path)?;
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

/// The read phase of authoring the property at `path` as a `kind` spec,
/// against `schema`, the schema of the prim it hangs off.
///
/// A property of a prim the stage does not hold — outside the population mask
/// or below an inactive prim — is
/// [`PrimNotValid`](StageAuthoringError::PrimNotValid), as C++ holds no
/// `UsdPrim` there to author through.
///
/// Otherwise, in C++ precedence order: a spec of that kind already on the edit target is
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
    schema: &PrimTypeInfo,
) -> Result<EnsurePlan, StageAuthoringError> {
    stage.require_included(path)?;
    if let Some(found) = stage.local_spec_type(path)? {
        return if found == kind {
            Ok(EnsurePlan::Existing)
        } else {
            Err(kind_mismatch(path, kind, found))
        };
    }
    let Some((_, name)) = path.split_property() else {
        return Err(sdf::AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "property authoring needs a property path",
        }
        .into());
    };

    if let Some(property) = schema.prim_definition().property(&tf::Token::from(name)) {
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
        .masked_opinions(path, |graph, cache| cache.property_stack(graph, path, None))?
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

/// The field `key` the schema declares for the object at `path`: a prim's
/// from its prim definition, a property's from the property's declaration
/// there (C++ `UsdPrimDefinition`, keyed by the property name or by the empty
/// one for the prim). `None` where no schema declares the object or the
/// field.
///
/// Everything a schema states about an object (a property's type and
/// variability, the display metadata of either) lives on that declaration,
/// whether or not any layer authors a spec.
pub(super) fn schema_field(stage: &Stage, path: &sdf::Path, key: &str) -> Result<Option<sdf::Value>, pcp::QueryError> {
    let schema = stage.prim_type_info_composed(path.prim_path())?;
    Ok(schema_field_in(&schema, path, key))
}

/// [`schema_field`] read from `schema`, the schema of the prim `path` names
/// or hangs off.
pub(super) fn schema_field_in(schema: &PrimTypeInfo, path: &sdf::Path, key: &str) -> Option<sdf::Value> {
    let name = path.split_property().map_or("", |(_, name)| name);
    let definition = schema.prim_definition();
    match name {
        "" => definition.metadata(key).cloned(),
        name => definition
            .property(&tf::Token::from(name))
            .and_then(|property| property.field(key).cloned()),
    }
}

/// The composed metadata field `key` of the object at `path` decoded to `T`
/// (C++ `UsdStage::_GetGeneralMetadataImpl`): the strongest layer opinion,
/// with the dictionary the schema declares composed under an authored
/// dictionary, or the schema's declaration where no layer authors the field.
pub(super) fn metadata<T>(stage: &Stage, path: &sdf::Path, key: &str) -> crate::Result<Option<T>>
where
    T: TryFrom<sdf::Value>,
    T::Error: Into<crate::Error>,
{
    let authored = match stage.field::<sdf::Value>(path, key)? {
        Some(sdf::Value::Dictionary(mut dict)) => {
            // TODO(perf): this clones the declared dictionary on every read; a
            // borrowing compose would copy only the keys no layer authors.
            if let Some(sdf::Value::Dictionary(declared)) = schema_field(stage, path, key)? {
                dict.over(declared);
            }
            sdf::Value::Dictionary(dict)
        }
        Some(authored) => authored,
        // Schema metadata parses untyped, so a declaration may hold a variant
        // the caller did not ask for; that is "not declared", not an error.
        None => return Ok(schema_field(stage, path, key)?.and_then(|value| T::try_from(value).ok())),
    };
    super::decode_value(Some(authored))
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
        // The layer stack and the namespace a stage composes are edited
        // through the operations that validate them.
        sdf::SpecType::PseudoRoot => &[
            sdf::FieldKey::DefaultPrim,
            sdf::FieldKey::SubLayers,
            sdf::FieldKey::SubLayerOffsets,
            sdf::FieldKey::LayerRelocates,
        ],
        _ => &[],
    };
    if reserved.iter().any(|field| field.as_str() == key) {
        return Err(StageAuthoringError::ReservedField { field: key });
    }
    Ok(())
}

/// `target` as the edit target of `stage` authors a target of the property
/// at `owner`, a relationship target or an attribute connection (C++
/// `UsdRelationship::_GetTargetForAuthoring`,
/// `UsdAttribute::_GetPathForAuthoring`): a relative path is anchored at the
/// owning prim, and the absolute prim or property path, as Sdf admits for
/// the field, is mapped into the target's layer namespace less its variant
/// selections. A target naming a prototype, or an object within one, is
/// [`PrototypeTarget`](StageAuthoringError::PrototypeTarget), and one the
/// mapping does not reach
/// [`OutsideEditTarget`](StageAuthoringError::OutsideEditTarget).
pub(super) fn target_for_authoring(
    stage: &Stage,
    owner: &sdf::Path,
    target: impl sdf::IntoPath,
) -> Result<sdf::Path, StageAuthoringError> {
    let target = sdf::list_edit::canonical(&owner.prim_path(), target)?.strip_variant_selections();
    if pcp::is_prototype_namespace(&target) {
        return Err(StageAuthoringError::PrototypeTarget { path: target });
    }
    if !(target.is_prim() || target.is_property()) {
        return Err(sdf::AuthoringError::InvalidPath {
            path: target,
            reason: "a target names a prim or property path",
        }
        .into());
    }
    stage.map_to_spec_target_path(&target)
}

/// [`target_for_authoring`] over each of `targets`, in order.
pub(super) fn targets_for_authoring(
    stage: &Stage,
    owner: &sdf::Path,
    targets: impl IntoIterator<Item: sdf::IntoPath>,
) -> Result<Vec<sdf::Path>, StageAuthoringError> {
    targets
        .into_iter()
        .map(|target| target_for_authoring(stage, owner, target))
        .collect()
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
    use crate::usd::stage::tests::{authored, scene, stage};
    use crate::usd::{EditTarget, Stage, StageAuthoringError, TimeCode, UndoStage};
    use crate::{Result, sdf, tf};

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
            Ok::<_, StageAuthoringError>((height, proxy))
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

    /// A caller's own error, as a layer above the stage would carry one.
    #[derive(Debug)]
    enum CallerError {
        Refused,
        Stage(StageAuthoringError),
    }

    impl From<StageAuthoringError> for CallerError {
        fn from(error: StageAuthoringError) -> Self {
            Self::Stage(error)
        }
    }

    /// The closure's own error comes back as it was, and nothing it queued is
    /// written.
    #[test]
    fn edit_carries_caller_error() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        let failed = stage.edit(|edit| {
            edit.prim("/World")
                .map_err(StageAuthoringError::from)?
                .attribute_builder("height", "double")
                .set(2.0)
                .build()?;
            Err::<(), _>(CallerError::Refused)
        });

        assert!(matches!(failed, Err(CallerError::Refused)));
        assert!(!prim.attribute("height").is_defined()?);
        Ok(())
    }

    /// A failure at the commit reaches the caller in the caller's error type.
    #[test]
    fn commit_error_converts() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        let variant = variant_target(&stage)?;
        let failed = stage.edit(|edit| {
            edit.attribute_builder("/World.height", "double").set(2.0).build()?;
            stage.set_edit_target(variant.clone())?;
            Ok::<_, CallerError>(())
        });

        assert!(matches!(
            failed,
            Err(CallerError::Stage(StageAuthoringError::EditTargetMoved))
        ));
        assert!(!prim.attribute("height").is_defined()?);
        Ok(())
    }

    /// A group's properties join the batch they were grouped in, and commit
    /// with it.
    #[test]
    fn group_joins_batch() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        stage.edit(|edit| {
            let world = edit.prim("/World")?;
            world.attribute_builder("radius", "double").set(1.0).build()?;
            world.group(|group| {
                group.attribute_builder("height", "double").set(2.0).build()?;
                group.attribute_builder("width", "double").set(3.0).build()?;
                Ok::<_, StageAuthoringError>(())
            })?;
            assert!(!prim.attribute("height").is_defined()?, "nothing is written yet");
            Ok::<_, crate::Error>(())
        })?;

        for (name, value) in [("radius", 1.0), ("height", 2.0), ("width", 3.0)] {
            assert_eq!(prim.attribute(name).get::<f64>()?, Some(value), "{name}");
        }
        Ok(())
    }

    /// A builder taken from the prim joins the batch it is handed to, and
    /// writes nothing until that batch commits.
    #[test]
    fn builder_joins_edit() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        stage
            .edit(|edit| {
                prim.attribute_builder("height", "double")
                    .set(2.0)
                    .in_edit(edit)
                    .build()?;
                prim.relationship_builder("proxy")
                    .set_targets(["/World"])
                    .in_edit(edit)
                    .build()?;
                assert!(!prim.attribute("height").is_defined()?, "nothing is written yet");
                Err::<(), crate::Error>(StageAuthoringError::EditTargetMoved.into())
            })
            .expect_err("the closure fails");
        assert!(!prim.attribute("height").is_defined()?, "a failed batch writes nothing");

        stage.edit(|edit| {
            prim.attribute_builder("height", "double")
                .set(2.0)
                .in_edit(edit)
                .build()?;
            Ok::<_, StageAuthoringError>(())
        })?;
        assert_eq!(prim.attribute("height").get::<f64>()?, Some(2.0));
        Ok(())
    }

    /// A batch has no layer of another stage to write to.
    #[test]
    fn foreign_builder_refused() -> Result<()> {
        let (stage, other) = (stage()?, stage()?);
        stage.define_prim("/World")?;
        let foreign = other.define_prim("/World")?;
        let refused = stage.edit(|edit| {
            foreign.attribute_builder("height", "double").in_edit(edit).build()?;
            Ok::<_, StageAuthoringError>(())
        });
        assert!(
            matches!(refused, Err(StageAuthoringError::EditOfAnotherStage { .. })),
            "{refused:?}"
        );
        assert!(!foreign.attribute("height").is_defined()?);
        Ok(())
    }

    /// A group that fails queues none of its properties, so a caller that
    /// goes on from the error commits only what it queued itself.
    #[test]
    fn group_error_queues_nothing() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        stage.edit(|edit| {
            let world = edit.prim("/World")?;
            world.attribute_builder("radius", "double").set(1.0).build()?;
            let failed = world.group(|group| {
                group.attribute_builder("height", "double").set(2.0).build()?;
                Err::<(), _>(CallerError::Refused)
            });
            assert!(matches!(failed, Err(CallerError::Refused)));
            Ok::<_, StageAuthoringError>(())
        })?;

        assert!(prim.attribute("radius").is_defined()?);
        assert!(!prim.attribute("height").is_defined()?);
        Ok(())
    }

    /// A group naming a property the batch already holds joins it with none
    /// of its properties, the ones that did not collide included.
    #[test]
    fn group_duplicate_absorbs_nothing() -> Result<()> {
        let stage = stage()?;
        let prim = stage.define_prim("/World")?;
        stage.edit(|edit| {
            let world = edit.prim("/World")?;
            world.attribute_builder("height", "double").set(2.0).build()?;
            let failed = world.group(|group| {
                group.attribute_builder("width", "double").set(3.0).build()?;
                group.attribute_builder("height", "double").set(4.0).build()?;
                Ok::<_, StageAuthoringError>(())
            });
            assert!(matches!(failed, Err(StageAuthoringError::DuplicateProperty { .. })));
            Ok::<_, StageAuthoringError>(())
        })?;

        assert_eq!(prim.attribute("height").get::<f64>()?, Some(2.0));
        assert!(!prim.attribute("width").is_defined()?);
        Ok(())
    }

    /// A group plans against the target its batch opened on, so a target
    /// moved under it is refused there as well.
    #[test]
    fn group_shares_target() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/World")?;
        let variant = variant_target(&stage)?;
        let failed = stage.edit(|edit| {
            edit.group(|group| {
                stage.set_edit_target(variant.clone())?;
                group.attribute_builder("/World.height", "double").set(2.0).build()
            })
        });

        assert!(matches!(failed, Err(StageAuthoringError::EditTargetMoved)));
        Ok(())
    }

    /// An empty batch is a no-op that still hands back the closure's value.
    #[test]
    fn empty_batch_authors_nothing() -> Result<()> {
        let stage = stage()?;
        assert_eq!(stage.edit(|_| Ok::<_, StageAuthoringError>(7))?, 7);
        Ok(())
    }

    /// The `typeName` the root layer authors at `path`.
    fn root_type(stage: &Stage, path: &str) -> Option<tf::Token> {
        authored(&stage.root_layer(), path, sdf::FieldKey::TypeName)
    }

    /// A prim defined in the batch and a schema attribute authored on it
    /// commit as one transaction, the attribute stamped with the declaration
    /// the queued type gives it.
    #[test]
    fn define_then_schema_attr() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "")])?;
        let undo = UndoStage::from(stage);
        undo.edit(|edit| {
            let light = edit.define_typed_prim("/Light", "DistantLight")?;
            light.attribute_builder("inputs:angle", "double").set(1.0_f32).build()
        })?;

        assert_eq!(undo.undo_depth(), 1);
        assert_eq!(root_type(&undo, "/Light"), Some(tf::Token::new("DistantLight")));
        assert_eq!(root_type(&undo, "/Light.inputs:angle"), Some(tf::Token::new("float")));
        assert!(!undo.attribute("/Light.inputs:angle")?.is_custom()?);
        Ok(())
    }

    /// A value is checked against the declaration the queued type gives, and
    /// a refused one leaves the queued prim unwritten too.
    #[test]
    fn queued_type_checks_value() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "")])?;
        let failed = stage.edit(|edit| {
            let light = edit.define_typed_prim("/Light", "DistantLight")?;
            light.attribute_builder("inputs:angle", "double").set(1.0_f64).build()
        });

        assert!(matches!(failed, Err(StageAuthoringError::ValueType(_))));
        assert!(!stage.prim("/Light")?.is_valid()?);
        Ok(())
    }

    /// A queued type keeps the prim's composed applied schemas, and maps
    /// through the root layer's `fallbackPrimTypes`.
    #[test]
    fn queued_type_applied_fallback() -> Result<()> {
        let root = "(\n    fallbackPrimTypes = {\n        token[] MyLight = [\"DistantLight\"]\n    }\n)\nover \"A\" (\n    prepend apiSchemas = [\"SlotAPI:a\"]\n)\n{\n}\n";
        let (_dir, stage) = scene(&[("root.usda", root)])?;
        stage.edit(|edit| {
            let a = edit.define_typed_prim("/A", "DomeLight")?;
            a.attribute_builder("slot:a:depth", "double").set(1.0_f32).build()?;
            let b = edit.define_typed_prim("/B", "MyLight")?;
            b.attribute_builder("inputs:angle", "double").set(1.0_f32).build()
        })?;

        assert_eq!(root_type(&stage, "/A.slot:a:depth"), Some(tf::Token::new("float")));
        assert_eq!(root_type(&stage, "/B.inputs:angle"), Some(tf::Token::new("float")));
        Ok(())
    }

    /// A retype and its undoing in one batch end where sequential calls end:
    /// the second define is decided against the first.
    #[test]
    fn retype_and_restore() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "def DomeLight \"A\"\n{\n}\n")])?;
        stage.edit(|edit| {
            edit.define_typed_prim("/A", "DistantLight")?;
            edit.define_typed_prim("/A", "DomeLight").map(|_| ())
        })?;
        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DomeLight")));

        stage.edit(|edit| {
            edit.group(|group| {
                group.define_typed_prim("/A", "DistantLight")?;
                group.define_typed_prim("/A", "DomeLight").map(|_| ())
            })
        })?;
        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DomeLight")));
        Ok(())
    }

    /// An untyped define over a typed `over` makes it a `def` and keeps its
    /// type, which a property planned after it resolves against.
    #[test]
    fn untyped_define_keeps_type() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "over DistantLight \"A\"\n{\n}\n")])?;
        stage.edit(|edit| {
            let a = edit.define_prim("/A")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()
        })?;

        let specifier: Option<sdf::Specifier> = authored(&stage.root_layer(), "/A", sdf::FieldKey::Specifier);
        assert_eq!(specifier, Some(sdf::Specifier::Def));
        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DistantLight")));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), Some(tf::Token::new("float")));
        Ok(())
    }

    /// A stronger layer's type outlives a weaker target's queued one, for the
    /// properties planned after it and for a define that follows, as
    /// sequential calls have it.
    #[test]
    fn stronger_type_wins() -> Result<()> {
        let (_dir, stage) = scene(&[
            ("root.usda", "(\n    subLayers = [@strong.usda@, @weak.usda@]\n)\n"),
            ("strong.usda", "over DistantLight \"A\"\n{\n}\n"),
            ("weak.usda", "def \"A\"\n{\n}\n"),
        ])?;
        let weak = stage
            .layer_identifiers()
            .into_iter()
            .find(|identifier| identifier.ends_with("weak.usda"))
            .expect("the weak layer is in the stage");
        stage.set_edit_target(stage.edit_target_for_local_layer(&weak).expect("a local layer"))?;
        stage.edit(|edit| {
            let a = edit.define_typed_prim("/A", "DomeLight")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()?;
            edit.define_typed_prim("/A", "DistantLight").map(|_| ())
        })?;

        let layer = stage.layer(&weak).expect("the weak layer");
        assert_eq!(
            authored::<tf::Token>(&layer, "/A", sdf::FieldKey::TypeName),
            Some(tf::Token::new("DomeLight"))
        );
        assert_eq!(
            authored::<tf::Token>(&layer, "/A.inputs:angle", sdf::FieldKey::TypeName),
            Some(tf::Token::new("float"))
        );
        Ok(())
    }

    /// A define that would change the schema a queued property was planned
    /// against is refused, and leaves nothing of itself in the batch.
    #[test]
    fn retype_after_property() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "def DistantLight \"A\"\n{\n}\n")])?;
        stage.edit(|edit| {
            let a = edit.prim("/A")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()?;
            let refused = edit.define_typed_prim("/A", "DomeLight");
            assert!(matches!(refused, Err(StageAuthoringError::PlannedTypeChanged { .. })));
            Ok::<_, StageAuthoringError>(())
        })?;

        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DistantLight")));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), Some(tf::Token::new("float")));
        Ok(())
    }

    /// A group that defines a prim and authors under it joins a batch that
    /// had queued nothing.
    #[test]
    fn group_defines_and_authors() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "")])?;
        stage.edit(|edit| {
            edit.group(|group| {
                let a = group.define_typed_prim("/A", "DistantLight")?;
                a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()
            })
        })?;

        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DistantLight")));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), Some(tf::Token::new("float")));
        Ok(())
    }

    /// A group's define is decided again when it joins: the batch retyped the
    /// prim while the group was open, so the group's no-op is a write by then.
    #[test]
    fn group_replans_define() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "def DomeLight \"A\"\n{\n}\n")])?;
        stage.edit(|edit| {
            edit.group(|group| {
                group.define_typed_prim("/A", "DomeLight")?;
                edit.define_typed_prim("/A", "DistantLight").map(|_| ())
            })
        })?;

        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DomeLight")));
        Ok(())
    }

    /// A group's property planned against a schema the batch changed while
    /// the group was open is refused when the group joins, and none of the
    /// group joins.
    #[test]
    fn group_stale_schema() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "def DistantLight \"A\"\n{\n}\n")])?;
        stage.edit(|edit| {
            let joined = edit.group(|group| {
                let a = group.prim("/A")?;
                a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()?;
                edit.define_typed_prim("/A", "DomeLight").map(|_| ())
            });
            assert!(matches!(joined, Err(StageAuthoringError::PlannedTypeChanged { .. })));
            Ok::<_, StageAuthoringError>(())
        })?;

        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DomeLight")));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), None);
        Ok(())
    }

    /// A queued retype reaches a prim that references the retyped one: a
    /// property planned after it resolves against the new schema, and one
    /// planned before it refuses the retype.
    #[test]
    fn retype_reaches_reference() -> Result<()> {
        let root = "def DomeLight \"Source\"\n{\n}\ndef \"Instance\" (\n    references = </Source>\n)\n{\n}\n";
        let (_dir, stage) = scene(&[("root.usda", root)])?;
        stage.edit(|edit| {
            edit.define_typed_prim("/Source", "DistantLight")?;
            let instance = edit.prim("/Instance")?;
            instance
                .attribute_builder("inputs:angle", "double")
                .set(1.0_f32)
                .build()
        })?;
        assert_eq!(
            root_type(&stage, "/Instance.inputs:angle"),
            Some(tf::Token::new("float"))
        );

        let (_dir, stage) = scene(&[("root.usda", root)])?;
        let failed = stage.edit(|edit| {
            let instance = edit.prim("/Instance")?;
            instance
                .attribute_builder("inputs:angle", "double")
                .set(1.0_f64)
                .build()?;
            edit.define_typed_prim("/Source", "DistantLight").map(|_| ())
        });
        assert!(matches!(failed, Err(StageAuthoringError::PlannedTypeChanged { .. })));
        assert_eq!(root_type(&stage, "/Source"), Some(tf::Token::new("DomeLight")));
        Ok(())
    }

    /// A spec at a site the index erased leaves what the prim composes to
    /// unknown: the selected variant's site of a prim no layer holds yet,
    /// written through a variant edit target. Defining such a prim queues, a
    /// property or a define planned under it afterwards is refused, and a define
    /// that would make a queued property's prim unknown is refused. A
    /// standalone define there defines its parent on its own first.
    #[test]
    fn culled_target_revival() -> Result<()> {
        let (_dir, stage) = scene(&[(
            "root.usda",
            "def \"A\" (\n    variants = {\n        string set = \"on\"\n    }\n    prepend variantSets = \"set\"\n)\n{\n    def \"W\"\n    {\n    }\n    variantSet \"set\" = {\n        \"on\" {\n        }\n    }\n}\n",
        )])?;
        let root_layer = stage.edit_target().layer_identifier().to_string();
        stage.set_edit_target(EditTarget::for_local_direct_variant(root_layer, "/A{set=on}")?)?;
        stage.edit(|edit| {
            let a = edit.prim("/A")?;
            a.attribute_builder("size", "double").set(1.0_f64).build()?;
            edit.define_prim("/A/X")?;
            let attribute = edit
                .prim("/A/X")?
                .attribute_builder("size", "double")
                .set(1.0_f64)
                .build();
            assert!(matches!(
                attribute,
                Err(StageAuthoringError::PlannedEffectUnknown { .. })
            ));
            let child = edit.define_prim("/A/X/Y");
            assert!(matches!(child, Err(StageAuthoringError::PlannedEffectUnknown { .. })));
            Ok::<_, StageAuthoringError>(())
        })?;
        assert!(stage.prim("/A/X")?.is_valid()?);

        // `/A/W` is held, by a spec outside the variant, so a property plans on
        // it; a define below it then writes the variant's site of `/A/W`.
        stage.edit(|edit| {
            let w = edit.prim("/A/W")?;
            w.attribute_builder("size", "double").set(1.0_f64).build()?;
            let refused = edit.define_prim("/A/W/C");
            assert!(matches!(refused, Err(StageAuthoringError::PlannedEffectUnknown { .. })));
            Ok::<_, StageAuthoringError>(())
        })?;
        assert!(!stage.prim("/A/W/C")?.is_valid()?);

        stage.define_prim("/A/P/Q")?;
        assert!(stage.prim("/A/P/Q")?.is_valid()?);
        Ok(())
    }

    /// A property brings its prim's spec into being on the edit target, so a
    /// prim operation or a prim-handle builder queued after it finds the prim.
    #[test]
    fn property_creates_prim() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "")])?;
        stage.edit(|edit| {
            edit.attribute_builder("/New.x", "float").build()?;
            let new = edit.prim("/New")?;
            new.set_type_name("")?;
            new.attribute_builder("y", "float").build()
        })?;

        assert!(stage.prim("/New")?.is_valid()?);
        assert!(stage.prim("/New")?.attribute("y").is_defined()?);
        Ok(())
    }

    /// A define through an unselected variant writes the variant's spec, as
    /// the standalone define does, while the prim keeps composing as before.
    #[test]
    fn unselected_variant_define() -> Result<()> {
        for variants in [
            "\"on\" {\n        }\n        \"off\" {\n        }\n",
            "\"on\" {\n        }\n",
        ] {
            let root = format!(
                "def DistantLight \"A\" (\n    variants = {{\n        string set = \"on\"\n    }}\n    prepend variantSets = \"set\"\n)\n{{\n    variantSet \"set\" = {{\n        {variants}    }}\n}}\n"
            );
            let (_dir, stage) = scene(&[("root.usda", &root)])?;
            let root_layer = stage.edit_target().layer_identifier().to_string();
            stage.set_edit_target(EditTarget::for_local_direct_variant(root_layer, "/A{set=off}")?)?;
            stage.edit(|edit| {
                let a = edit.define_typed_prim("/A", "DomeLight")?;
                a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()
            })?;

            assert_eq!(root_type(&stage, "/A{set=off}"), Some(tf::Token::new("DomeLight")));
            assert_eq!(
                root_type(&stage, "/A{set=off}.inputs:angle"),
                Some(tf::Token::new("float"))
            );
            assert_eq!(stage.prim("/A")?.type_name()?, Some(tf::Token::new("DistantLight")));
        }
        Ok(())
    }

    /// A type queued in the selected variant takes effect at the variant's
    /// strength, under a local opinion that authors no type.
    #[test]
    fn selected_variant_type() -> Result<()> {
        let root = "def \"A\" (\n    variants = {\n        string set = \"on\"\n    }\n    prepend variantSets = \"set\"\n)\n{\n    variantSet \"set\" = {\n        \"on\" {\n        }\n    }\n}\n";
        let (_dir, stage) = scene(&[("root.usda", root)])?;
        let root_layer = stage.edit_target().layer_identifier().to_string();
        stage.set_edit_target(EditTarget::for_local_direct_variant(root_layer, "/A{set=on}")?)?;
        stage.edit(|edit| {
            let a = edit.define_typed_prim("/A", "DistantLight")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()
        })?;

        assert_eq!(
            root_type(&stage, "/A{set=on}.inputs:angle"),
            Some(tf::Token::new("float"))
        );
        Ok(())
    }

    /// `override_prim` authors nothing for a prim a weaker layer already
    /// composes, on its own or queued, and a prim the batch defined counts as
    /// held.
    #[test]
    fn override_existing_prim() -> Result<()> {
        let (_dir, stage) = scene(&[
            ("root.usda", "(\n    subLayers = [@weak.usda@]\n)\n"),
            ("weak.usda", "def \"A\"\n{\n}\n"),
        ])?;
        assert!(stage.override_prim("/A")?.is_valid()?);
        stage.edit(|edit| edit.override_prim("/A").map(|_| ()))?;
        assert!(!stage.root_layer().data().has_spec(&sdf::Path::new("/A")?));

        stage.override_prim("/New")?;
        let specifier: Option<sdf::Specifier> = authored(&stage.root_layer(), "/New", sdf::FieldKey::Specifier);
        assert_eq!(specifier, Some(sdf::Specifier::Over));

        stage.edit(|edit| {
            edit.define_prim("/Defined")?;
            edit.override_prim("/Defined").map(|_| ())
        })?;
        let specifier: Option<sdf::Specifier> = authored(&stage.root_layer(), "/Defined", sdf::FieldKey::Specifier);
        assert_eq!(specifier, Some(sdf::Specifier::Def));
        Ok(())
    }

    /// Defines that share an undefined ancestor define it once, and a define
    /// below an inactive ancestor still writes its spec.
    #[test]
    fn define_ancestors() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "def \"Off\" (\n    active = false\n)\n{\n}\n")])?;
        stage.edit(|edit| {
            edit.define_prim("/P/A")?;
            edit.define_prim("/P/B").map(|_| ())
        })?;
        let specifier: Option<sdf::Specifier> = authored(&stage.root_layer(), "/P", sdf::FieldKey::Specifier);
        assert_eq!(specifier, Some(sdf::Specifier::Def));
        assert!(stage.prim("/P/A")?.is_valid()? && stage.prim("/P/B")?.is_valid()?);

        stage.define_prim("/Off/Child")?;
        assert!(stage.root_layer().data().has_spec(&sdf::Path::new("/Off/Child")?));
        assert!(!stage.prim("/Off/Child")?.is_valid()?);
        Ok(())
    }

    /// A commit through an ordinary handle that changes a prim the batch
    /// planned against makes the batch's commit stale, and nothing of it is
    /// written; so does one that changes the root layer's
    /// `fallbackPrimTypes`.
    #[test]
    fn outside_commit_stale() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "def DistantLight \"A\"\n{\n    double size = 1\n}\n")])?;
        let failed = stage.edit(|edit| {
            let a = edit.prim("/A")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()?;
            stage.prim("/A")?.attribute("size").set(2.0_f64)?;
            Ok::<_, StageAuthoringError>(())
        });
        assert!(matches!(failed, Err(StageAuthoringError::PlanStale { .. })));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), None);

        let failed = stage.edit(|edit| {
            let a = edit.prim("/A")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()?;
            let root = stage.root_layer().identifier.clone();
            stage.layer_mut(&root).expect("the root layer").edit(|layer| {
                layer.pseudo_root_mut().expect("a pseudo-root").set(
                    "fallbackPrimTypes",
                    sdf::Value::Dictionary(sdf::Dictionary::from([(
                        "MyLight".to_owned(),
                        sdf::Value::token_vec(["DistantLight"]),
                    )])),
                );
                Ok(())
            })?;
            Ok::<_, StageAuthoringError>(())
        });
        assert!(matches!(failed, Err(StageAuthoringError::PlanStale { .. })));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), None);
        Ok(())
    }

    /// A prim defined, typed and given a schema attribute in one batch is one
    /// transaction; a type set after a property is planned under the prim is
    /// refused, and so is one on a prim the stage would not hold.
    #[test]
    fn set_type_queued() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "")])?;
        let undo = UndoStage::from(stage);
        undo.edit(|edit| {
            let light = edit.define_prim("/Light")?;
            light.set_type_name("DistantLight")?;
            light.attribute_builder("inputs:angle", "double").set(1.0_f32).build()?;
            let refused = light.set_type_name("DomeLight");
            assert!(matches!(refused, Err(StageAuthoringError::PlannedTypeChanged { .. })));
            let missing = edit.prim("/Missing")?.set_type_name("DomeLight").map(|_| ());
            assert!(matches!(missing, Err(StageAuthoringError::PrimNotValid { .. })));
            Ok::<_, StageAuthoringError>(())
        })?;

        assert_eq!(undo.undo_depth(), 1);
        assert_eq!(root_type(&undo, "/Light"), Some(tf::Token::new("DistantLight")));
        assert_eq!(root_type(&undo, "/Light.inputs:angle"), Some(tf::Token::new("float")));
        Ok(())
    }

    /// Muting a layer while a batch is open changes what the stage composes
    /// without a layer commit, and makes the batch's plans stale all the same.
    #[test]
    fn muting_makes_stale() -> Result<()> {
        let (_dir, stage) = scene(&[
            ("root.usda", "(\n    subLayers = [@strong.usda@]\n)\ndef \"A\"\n{\n}\n"),
            ("strong.usda", "over DistantLight \"A\"\n{\n}\n"),
        ])?;
        let strong = stage
            .layer_identifiers()
            .into_iter()
            .find(|identifier| identifier.ends_with("strong.usda"))
            .expect("the sublayer is in the stage");
        let failed = stage.edit(|edit| {
            let a = edit.prim("/A")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()?;
            stage.mute_layer(strong.clone());
            Ok::<_, StageAuthoringError>(())
        });

        assert!(matches!(failed, Err(StageAuthoringError::PlanStale { .. })));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), None);
        Ok(())
    }

    /// An empty type erases the edit target's `typeName`, so a property queued
    /// after it plans against the weaker layer's type.
    #[test]
    fn set_type_erases() -> Result<()> {
        let (_dir, stage) = scene(&[
            (
                "root.usda",
                "(\n    subLayers = [@weak.usda@]\n)\nover DomeLight \"A\"\n{\n}\n",
            ),
            ("weak.usda", "def DistantLight \"A\"\n{\n}\n"),
        ])?;
        stage.edit(|edit| {
            let a = edit.prim("/A")?;
            a.set_type_name("")?;
            a.attribute_builder("inputs:angle", "double").set(1.0_f32).build()
        })?;

        assert_eq!(root_type(&stage, "/A"), None);
        assert_eq!(root_type(&stage, "/A.inputs:angle"), Some(tf::Token::new("float")));
        Ok(())
    }

    /// A schema a builder read before a change outside the batch is read
    /// again once the change commits: the attribute is declared from the type
    /// the prim has when it is built.
    #[test]
    fn outside_retype_rereads() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "def DistantLight \"A\"\n{\n}\n")])?;
        stage.edit(|edit| {
            let builder = edit.prim("/A")?.attribute_builder("inputs:angle", "double");
            assert_eq!(builder.declared_type()?, Some(sdf::ValueTypeName::FLOAT));
            stage.prim("/A")?.set_type_name("DomeLight")?;
            builder.set(1.0_f64).build()
        })?;

        assert_eq!(root_type(&stage, "/A"), Some(tf::Token::new("DomeLight")));
        assert_eq!(root_type(&stage, "/A.inputs:angle"), Some(tf::Token::new("double")));
        Ok(())
    }
}
