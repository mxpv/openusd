//! High-level USD composition and authoring APIs.
//!
//! This module mirrors OpenUSD's `pxr/usd/usd` layer. The stage implementation
//! lives in the local `stage` module, while this module re-exports the public
//! `Usd*` surface under `openusd::usd`.

mod attribute;
mod authoring;
mod capture;
mod clips;
mod collection;
mod collection_expr;
mod composition;
mod connections;
mod diff;
mod editor;
mod flatten;
mod interp;
mod prim;
mod prim_definition;
mod prim_type_info;
mod relationship;
mod resolve_info;
mod schema;
mod schema_registry;
mod sink;
mod stage;
mod timecode;

pub use attribute::{Attribute, AttributeQuery};
pub use capture::{ReplayStage, UndoStage};
pub use clips::ClipsAPI;
pub use collection::{
    Collection, CollectionMode, ExpansionRule, MembershipQuery, PathExpansionRuleMap, PathRule, apply_collection,
    collections_on, compute_included_paths, is_collection_api_path,
};
pub use collection_expr::{CollectionEvaluator, CollectionSearcher, resolve_complete_membership_expression};
pub use connections::ConnectionGraph;
pub use diff::{ApplyMode, Diff, Edit, FieldValue};
pub use editor::{NamespaceEditError, NamespaceEditor};
pub use interp::InterpolationType;
pub use prim::{Prim, PrimIndexRef, VariantSets};
pub use prim_definition::{DefProperty, PrimDefinition};
pub use prim_type_info::{PrimTypeId, PrimTypeInfo};
pub use relationship::Relationship;
pub use resolve_info::{ResolveInfo, ResolveInfoSource};
pub use schema::{APISchemaBase, SchemaBase, SchemaKind, Typed};
pub use schema_registry::{
    ApplyApiError, FamilySource, SchemaInfo, SchemaRegistry, SchemaRegistryBuilder, SchemaRegistryError, Schematics,
    VersionFilter,
};
pub use sink::{CommittedChange, PendingChange, Provenance, StageSink, StageSinkId};
pub use stage::{
    EditContext, EditTarget, EditTargetArc, InitialLoadSet, LoadPolicy, PrimPredicate, PrimStatus, Stage,
    StageAuthoringError, StageBuilder, TypeConflict, WeakStage,
};

/// The population mask limiting which prims a [`Stage`] exposes, under its C++
/// name. The type lives in [`pcp`](crate::pcp) because an instance-relative
/// mask is part of a prototype's instancing key, but C++ defines it as
/// `UsdStagePopulationMask` and reaches it through `UsdStage`, so that is the
/// spelling this crate publishes.
pub use crate::pcp::PopulationMask as StagePopulationMask;
/// Why a path was rejected from a [`StagePopulationMask`].
pub use crate::pcp::PopulationMaskError as StagePopulationMaskError;
/// One spec contributing to a composed property or prim, under the name the
/// stack queries report it by.
pub use crate::pcp::SpecSiteRecord as SpecSite;
pub use timecode::TimeCode;

use crate::Result;
use crate::sdf;

/// Decodes an optionally-composed value to `T`, folding the conversion
/// failure into the caller's error. The one decode step behind every generic
/// read accessor ([`Attribute::get_at`], [`Prim::get_metadata`], ...), so a
/// future decode nuance lands in one place.
pub(crate) fn decode_value<T, E>(value: Option<sdf::Value>) -> Result<Option<T>, E>
where
    T: TryFrom<sdf::Value>,
    T::Error: Into<E>,
{
    value.map(T::try_from).transpose().map_err(Into::into)
}
