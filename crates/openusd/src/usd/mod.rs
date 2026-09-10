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
mod schema_decl;
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
pub use core_schemas::{SCHEMAS, tokens};
pub use diff::{ApplyMode, Diff, Edit, FieldValue};
pub use editor::{NamespaceEditError, NamespaceEditor};
pub use interp::InterpolationType;
pub use prim::{Prim, PrimIndexRef, VariantSets};
pub use prim_definition::{DefProperty, PrimDefinition};
pub use prim_type_info::{PrimTypeId, PrimTypeInfo};
pub use relationship::Relationship;
pub use resolve_info::{ResolveInfo, ResolveInfoSource};
pub use schema::{APISchemaBase, SchemaBase, SchemaKind, Typed};
pub use schema_decl::{Field, InstanceRestriction, PropertyDecl, SchemaDecl, SchemaFamily};
pub use schema_registry::{
    ApplyApiError, FamilySource, SchemaInfo, SchemaRegistry, SchemaRegistryBuilder, SchemaRegistryError, Schematics,
    VersionFilter,
};
pub use sink::{CommittedChange, PendingChange, Provenance, StageSink, StageSinkId};
pub use stage::{
    EditContext, EditTarget, EditTargetArc, InitialLoadSet, LoadPolicy, PrimPredicate, PrimStatus, Stage,
    StageAuthoringError, StageBuilder, TypeConflict, WeakStage,
};

/// The core `usd` family's schema data, generated from OpenUSD's own
/// `usd/schema.usda` and committed rather than built here: `openusd-build`
/// depends on this crate, so generating it at build time would be a cycle. The
/// `core_family` test there rewrites it and fails when it drifts.
///
/// Only the declarations are generated; the views for these schemas
/// ([`Collection`], [`ClipsAPI`]) are hand-written beside them. What it
/// declares is re-exported as [`SCHEMAS`] and [`tokens`], the shape every
/// generated family takes, so a caller can register the core family on a
/// builder of its own and name what its schemas call things.
mod core_schemas {
    // Included rather than declared, which is also how a consumer's own
    // generated views reach it: `cargo fmt` walks modules and would lay this
    // file out its own way, which is not how the generator wrote it, so the two
    // would fight over every regeneration. A macro is not a module, so rustfmt
    // never walks into it.
    include!("core_schemas.rs");
}

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
