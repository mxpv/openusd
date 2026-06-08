//! High-level USD composition and authoring APIs.
//!
//! This module mirrors OpenUSD's `pxr/usd/usd` layer. The stage implementation
//! lives in the local `stage` module, while this module re-exports the public
//! `Usd*` surface under `openusd::usd`.

mod attribute;
mod clips;
mod collection;
mod connections;
mod interp;
mod prim;
mod relationship;
mod schema;
mod stage;

pub use attribute::Attribute;
pub use clips::ClipsAPI;
pub use collection::{
    apply_collection, collections_on, compute_included_paths, is_collection_api_path, Collection, ExpansionRule,
    MembershipQuery, PathExpansionRuleMap, PathRule,
};
pub use connections::ConnectionGraph;
pub use interp::InterpolationType;
pub use prim::{Prim, PrimIndexRef, VariantSets};
pub use relationship::Relationship;
pub use schema::{SchemaBase, SchemaKind};
pub use stage::{
    EditContext, EditTarget, InitialLoadSet, PrimPredicate, PrimStatus, Stage, StageAuthoringError, StageBuilder,
    StagePopulationMask,
};
