//! High-level USD composition and authoring APIs.
//!
//! This module mirrors OpenUSD's `pxr/usd/usd` layer. The stage implementation
//! lives in the local `stage` module, while this module re-exports the public
//! `Usd*` surface under `openusd::usd`.

mod collection;
mod connections;
mod interp;
mod prim;
mod stage;

pub use collection::{
    collections_on, compute_included_paths, is_collection_api_path, Collection, ExpansionRule, MembershipQuery,
    PathExpansionRuleMap, PathRule,
};
pub use connections::ConnectionGraph;
pub use interp::InterpolationType;
pub use prim::{Attribute, Prim, Relationship};
pub use stage::{
    CompositionError, EditContext, EditTarget, InitialLoadSet, PrimPredicate, PrimStatus, Stage, StageAuthoringError,
    StageBuilder, StagePopulationMask,
};
