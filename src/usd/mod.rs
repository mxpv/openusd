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
mod timecode;

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
    EditContext, EditTarget, EditTargetArc, InitialLoadSet, PrimPredicate, PrimStatus, Stage, StageAuthoringError,
    StageBuilder, StagePopulationMask,
};
pub use timecode::TimeCode;

use crate::sdf;

/// Run `f` on the typed spec at `path` on the edit-target layer, or return
/// [`sdf::AuthoringError::InvalidPath`] when no such spec exists. `get` is the
/// spec view's constructor (e.g. `sdf::PrimSpecMut::get`); `reason` names the
/// missing spec. The shared body of the `usd`-tier authoring closures.
fn edit_spec<'a, S>(
    data: &'a mut dyn sdf::AbstractData,
    path: sdf::Path,
    reason: &'static str,
    get: impl FnOnce(&'a mut dyn sdf::AbstractData, sdf::Path) -> Option<S>,
    f: impl FnOnce(&mut S) -> Result<(), sdf::AuthoringError>,
) -> Result<(), sdf::AuthoringError> {
    match get(data, path.clone()) {
        Some(mut spec) => f(&mut spec),
        None => Err(sdf::AuthoringError::InvalidPath { path, reason }),
    }
}
