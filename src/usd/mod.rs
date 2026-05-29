//! High-level USD composition and authoring APIs.
//!
//! This module mirrors OpenUSD's `pxr/usd/usd` layer. The stage implementation
//! lives in the local `stage` module, while this module re-exports the public
//! `Usd*` surface under `openusd::usd`.

mod connections;
mod interp;
mod prim;
mod stage;

pub use connections::ConnectionGraph;
pub use interp::InterpolationType;
pub use prim::{Attribute, Prim, Relationship};
pub use stage::{
    CompositionError, EditTarget, InitialLoadSet, PrimPredicate, PrimStatus, Stage, StageAuthoringError, StageBuilder,
    StagePopulationMask,
};
