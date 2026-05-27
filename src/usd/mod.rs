//! High-level USD composition and authoring APIs.
//!
//! This module mirrors OpenUSD's `pxr/usd/usd` layer. The stage implementation
//! lives in the local `stage` module, while this module re-exports the public
//! `Usd*` surface under `openusd::usd`.

mod interp;
mod stage;

pub use interp::InterpolationType;
pub use stage::{
    CompositionError, EditTarget, InitialLoadSet, PrimPredicate, PrimStatus, Stage, StageAuthoringError, StageBuilder,
    StagePopulationMask,
};
