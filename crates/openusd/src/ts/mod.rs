//! Time splines (C++ `Ts`): [`Spline`], a scalar curve over time built from
//! [`Knot`]s, the value an attribute's `spline` field holds (C++ `TsSpline`).
//!
//! A spline is a sequence of knots in time order. Each knot starts a segment
//! that runs to the next knot and is interpolated as its [`InterpMode`] says;
//! a curve segment is a Bezier or a Hermite curve, as the spline's
//! [`CurveType`] says, shaped by the tangents facing it. Outside the knots the
//! spline is extrapolated ([`Extrapolation`]), and a span of it can repeat
//! ([`LoopParams`]).
//!
//! A tangent is a width and a slope: the width is how far it reaches in time,
//! the slope its rise over run. Text and binary layers store the same pair.
//!
//! Start at [`Spline`]. `eval.rs` is the evaluator, `regression.rs` the
//! shortening of Bezier tangents that would make a segment run backwards in
//! time, and `binary.rs` the encoding a `usdc` layer stores.
//!
//! <https://openusd.org/dev/api/ts_page_front.html>

mod binary;
mod eval;
mod knot;
mod regression;
mod spline;

pub use binary::DecodeError;
pub use knot::{InterpMode, Knot, Tangent, TangentAlgorithm};
pub use regression::AntiRegression;
pub use spline::{CurveType, Error, Extrapolation, LoopParams, Spline, ValueType};
