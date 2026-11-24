//! Spline evaluation (C++ `Ts_Eval`, `pxr/base/ts/eval.cpp`).
//!
//! An evaluation first resolves loops: a time in an echo of the spline's
//! knots, made by inner looping or by a looping extrapolation, is moved to the
//! time it copies, with the value offset the copy adds. The moved time is then
//! evaluated against the authored knots: at a knot, in an extrapolation
//! region, or in the segment between two knots.
//!
//! The evaluation follows C++ step for step, and departs from it where C++
//! loses the answer:
//!
//! - A Bezier segment's time cubic is built from the segment's start and
//!   solved in closed form as C++ solves it, then bisected for where the
//!   closed form misses the root. C++ builds the cubic in absolute time and
//!   keeps the closed form's answer.
//! - A looping extrapolation places the time by its remainder in the knots'
//!   span. C++ counts the iterations in an `int`, which overflows far
//!   outside the knots.
//! - A copy of a prototype knot carries its echo's value offset whatever is
//!   evaluated, so the slope of a linear segment that ends at one is the
//!   slope of the curve. C++ offsets the copy only for a value.
//! - The last authored knot, where it lies in the inner loop's prototype,
//!   starts the segment the loop closes. C++ reads the post-extrapolation
//!   there.
//! - The slope of a Bezier segment where the curve stands still in both time
//!   and value is the limit of their ratio. C++ divides zero by zero.
//!
//! TODO: an evaluation exactly where two iterations of an inner loop join
//! reads the prototype's first knot, as C++ reads it. The side before the
//! join then misses the segment that closes the earlier iteration, and the
//! end of the last echo misses the post-extrapolation that follows it. The
//! missing piece is a model of the join as a knot of its own, with the
//! closing segment before it and the echo's first segment, or the
//! extrapolation, after it.

use std::f64::consts::PI;

use crate::gf;

use super::spline::Data;
use super::{AntiRegression, CurveType, Extrapolation, InterpMode, Knot, regression};

/// What an evaluation computes (C++ `Ts_EvalAspect`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Aspect {
    /// The spline's value.
    Value,
    /// The spline's value with every segment read as held.
    HeldValue,
    /// The spline's slope.
    Derivative,
}

/// Which side of a time an evaluation reads (C++ `Ts_EvalLocation`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Location {
    /// The limit as time rises to the evaluation time.
    Pre,
    /// The evaluation time itself, which is also the limit from above.
    AtTime,
}

/// The value or slope of `data` at `time`, or `None` where it has none.
pub(super) fn eval(data: &Data, time: f64, aspect: Aspect, location: Location) -> Option<f64> {
    if data.knots.is_empty() {
        return None;
    }
    let resolver = LoopResolver::new(data, time, aspect, location);
    let result = eval_main(data, &resolver, aspect)? + resolver.value_offset;
    Some(if resolver.negate { -result } else { result })
}

/// The numbers of a knot an evaluation reads, which a loop may shift (C++
/// `Ts_TypedKnotData<double>`).
#[derive(Debug, Clone, Copy, Default)]
struct KnotData {
    time: f64,
    value: f64,
    pre_value: Option<f64>,
    pre_width: f64,
    pre_slope: f64,
    post_width: f64,
    post_slope: f64,
    next_interp: InterpMode,
}

impl KnotData {
    fn pre_value(&self) -> f64 {
        self.pre_value.unwrap_or(self.value)
    }

    /// How far the pre-tangent's end point is above the knot's pre-value.
    fn pre_height(&self) -> f64 {
        -self.pre_width * self.pre_slope
    }

    /// How far the post-tangent's end point is above the knot's value.
    fn post_height(&self) -> f64 {
        self.post_width * self.post_slope
    }
}

impl From<&Knot> for KnotData {
    fn from(knot: &Knot) -> Self {
        Self {
            time: knot.time,
            value: knot.value,
            pre_value: knot.pre_value,
            pre_width: knot.pre_tangent.width,
            pre_slope: knot.pre_tangent.slope,
            post_width: knot.post_tangent.width,
            post_slope: knot.post_tangent.slope,
            next_interp: knot.next_interp,
        }
    }
}

/// Where an evaluation in an echo of the spline's knots reads instead, and
/// what to do with the answer (C++ `_LoopResolver`).
///
/// A looping extrapolation is resolved before inner loops: the reverse of the
/// order the copies are made in, which echoes the inner loop's prototype
/// first and repeats the result.
struct LoopResolver<'a> {
    data: &'a Data,
    aspect: Aspect,
    /// The time to evaluate at, outside every echo.
    eval_time: f64,
    /// The side to evaluate on, which an oscillating loop flips.
    location: Location,
    /// What the copy adds to the value read at [`eval_time`](Self::eval_time).
    value_offset: f64,
    /// Whether the answer is negated: a slope read in a reversed copy.
    negate: bool,

    /// The index of the knot the inner loop's prototype starts at, where
    /// inner looping is on.
    first_proto_index: Option<usize>,
    /// The first and last knot times, authored or echoed by inner looping.
    first_time: f64,
    last_time: f64,
    /// Whether inner looping made the first knot, and the last.
    first_time_looped: bool,
    last_time_looped: bool,

    /// The evaluation time lies after the prototype's last knot and before
    /// its end, where the next knot is a copy of the prototype's first.
    between_last_proto_and_end: bool,
    /// The evaluation time lies between the last knot before the looped span
    /// and the span's start.
    between_pre_unlooped_and_looped: bool,
    /// The evaluation time lies between the looped span's end and the first
    /// knot after it.
    between_looped_and_post_unlooped: bool,
    /// The spline's end knot and the one inward of it, where inner looping
    /// made them and the evaluation extrapolates from them.
    extrap_knots: Option<(KnotData, KnotData)>,
}

impl<'a> LoopResolver<'a> {
    fn new(data: &'a Data, time: f64, aspect: Aspect, location: Location) -> Self {
        let mut resolver = Self {
            data,
            aspect,
            eval_time: time,
            location,
            value_offset: 0.0,
            negate: false,
            first_proto_index: data.first_proto_index(),
            first_time: 0.0,
            last_time: 0.0,
            first_time_looped: false,
            last_time_looped: false,
            between_last_proto_and_end: false,
            between_pre_unlooped_and_looped: false,
            between_looped_and_post_unlooped: false,
            extrap_knots: None,
        };
        let have_inner_loops = resolver.first_proto_index.is_some();

        // Valid inner looping always makes a second knot.
        let have_multiple_knots = have_inner_loops || data.knots.len() > 1;
        let pre_loops = have_multiple_knots && data.pre_extrapolation.is_looping();
        let post_loops = have_multiple_knots && data.post_extrapolation.is_looping();
        if !have_inner_loops && !pre_loops && !post_loops {
            return resolver;
        }

        let (Some(first), Some(last)) = (data.knots.first(), data.knots.last()) else {
            return resolver;
        };
        resolver.first_time = first.time;
        resolver.last_time = last.time;
        if have_inner_loops {
            let looped = data.loop_params.looped_interval();
            if looped.min() < first.time {
                resolver.first_time = looped.min();
                resolver.first_time_looped = true;
            }
            if looped.max() > last.time {
                resolver.last_time = looped.max();
                resolver.last_time_looped = true;
            }
        }

        if pre_loops || post_loops {
            resolver.resolve_extrap(pre_loops, post_loops);
        }
        if let Some(first_proto) = resolver.first_proto_index {
            resolver.resolve_inner(first_proto);
        }
        resolver
    }

    /// Moves an evaluation in a looping extrapolation region into the span of
    /// the knots (C++ `_LoopResolver::_ResolveExtrap`).
    fn resolve_extrap(&mut self, pre_loops: bool, post_loops: bool) {
        // The span that needs no extrapolation is closed at the end the
        // evaluation reads from.
        let pre = self.location == Location::Pre;
        let knot_interval = gf::Interval::new(self.first_time, self.last_time, !pre, pre);
        if knot_interval.contains(self.eval_time) {
            return;
        }
        if pre_loops && self.eval_time < self.last_time {
            self.do_extrap(self.data.pre_extrapolation);
        } else if post_loops && self.eval_time > self.first_time {
            self.do_extrap(self.data.post_extrapolation);
        }
    }

    /// Moves the evaluation time from a looping extrapolation region into the
    /// span of the knots, `extrapolation` being that region's (C++
    /// `_LoopResolver::_DoExtrap`).
    ///
    /// The time is placed by its remainder in the knots' span, which is
    /// exact however far outside the knots it is.
    fn do_extrap(&mut self, extrapolation: Extrapolation) {
        let span = self.last_time - self.first_time;
        // Where the time falls in a pair of iterations, counted from the
        // first knot: the first of the pair runs as the knots do, and an
        // oscillation reverses the second.
        let period = 2.0 * span;
        let position = (self.eval_time % period - self.first_time % period).rem_euclid(period);
        let (mut odd, mut local) = match position >= span {
            true => (true, position - span),
            false => (false, position),
        };
        // A time a hair before the pair's start rounds to the pair's end. It
        // lies before that join, and reads the end of the second iteration
        // from that side.
        if local >= span {
            (odd, local) = (false, 0.0);
            self.location = Location::Pre;
        }
        // How many iterations the time is from the knots' own.
        let mut iteration = ((self.eval_time - self.first_time - local) / span).round();

        // Exactly where two iterations join, the side before the join reads
        // the end of the earlier one.
        if local == 0.0 && self.location == Location::Pre {
            iteration -= 1.0;
            odd = !odd;
            self.eval_time = self.last_time;
        } else {
            self.eval_time = self.first_time + local;
        }

        match extrapolation {
            // Each iteration starts from the value the one before it ended
            // at, so the offsets accumulate.
            Extrapolation::LoopRepeat if self.aspect != Aspect::Derivative => {
                // A curve that ends where it starts repeats with no offset,
                // however many iterations away.
                let rise = self.extrap_value_offset();
                if rise != 0.0 {
                    self.value_offset += iteration * rise;
                }
            }
            // Every other iteration is reflected in time.
            Extrapolation::LoopOscillate if odd => {
                self.eval_time = self.first_time + (span - (self.eval_time - self.first_time));
                self.location = match self.location {
                    Location::Pre => Location::AtTime,
                    Location::AtTime => Location::Pre,
                };
                self.negate = self.aspect == Aspect::Derivative;
            }
            // A reset iteration is an exact copy. Its jump comes from the two
            // sides of a join reading different iterations.
            _ => {}
        }
    }

    /// How much the spline's value rises from its first knot to its last,
    /// either of which inner looping may have made (C++
    /// `_LoopResolver::_ComputeExtrapValueOffset`).
    fn extrap_value_offset(&self) -> f64 {
        let params = &self.data.loop_params;
        let knots = &self.data.knots;
        let proto = self.first_proto_index.map(|index| &knots[index]);
        let first_value = match proto {
            Some(proto) if self.first_time_looped => {
                proto.pre_value() - f64::from(params.num_pre_loops) * params.value_offset
            }
            _ => knots[0].pre_value(),
        };
        let last_value = match proto {
            // The final echo of the prototype's start knot.
            Some(proto) if self.last_time_looped => {
                proto.value + (f64::from(params.num_post_loops) + 1.0) * params.value_offset
            }
            _ => knots[knots.len() - 1].value,
        };
        last_value - first_value
    }

    /// Moves an evaluation in an echo of the inner loop's prototype into the
    /// prototype, and notes where the knots beside the evaluation time are
    /// copies (C++ `_LoopResolver::_ResolveInner`).
    fn resolve_inner(&mut self, first_proto: usize) {
        let params = self.data.loop_params;
        let (pre_loops, post_loops) = (f64::from(params.num_pre_loops), f64::from(params.num_post_loops));
        let looped = params.looped_interval();
        let proto = params.prototype_interval();
        let knots = &self.data.knots;

        if looped.contains(self.eval_time) && !proto.contains(self.eval_time) {
            let proto_span = params.proto_end - params.proto_start;
            // Which iteration the evaluation falls in.
            let hop = if self.eval_time < params.proto_start {
                ((params.proto_start - self.eval_time) / proto_span).ceil()
            } else {
                -(((self.eval_time - params.proto_end) / proto_span).trunc() + 1.0)
            };
            self.eval_time += hop * proto_span;
            if self.aspect != Aspect::Derivative {
                self.value_offset -= hop * params.value_offset;
            }
        }

        // The index one past the prototype's last authored knot. A knot
        // exactly at the prototype's end is not part of it, and the
        // prototype always holds its first knot.
        let proto_knots_end = first_proto + knots[first_proto..].partition_point(|knot| knot.time < params.proto_end);

        if proto.contains(self.eval_time) {
            self.between_last_proto_and_end = self.eval_time > knots[proto_knots_end - 1].time;
        } else if self.eval_time < self.first_time {
            // Pre-extrapolating from knots inner looping made: a copy of the
            // prototype's first knot, then one of its second, or of its
            // first again where it has no second.
            // TODO: C++ leaves unhandled the case where the spline's first
            // knot is authored and its second is an echo, so a linear
            // extrapolation takes its slope from the authored second knot.
            // The same holds at the spline's end.
            if self.first_time_looped {
                let second = match knots.get(first_proto + 1) {
                    Some(second) if proto.contains(second.time) => self.copy_proto_knot(first_proto + 1, -pre_loops),
                    _ => self.copy_proto_knot(first_proto, -pre_loops + 1.0),
                };
                self.extrap_knots = Some((self.copy_proto_knot(first_proto, -pre_loops), second));
            }
        } else if self.eval_time > self.last_time {
            // Post-extrapolating from knots inner looping made: the final
            // copy of the prototype's first knot, preceded by the last copy
            // of its last.
            if self.last_time_looped {
                self.extrap_knots = Some((
                    self.copy_proto_knot(first_proto, post_loops + 1.0),
                    self.copy_proto_knot(proto_knots_end - 1, post_loops),
                ));
            }
        } else if self.eval_time < looped.min() {
            // The last authored knot before the looped span, if any.
            let before = knots[..first_proto].partition_point(|knot| knot.time < looped.min());
            if let Some(last_unlooped) = before.checked_sub(1) {
                self.between_pre_unlooped_and_looped = self.eval_time > knots[last_unlooped].time;
            }
        } else if self.eval_time > looped.max() {
            // The first authored knot strictly after the looped span, if any.
            let after = first_proto + 1 + knots[first_proto + 1..].partition_point(|knot| knot.time <= looped.max());
            if let Some(first_unlooped) = knots.get(after) {
                self.between_looped_and_post_unlooped = self.eval_time < first_unlooped.time;
            }
        }
    }

    /// The knot at `index`, shifted `shift_iters` iterations of the inner
    /// loop (C++ `_LoopResolver::_CopyProtoKnotData`).
    fn copy_proto_knot(&self, index: usize, shift_iters: f64) -> KnotData {
        let params = &self.data.loop_params;
        let mut knot = KnotData::from(&self.data.knots[index]);
        knot.time += shift_iters * (params.proto_end - params.proto_start);
        let offset = shift_iters * params.value_offset;
        knot.value += offset;
        knot.pre_value = knot.pre_value.map(|value| value + offset);
        knot
    }

    /// Replaces one of the knots around the evaluation time with the copy of
    /// the prototype's first knot that inner looping puts there (C++
    /// `_LoopResolver::ReplaceBoundaryKnots`).
    fn replace_boundary_knots(&self, prev: &mut KnotData, next: &mut KnotData) {
        let Some(first_proto) = self.first_proto_index else {
            return;
        };
        let params = &self.data.loop_params;
        if self.between_last_proto_and_end {
            *next = self.copy_proto_knot(first_proto, 1.0);
        } else if self.between_pre_unlooped_and_looped {
            *next = self.copy_proto_knot(first_proto, -f64::from(params.num_pre_loops));
        } else if self.between_looped_and_post_unlooped {
            *prev = self.copy_proto_knot(first_proto, f64::from(params.num_post_loops) + 1.0);
        }
    }
}

/// Evaluates at the resolver's time against the authored knots (C++
/// `_EvalMain`).
fn eval_main(data: &Data, resolver: &LoopResolver<'_>, aspect: Aspect) -> Option<f64> {
    let time = resolver.eval_time;
    let location = resolver.location;
    let knots = &data.knots;
    let count = knots.len();
    let at = |index: usize| knots.get(index).map(KnotData::from);

    // The knots around the time: the one before it, the one at it if there
    // is one, and the one after it. A missing knot reads as a default one,
    // which the branches below never draw a value from.
    let (knot_index, next_index) = match data.index_of(time) {
        Ok(index) => (Some(index), index + 1),
        Err(index) => (None, index),
    };
    let lower = knot_index.unwrap_or(next_index);
    let prev_index = lower.checked_sub(1);
    let before_start = next_index == 0;
    let after_end = !resolver.between_last_proto_and_end && prev_index == Some(count - 1);
    let have_multiple_knots = count > 1;

    let mut prev = prev_index.and_then(at).unwrap_or_default();
    let mut next = at(next_index).unwrap_or_default();

    if let Some(index) = knot_index {
        let knot = KnotData::from(&knots[index]);
        let at_first = index == 0;
        // The prototype's last knot is followed by the segment a copy of
        // its first knot closes, whatever knots are authored after it.
        let params = &data.loop_params;
        let closing = resolver.first_proto_index.filter(|&first_proto| {
            let proto_knots_end =
                first_proto + knots[first_proto..].partition_point(|knot| knot.time < params.proto_end);
            index + 1 == proto_knots_end && params.prototype_interval().contains(time)
        });
        if let Some(first_proto) = closing {
            next = resolver.copy_proto_knot(first_proto, 1.0);
        }
        let at_last = index == count - 1 && closing.is_none();
        return match (aspect, location) {
            (Aspect::Value | Aspect::HeldValue, Location::Pre) => {
                if at_first {
                    if data.pre_extrapolation == Extrapolation::ValueBlock {
                        return None;
                    }
                } else if prev.next_interp == InterpMode::ValueBlock {
                    return None;
                } else if prev.next_interp == InterpMode::Held || aspect == Aspect::HeldValue {
                    // The pre-value after a held segment is the value of the
                    // knot the segment started at.
                    return Some(prev.value);
                }
                Some(knot.pre_value())
            }
            (Aspect::Value | Aspect::HeldValue, Location::AtTime) => {
                let blocked = match at_last {
                    true => data.post_extrapolation == Extrapolation::ValueBlock,
                    false => knot.next_interp == InterpMode::ValueBlock,
                };
                (!blocked).then_some(knot.value)
            }
            (Aspect::Derivative, Location::Pre) => {
                if at_first {
                    return extrapolation_slope(
                        data.pre_extrapolation,
                        have_multiple_knots,
                        &knot,
                        &next,
                        Location::Pre,
                    );
                }
                match prev.next_interp {
                    InterpMode::ValueBlock => None,
                    InterpMode::Held => Some(0.0),
                    InterpMode::Linear => Some(segment_slope(&prev, &knot)),
                    InterpMode::Curve => Some(knot.pre_slope),
                }
            }
            (Aspect::Derivative, Location::AtTime) => {
                if at_last {
                    return extrapolation_slope(
                        data.post_extrapolation,
                        have_multiple_knots,
                        &knot,
                        &prev,
                        Location::AtTime,
                    );
                }
                match knot.next_interp {
                    InterpMode::ValueBlock => None,
                    InterpMode::Held => Some(0.0),
                    InterpMode::Linear => Some(segment_slope(&knot, &next)),
                    InterpMode::Curve => Some(knot.post_slope),
                }
            }
        };
    }

    if before_start {
        if data.pre_extrapolation == Extrapolation::ValueBlock {
            return None;
        }
        // `next` is the first knot; the slope may need the one after it.
        let mut next2 = at(next_index + 1).unwrap_or_default();
        if let Some((end, inward)) = resolver.extrap_knots {
            (next, next2) = (end, inward);
        }
        if aspect == Aspect::HeldValue {
            // No held value is natural before the first knot. C++ answers
            // with the first knot's, like the answer after the last.
            return Some(next.pre_value());
        }
        let slope = extrapolation_slope(
            data.pre_extrapolation,
            have_multiple_knots,
            &next,
            &next2,
            Location::Pre,
        )?;
        return Some(match aspect {
            Aspect::Derivative => slope,
            _ => extrapolate_linear(&next, slope, time, Location::Pre),
        });
    }

    if after_end {
        if data.post_extrapolation == Extrapolation::ValueBlock {
            return None;
        }
        // `prev` is the last knot; the slope may need the one before it.
        let mut prev2 = prev_index
            .and_then(|index| index.checked_sub(1))
            .and_then(at)
            .unwrap_or_default();
        if let Some((end, inward)) = resolver.extrap_knots {
            (prev, prev2) = (end, inward);
        }
        if aspect == Aspect::HeldValue {
            return Some(prev.value);
        }
        let slope = extrapolation_slope(
            data.post_extrapolation,
            have_multiple_knots,
            &prev,
            &prev2,
            Location::AtTime,
        )?;
        return Some(match aspect {
            Aspect::Derivative => slope,
            _ => extrapolate_linear(&prev, slope, time, Location::AtTime),
        });
    }

    resolver.replace_boundary_knots(&mut prev, &mut next);
    interpolate(&prev, &next, time, aspect, data.curve_type)
}

/// Interpolates the segment from `begin` to `end` at `time` (C++
/// `_Interpolate`).
fn interpolate(begin: &KnotData, end: &KnotData, time: f64, aspect: Aspect, curve_type: CurveType) -> Option<f64> {
    match (begin.next_interp, aspect) {
        (InterpMode::ValueBlock, _) => None,
        (_, Aspect::HeldValue) | (InterpMode::Held, Aspect::Value) => Some(begin.value),
        (InterpMode::Curve, _) => Some(match curve_type {
            CurveType::Bezier => eval_bezier(begin, end, time, aspect),
            CurveType::Hermite => eval_hermite(begin, end, time, aspect),
        }),
        (InterpMode::Held, Aspect::Derivative) => Some(0.0),
        (InterpMode::Linear, _) => {
            let slope = segment_slope(begin, end);
            Some(match aspect {
                Aspect::Derivative => slope,
                _ => extrapolate_linear(begin, slope, time, Location::AtTime),
            })
        }
    }
}

/// The slope of the straight line from `begin` to `end`, which a linear
/// segment follows whatever its tangents say.
fn segment_slope(begin: &KnotData, end: &KnotData) -> f64 {
    (end.pre_value() - begin.value) / (end.time - begin.time)
}

/// The slope of an extrapolation region, or `None` where it is a value block
/// (C++ `_GetExtrapolationSlope`). `end_knot` is the spline's end knot on
/// that side and `adjacent` the knot inward of it. A looping extrapolation
/// has been resolved into the knots' span before this is asked.
fn extrapolation_slope(
    extrapolation: Extrapolation,
    have_multiple_knots: bool,
    end_knot: &KnotData,
    adjacent: &KnotData,
    location: Location,
) -> Option<f64> {
    match extrapolation {
        Extrapolation::ValueBlock => return None,
        Extrapolation::Held => return Some(0.0),
        Extrapolation::Sloped(slope) => return Some(slope),
        _ => {}
    }
    // A lone knot and a dual-valued end knot extrapolate flat.
    if !have_multiple_knots || extrapolation != Extrapolation::Linear || end_knot.pre_value.is_some() {
        return Some(0.0);
    }
    // The segment the region continues: the first, starting at the end knot,
    // or the last, starting at the knot inward of it.
    let (begin, end, tangent_slope) = match location {
        Location::Pre => (end_knot, adjacent, end_knot.post_slope),
        Location::AtTime => (adjacent, end_knot, end_knot.pre_slope),
    };
    Some(match begin.next_interp {
        InterpMode::Held | InterpMode::ValueBlock => 0.0,
        InterpMode::Linear => segment_slope(begin, end),
        // A curve continues the slope of the end knot's inward tangent.
        InterpMode::Curve => tangent_slope,
    })
}

/// The value at `time` on the straight line with `slope` through `knot`,
/// leaving from the side `location` names.
fn extrapolate_linear(knot: &KnotData, slope: f64, time: f64, location: Location) -> f64 {
    let value = match location {
        Location::Pre => knot.pre_value(),
        Location::AtTime => knot.value,
    };
    // A flat line holds the knot's value however far away the time is, an
    // infinite time included, where the product below is not a number.
    if slope == 0.0 {
        return value;
    }
    value + slope * (time - knot.time)
}

/// A Bezier parameter this far outside `[0, 1]` is rounding noise.
const PARAMETER_EPSILON: f64 = 1.0e-10;

/// One of a Bezier segment's two cubics, time or value over the parameter,
/// in power form: `a t^3 + b t^2 + c t + d`.
#[derive(Debug, Clone, Copy)]
struct Cubic {
    a: f64,
    b: f64,
    c: f64,
    d: f64,
}

impl Cubic {
    /// The cubic through the segment's start `p0`, its two tangent end points
    /// `p1` and `p2`, and its end `p3`.
    fn from_points(p0: f64, p1: f64, p2: f64, p3: f64) -> Self {
        Self {
            a: -p0 + 3.0 * p1 - 3.0 * p2 + p3,
            b: 3.0 * p0 - 6.0 * p1 + 3.0 * p2,
            c: -3.0 * p0 + 3.0 * p1,
            d: p0,
        }
    }

    fn eval(&self, t: f64) -> f64 {
        t * (t * (t * self.a + self.b) + self.c) + self.d
    }

    /// The cubic's derivative at `t`.
    fn derivative(&self, t: f64) -> f64 {
        t * (t * 3.0 * self.a + 2.0 * self.b) + self.c
    }

    /// The cubic's second derivative at `t`.
    fn second_derivative(&self, t: f64) -> f64 {
        6.0 * self.a * t + 2.0 * self.b
    }

    /// The `t` in `[0, 1]` at which the cubic is zero, given that it rises
    /// monotonically there through zero.
    ///
    /// The closed form answers ([`monotonic_zero`](Self::monotonic_zero)),
    /// as it does in C++. It divides by the cubic's leading coefficient,
    /// and where that is nearly zero the root is lost to cancellation: the
    /// answer then leaves the cubic far from zero, and the root is bisected
    /// for.
    fn zero_in_unit(&self) -> f64 {
        let t = self.monotonic_zero().clamp(0.0, 1.0);
        // The cubic rises by one across the segment, so what it leaves is a
        // fraction of the segment.
        if self.eval(t).abs() <= 1e-9 {
            return t;
        }
        let (mut low, mut high) = (0.0_f64, 1.0_f64);
        // Each pass halves the bracket, down to the spacing of doubles.
        for _ in 0..64 {
            let middle = 0.5 * (low + high);
            match self.eval(middle) < 0.0 {
                true => low = middle,
                false => high = middle,
            }
        }
        0.5 * (low + high)
    }

    /// The zero of the cubic in closed form (C++ `_FindMonotonicZero`).
    fn monotonic_zero(&self) -> f64 {
        let near_zero = |value: f64| value.abs() < PARAMETER_EPSILON;
        let (a_zero, b_zero, c_zero) = (near_zero(self.a), near_zero(self.b), near_zero(self.c));
        if a_zero && b_zero {
            // A line, or a constant, which has no zero to find.
            return if c_zero { 0.0 } else { -self.d / self.c };
        }
        if a_zero {
            // A quadratic.
            let root = (self.c.powi(2) - 4.0 * self.b * self.d).sqrt();
            return nearest_zero(&[(-self.c - root) / (2.0 * self.b), (-self.c + root) / (2.0 * self.b)]);
        }

        // Cardano's method, on the cubic scaled so that its leading
        // coefficient is one.
        let (b, c, d) = (self.b / self.a, self.c / self.a, self.d / self.a);
        let p = (3.0 * c - b * b) / 3.0;
        let p3 = p / 3.0;
        let p33 = p3 * p3 * p3;
        let q = (2.0 * b * b * b - 9.0 * b * c + 27.0 * d) / 27.0;
        let q2 = q / 2.0;
        let discriminant = q2 * q2 + p33;
        let b3 = b / 3.0;

        if discriminant < 0.0 {
            // Three real roots.
            let r = (-p33).sqrt();
            let phi = (-q / (2.0 * r)).clamp(-1.0, 1.0).acos();
            let t1 = 2.0 * r.cbrt();
            nearest_zero(&[
                t1 * (phi / 3.0).cos() - b3,
                t1 * ((phi + 2.0 * PI) / 3.0).cos() - b3,
                t1 * ((phi + 4.0 * PI) / 3.0).cos() - b3,
            ])
        } else if discriminant == 0.0 {
            // Two real roots.
            let u1 = -q2.cbrt();
            nearest_zero(&[2.0 * u1 - b3, -u1 - b3])
        } else {
            // One real root.
            let root = discriminant.sqrt();
            (root - q2).cbrt() - (root + q2).cbrt() - b3
        }
    }
}

/// The zero nearest the middle of `[0, 1]`, the first of equals (C++
/// `_FilterZeros`).
fn nearest_zero(zeros: &[f64]) -> f64 {
    let mut result = zeros[0];
    for &zero in &zeros[1..] {
        if (zero - 0.5).abs() < (result - 0.5).abs() {
            result = zero;
        }
    }
    result
}

/// The value or slope at `time` of the Bezier segment from `begin` to `end`
/// (C++ `_EvalBezier`).
fn eval_bezier(begin: &KnotData, end: &KnotData, time: f64, aspect: Aspect) -> f64 {
    // A regressive segment is evaluated with its tangents shortened in
    // proportion, whatever the spline was authored with.
    let (mut begin, mut end) = (*begin, *end);
    let (start_width, end_width) = regression::adjust(
        AntiRegression::KeepRatio,
        end.time - begin.time,
        begin.post_width,
        end.pre_width,
    );
    begin.post_width = start_width.unwrap_or(begin.post_width);
    end.pre_width = end_width.unwrap_or(end.pre_width);

    // The segment's time over its parameter, as a fraction of the segment:
    // a cubic from 0 to 1 wherever the segment sits and whatever unit its
    // times are in.
    let duration = end.time - begin.time;
    let time_cubic = Cubic::from_points(0.0, begin.post_width / duration, 1.0 - end.pre_width / duration, 1.0);
    // The parameter at which the segment reaches `time`: the zero of its
    // time cubic, offset by `time`.
    let t = Cubic {
        d: -(time - begin.time) / duration,
        ..time_cubic
    }
    .zero_in_unit();

    let value = Cubic::from_points(
        begin.value,
        begin.value + begin.post_height(),
        end.pre_value() + end.pre_height(),
        end.pre_value(),
    );
    match aspect {
        // The value's rate over the parameter, by the time's. Where the
        // curve stands still in both, the slope is the limit of that ratio:
        // the ratio of the next derivatives that do not both vanish.
        Aspect::Derivative => [
            (value.derivative(t), time_cubic.derivative(t)),
            (value.second_derivative(t), time_cubic.second_derivative(t)),
            (value.a, time_cubic.a),
        ]
        .into_iter()
        .find(|(rise, run)| *rise != 0.0 || *run != 0.0)
        .map_or(0.0, |(rise, run)| rise / (run * duration)),
        _ => value.eval(t),
    }
}

/// The value or slope at `time` of the Hermite segment from `begin` to `end`
/// (C++ `_EvalHermite`): the cubic through the two knots with the slopes of
/// the tangents facing the segment.
fn eval_hermite(begin: &KnotData, end: &KnotData, time: f64, aspect: Aspect) -> f64 {
    let (t0, v0) = (begin.time, begin.value);
    let (t1, v1) = (end.time, end.pre_value());
    if t0 >= t1 {
        return v0;
    }
    let dt = t1 - t0;
    let dv = v1 - v0;

    // Over a unit span, with the slopes scaled to match.
    let u = (time - t0) / dt;
    let m0 = begin.post_slope * dt;
    let m1 = end.pre_slope * dt;

    let cubic = Cubic {
        a: -2.0 * dv + m0 + m1,
        b: 3.0 * dv - 2.0 * m0 - m1,
        c: m0,
        d: v0,
    };
    match aspect {
        Aspect::Derivative => cubic.derivative(u) / dt,
        _ => cubic.eval(u),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::{LoopParams, Spline, Tangent, ValueType};

    /// The knots of C++ `testTsSplineEval`: a held, a blocked, a linear and a
    /// curved segment, every knot dual-valued.
    fn spline(value_type: ValueType) -> Spline {
        let knot = |time: f64, next_interp, pre_value: f64, value: f64, pre: (f64, f64), post: (f64, f64)| Knot {
            pre_value: Some(pre_value),
            pre_tangent: Tangent::new(pre.0, pre.1),
            post_tangent: Tangent::new(post.0, post.1),
            next_interp,
            ..Knot::new(time, value)
        };
        let mut spline = Spline::new(value_type);
        spline
            .set_knots([
                knot(0.0, InterpMode::Held, 5.0, 10.0, (1.0, 1.0), (1.0, -1.0)),
                knot(4.0, InterpMode::ValueBlock, 3.0, 6.0, (1.0, 1.0), (1.0, -1.0)),
                knot(8.0, InterpMode::Linear, 8.0, 8.0, (1.0, 1.0), (1.0, -2.0)),
                knot(12.0, InterpMode::Curve, 0.0, 4.0, (1.0, 1.0), (2.0, 1.0)),
                knot(16.0, InterpMode::Linear, 8.0, 10.0, (2.0, 0.0), (1.0, -1.0)),
            ])
            .expect("valid knots");
        spline
    }

    /// What C++ expects at one time: the pre-value and value, the pre-slope
    /// and slope, and the held pre-value and value.
    type Expected = (f64, [Option<f64>; 6]);

    fn check(spline: &Spline, expected: &[Expected], tolerance: f64) {
        for &(time, expected) in expected {
            let got = [
                spline.eval_pre_value(time),
                spline.eval(time),
                spline.eval_pre_derivative(time),
                spline.eval_derivative(time),
                spline.eval_pre_value_held(time),
                spline.eval_held(time),
            ];
            for (aspect, (got, expected)) in got.iter().zip(expected).enumerate() {
                let close = match (got, expected) {
                    (Some(got), Some(expected)) => (got - expected).abs() <= tolerance,
                    (None, None) => true,
                    _ => false,
                };
                assert!(close, "at {time}, aspect {aspect}: {got:?}, expected {expected:?}");
            }
        }
    }

    /// The expectations of C++ `testTsSplineEval`, at each value type.
    #[test]
    fn cpp_spline_eval() {
        let all = |v: [f64; 6]| v.map(Some);
        let non_curved: [Expected; 7] = [
            (0.0, all([5.0, 10.0, 0.0, 0.0, 5.0, 10.0])),
            (2.0, all([10.0, 10.0, 0.0, 0.0, 10.0, 10.0])),
            (4.0, [Some(10.0), None, Some(0.0), None, Some(10.0), None]),
            (6.0, [None; 6]),
            (8.0, [None, Some(8.0), None, Some(-2.0), None, Some(8.0)]),
            (10.0, all([4.0, 4.0, -2.0, -2.0, 8.0, 8.0])),
            (12.0, all([0.0, 4.0, -2.0, 1.0, 8.0, 4.0])),
        ];
        let bezier: [Expected; 4] = [
            (
                13.0,
                all([
                    5.195309037843946,
                    5.195309037843946,
                    1.4154939577019203,
                    1.4154939577019203,
                    4.0,
                    4.0,
                ]),
            ),
            (14.0, all([6.75, 6.75, 1.5, 1.5, 4.0, 4.0])),
            (
                15.0,
                all([
                    7.771738865743875,
                    7.771738865743875,
                    0.5358790778895212,
                    0.5358790778895212,
                    4.0,
                    4.0,
                ]),
            ),
            (16.0, all([8.0, 10.0, 0.0, 0.0, 4.0, 10.0])),
        ];
        let hermite: [Expected; 4] = [
            (13.0, all([5.1875, 5.1875, 1.3125, 1.3125, 4.0, 4.0])),
            (14.0, all([6.5, 6.5, 1.25, 1.25, 4.0, 4.0])),
            (15.0, all([7.5625, 7.5625, 0.8125, 0.8125, 4.0, 4.0])),
            (16.0, all([8.0, 10.0, 0.0, 0.0, 4.0, 10.0])),
        ];

        for value_type in [ValueType::Double, ValueType::Float, ValueType::Half] {
            let mut spline = spline(value_type);
            check(&spline, &non_curved, 1e-12);
            check(&spline, &bezier, 1e-12);
            spline.set_curve_type(CurveType::Hermite);
            check(&spline, &non_curved, 1e-12);
            check(&spline, &hermite, 1e-12);
        }
    }

    /// An empty spline has no value, and a lone knot's value everywhere.
    #[test]
    fn empty_and_single() {
        let mut spline = Spline::new(ValueType::Double);
        assert_eq!(spline.eval(0.0), None);
        spline.set_knot(Knot::new(1.0, 7.0)).expect("a valid knot");
        for time in [-5.0, 1.0, 9.0] {
            assert_eq!(spline.eval(time), Some(7.0));
            assert_eq!(spline.eval_derivative(time), Some(0.0));
        }
        // A straight Bezier whose time cubic is all but a quadratic reads as
        // the line it is.
        let mut line = Spline::new(ValueType::Double);
        let curve = |time: f64, pre_width: f64, post_width: f64| Knot {
            pre_tangent: Tangent::new(pre_width, 1.0),
            post_tangent: Tangent::new(post_width, 1.0),
            next_interp: InterpMode::Curve,
            ..Knot::new(time, time)
        };
        line.set_knots([curve(0.0, 0.0, 0.666_666_666_6), curve(1.0, 0.0, 0.0)])
            .expect("valid knots");
        for time in [0.1, 0.25, 0.5, 0.75, 0.9] {
            let value = line.eval(time).expect("a value on the segment");
            assert!((value - time).abs() < 1e-9, "{value} at {time}");
        }

        // A straight Bezier that stands still at its middle keeps its slope
        // there.
        let mut still = Spline::new(ValueType::Double);
        still
            .set_knots([curve(0.0, 1.0, 1.0), curve(1.0, 1.0, 1.0)])
            .expect("valid knots");
        for time in [0.49, 0.5, 0.51] {
            let slope = still.eval_derivative(time).expect("a slope on the segment");
            assert!((slope - 1.0).abs() < 1e-6, "{slope} at {time}");
        }

        // A segment far from zero reads as it does at zero.
        let mut far = Spline::new(ValueType::Double);
        let unit = |time: f64, value: f64| Knot {
            pre_tangent: Tangent::new(1.0, 1.0),
            post_tangent: Tangent::new(1.0, 1.0),
            next_interp: InterpMode::Curve,
            ..Knot::new(time, value)
        };
        far.set_knots([unit(1e16, 0.0), unit(1e16 + 4.0, 4.0)])
            .expect("valid knots");
        let value = far.eval(1e16 + 2.0).expect("a value on the segment");
        let slope = far.eval_derivative(1e16 + 2.0).expect("a slope on the segment");
        assert!(
            (value - 2.0).abs() < 1e-9 && (slope - 1.0).abs() < 1e-9,
            "{value}, {slope}"
        );

        // A lone knot has nothing to loop over.
        spline.set_post_extrapolation(Extrapolation::LoopRepeat);
        assert_eq!(spline.eval(9.0), Some(7.0));
        // A held value holds at every time there is.
        assert_eq!(spline.eval(f64::NEG_INFINITY), Some(7.0));
        assert_eq!(spline.eval(f64::MIN), Some(7.0));
    }

    /// The three looping extrapolations: a repeat continues from where the
    /// knots ended, a reset starts over, and an oscillation runs back.
    #[test]
    fn extrapolating_loops() {
        let linear = |time: f64, value: f64| Knot {
            next_interp: InterpMode::Linear,
            ..Knot::new(time, value)
        };
        let mut spline = Spline::new(ValueType::Double);
        spline
            .set_knots([linear(0.0, 0.0), linear(4.0, 8.0)])
            .expect("valid knots");

        spline.set_post_extrapolation(Extrapolation::LoopRepeat);
        spline.set_pre_extrapolation(Extrapolation::LoopRepeat);
        assert_eq!(spline.eval(5.0), Some(10.0));
        assert_eq!(spline.eval(-1.0), Some(-2.0));
        assert_eq!(spline.eval_derivative(5.0), Some(2.0));

        spline.set_post_extrapolation(Extrapolation::LoopReset);
        assert_eq!(spline.eval(5.0), Some(2.0));
        // Where two copies join, each side reads its own copy.
        assert_eq!(spline.eval(8.0), Some(0.0));
        assert_eq!(spline.eval_pre_value(8.0), Some(8.0));

        // A time more iterations away than an integer counts still lands in
        // a copy of the knots.
        for time in [1e300, f64::MAX] {
            let value = spline.eval(time).expect("a value in some copy");
            assert!((0.0..=8.0).contains(&value), "{value} at {time}");
        }
        // Before the knots each copy starts lower than the last.
        for time in [-1e300, f64::MIN] {
            assert!(spline.eval(time).is_some_and(|value| value < 0.0), "at {time}");
        }

        // A time a hair before the knots is still in the copy before them,
        // short of that copy's last knot.
        spline.set_pre_extrapolation(Extrapolation::LoopReset);
        assert_eq!(spline.eval(-1e-16), Some(8.0));
        let mut steps = Spline::new(ValueType::Double);
        steps
            .set_knots([Knot::new(0.0, 2.0), Knot::new(1.0, 3.0)])
            .expect("valid knots");
        steps.set_pre_extrapolation(Extrapolation::LoopReset);
        assert_eq!(steps.eval(-1e-16), Some(2.0));
        steps.set_post_extrapolation(Extrapolation::ValueBlock);
        assert_eq!(steps.eval(-1e-16), Some(2.0));
        spline.set_pre_extrapolation(Extrapolation::LoopRepeat);

        spline.set_post_extrapolation(Extrapolation::LoopOscillate);
        assert_eq!(spline.eval(5.0), Some(6.0));
        // The phase holds at a time too large to count iterations to. The
        // knots span four, and an oscillation repeats every eight.
        let far = 2.0_f64.powi(54);
        assert_eq!(spline.eval(far), spline.eval(far % 8.0));
        assert_eq!(spline.eval(far + 4.0), spline.eval((far + 4.0) % 8.0));
        assert_eq!(spline.eval_derivative(5.0), Some(-2.0));
        assert_eq!(spline.eval(9.0), Some(2.0));
    }

    /// A prototype of `(0, 2)` and `(1, 3)` over `[0, 3)`, echoed once after
    /// it and five higher each time.
    fn looped() -> Spline {
        let linear = |time: f64, value: f64| Knot {
            next_interp: InterpMode::Linear,
            ..Knot::new(time, value)
        };
        let mut spline = Spline::new(ValueType::Double);
        spline.set_loop_params(LoopParams {
            proto_start: 0.0,
            proto_end: 3.0,
            num_pre_loops: 0,
            num_post_loops: 1,
            value_offset: 5.0,
        });
        spline
            .set_knots([linear(0.0, 2.0), linear(1.0, 3.0)])
            .expect("valid knots");
        spline
    }

    /// The segment that closes the prototype ends at the echo of its first
    /// knot, value offset included, for a value and for a slope.
    #[test]
    fn closing_segment() {
        let spline = looped();
        assert_eq!(spline.eval(1.5), Some(4.0));
        assert_eq!(spline.eval(2.0), Some(5.0));
        assert_eq!(spline.eval_derivative(1.5), Some(2.0));
        // The echo repeats it, five higher.
        assert_eq!(spline.eval(4.5), Some(9.0));
        assert_eq!(spline.eval_derivative(4.5), Some(2.0));
        assert_eq!(spline.eval_held(4.5), Some(8.0));
    }

    /// The prototype's last authored knot starts the closing segment, and is
    /// not where the spline ends.
    #[test]
    fn last_proto_knot() {
        let mut spline = looped();
        spline.set_post_extrapolation(Extrapolation::ValueBlock);
        assert_eq!(spline.eval(1.0), Some(3.0));
        assert_eq!(spline.eval_derivative(1.0), Some(2.0));
        // Past the echoes the spline has no value.
        assert_eq!(spline.eval(7.0), None);

        // A knot authored after the echoes leaves the closing segment as it
        // is.
        let mut spline = looped();
        spline.set_knot(Knot::new(20.0, 0.0)).expect("a valid knot");
        assert_eq!(spline.eval_derivative(1.0), Some(2.0));
        assert_eq!(spline.eval_derivative(1.5), Some(2.0));
    }
}
