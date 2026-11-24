//! [`Spline`] and the parameters that apply to the whole of one.

use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::Range;
use std::sync::Arc;

use strum::{Display, EnumString, FromRepr, IntoStaticStr};

use crate::gf::{self, f16};
use crate::tf;
use crate::vt::{self, stream_out};

use super::eval::{self, Aspect, Location};
use super::knot::Neighbor;
use super::regression;
use super::{AntiRegression, InterpMode, Knot, TangentAlgorithm};

/// A scalar curve over time (C++ `TsSpline`): the value an attribute's
/// `spline` field holds, and what the attribute reads from at a time where no
/// time sample answers.
///
/// A spline holds its knots in time order, one to a time. Setting knots
/// recomputes the tangents an algorithm owns, and shortens Bezier tangents
/// that would make a segment regress as an [`AntiRegression`] mode says.
///
/// A clone shares the spline's data until one of the two is changed.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Spline {
    data: Arc<Data>,
}

/// What a [`Spline`] holds (C++ `Ts_SplineData`).
#[derive(Debug, Clone, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub(super) struct Data {
    pub(super) value_type: ValueType,
    pub(super) time_valued: bool,
    pub(super) curve_type: CurveType,
    pub(super) pre_extrapolation: Extrapolation,
    pub(super) post_extrapolation: Extrapolation,
    pub(super) loop_params: LoopParams,
    /// In time order, one to a time.
    pub(super) knots: Vec<Knot>,
}

impl Spline {
    /// An empty Bezier spline of `value_type`, held outside its knots.
    pub fn new(value_type: ValueType) -> Self {
        Self {
            data: Arc::new(Data {
                value_type,
                ..Data::default()
            }),
        }
    }

    /// The precision the spline's values are stored and read at (C++
    /// `TsSpline::GetValueType`).
    pub fn value_type(&self) -> ValueType {
        self.data.value_type
    }

    /// Whether the spline's values are times, which a layer offset then
    /// retimes along with its knot times (C++ `TsSpline::IsTimeValued`). The
    /// spline of a `timecode` attribute is.
    pub fn is_time_valued(&self) -> bool {
        self.data.time_valued
    }

    /// Sets whether the spline's values are times.
    pub fn set_time_valued(&mut self, time_valued: bool) {
        self.data_mut().time_valued = time_valued;
    }

    /// The kind of curve the spline's curve segments are.
    pub fn curve_type(&self) -> CurveType {
        self.data.curve_type
    }

    /// Sets the kind of curve the spline's curve segments are (C++
    /// `TsSpline::SetCurveType`). Switching to Hermite sets every tangent's
    /// width to a third of its segment.
    pub fn set_curve_type(&mut self, curve_type: CurveType) {
        if self.data.curve_type == curve_type {
            return;
        }
        let data = self.data_mut();
        data.curve_type = curve_type;
        if curve_type == CurveType::Hermite {
            data.update_tangents(0..data.knots.len());
        }
    }

    /// How the spline is extrapolated before its first knot.
    pub fn pre_extrapolation(&self) -> Extrapolation {
        self.data.pre_extrapolation
    }

    /// Sets how the spline is extrapolated before its first knot.
    pub fn set_pre_extrapolation(&mut self, extrapolation: Extrapolation) {
        self.data_mut().pre_extrapolation = extrapolation;
    }

    /// How the spline is extrapolated after its last knot.
    pub fn post_extrapolation(&self) -> Extrapolation {
        self.data.post_extrapolation
    }

    /// Sets how the spline is extrapolated after its last knot.
    pub fn set_post_extrapolation(&mut self, extrapolation: Extrapolation) {
        self.data_mut().post_extrapolation = extrapolation;
    }

    /// The span of the spline that repeats, and how often (C++
    /// `TsSpline::GetInnerLoopParams`). They take effect only where
    /// [`has_inner_loops`](Self::has_inner_loops) says so.
    pub fn loop_params(&self) -> LoopParams {
        self.data.loop_params
    }

    /// Sets the span of the spline that repeats (C++
    /// `TsSpline::SetInnerLoopParams`). A negative loop count is stored as
    /// zero.
    pub fn set_loop_params(&mut self, params: LoopParams) {
        self.data_mut().loop_params = LoopParams {
            num_pre_loops: params.num_pre_loops.max(0),
            num_post_loops: params.num_post_loops.max(0),
            ..params
        };
    }

    /// The spline's knots, in time order.
    pub fn knots(&self) -> &[Knot] {
        &self.data.knots
    }

    /// Whether any knot specifies a tangent algorithm.
    pub(crate) fn has_tangent_algorithms(&self) -> bool {
        self.knots().iter().any(|knot| {
            knot.pre_tangent.algorithm != TangentAlgorithm::None
                || knot.post_tangent.algorithm != TangentAlgorithm::None
        })
    }

    /// The knot at exactly `time`.
    pub fn knot(&self, time: f64) -> Option<&Knot> {
        self.data.index_of(time).ok().map(|index| &self.data.knots[index])
    }

    /// Replaces the spline's knots (C++ `TsSpline::SetKnots`), shortening
    /// regressive Bezier tangents as [`AntiRegression::KeepRatio`] does.
    ///
    /// Of two knots at one time the later replaces the earlier. Nothing
    /// changes where a knot is refused.
    pub fn set_knots(&mut self, knots: impl IntoIterator<Item = Knot>) -> Result<(), Error> {
        self.set_knots_with(knots, AntiRegression::default())
    }

    // TODO: a tangent an algorithm owns is shortened like any other, as C++
    // shortens it, and the algorithm gives it back its width when the spline
    // is next read from a layer. The segment then holds a different pair of
    // widths than it was evaluated with. Anti-regression would need to keep
    // an owned width and solve for the tangent facing it.
    /// Replaces the spline's knots, shortening regressive Bezier tangents as
    /// `mode` says. A text layer is read with [`AntiRegression::None`], so
    /// that reading one changes none of its tangents.
    pub fn set_knots_with(&mut self, knots: impl IntoIterator<Item = Knot>, mode: AntiRegression) -> Result<(), Error> {
        let value_type = self.data.value_type;
        let mut knots = knots
            .into_iter()
            .map(|knot| value_type.check(knot))
            .collect::<Result<Vec<_>, _>>()?;
        // The sort is stable, so the last knot of a run at one time is the
        // last one given.
        knots.sort_by(by_time);
        knots.dedup_by(|later, kept| {
            let same = later.time == kept.time;
            if same {
                mem::swap(later, kept);
            }
            same
        });

        let data = self.data_mut();
        data.knots = knots;
        data.update_tangents(0..data.knots.len());
        data.adjust_regressive(0..data.knots.len(), mode);
        Ok(())
    }

    /// Adds `knot`, replacing the knot at its time if there is one (C++
    /// `TsSpline::SetKnot`). The tangents of the knot and of the knots beside
    /// it are recomputed, and shortened where a Bezier segment would regress,
    /// as [`AntiRegression::KeepRatio`] does.
    pub fn set_knot(&mut self, knot: Knot) -> Result<(), Error> {
        let knot = self.data.value_type.check(knot)?;
        let data = self.data_mut();
        let index = match data.index_of(knot.time) {
            Ok(index) => {
                data.knots[index] = knot;
                index
            }
            Err(index) => {
                data.knots.insert(index, knot);
                index
            }
        };
        let around = index.saturating_sub(1)..(index + 2).min(data.knots.len());
        data.update_tangents(around.clone());
        data.adjust_regressive(around, AntiRegression::default());
        Ok(())
    }

    /// Replaces the custom data of the knot at exactly `time`, and returns
    /// whether there is such a knot.
    pub fn set_custom_data(&mut self, time: f64, custom_data: vt::Dictionary) -> bool {
        let Ok(index) = self.data.index_of(time) else {
            return false;
        };
        self.data_mut().knots[index].custom_data = custom_data;
        true
    }

    /// Removes the knot at exactly `time` and returns it (C++
    /// `TsSpline::RemoveKnot`). The tangents of the knots that were beside
    /// it are recomputed for the segment they share.
    pub fn remove_knot(&mut self, time: f64) -> Option<Knot> {
        let index = self.data.index_of(time).ok()?;
        let data = self.data_mut();
        let knot = data.knots.remove(index);
        data.update_tangents(index.saturating_sub(1)..(index + 1).min(data.knots.len()));
        Some(knot)
    }

    /// Removes every knot (C++ `TsSpline::ClearKnots`).
    pub fn clear_knots(&mut self) {
        self.data_mut().knots.clear();
    }

    /// Whether the spline has no knots, and so no value at any time.
    pub fn is_empty(&self) -> bool {
        self.data.knots.is_empty()
    }

    /// The spline's value at `time`, or `None` where it has none: it is
    /// empty, or `time` falls in a segment or an extrapolation region that is
    /// a value block (C++ `TsSpline::Eval`).
    ///
    /// The answer is computed in double precision;
    /// [`ValueType::value`] gives it the spline's own.
    pub fn eval(&self, time: f64) -> Option<f64> {
        eval::eval(&self.data, time, Aspect::Value, Location::AtTime)
    }

    /// The value the spline approaches as time rises to `time`, which differs
    /// from [`eval`](Self::eval) at a dual-valued knot and where a held
    /// segment ends (C++ `TsSpline::EvalPreValue`).
    pub fn eval_pre_value(&self, time: f64) -> Option<f64> {
        eval::eval(&self.data, time, Aspect::Value, Location::Pre)
    }

    /// The spline's slope at `time` (C++ `TsSpline::EvalDerivative`).
    pub fn eval_derivative(&self, time: f64) -> Option<f64> {
        eval::eval(&self.data, time, Aspect::Derivative, Location::AtTime)
    }

    /// The slope the spline approaches as time rises to `time` (C++
    /// `TsSpline::EvalPreDerivative`).
    pub fn eval_pre_derivative(&self, time: f64) -> Option<f64> {
        eval::eval(&self.data, time, Aspect::Derivative, Location::Pre)
    }

    /// The spline's value at `time` with every segment read as held (C++
    /// `TsSpline::EvalHeld`).
    pub fn eval_held(&self, time: f64) -> Option<f64> {
        eval::eval(&self.data, time, Aspect::HeldValue, Location::AtTime)
    }

    /// The value the spline approaches as time rises to `time`, with every
    /// segment read as held (C++ `TsSpline::EvalPreValueHeld`).
    pub fn eval_pre_value_held(&self, time: f64) -> Option<f64> {
        eval::eval(&self.data, time, Aspect::HeldValue, Location::Pre)
    }

    /// Whether any segment or extrapolation region of the spline is a value
    /// block (C++ `TsSpline::HasValueBlocks`).
    pub fn has_value_blocks(&self) -> bool {
        let data = &*self.data;
        !data.knots.is_empty()
            && (data.pre_extrapolation == Extrapolation::ValueBlock
                || data.post_extrapolation == Extrapolation::ValueBlock
                || data.knots.iter().any(|knot| knot.next_interp == InterpMode::ValueBlock))
    }

    /// Whether `time` falls in a segment or an extrapolation region that is a
    /// value block (C++ `TsSpline::HasValueBlockAtTime`).
    pub fn has_value_block_at(&self, time: f64) -> bool {
        let data = &*self.data;
        let knots = &data.knots;
        if knots.is_empty() {
            return false;
        }
        match data.index_of(time) {
            Ok(index) => knots[index].next_interp == InterpMode::ValueBlock,
            Err(0) => data.pre_extrapolation == Extrapolation::ValueBlock,
            Err(index) if index == knots.len() => data.post_extrapolation == Extrapolation::ValueBlock,
            Err(index) => knots[index - 1].next_interp == InterpMode::ValueBlock,
        }
    }

    /// Whether the spline's loop parameters describe a loop: a span with a
    /// length, a loop count, and a knot at its start (C++
    /// `TsSpline::HasInnerLoops`).
    pub fn has_inner_loops(&self) -> bool {
        self.data.first_proto_index().is_some()
    }

    /// Whether either extrapolation region repeats the spline (C++
    /// `TsSpline::HasExtrapolatingLoops`).
    pub fn has_extrapolating_loops(&self) -> bool {
        self.data.pre_extrapolation.is_looping() || self.data.post_extrapolation.is_looping()
    }

    /// Whether a Bezier segment of the spline regresses (C++
    /// `TsSpline::HasRegressiveTangents`).
    pub fn has_regressive_tangents(&self) -> bool {
        self.data
            .bezier_segments()
            .any(|(interval, start, end)| regression::is_regressive(AntiRegression::default(), interval, start, end))
    }

    /// Shortens the tangents of every Bezier segment that regresses, as
    /// `mode` says, and returns whether any changed (C++
    /// `TsSpline::AdjustRegressiveTangents`).
    pub fn adjust_regressive_tangents(&mut self, mode: AntiRegression) -> bool {
        // Asked first, so that a spline with nothing to shorten keeps
        // sharing its data.
        let shortens = self
            .data
            .bezier_segments()
            .any(|(interval, start, end)| regression::adjust(mode, interval, start, end) != (None, None));
        shortens && {
            let all = 0..self.data.knots.len();
            self.data_mut().adjust_regressive(all, mode)
        }
    }

    /// Retimes the spline: every time becomes `time * scale + offset` (C++
    /// `Ts_SplineOffsetAccess::ApplyOffsetAndScale`).
    ///
    /// Knot times and the loop span move, and tangent widths scale. A slope
    /// is a rise in value over a run in time, and scales inversely.
    ///
    /// The values of a time-valued spline are times, and are retimed with
    /// its knot times. Rise and run then scale together: the slopes stay as
    /// they are and the loop's value offset scales. C++ scales a time-valued
    /// spline's slopes inversely all the same and leaves its value offset,
    /// which makes the spline it retimes a different curve from the one it
    /// evaluates through the offset.
    ///
    /// A retiming that would not leave the knots ones a spline holds, at
    /// distinct times in the order they are in, is refused: a scale that is
    /// not positive, an offset that is not finite, one large enough to round
    /// two times together, and a scale that takes a slope past the spline's
    /// precision.
    pub fn retime(&mut self, offset: f64, scale: f64) -> Result<(), Error> {
        let refused = Error::Retime { offset, scale };
        if !(scale > 0.0 && scale.is_finite() && offset.is_finite()) {
            return Err(refused);
        }
        let retimed = |time: f64| time * scale + offset;

        // Every retimed part is made and checked before any is kept.
        let (value_type, time_valued) = (self.data.value_type, self.data.time_valued);
        let slope = |slope: f64| if time_valued { slope } else { slope / scale };
        let mut params = self.data.loop_params;
        if params.proto_end > params.proto_start {
            params.proto_start = retimed(params.proto_start);
            params.proto_end = retimed(params.proto_end);
            // A span rounded away would turn the loop off.
            if params.proto_end <= params.proto_start {
                return Err(refused);
            }
        }
        if time_valued {
            params.value_offset *= scale;
        }
        let knots = self.data.knots.iter().cloned().map(|mut knot| {
            knot.time = retimed(knot.time);
            for tangent in [&mut knot.pre_tangent, &mut knot.post_tangent] {
                tangent.width *= scale;
                tangent.slope = slope(tangent.slope);
            }
            if time_valued {
                knot.value = retimed(knot.value);
                knot.pre_value = knot.pre_value.map(retimed);
            }
            value_type.check(knot)
        });
        let knots = knots.collect::<Result<Vec<_>, _>>().map_err(|_| refused)?;
        if !knots.windows(2).all(|pair| pair[0].time < pair[1].time) {
            return Err(refused);
        }

        let data = self.data_mut();
        for extrapolation in [&mut data.pre_extrapolation, &mut data.post_extrapolation] {
            if let Extrapolation::Sloped(sloped) = extrapolation {
                *sloped = slope(*sloped);
            }
        }
        data.loop_params = params;
        data.knots = knots;
        Ok(())
    }

    /// The spline's data, for the binary encoding to read.
    pub(super) fn data(&self) -> &Data {
        &self.data
    }

    /// The spline's data to change, unshared from any clone first.
    fn data_mut(&mut self) -> &mut Data {
        Arc::make_mut(&mut self.data)
    }
}

/// The dump C++ streams for a `TsSpline`: its parameters, then each knot, a
/// field to a line.
impl fmt::Display for Spline {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let data = &*self.data;
        let value_type = match data.value_type {
            ValueType::Double => "double",
            ValueType::Float => "float",
            ValueType::Half => "pxr_half::half",
        };
        let double = |value: f64| {
            let mut text = String::new();
            tf::stringify_float(&mut text, value);
            text
        };
        let number = |value: f64| {
            let mut text = String::new();
            data.value_type.stringify(&mut text, value);
            text
        };
        let extrapolation = |extrapolation: Extrapolation| match extrapolation {
            Extrapolation::Sloped(slope) => format!("Sloped {}", double(slope)),
            other => format!("{other:?}"),
        };

        writeln!(f, "Spline:")?;
        writeln!(f, "  value type {value_type}")?;
        writeln!(f, "  time valued {}", u8::from(data.time_valued))?;
        writeln!(f, "  curve type {:?}", data.curve_type)?;
        writeln!(f, "  pre extrap {}", extrapolation(data.pre_extrapolation))?;
        writeln!(f, "  post extrap {}", extrapolation(data.post_extrapolation))?;
        if self.has_inner_loops() {
            let params = &data.loop_params;
            writeln!(f, "Loop:")?;
            writeln!(
                f,
                "  start {}, end {}, numPreLoops {}, numPostLoops {}, valueOffset {}",
                double(params.proto_start),
                double(params.proto_end),
                params.num_pre_loops,
                params.num_post_loops,
                double(params.value_offset),
            )?;
        }
        for knot in &data.knots {
            writeln!(f, "Knot:")?;
            writeln!(f, "  value type {value_type}")?;
            writeln!(f, "  time {}", double(knot.time))?;
            writeln!(f, "  value {}", number(knot.value))?;
            writeln!(f, "  next interp {:?}", knot.next_interp)?;
            if let Some(pre_value) = knot.pre_value {
                writeln!(f, "  preValue {}", number(pre_value))?;
            }
            for (side, tangent) in [("pre", &knot.pre_tangent), ("post", &knot.post_tangent)] {
                writeln!(f, "  {side}-tan width {}", double(tangent.width))?;
                writeln!(f, "  {side}-tan slope {}", number(tangent.slope))?;
                if tangent.algorithm != TangentAlgorithm::None {
                    writeln!(f, "  {side}-tan algorithm {:?}", tangent.algorithm)?;
                }
            }
            if !knot.custom_data.is_empty() {
                let mut text = String::new();
                stream_out::dictionary(&mut text, &knot.custom_data);
                writeln!(f, "  custom data {text}")?;
            }
        }
        Ok(())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Spline {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.data.serialize(serializer)
    }
}

impl Data {
    /// The index of the knot at exactly `time`, or else the index a knot at
    /// `time` would be inserted at.
    pub(super) fn index_of(&self, time: f64) -> Result<usize, usize> {
        let index = self.knots.partition_point(|knot| knot.time < time);
        match self.knots.get(index) {
            Some(knot) if knot.time == time => Ok(index),
            _ => Err(index),
        }
    }

    /// The index of the knot the loop's prototype span starts at, where the
    /// loop parameters describe a loop (C++ `Ts_SplineData::HasInnerLoops`).
    pub(super) fn first_proto_index(&self) -> Option<usize> {
        let params = &self.loop_params;
        if params.proto_end <= params.proto_start || (params.num_pre_loops == 0 && params.num_post_loops == 0) {
            return None;
        }
        self.index_of(params.proto_start).ok()
    }

    /// The curve segments of a Bezier spline, each as its length in time
    /// and the widths of the two tangents facing it: what decides whether it
    /// regresses.
    fn bezier_segments(&self) -> impl Iterator<Item = (f64, f64, f64)> + '_ {
        let curves = match self.curve_type {
            CurveType::Bezier => self.knots.windows(2),
            CurveType::Hermite => [].windows(2),
        };
        curves
            .filter(|pair| pair[0].next_interp == InterpMode::Curve)
            .map(|pair| {
                (
                    pair[1].time - pair[0].time,
                    pair[0].post_tangent.width,
                    pair[1].pre_tangent.width,
                )
            })
    }

    /// Recomputes the tangents of the knots at `indices`, each from the knots
    /// beside it as they then stand (C++
    /// `Ts_TypedSplineData::UpdateKnotTangentsAtIndex`).
    pub(super) fn update_tangents(&mut self, indices: impl IntoIterator<Item = usize>) {
        for index in indices {
            let neighbor = |at: Option<usize>| at.and_then(|at| self.knots.get(at)).map(Neighbor::from);
            let prev = neighbor(index.checked_sub(1));
            let next = neighbor(Some(index + 1));
            self.knots[index].update_tangents(prev, next, self.curve_type, self.value_type);
        }
    }

    /// Shortens the tangents of the Bezier segments between the knots at
    /// `indices` that `mode` finds too long, and returns whether any changed.
    pub(super) fn adjust_regressive(&mut self, indices: Range<usize>, mode: AntiRegression) -> bool {
        if self.curve_type != CurveType::Bezier {
            return false;
        }
        let mut changed = false;
        for start in indices.start..indices.end.saturating_sub(1) {
            let [first, second] = &mut self.knots[start..start + 2] else {
                break;
            };
            if first.next_interp != InterpMode::Curve {
                continue;
            }
            let (start_width, end_width) = regression::adjust(
                mode,
                second.time - first.time,
                first.post_tangent.width,
                second.pre_tangent.width,
            );
            if let Some(width) = start_width {
                first.post_tangent.width = width;
                changed = true;
            }
            if let Some(width) = end_width {
                second.pre_tangent.width = width;
                changed = true;
            }
        }
        changed
    }
}

/// Orders knots by time. A knot's time is finite, and the two zeros are one
/// time.
fn by_time(a: &Knot, b: &Knot) -> Ordering {
    a.time.partial_cmp(&b.time).unwrap_or(Ordering::Equal)
}

/// The precision a [`Spline`] stores and reads its values at: the value types
/// a spline supports (C++ `TS_SPLINE_SUPPORTED_VALUE_TYPES`).
///
/// A knot's times and tangent widths are doubles whatever the value type.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Display, IntoStaticStr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[strum(serialize_all = "lowercase")]
pub enum ValueType {
    /// `double`, and `timecode` on a time-valued spline.
    #[default]
    Double,
    /// `float`.
    Float,
    /// `half`.
    Half,
}

impl ValueType {
    /// The value type of a spline on an attribute holding `kind`, or `None`
    /// where such an attribute cannot hold one (C++
    /// `TsSpline::IsSupportedValueType`). A `timecode` attribute's spline
    /// stores doubles.
    pub fn of(kind: vt::ValueKind) -> Option<Self> {
        match kind {
            vt::ValueKind::Double | vt::ValueKind::TimeCode => Some(Self::Double),
            vt::ValueKind::Float => Some(Self::Float),
            vt::ValueKind::Half => Some(Self::Half),
            _ => None,
        }
    }

    /// `value` at this precision, widened back to a double.
    pub fn round(self, value: f64) -> f64 {
        match self {
            Self::Double => value,
            // Narrowing is the point: a value past the type's range becomes
            // an infinity, as a C++ cast makes it.
            #[allow(clippy::cast_possible_truncation)]
            Self::Float => f64::from(value as f32),
            Self::Half => f16::from_f64(value).to_f64(),
        }
    }

    /// `value` as the [`vt::Value`] an attribute of this type holds.
    pub fn value(self, value: f64) -> vt::Value {
        match self {
            Self::Double => vt::Value::Double(value),
            // See `round`.
            #[allow(clippy::cast_possible_truncation)]
            Self::Float => vt::Value::Float(value as f32),
            Self::Half => vt::Value::Half(f16::from_f64(value)),
        }
    }

    /// Appends `value` as C++ streams a value of the type: the shortest
    /// digits that read back as the same double or float, and a half at the
    /// precision of a stream.
    pub(crate) fn stringify(self, s: &mut String, value: f64) {
        match self {
            Self::Double => tf::stringify_float(s, value),
            // A spline's values are already at its precision.
            #[allow(clippy::cast_possible_truncation)]
            Self::Float => tf::stringify_float(s, value as f32),
            Self::Half => stream_out::half(s, &f16::from_f64(value)),
        }
    }

    /// `knot` with what a spline of this type would refuse reset to a new
    /// knot's: a negative or non-finite tangent width, and a value, pre-value
    /// or slope that is not finite at the type's precision. C++ knot setters
    /// refuse each of these and leave the member as it was, which is how a
    /// text layer that holds one reads.
    pub fn sanitize(self, mut knot: Knot) -> Knot {
        let finite = |value: f64| self.round(value).is_finite();
        knot.value = Some(knot.value).filter(|value| finite(*value)).unwrap_or_default();
        knot.pre_value = knot.pre_value.filter(|value| finite(*value));
        for tangent in [&mut knot.pre_tangent, &mut knot.post_tangent] {
            if !tangent.width.is_finite() || tangent.width < 0.0 {
                tangent.width = 0.0;
            }
            if !finite(tangent.slope) {
                tangent.slope = 0.0;
            }
        }
        knot
    }

    /// The largest finite value of the type.
    pub(super) fn max(self) -> f64 {
        match self {
            Self::Double => f64::MAX,
            Self::Float => f64::from(f32::MAX),
            Self::Half => f16::MAX.to_f64(),
        }
    }

    /// `knot` as a spline of this type stores it: checked, with its value,
    /// pre-value and slopes at the type's precision.
    fn check(self, mut knot: Knot) -> Result<Knot, Error> {
        let time = knot.time;
        if !time.is_finite() {
            return Err(Error::Time(time));
        }
        for width in [knot.pre_tangent.width, knot.post_tangent.width] {
            if !width.is_finite() || width < 0.0 {
                return Err(Error::TangentWidth { time, width });
            }
        }
        knot.value = self.round(knot.value);
        knot.pre_value = knot.pre_value.map(|value| self.round(value));
        knot.pre_tangent.slope = self.round(knot.pre_tangent.slope);
        knot.post_tangent.slope = self.round(knot.post_tangent.slope);
        let values = [
            knot.value,
            knot.pre_value(),
            knot.pre_tangent.slope,
            knot.post_tangent.slope,
        ];
        if values.iter().any(|value| !value.is_finite()) {
            return Err(Error::Value { time, value_type: self });
        }
        Ok(knot)
    }
}

/// The kind of curve a [`Spline`]'s curve segments are (C++ `TsCurveType`).
///
/// The discriminants are the ones the binary format stores.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Display, EnumString, IntoStaticStr, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[strum(serialize_all = "lowercase")]
#[repr(u8)]
pub enum CurveType {
    /// A cubic Bezier curve, whose tangents have any width.
    #[default]
    Bezier = 0,
    /// A cubic Hermite curve: a Bezier whose tangents are each a third of
    /// the segment wide.
    Hermite = 1,
}

/// How a [`Spline`] is extrapolated before its first knot or after its last
/// (C++ `TsExtrapolation`).
#[derive(Debug, Clone, Copy, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum Extrapolation {
    /// The region has no value.
    ValueBlock,
    /// The region holds the value of the knot at the spline's end.
    #[default]
    Held,
    /// A straight line continuing the slope the spline ends with.
    Linear,
    /// A straight line with this slope.
    Sloped(f64),
    /// The knots repeat, each copy offset in value so that it starts where
    /// the one before it ended.
    LoopRepeat,
    /// The knots repeat exactly, with a jump where the copies join.
    LoopReset,
    /// The knots repeat, every other copy reversed in time.
    LoopOscillate,
}

impl Extrapolation {
    /// Whether the region repeats the spline's knots (C++
    /// `TsExtrapolation::IsLooping`).
    pub fn is_looping(self) -> bool {
        matches!(self, Self::LoopRepeat | Self::LoopReset | Self::LoopOscillate)
    }
}

/// The span of a [`Spline`] that repeats, and how often (C++ `TsLoopParams`).
///
/// The prototype span runs from `proto_start` up to, but not including,
/// `proto_end`, and must have a knot at its start. Its knots are echoed
/// `num_pre_loops` times before it and `num_post_loops` times after it, each
/// echo `value_offset` higher than the one before it, and a copy of the start
/// knot ends the last. Knots authored in the echoed spans are ignored.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct LoopParams {
    /// Where the prototype span starts.
    pub proto_start: f64,
    /// Where the prototype span ends. Looping is off unless it is later than
    /// [`proto_start`](Self::proto_start).
    pub proto_end: f64,
    /// How many times the prototype is echoed before it.
    pub num_pre_loops: i32,
    /// How many times the prototype is echoed after it.
    pub num_post_loops: i32,
    /// How much higher each echo's values are than those of the one before.
    pub value_offset: f64,
}

impl LoopParams {
    /// The prototype span, `[proto_start, proto_end)` (C++
    /// `TsLoopParams::GetPrototypeInterval`).
    pub fn prototype_interval(&self) -> gf::Interval {
        gf::Interval::new(self.proto_start, self.proto_end, true, false)
    }

    /// The prototype span and its echoes together (C++
    /// `TsLoopParams::GetLoopedInterval`).
    pub fn looped_interval(&self) -> gf::Interval {
        let span = self.proto_end - self.proto_start;
        gf::Interval::closed(
            self.proto_start - f64::from(self.num_pre_loops) * span,
            self.proto_end + f64::from(self.num_post_loops) * span,
        )
    }
}

/// Why a [`Spline`] refused a change.
#[derive(Debug, Clone, Copy, PartialEq, thiserror::Error)]
pub enum Error {
    /// A knot's time is not finite.
    #[error("spline knot time {0} is not finite")]
    Time(f64),
    /// A knot's value, pre-value or tangent slope is not finite at the
    /// spline's precision.
    #[error("spline knot at time {time} holds a value that is not finite as a {value_type}")]
    Value {
        /// The knot's time.
        time: f64,
        /// The spline's value type.
        value_type: ValueType,
    },
    /// A tangent's width is negative or not finite.
    #[error("spline knot at time {time} has tangent width {width}, which is negative or not finite")]
    TangentWidth {
        /// The knot's time.
        time: f64,
        /// The refused width.
        width: f64,
    },
    /// A retiming would not leave the spline's knots at finite, distinct
    /// times in the order they are in.
    #[error("a spline cannot be retimed by offset {offset} and scale {scale}")]
    Retime {
        /// The refused offset.
        offset: f64,
        /// The refused scale.
        scale: f64,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ts::Tangent;

    fn curve(time: f64, value: f64, pre: Tangent, post: Tangent) -> Knot {
        Knot {
            pre_tangent: pre,
            post_tangent: post,
            next_interp: InterpMode::Curve,
            ..Knot::new(time, value)
        }
    }

    /// Knots are kept in time order, and the later of two at one time wins.
    #[test]
    fn knots_sorted_unique() -> Result<(), Error> {
        let mut spline = Spline::new(ValueType::Double);
        spline.set_knots([Knot::new(5.0, 1.0), Knot::new(1.0, 2.0), Knot::new(5.0, 3.0)])?;
        let knots: Vec<_> = spline.knots().iter().map(|knot| (knot.time, knot.value)).collect();
        assert_eq!(knots, [(1.0, 2.0), (5.0, 3.0)]);

        spline.set_knot(Knot::new(3.0, 7.0))?;
        spline.set_knot(Knot::new(1.0, 9.0))?;
        let knots: Vec<_> = spline.knots().iter().map(|knot| (knot.time, knot.value)).collect();
        assert_eq!(knots, [(1.0, 9.0), (3.0, 7.0), (5.0, 3.0)]);
        assert_eq!(spline.knot(3.0).map(|knot| knot.value), Some(7.0));

        // The two zeros are one time, at which the later knot wins.
        let mut zeros = Spline::new(ValueType::Double);
        zeros.set_knots([Knot::new(0.0, 1.0), Knot::new(-0.0, 2.0)])?;
        assert_eq!(zeros.knots().len(), 1);
        assert_eq!(zeros.knots()[0].value, 2.0);
        assert_eq!(spline.remove_knot(3.0).map(|knot| knot.value), Some(7.0));
        assert_eq!(spline.remove_knot(3.0), None);

        // The knots beside a removed one face a new segment.
        let tangent = Tangent::new(0.0, 1.0);
        let mut hermite = Spline::new(ValueType::Double);
        hermite.set_curve_type(CurveType::Hermite);
        hermite.set_knots([
            curve(0.0, 0.0, tangent, tangent),
            curve(3.0, 1.0, tangent, tangent),
            curve(6.0, 2.0, tangent, tangent),
        ])?;
        assert_eq!(hermite.knots()[0].post_tangent.width, 1.0);
        hermite.remove_knot(3.0);
        let [first, second] = hermite.knots() else {
            panic!("two knots")
        };
        assert_eq!((first.post_tangent.width, second.pre_tangent.width), (2.0, 2.0));
        Ok(())
    }

    /// A knot a spline cannot hold is refused, and the spline left alone.
    #[test]
    fn bad_knots_refused() {
        let mut spline = Spline::new(ValueType::Float);
        spline.set_knot(Knot::new(1.0, 1.0)).expect("a plain knot");
        assert_eq!(
            spline.set_knot(Knot::new(f64::NAN, 1.0)).map_err(|e| e.to_string()),
            Err("spline knot time NaN is not finite".to_owned())
        );
        assert!(matches!(
            spline.set_knots([Knot::new(2.0, 1e39)]),
            Err(Error::Value { time: 2.0, .. })
        ));
        let negative = Knot {
            pre_tangent: Tangent::new(-1.0, 0.0),
            ..Knot::new(2.0, 1.0)
        };
        assert!(matches!(
            spline.set_knot(negative),
            Err(Error::TangentWidth { width: -1.0, .. })
        ));
        assert_eq!(spline.knots().len(), 1);
    }

    /// Values are stored at the spline's precision.
    #[test]
    fn values_rounded() -> Result<(), Error> {
        let mut spline = Spline::new(ValueType::Float);
        spline.set_knot(Knot::new(0.0, 0.1))?;
        assert_eq!(spline.knots()[0].value, f64::from(0.1_f32));
        assert_eq!(ValueType::Half.value(0.1), vt::Value::Half(f16::from_f64(0.1)));
        Ok(())
    }

    /// A Hermite spline keeps each tangent a third of its segment wide, and
    /// a tangent facing no segment as it was given.
    #[test]
    fn hermite_widths() -> Result<(), Error> {
        let mut spline = Spline::new(ValueType::Double);
        let tangent = Tangent::new(7.0, 1.0);
        spline.set_knots_with(
            [curve(0.0, 0.0, tangent, tangent), curve(6.0, 1.0, tangent, tangent)],
            AntiRegression::None,
        )?;
        assert_eq!(spline.knots()[0].post_tangent.width, 7.0);

        spline.set_curve_type(CurveType::Hermite);
        let [first, second] = spline.knots() else {
            panic!("two knots")
        };
        assert_eq!((first.pre_tangent.width, first.post_tangent.width), (7.0, 2.0));
        assert_eq!((second.pre_tangent.width, second.post_tangent.width), (2.0, 7.0));
        Ok(())
    }

    /// Auto Ease blends the slopes to the neighbors, and is flat at an end
    /// knot and where the knot is a local extreme.
    #[test]
    fn auto_ease() -> Result<(), Error> {
        let auto = Tangent {
            algorithm: TangentAlgorithm::AutoEase,
            ..Tangent::default()
        };
        let mut spline = Spline::new(ValueType::Double);
        spline.set_knots([
            curve(0.0, 0.0, auto, auto),
            curve(3.0, 3.0, auto, auto),
            curve(6.0, 9.0, auto, auto),
            curve(9.0, 0.0, auto, auto),
        ])?;
        let knots = spline.knots();
        // An end knot: flat, and only the side that faces a segment.
        assert_eq!(knots[0].pre_tangent, auto);
        assert_eq!(knots[0].post_tangent, Tangent { width: 1.0, ..auto });
        // Midway between slopes 1 and 2.
        assert_eq!(
            knots[1].post_tangent,
            Tangent {
                width: 1.0,
                slope: 1.5,
                ..auto
            }
        );
        assert_eq!(knots[1].pre_tangent, knots[1].post_tangent);
        // A local extreme.
        assert_eq!(knots[2].pre_tangent.slope, 0.0);
        Ok(())
    }

    /// Setting knots shortens regressive tangents unless told not to, and a
    /// spline left regressive says so.
    #[test]
    fn regression_adjusted() -> Result<(), Error> {
        let long = Tangent::new(2.0, 0.0);
        let knots = [curve(0.0, 0.0, long, long), curve(1.0, 1.0, long, long)];

        let mut read = Spline::new(ValueType::Double);
        read.set_knots_with(knots.clone(), AntiRegression::None)?;
        assert_eq!(read.knots()[0].post_tangent.width, 2.0);
        assert!(read.has_regressive_tangents());

        let mut authored = Spline::new(ValueType::Double);
        authored.set_knots(knots)?;
        assert!(authored.knots()[0].post_tangent.width < 1.0);
        assert!(!authored.has_regressive_tangents());

        let shared = read.clone();
        assert!(read.adjust_regressive_tangents(AntiRegression::KeepRatio));
        assert_eq!(read, authored);
        assert!(shared.has_regressive_tangents());
        assert!(!read.adjust_regressive_tangents(AntiRegression::KeepRatio));
        Ok(())
    }

    /// Retiming moves times, scales widths, and scales slopes inversely; a
    /// time-valued spline's values move with its times.
    #[test]
    fn offset_and_scale() -> Result<(), Error> {
        let mut spline = Spline::new(ValueType::Double);
        spline.set_post_extrapolation(Extrapolation::Sloped(4.0));
        spline.set_loop_params(LoopParams {
            proto_start: 1.0,
            proto_end: 2.0,
            num_pre_loops: -3,
            num_post_loops: 1,
            value_offset: 5.0,
        });
        spline.set_knots([curve(1.0, 10.0, Tangent::new(1.0, 2.0), Tangent::new(1.0, 2.0))])?;
        assert_eq!(spline.loop_params().num_pre_loops, 0);
        assert!(spline.has_inner_loops());

        let mut timed = spline.clone();
        timed.set_time_valued(true);
        let timed_source = timed.clone();
        spline.retime(10.0, 2.0)?;
        timed.retime(10.0, 2.0)?;

        let knot = &spline.knots()[0];
        assert_eq!((knot.time, knot.value), (12.0, 10.0));
        assert_eq!(knot.post_tangent, Tangent::new(2.0, 1.0));
        assert_eq!(spline.post_extrapolation(), Extrapolation::Sloped(2.0));
        assert_eq!(
            (spline.loop_params().proto_start, spline.loop_params().proto_end),
            (12.0, 14.0)
        );
        // A time-valued spline's values move with its times, so its slopes
        // stay and its loop offset scales.
        let knot = &timed.knots()[0];
        assert_eq!((knot.time, knot.value), (12.0, 30.0));
        assert_eq!(knot.post_tangent, Tangent::new(2.0, 2.0));
        assert_eq!(timed.post_extrapolation(), Extrapolation::Sloped(4.0));
        assert_eq!(timed.loop_params().value_offset, 10.0);
        // It is then the curve an evaluation through the offset reads.
        for time in [-3.0, 1.0, 1.25, 1.5, 2.0, 2.75, 3.5, 9.0] {
            let through = timed_source.eval(time).map(|value| value * 2.0 + 10.0);
            assert_eq!(timed.eval(time * 2.0 + 10.0), through, "at {time}");
        }

        for (offset, scale) in [
            (0.0, 0.0),
            (0.0, -1.0),
            (0.0, f64::NAN),
            (f64::INFINITY, 1.0),
            (0.0, f64::INFINITY),
        ] {
            let before = spline.clone();
            assert!(matches!(spline.retime(offset, scale), Err(Error::Retime { .. })));
            assert_eq!(spline, before);
        }
        // An offset that rounds two knot times together.
        let mut close = Spline::new(ValueType::Double);
        close.set_knots([Knot::new(0.0, 0.0), Knot::new(1.0, 1.0)])?;
        assert!(close.retime(1e17, 1.0).is_err());
        // An offset that rounds a loop's span away.
        let mut looped = Spline::new(ValueType::Double);
        looped.set_loop_params(LoopParams {
            proto_start: 0.0,
            proto_end: 1.0,
            num_pre_loops: 0,
            num_post_loops: 2,
            value_offset: 5.0,
        });
        looped.set_knots([Knot::new(0.0, 0.0)])?;
        assert!(looped.retime(1e16, 1.0).is_err());
        assert_eq!(looped.eval(2.0), Some(10.0));
        // A scale that takes a slope past what a half holds.
        let mut steep = Spline::new(ValueType::Half);
        steep.set_knots([curve(0.0, 0.0, Tangent::default(), Tangent::new(0.0, 40_000.0))])?;
        let before = steep.clone();
        assert!(steep.retime(0.0, 0.5).is_err());
        assert_eq!(steep, before);
        Ok(())
    }

    /// Value blocks are found in segments and in extrapolation regions.
    #[test]
    fn value_blocks() -> Result<(), Error> {
        let mut spline = Spline::new(ValueType::Double);
        assert!(!spline.has_value_blocks());
        let blocked = Knot {
            next_interp: InterpMode::ValueBlock,
            ..Knot::new(1.0, 0.0)
        };
        spline.set_knots([blocked, Knot::new(2.0, 0.0)])?;
        spline.set_pre_extrapolation(Extrapolation::ValueBlock);
        assert!(spline.has_value_blocks());
        assert!(spline.has_value_block_at(0.0));
        assert!(spline.has_value_block_at(1.0));
        assert!(spline.has_value_block_at(1.5));
        assert!(!spline.has_value_block_at(2.0));
        assert!(!spline.has_value_block_at(3.0));

        assert!(!spline.has_extrapolating_loops());
        spline.set_post_extrapolation(Extrapolation::LoopReset);
        assert!(spline.has_extrapolating_loops());
        spline.clear_knots();
        assert!(spline.is_empty() && !spline.has_value_blocks());
        Ok(())
    }
}
