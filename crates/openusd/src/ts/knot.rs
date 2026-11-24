//! One knot of a [`Spline`](super::Spline) and the tangents on its two sides.

use strum::{Display, EnumString, FromRepr, IntoStaticStr};

use crate::vt;

use super::{CurveType, ValueType};

/// One knot of a [`Spline`](super::Spline): a time, the value there, and the
/// shape of the curve on either side (C++ `TsKnot`).
///
/// A knot is plain data. A spline checks it when it takes it
/// ([`Spline::set_knot`](super::Spline::set_knot)) and stores its value,
/// pre-value and tangent slopes at the precision of its
/// [`ValueType`].
#[derive(Debug, Clone, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Knot {
    /// The knot's time, which must be finite.
    pub time: f64,
    /// The value at the knot, and the one the segment after it starts from.
    pub value: f64,
    /// The value the segment before the knot ends at, where it differs from
    /// [`value`](Self::value). A knot that has one is dual-valued: the curve
    /// jumps at it (C++ `TsKnot::IsDualValued`).
    pub pre_value: Option<f64>,
    /// The tangent facing the segment before the knot.
    pub pre_tangent: Tangent,
    /// The tangent facing the segment after the knot.
    pub post_tangent: Tangent,
    /// How the segment from this knot to the next is interpolated.
    pub next_interp: InterpMode,
    /// Data an application keeps with the knot (C++ `TsKnot::GetCustomData`).
    pub custom_data: vt::Dictionary,
}

impl Knot {
    /// A knot at `time` holding `value`, with a held segment after it and no
    /// tangents.
    pub fn new(time: f64, value: f64) -> Self {
        Self {
            time,
            value,
            ..Self::default()
        }
    }

    /// The value on the knot's pre-side: its pre-value, or its value where it
    /// has none.
    pub fn pre_value(&self) -> f64 {
        self.pre_value.unwrap_or(self.value)
    }

    /// Whether the curve jumps at the knot (C++ `TsKnot::IsDualValued`).
    pub fn is_dual_valued(&self) -> bool {
        self.pre_value.is_some()
    }

    /// Recomputes the knot's tangents from the knots beside it (C++
    /// `Ts_TypedKnotData::UpdateTangents`): a tangent with an algorithm gets
    /// the slope and width the algorithm gives, and a Hermite tangent a third
    /// of its segment for a width.
    pub(super) fn update_tangents(
        &mut self,
        prev: Option<Neighbor>,
        next: Option<Neighbor>,
        curve_type: CurveType,
        value_type: ValueType,
    ) {
        for pre in [true, false] {
            let (tangent, neighbor) = match pre {
                true => (self.pre_tangent, prev),
                false => (self.post_tangent, next),
            };
            let updated = match tangent.algorithm {
                // C++ has no custom algorithm yet, and treats one as none.
                TangentAlgorithm::None | TangentAlgorithm::Custom => match (curve_type, neighbor) {
                    (CurveType::Hermite, Some(neighbor)) => Tangent {
                        width: (neighbor.time - self.time).abs() / 3.0,
                        ..tangent
                    },
                    _ => tangent,
                },
                TangentAlgorithm::AutoEase => match neighbor {
                    Some(neighbor) => self.auto_ease(tangent, neighbor, prev, next, value_type),
                    // A tangent facing an extrapolation region has nothing to
                    // blend, and no effect on the curve.
                    None => tangent,
                },
            };
            match pre {
                true => self.pre_tangent = updated,
                false => self.post_tangent = updated,
            }
        }
    }

    /// The tangent facing `neighbor` as the Maya and animX "Auto Ease"
    /// algorithm computes it (C++ `_UpdateTangentAutoEase`): a third of the
    /// segment wide, with a slope blended from the slopes of the straight
    /// lines to the knots on either side, and flat at a discontinuity.
    fn auto_ease(
        &self,
        tangent: Tangent,
        neighbor: Neighbor,
        prev: Option<Neighbor>,
        next: Option<Neighbor>,
        value_type: ValueType,
    ) -> Tangent {
        let mut width = (neighbor.time - self.time).abs() / 3.0;
        // An end knot, a dual-valued knot and a value block beside the knot
        // are all discontinuities.
        let (prev, next) = match (prev, next) {
            (Some(prev), Some(next))
                if !self.is_dual_valued()
                    && self.next_interp != InterpMode::ValueBlock
                    && prev.next_interp != InterpMode::ValueBlock =>
            {
                (prev, next)
            }
            _ => {
                return Tangent {
                    width,
                    slope: 0.0,
                    ..tangent
                };
            }
        };

        let prev_slope = (self.value - prev.value) / (self.time - prev.time);
        let next_slope = (next.pre_value - self.value) / (next.time - self.time);

        // The slope is blended only where the knot's value lies between its
        // neighbors' values.
        let mut slope = 0.0;
        if prev_slope * next_slope > 0.0 {
            let u = (self.time - prev.time) / (next.time - prev.time) - 0.5;
            // The cubic that gives the nearer neighbor the stronger influence.
            let blend = 0.5 + u * (0.5 + 2.0 * u * u);
            slope = (1.0 - blend) * prev_slope + blend * next_slope;
            slope = match next_slope > 0.0 {
                true => slope.min(3.0 * next_slope).min(3.0 * prev_slope),
                false => slope.max(3.0 * next_slope).max(3.0 * prev_slope),
            };
        }

        // A slope the value type cannot hold is clamped to the largest it
        // can, and the tangent widened so that its end point stays put.
        let mut typed = value_type.round(slope);
        if !typed.is_finite() {
            let height = slope * width;
            typed = value_type.max().copysign(slope);
            width = height / typed;
        }
        Tangent {
            width,
            slope: typed,
            ..tangent
        }
    }
}

/// What a knot's tangent update reads of the knot beside it.
#[derive(Debug, Clone, Copy)]
pub(super) struct Neighbor {
    pub(super) time: f64,
    pub(super) value: f64,
    pub(super) pre_value: f64,
    pub(super) next_interp: InterpMode,
}

impl From<&Knot> for Neighbor {
    fn from(knot: &Knot) -> Self {
        Self {
            time: knot.time,
            value: knot.value,
            pre_value: knot.pre_value(),
            next_interp: knot.next_interp,
        }
    }
}

/// One side's tangent at a [`Knot`]: how far it reaches and how steep it is.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Tangent {
    /// How far the tangent reaches in time, which must be finite and not
    /// negative. A Hermite spline keeps it at a third of the segment the
    /// tangent faces.
    pub width: f64,
    /// The tangent's slope: its rise in value over its run in time.
    pub slope: f64,
    /// The algorithm that computes the tangent, where one does.
    pub algorithm: TangentAlgorithm,
}

impl Tangent {
    /// A tangent `width` wide with slope `slope`, computed by no algorithm.
    pub fn new(width: f64, slope: f64) -> Self {
        Self {
            width,
            slope,
            algorithm: TangentAlgorithm::None,
        }
    }
}

/// How the segment from one knot to the next is interpolated (C++
/// `TsInterpMode`).
///
/// The discriminants are the ones the binary format stores.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Display, EnumString, IntoStaticStr, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[strum(serialize_all = "lowercase")]
#[repr(u8)]
pub enum InterpMode {
    /// The segment has no value.
    #[strum(serialize = "none")]
    ValueBlock = 0,
    /// The segment holds the value of the knot it starts at.
    #[default]
    Held = 1,
    /// A straight line between the two knots.
    Linear = 2,
    /// A Bezier or Hermite curve, as the spline's
    /// [`CurveType`] says.
    Curve = 3,
}

/// The algorithm that computes a [`Tangent`] (C++ `TsTangentAlgorithm`).
///
/// The discriminants are the ones the binary format stores.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash, Display, EnumString, IntoStaticStr, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[strum(serialize_all = "camelCase")]
#[repr(u8)]
pub enum TangentAlgorithm {
    /// The tangent is used as authored.
    #[default]
    None = 0,
    /// An algorithm the knot's custom data names. C++ implements none yet, so
    /// the tangent is used as authored.
    Custom = 1,
    /// The "Auto Ease" algorithm of Maya and animX: a slope blended from the
    /// slopes to the knots on either side, flat at a discontinuity.
    AutoEase = 2,
}
