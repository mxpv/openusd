//! Time-query parameter — a numeric time code passed to attribute value
//! resolution, mirroring C++ `UsdTimeCode`.
//!
//! This is the *query* type: the time at which an [`Attribute`] value is read
//! or authored. It is distinct from [`sdf::TimeCode`], the authored *value*
//! held by a `timecode`-typed attribute (C++ `SdfTimeCode`).
//!
//! Absence of a time — "resolve the attribute default rather than a time
//! sample" — is expressed at the call site as the `None` arm of the
//! `impl Into<Option<TimeCode>>` parameter on [`Attribute::get`] /
//! [`Attribute::set`], so a `TimeCode` itself is always a concrete numeric
//! time and needs no sentinel for the default.
//!
//! [`Attribute`]: super::Attribute
//! [`Attribute::get`]: super::Attribute::get
//! [`Attribute::set`]: super::Attribute::set

use crate::sdf;

/// A numeric time code identifying when an attribute value is resolved.
/// Mirrors C++ `UsdTimeCode`.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, derive_more::From)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct TimeCode(f64);

impl TimeCode {
    /// The earliest possible time code (C++ `UsdTimeCode::EarliestTime`). A
    /// query at this time resolves the earliest authored time sample.
    pub const EARLIEST: TimeCode = TimeCode(f64::MIN);

    /// Construct a time code at `t`.
    pub const fn new(t: f64) -> Self {
        Self(t)
    }

    /// The wrapped time value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Whether this is [`TimeCode::EARLIEST`].
    pub fn is_earliest_time(self) -> bool {
        self.0 == f64::MIN
    }

    /// A time delta safe to add to or subtract from any numeric time in
    /// `[-max_value, max_value]` so the result stays distinct from the
    /// original under `f64` rounding, with `max_compression` headroom against
    /// the worst case. Mirrors C++ `UsdTimeCode::SafeStep`.
    ///
    /// Returns an `f64` because it is added to a time before a code is built:
    /// authoring two samples bracketing a discontinuity is two writes, e.g.
    /// `set_at(v0, t)` then `set_at(v1, TimeCode::new(t + TimeCode::safe_step_default()))`
    /// for a hold-then-jump on `timeSamples`, or two non-overlapping
    /// `(stageTime, value)` entries in `ClipsAPI::set_clip_active` /
    /// `set_clip_times`.
    pub const fn safe_step(max_value: f64, max_compression: f64) -> f64 {
        f64::EPSILON * max_value * max_compression
    }

    /// [`safe_step`](Self::safe_step) with C++'s defaults: `max_value = 1e6`,
    /// `max_compression = 10.0`.
    pub const fn safe_step_default() -> f64 {
        Self::safe_step(1e6, 10.0)
    }
}

impl From<f32> for TimeCode {
    fn from(t: f32) -> Self {
        Self::new(t as f64)
    }
}

impl From<i32> for TimeCode {
    fn from(t: i32) -> Self {
        Self::new(t as f64)
    }
}

impl From<u32> for TimeCode {
    fn from(t: u32) -> Self {
        Self::new(t as f64)
    }
}

impl From<sdf::TimeCode> for TimeCode {
    fn from(t: sdf::TimeCode) -> Self {
        Self::new(t.value())
    }
}

impl From<TimeCode> for f64 {
    fn from(t: TimeCode) -> Self {
        t.value()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn earliest_is_min() {
        assert!(TimeCode::EARLIEST.is_earliest_time());
        assert!(!TimeCode::new(0.0).is_earliest_time());
    }

    #[test]
    fn numeric_round_trip() {
        assert_eq!(TimeCode::new(12.5).value(), 12.5);
    }

    /// `safe_step` yields a positive delta that perturbs a time within the
    /// stated range, and the default matches the explicit C++ defaults.
    #[test]
    fn safe_step_perturbs() {
        let s = TimeCode::safe_step_default();
        assert!(s > 0.0);
        let t = 1.0e6;
        assert_ne!(t + s, t);
        assert_eq!(TimeCode::safe_step(1e6, 10.0), s);
    }

    #[test]
    fn from_conversions() {
        assert_eq!(TimeCode::from(5.0_f64).value(), 5.0);
        assert_eq!(TimeCode::from(5.0_f32).value(), 5.0);
        assert_eq!(TimeCode::from(5_i32).value(), 5.0);
        assert_eq!(TimeCode::from(5_u32).value(), 5.0);
        assert_eq!(TimeCode::from(sdf::TimeCode(7.0)).value(), 7.0);
        assert_eq!(f64::from(TimeCode::new(9.0)), 9.0);
    }

    /// A bare `TimeCode` coerces into the `impl Into<Option<TimeCode>>`
    /// parameter via the std blanket `From<T> for Option<T>`, alongside
    /// `None` and `Some(..)`.
    #[test]
    fn into_option_coerces() {
        fn take(t: impl Into<Option<TimeCode>>) -> Option<TimeCode> {
            t.into()
        }
        assert_eq!(take(None), None);
        assert_eq!(take(TimeCode::new(3.0)), Some(TimeCode::new(3.0)));
        assert_eq!(take(Some(TimeCode::new(3.0))), Some(TimeCode::new(3.0)));
    }
}
