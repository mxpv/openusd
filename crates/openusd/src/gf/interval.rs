//! `GfInterval` — a span of the real line with each end open or closed.

use std::ops::{Bound, RangeBounds};

/// A span of the real line, each end open or closed (C++ `GfInterval`): the
/// bounds a time-sample query is asked over.
///
/// A closed end contains its bound and an open one does not, so `[0, 5)` holds
/// a sample at 0 and not one at 5. Anything with [`RangeBounds<f64>`] converts
/// into one: `a..=b` is closed at both ends, `a..b` is open at the top, `a..`
/// and `..=b` run to an infinity, `..` is the whole line, and a pair of
/// [`Bound`]s spells any other combination.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Interval {
    min: f64,
    max: f64,
    min_closed: bool,
    max_closed: bool,
}

impl Interval {
    /// An interval with each end as closed as asked
    /// (C++ `GfInterval(min, max, minClosed, maxClosed)`).
    pub const fn new(min: f64, max: f64, min_closed: bool, max_closed: bool) -> Self {
        Interval {
            min,
            max,
            min_closed,
            max_closed,
        }
    }

    /// The closed interval `[min, max]`.
    pub const fn closed(min: f64, max: f64) -> Self {
        Self::new(min, max, true, true)
    }

    /// The open interval `(min, max)`.
    pub const fn open(min: f64, max: f64) -> Self {
        Self::new(min, max, false, false)
    }

    /// The lower bound, whether or not the interval contains it.
    pub const fn min(&self) -> f64 {
        self.min
    }

    /// The upper bound, whether or not the interval contains it.
    pub const fn max(&self) -> f64 {
        self.max
    }

    /// Whether the lower bound lies in the interval.
    pub const fn is_min_closed(&self) -> bool {
        self.min_closed
    }

    /// Whether the upper bound lies in the interval.
    pub const fn is_max_closed(&self) -> bool {
        self.max_closed
    }

    /// Whether nothing lies in the interval: its bounds cross, meet at an end
    /// that is open, or are not numbers at all. C++ `GfInterval::IsEmpty`
    /// reports an interval with a NaN bound as nonempty.
    pub const fn is_empty(&self) -> bool {
        !(self.min < self.max || (self.min == self.max && self.min_closed && self.max_closed))
    }

    /// Whether `value` lies in the interval. An empty interval holds nothing.
    pub const fn contains(&self, value: f64) -> bool {
        (value > self.min || (value == self.min && self.min_closed))
            && (value < self.max || (value == self.max && self.max_closed))
    }
}

/// An included bound is a closed end, an excluded one an open end, and an
/// unbounded one runs open to the infinity on its side.
impl<R: RangeBounds<f64>> From<R> for Interval {
    fn from(range: R) -> Self {
        let end = |bound: Bound<&f64>, unbounded: f64| match bound {
            Bound::Included(&value) => (value, true),
            Bound::Excluded(&value) => (value, false),
            Bound::Unbounded => (unbounded, false),
        };
        let (min, min_closed) = end(range.start_bound(), f64::NEG_INFINITY);
        let (max, max_closed) = end(range.end_bound(), f64::INFINITY);
        Self::new(min, max, min_closed, max_closed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ends_open_or_closed() {
        let closed = Interval::closed(0.0, 5.0);
        assert!(closed.contains(0.0) && closed.contains(5.0) && closed.contains(2.5));
        assert!(!closed.contains(-0.1) && !closed.contains(5.1));

        let open = Interval::open(0.0, 5.0);
        assert!(!open.contains(0.0) && !open.contains(5.0) && open.contains(2.5));

        let half = Interval::new(0.0, 5.0, true, false);
        assert!(half.contains(0.0) && !half.contains(5.0));
        assert!(!closed.contains(f64::NAN));
    }

    #[test]
    fn emptiness() {
        assert!(Interval::closed(5.0, 1.0).is_empty());
        assert!(Interval::open(2.0, 2.0).is_empty());
        assert!(Interval::new(2.0, 2.0, true, false).is_empty());
        assert!(Interval::closed(1.0, f64::NAN).is_empty());
        assert!(Interval::closed(f64::NAN, 1.0).is_empty());
        assert!(!Interval::closed(2.0, 2.0).is_empty());
        assert!(!Interval::open(f64::NEG_INFINITY, f64::INFINITY).is_empty());
    }

    #[test]
    fn from_ranges() {
        assert_eq!(Interval::from(0.0..5.0), Interval::new(0.0, 5.0, true, false));
        assert_eq!(Interval::from(0.0..=5.0), Interval::closed(0.0, 5.0));
        assert_eq!(Interval::from(2.0..), Interval::new(2.0, f64::INFINITY, true, false));
        assert_eq!(Interval::from(..3.0), Interval::open(f64::NEG_INFINITY, 3.0));
        assert_eq!(
            Interval::from(..=3.0),
            Interval::new(f64::NEG_INFINITY, 3.0, false, true)
        );
        assert_eq!(Interval::from(..), Interval::open(f64::NEG_INFINITY, f64::INFINITY));
        assert_eq!(
            Interval::from((Bound::Excluded(1.0), Bound::Included(5.0))),
            Interval::new(1.0, 5.0, false, true)
        );
        assert!(!Interval::from(..).contains(f64::INFINITY));
    }
}
