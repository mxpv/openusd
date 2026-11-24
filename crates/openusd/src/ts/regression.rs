//! Anti-regression: shortening the tangents of a Bezier segment that would
//! otherwise run backwards in time (C++ `TsRegressionPreventer`, the batch
//! half).
//!
//! A Bezier segment is a curve in time as well as in value, and tangents long
//! enough make its time decrease along part of it, so that the segment has
//! several values at one time. Whether it does depends only on the two tangent
//! widths facing the segment, each as a fraction of the segment's length: the
//! pairs that do not regress lie inside an ellipse.

/// How tangents that make a Bezier segment regress are shortened (C++
/// `TsAntiRegressionMode`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum AntiRegression {
    /// Tangents are left as they are. Evaluation shortens a regressive
    /// segment's tangents as [`KeepRatio`](Self::KeepRatio) does, without
    /// changing the spline.
    None,
    /// No tangent reaches past the knot at the other end of its segment. This
    /// rules out regression and some curves that do not regress.
    Contain,
    /// Both tangents of a regressive segment are shortened, in proportion,
    /// until the curve only just stops regressing.
    #[default]
    KeepRatio,
    /// The start tangent of a regressive segment is kept and the end tangent
    /// shortened until the curve only just stops regressing, as Maya does.
    KeepStart,
}

/// The fraction of a segment by which a shortened tangent undershoots the
/// exact answer, so that the result still reads as non-regressive after
/// imprecise processing.
const WRITE_PADDING: f64 = 1e-5;

/// The fraction of a segment by which a pair of widths must clear the ellipse
/// to count as non-regressive. Smaller than [`WRITE_PADDING`], so a shortened
/// pair passes.
const READ_PADDING: f64 = 1e-6;

/// The longest tangent that stays within its segment.
const CONTAINED_MAX: f64 = 1.0;

/// The longest and shortest widths of a pair at which the curve is vertical
/// at a single point.
const VERTICAL_MAX: f64 = 4.0 / 3.0;
const VERTICAL_MIN: f64 = 1.0 / 3.0;

/// Whether a curve segment `interval` long, with tangents `start_width` and
/// `end_width` wide facing it, is regressive under `mode` (C++
/// `Ts_RegressionPreventerBatchAccess::IsSegmentRegressive`).
pub(super) fn is_regressive(mode: AntiRegression, interval: f64, start_width: f64, end_width: f64) -> bool {
    let (start, end) = (start_width / interval, end_width / interval);
    match mode {
        AntiRegression::Contain => start > CONTAINED_MAX || end > CONTAINED_MAX,
        _ => widths_regress(start, end),
    }
}

/// The widths `mode` shortens a curve segment's two tangents to, each `None`
/// where the tangent keeps its width (C++
/// `Ts_RegressionPreventerBatchAccess::ProcessSegment`).
///
/// `interval` is the segment's length in time, `start_width` the width of the
/// start knot's post-tangent and `end_width` that of the end knot's
/// pre-tangent.
pub(super) fn adjust(
    mode: AntiRegression,
    interval: f64,
    start_width: f64,
    end_width: f64,
) -> (Option<f64>, Option<f64>) {
    // C++ gives a segment with no length a unit one.
    let interval = if interval > 0.0 { interval } else { 1.0 };
    let (start, end) = (start_width / interval, end_width / interval);

    let (new_start, new_end) = match mode {
        AntiRegression::None => return (None, None),
        // Contain shortens a tangent whether or not the segment regresses,
        // and to the segment's exact length.
        AntiRegression::Contain => (start.min(CONTAINED_MAX), end.min(CONTAINED_MAX)),
        _ if !widths_regress(start, end) => return (None, None),
        AntiRegression::KeepRatio => {
            if start < READ_PADDING {
                (start, CONTAINED_MAX - WRITE_PADDING)
            } else if end < READ_PADDING {
                (CONTAINED_MAX - WRITE_PADDING, end)
            } else {
                // Where the line through the origin and the pair meets the
                // ellipse.
                let ratio = start / end;
                let adjusted = (ratio.sqrt() + ratio + 1.0) / (ratio * ratio + ratio + 1.0);
                (ratio * adjusted - WRITE_PADDING, adjusted - WRITE_PADDING)
            }
        }
        AntiRegression::KeepStart => {
            if start >= VERTICAL_MAX {
                (VERTICAL_MAX - WRITE_PADDING, VERTICAL_MIN - WRITE_PADDING)
            } else {
                (start, other_width_for_vertical(start, end) - WRITE_PADDING)
            }
        }
    };

    // The padding can exceed a tangent much shorter than the one it is paired
    // with, and a width is never negative.
    let (new_start, new_end) = (new_start.max(0.0), new_end.max(0.0));
    (
        (new_start != start).then_some(new_start * interval),
        (new_end != end).then_some(new_end * interval),
    )
}

/// Whether a pair of normalized tangent widths makes its segment regress: the
/// pair lies outside the ellipse, and not inside the unit square, where some
/// pairs outside the ellipse do not regress.
fn widths_regress(width1: f64, width2: f64) -> bool {
    if width1 <= CONTAINED_MAX && width2 <= CONTAINED_MAX {
        return false;
    }
    let w1 = width1 + READ_PADDING;
    let w2 = width2 + READ_PADDING;
    w1 * w1 + w2 * w2 - 2.0 * (w1 + w2) + w1 * w2 + 1.0 > 0.0
}

/// The width that, paired with `width`, puts the pair on the ellipse, taking
/// the one of the two solutions nearer `hint`.
fn other_width_for_vertical(width: f64, hint: f64) -> f64 {
    if width > VERTICAL_MAX {
        return VERTICAL_MIN;
    }
    let b = width - 2.0;
    let c = (width - 1.0).powi(2);
    let root_base = -b / 2.0;
    let root_offset = (b * b - 4.0 * c).sqrt() / 2.0;
    match hint > root_base {
        true => root_base + root_offset,
        false => root_base - root_offset,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tangents inside their segment are never shortened, by any mode.
    #[test]
    fn contained_kept() {
        for mode in [
            AntiRegression::Contain,
            AntiRegression::KeepRatio,
            AntiRegression::KeepStart,
        ] {
            assert_eq!(adjust(mode, 10.0, 10.0, 3.0), (None, None));
            assert!(!is_regressive(mode, 10.0, 10.0, 3.0));
        }
    }

    /// Contain clips each tangent to the segment's exact length.
    #[test]
    fn contain_clips() {
        assert_eq!(adjust(AntiRegression::Contain, 10.0, 12.0, 3.0), (Some(10.0), None));
        // Not regressive, and clipped all the same.
        assert!(!is_regressive(AntiRegression::KeepRatio, 10.0, 12.0, 3.0));
    }

    /// Keep Ratio shortens both tangents by the same factor, to a pair that
    /// does not regress.
    #[test]
    fn keep_ratio_shortens() {
        let (start, end) = adjust(AntiRegression::KeepRatio, 1.0, 2.0, 1.0);
        let (start, end) = (start.expect("start shortened"), end.expect("end shortened"));
        assert!((start / end - 2.0).abs() < 1e-4, "{start} / {end}");
        assert!(!is_regressive(AntiRegression::KeepRatio, 1.0, start, end));
        assert!(is_regressive(AntiRegression::KeepRatio, 1.0, 2.0, 1.0));
        // With no tangent on one side, the other is clipped to the segment.
        assert_eq!(
            adjust(AntiRegression::KeepRatio, 1.0, 0.0, 3.0),
            (None, Some(1.0 - WRITE_PADDING))
        );
    }

    /// A tangent far shorter than the one it is paired with is shortened to
    /// nothing, and no further.
    #[test]
    fn unequal_widths_stay_positive() {
        for mode in [AntiRegression::KeepRatio, AntiRegression::KeepStart] {
            let (start, end) = adjust(mode, 1.0, 100_000.0, 0.01);
            let (start, end) = (start.expect("start shortened"), end.unwrap_or(0.01));
            assert!(start >= 0.0 && end >= 0.0, "{mode:?}: {start}, {end}");
            assert!(!is_regressive(mode, 1.0, start, end), "{mode:?}: {start}, {end}");
        }
    }

    /// Keep Start leaves the start tangent alone unless it is longer than any
    /// non-regressive pair allows.
    #[test]
    fn keep_start_keeps() {
        let (start, end) = adjust(AntiRegression::KeepStart, 1.0, 1.2, 1.0);
        assert_eq!(start, None);
        let end = end.expect("end shortened");
        assert!(!is_regressive(AntiRegression::KeepStart, 1.0, 1.2, end));

        assert_eq!(
            adjust(AntiRegression::KeepStart, 1.0, 2.0, 1.0),
            (Some(VERTICAL_MAX - WRITE_PADDING), Some(VERTICAL_MIN - WRITE_PADDING))
        );
    }

    /// No mode, no change.
    #[test]
    fn none_keeps() {
        assert_eq!(adjust(AntiRegression::None, 1.0, 2.0, 2.0), (None, None));
    }
}
