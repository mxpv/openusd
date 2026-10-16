//! Joint-influence array utilities: normalizing, sorting, resizing and
//! interleaving the flat `(index, weight)` runs a skinned prim's
//! `primvars:skel:jointIndices` and `primvars:skel:jointWeights` hold, one
//! run of `per_component` entries per point (C++ `usdSkel/utils.h`).
//!
//! An array of constant influences expands to one run per point with
//! [`slice::repeat`] (C++ `UsdSkelExpandConstantInfluencesToVarying`).

use std::cmp::Ordering;

use openusd::gf;

/// Scale each run of `per_component` weights to sum to one, and set a run
/// whose sum lies within `eps` of zero to zeros (C++
/// `UsdSkelNormalizeWeights`; C++ defaults `eps` to `f32::EPSILON`). `false`,
/// with `weights` untouched, when `per_component` is zero or does not divide
/// the array.
pub fn normalize_weights(weights: &mut [f32], per_component: usize, eps: f32) -> bool {
    if !has_shape(weights.len(), per_component) {
        return false;
    }
    for run in weights.chunks_exact_mut(per_component) {
        let sum: f32 = run.iter().sum();
        if sum.abs() > eps {
            for weight in run.iter_mut() {
                *weight /= sum;
            }
        } else {
            run.fill(0.0);
        }
    }
    true
}

/// Sort each run of `per_component` influences by descending weight, ties
/// going to the higher index (C++ `UsdSkelSortInfluences`). `false`, with
/// both arrays untouched, when they differ in length, or `per_component` is
/// zero or does not divide them.
pub fn sort_influences(indices: &mut [i32], weights: &mut [f32], per_component: usize) -> bool {
    if indices.len() != weights.len() || !has_shape(indices.len(), per_component) {
        return false;
    }
    if per_component < 2 {
        return true;
    }
    let mut run = Vec::with_capacity(per_component);
    for (indices, weights) in indices
        .chunks_exact_mut(per_component)
        .zip(weights.chunks_exact_mut(per_component))
    {
        run.clear();
        run.extend(weights.iter().copied().zip(indices.iter().copied()));
        run.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(Ordering::Equal).then(b.1.cmp(&a.1)));
        for (slot, &(weight, index)) in run.iter().enumerate() {
            weights[slot] = weight;
            indices[slot] = index;
        }
    }
    true
}

/// Resize each run of influences from `from` entries to `to`, truncating a
/// run or padding it with the default value (C++ `UsdSkelResizeInfluences`
/// over an int array). Unchanged and `true` when the two sizes match;
/// `false`, with `array` untouched, when `from` is zero or does not divide
/// the array. Weights resize through [`resize_weights`], which renormalizes.
pub fn resize_influences<T: Copy + Default>(array: &mut Vec<T>, from: usize, to: usize) -> bool {
    if from == to {
        return true;
    }
    if !has_shape(array.len(), from) {
        return false;
    }
    let mut resized = Vec::with_capacity(array.len() / from * to);
    for run in array.chunks_exact(from) {
        resized.extend(run.iter().copied().take(to));
        resized.resize(resized.len() + to.saturating_sub(from), T::default());
    }
    *array = resized;
    true
}

/// [`resize_influences`] over weights. A truncated run is renormalized, as
/// C++ `UsdSkelResizeInfluences` over a float array does; `false` when that
/// renormalization does (a `to` of zero).
pub fn resize_weights(weights: &mut Vec<f32>, from: usize, to: usize) -> bool {
    if !resize_influences(weights, from, to) {
        return false;
    }
    to >= from || normalize_weights(weights, to, f32::EPSILON)
}

/// Each joint index paired with its weight, as `(index, weight)` (C++
/// `UsdSkelInterleaveInfluences`). `None` unless the arrays have the same
/// length.
pub fn interleave_influences(indices: &[i32], weights: &[f32]) -> Option<Vec<gf::Vec2f>> {
    (indices.len() == weights.len()).then(|| {
        indices
            .iter()
            .zip(weights)
            .map(|(&index, &weight)| gf::vec2f(index as f32, weight))
            .collect()
    })
}

/// `true` when an array of `len` entries splits into whole runs of
/// `per_component`, which must be positive.
pub(crate) fn has_shape(len: usize, per_component: usize) -> bool {
    per_component > 0 && len.is_multiple_of(per_component)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn weights_normalize() {
        let mut weights = vec![
            3.0, 1.0, 1.0, 0.0, 4.0, 3.0, 2.0, 1.0, 40.0, 30.0, 20.0, 10.0, 0.0, 0.0, 0.0, 0.0,
        ];
        assert!(normalize_weights(&mut weights, 4, f32::EPSILON));
        let expected = [
            0.6, 0.2, 0.2, 0.0, 0.4, 0.3, 0.2, 0.1, 0.4, 0.3, 0.2, 0.1, 0.0, 0.0, 0.0, 0.0,
        ];
        for (a, b) in weights.iter().zip(expected) {
            assert!((a - b).abs() < 1e-6, "{weights:?}");
        }
        assert!(normalize_weights(&mut [], 4, f32::EPSILON));
        assert!(!normalize_weights(&mut [1.0], 4, f32::EPSILON));
        assert!(!normalize_weights(&mut [1.0], 0, f32::EPSILON));
    }

    #[test]
    fn influences_sort() {
        let mut indices = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
        let mut weights = vec![3.0, 1.0, 4.0, 2.0, 1.0, 2.0, 3.0, 4.0, 4.0, 3.0, 2.0, 1.0];
        assert!(sort_influences(&mut indices, &mut weights, 4));
        assert_eq!(indices, [3, 1, 4, 2, 8, 7, 6, 5, 9, 10, 11, 12]);
        assert_eq!(weights, [4.0, 3.0, 2.0, 1.0, 4.0, 3.0, 2.0, 1.0, 4.0, 3.0, 2.0, 1.0]);

        // One influence per component is already sorted.
        let mut indices = vec![1, 2, 3, 4];
        let mut weights = vec![3.0, 1.0, 4.0, 2.0];
        assert!(sort_influences(&mut indices, &mut weights, 1));
        assert_eq!(indices, [1, 2, 3, 4]);
        assert!(!sort_influences(&mut indices, &mut weights[..3], 1));
    }

    #[test]
    fn influences_resize() {
        let original = vec![1, 2, 3, 4, 5, 6, 7, 8];
        let mut indices = original.clone();
        assert!(resize_influences(&mut indices, 4, 2));
        assert_eq!(indices, [1, 2, 5, 6]);
        let mut indices = original;
        assert!(resize_influences(&mut indices, 2, 4));
        assert_eq!(indices, [1, 2, 0, 0, 3, 4, 0, 0, 5, 6, 0, 0, 7, 8, 0, 0]);

        // Truncated weights renormalize; expanded weights pad with zeros.
        let mut weights = vec![
            3.0, 1.0, 1.0, 5.0, 6.0, 1.0, 1.0, 3.0, 7.0, 8.0, 1.0, 3.0, 1.0, 9.0, 10.0,
        ];
        assert!(resize_weights(&mut weights, 5, 3));
        let expected = [0.6, 0.2, 0.2, 0.2, 0.2, 0.6, 0.2, 0.6, 0.2];
        for (a, b) in weights.iter().zip(expected) {
            assert!((a - b).abs() < 1e-6, "{weights:?}");
        }
        let mut weights = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0];
        assert!(resize_weights(&mut weights, 3, 5));
        assert_eq!(
            weights,
            [
                1.0, 2.0, 3.0, 0.0, 0.0, 4.0, 5.0, 6.0, 0.0, 0.0, 7.0, 8.0, 9.0, 0.0, 0.0
            ]
        );

        // Empty arrays resize; misshapen ones do not.
        assert!(resize_influences(&mut Vec::<i32>::new(), 10, 4));
        assert!(resize_weights(&mut Vec::new(), 4, 10));
        assert!(!resize_weights(&mut vec![1.0], 3, 2));
        assert!(!resize_weights(&mut vec![1.0], 3, 0));
    }

    #[test]
    fn influences_interleave() {
        assert_eq!(
            interleave_influences(&[2, 5], &[0.25, 0.75]),
            Some(vec![gf::vec2f(2.0, 0.25), gf::vec2f(5.0, 0.75)])
        );
        assert!(interleave_influences(&[2], &[]).is_none());
    }
}
