//! Per-joint array remapping between two joint orderings.
//!
//! Mirrors Pixar's `UsdSkelAnimMapper`. Built from a *source* joint
//! order (e.g. a SkelAnimation's `joints`) and a *target* joint order
//! (e.g. a bound Skeleton's `joints`, or a per-mesh `skel:joints`
//! subset). The resulting mapper can then transfer arrays whose
//! per-joint stride is known — translations (`[f32; 3]`), rotations
//! (`[f32; 4]`), scales, etc. — from source into target order
//! efficiently.
//!
//! Joints present in the target but not in the source are filled with
//! a caller-supplied default value. Joints present in the source but
//! not in the target are dropped.

/// Index `i` in [`AnimMapper::indices`] is the position in the source
/// array of the joint that should land at target index `i`, or
/// [`MISSING`] when the target joint isn't present in the source.
pub const MISSING: i32 = -1;

/// Pre-computed source→target remap. Build with
/// [`AnimMapper::new`]; apply with [`AnimMapper::remap`] (or
/// [`AnimMapper::remap_with_stride`] when each joint slot is a flat
/// sub-array — useful for matrix data laid out as `[f64; 16]`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnimMapper {
    /// `indices[t]` = the source index that should land at target `t`,
    /// or [`MISSING`] if the target joint isn't in the source.
    indices: Vec<i32>,
    /// `true` iff `indices == [0, 1, 2, …, n-1]` AND `source.len() ==
    /// target.len()`. When set, [`remap`] is a straight clone.
    identity: bool,
    /// `true` iff every target joint resolved to a source slot — i.e.
    /// no [`MISSING`] entries. When set the fill value is unused.
    full: bool,
}

impl AnimMapper {
    /// Build a mapper that translates per-joint arrays in `source`
    /// order into `target` order.
    pub fn new(source: &[String], target: &[String]) -> Self {
        use std::collections::HashMap;
        let by_name: HashMap<&str, i32> = source.iter().enumerate().map(|(i, n)| (n.as_str(), i as i32)).collect();
        let indices: Vec<i32> = target
            .iter()
            .map(|n| by_name.get(n.as_str()).copied().unwrap_or(MISSING))
            .collect();
        let full = indices.iter().all(|&i| i != MISSING);
        let identity = source.len() == target.len() && indices.iter().enumerate().all(|(i, &j)| j == i as i32);
        Self {
            indices,
            identity,
            full,
        }
    }

    /// Borrow the underlying source-index array.
    pub fn indices(&self) -> &[i32] {
        &self.indices
    }

    /// Number of joints in the target ordering.
    pub fn target_len(&self) -> usize {
        self.indices.len()
    }

    /// `true` when the mapper is a no-op (source order equals target
    /// order). [`remap`] still works but skipping it entirely is
    /// cheaper.
    pub fn is_identity(&self) -> bool {
        self.identity
    }

    /// `true` when every target joint resolved to a source slot.
    pub fn is_full(&self) -> bool {
        self.full
    }

    /// `true` when at least one target joint is missing from the
    /// source — i.e. [`remap`] will fall back to the caller's
    /// `default` for some entries.
    pub fn is_sparse(&self) -> bool {
        !self.full
    }

    /// Remap a per-joint array `source` (one element per source
    /// joint) into target order. Missing entries get `default`.
    /// Panics if `source.len()` doesn't match the source length the
    /// mapper was built with.
    pub fn remap<T: Clone>(&self, source: &[T], default: T) -> Vec<T> {
        if self.identity {
            return source.to_vec();
        }
        self.indices
            .iter()
            .map(|&i| {
                if i == MISSING {
                    default.clone()
                } else {
                    source[i as usize].clone()
                }
            })
            .collect()
    }

    /// Remap a flat array of `stride`-sized slots — useful for
    /// matrix data stored as a flat `Vec<f64>` (stride = 16) or any
    /// other strided per-joint buffer. `default` is the value to copy
    /// into each entry of a missing slot.
    pub fn remap_with_stride<T: Copy>(&self, source: &[T], stride: usize, default: T) -> Vec<T> {
        let mut out = Vec::with_capacity(self.indices.len() * stride);
        for &i in &self.indices {
            if i == MISSING {
                for _ in 0..stride {
                    out.push(default);
                }
            } else {
                let start = (i as usize) * stride;
                out.extend_from_slice(&source[start..start + stride]);
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(items: &[&str]) -> Vec<String> {
        items.iter().map(|x| x.to_string()).collect()
    }

    #[test]
    fn identity_when_orders_match() {
        let m = AnimMapper::new(&s(&["A", "B", "C"]), &s(&["A", "B", "C"]));
        assert!(m.is_identity());
        assert!(m.is_full());
        assert_eq!(m.remap(&[10, 20, 30], 0), vec![10, 20, 30]);
    }

    #[test]
    fn reorders_when_target_permutes() {
        let m = AnimMapper::new(&s(&["A", "B", "C"]), &s(&["C", "A", "B"]));
        assert!(!m.is_identity());
        assert!(m.is_full());
        assert_eq!(m.remap(&[1.0, 2.0, 3.0], 0.0), vec![3.0, 1.0, 2.0]);
    }

    #[test]
    fn fills_missing_with_default() {
        let m = AnimMapper::new(&s(&["A"]), &s(&["A", "B"]));
        assert!(m.is_sparse());
        assert_eq!(m.indices(), &[0, MISSING]);
        assert_eq!(m.remap(&[42], 0), vec![42, 0]);
    }

    #[test]
    fn remap_with_stride_handles_flat_matrices() {
        // Two source joints, each a stride-4 row.
        let src = [
            1.0, 2.0, 3.0, 4.0, // joint A
            5.0, 6.0, 7.0, 8.0, // joint B
        ];
        let m = AnimMapper::new(&s(&["A", "B"]), &s(&["B", "missing", "A"]));
        let out = m.remap_with_stride(&src, 4, 0.0);
        assert_eq!(out, vec![5.0, 6.0, 7.0, 8.0, 0.0, 0.0, 0.0, 0.0, 1.0, 2.0, 3.0, 4.0]);
    }
}
