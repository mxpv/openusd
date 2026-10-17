//! The check that joint or point indices name only what they index.

use thiserror::Error;

/// An index outside the joints or points it names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
#[error("index {index} at element {position} is not in the range [0, {len})")]
pub struct IndexError {
    /// The index found.
    pub index: i32,
    /// Its position among the indices.
    pub position: usize,
    /// How many joints or points there are to index.
    pub len: usize,
}

/// `Ok` when every one of `indices` names one of `len` joints or points, else
/// the first that does not (C++ `UsdSkelBindingAPI::ValidateJointIndices`
/// over a binding's joint indices, `UsdSkelBlendShape::ValidatePointIndices`
/// over a blend shape's point indices).
pub fn validate_indices(indices: &[i32], len: usize) -> Result<(), IndexError> {
    let inside = |index: i32| usize::try_from(index).is_ok_and(|index| index < len);
    match indices.iter().position(|&index| !inside(index)) {
        Some(position) => Err(IndexError {
            index: indices[position],
            position,
            len,
        }),
        None => Ok(()),
    }
}
