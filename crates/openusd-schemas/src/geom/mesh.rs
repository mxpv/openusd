//! What `UsdGeomMesh` answers beyond its own properties.

use openusd::Result;
use openusd::usd;

use super::{Mesh, MeshSchema, array_len};

impl Mesh {
    /// The sharpness that marks a crease or a corner as perfectly sharp, as
    /// an element of `creaseSharpnesses` or `cornerSharpnesses` (C++
    /// `UsdGeomMesh::SHARPNESS_INFINITE`).
    pub const SHARPNESS_INFINITE: f32 = 10.0;

    /// Whether `sharpness` makes a crease or a corner perfectly sharp (C++
    /// `IsSharpnessInfinite`): it is at least
    /// [`SHARPNESS_INFINITE`](Self::SHARPNESS_INFINITE).
    pub fn is_sharpness_infinite(sharpness: f32) -> bool {
        sharpness >= Self::SHARPNESS_INFINITE
    }

    /// Check that `face_vertex_counts` and `face_vertex_indices` describe the
    /// faces of a mesh of `num_points` points (C++ `ValidateTopology`).
    ///
    /// The counts sum to the number of indices, and every index is in
    /// `0..num_points`. The error is the first rule broken, the sum being
    /// checked first, and its message is the reason C++ reports.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd_schemas::geom::{Mesh, MeshTopologyError};
    ///
    /// // Two triangles over four points.
    /// assert_eq!(Mesh::validate_topology(&[0, 1, 2, 2, 1, 3], &[3, 3], 4), Ok(()));
    ///
    /// // Index 3 names a fourth point, and there are three.
    /// assert_eq!(
    ///     Mesh::validate_topology(&[0, 1, 3], &[3], 3),
    ///     Err(MeshTopologyError::IndexOutOfRange { index: 3, num_points: 3 })
    /// );
    /// ```
    pub fn validate_topology(
        face_vertex_indices: &[i32],
        face_vertex_counts: &[i32],
        num_points: usize,
    ) -> Result<(), MeshTopologyError> {
        let counts_sum: i64 = face_vertex_counts.iter().copied().map(i64::from).sum();
        let indices = face_vertex_indices.len();
        if i64::try_from(indices).ok() != Some(counts_sum) {
            return Err(MeshTopologyError::CountMismatch { counts_sum, indices });
        }

        let out_of_range = |index: i32| usize::try_from(index).map_or(true, |index| index >= num_points);
        match face_vertex_indices.iter().copied().find(|&index| out_of_range(index)) {
            Some(index) => Err(MeshTopologyError::IndexOutOfRange { index, num_points }),
            None => Ok(()),
        }
    }

    /// The number of faces at `time`, where `None` is the default time (C++
    /// `GetFaceCount`): the length of `faceVertexCounts` there, and 0 where
    /// the attribute reads no value.
    pub fn face_count(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        Ok(array_len(self.face_vertex_counts_at(time)?))
    }
}

/// Why face vertex counts and indices are not the topology of a mesh: what
/// [`Mesh::validate_topology`] reports in place of the `reason` string of C++
/// `UsdGeomMesh::ValidateTopology`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum MeshTopologyError {
    /// The face vertex counts do not sum to the number of face vertex
    /// indices.
    #[error("Sum of faceVertexCounts [{counts_sum}] != size of faceVertexIndices [{indices}].")]
    CountMismatch {
        /// The sum of the face vertex counts, which is negative where negative
        /// counts outweigh the others.
        counts_sum: i64,
        /// How many face vertex indices there are.
        indices: usize,
    },

    /// A face vertex index names no point.
    #[error("Out of range face vertex index {index}: Vertex must be in the range [0,{num_points}).")]
    IndexOutOfRange {
        /// The first index out of range.
        index: i32,
        /// How many points the mesh has.
        num_points: usize,
    },
}

#[cfg(test)]
mod tests {
    use openusd::Result;
    use openusd::usd::TimeCode;

    use super::MeshTopologyError;
    use crate::geom::{Mesh, MeshSchema};

    /// The cases of C++ `testUsdGeomMesh.test_ValidateTopology`: each
    /// invalid topology comes with its reason.
    #[test]
    fn validate_topology() {
        let mismatch = Mesh::validate_topology(&[0, 1, 2], &[2, 2], 3).expect_err("counts sum to 4");
        assert_eq!(
            mismatch,
            MeshTopologyError::CountMismatch {
                counts_sum: 4,
                indices: 3
            }
        );
        assert_eq!(
            mismatch.to_string(),
            "Sum of faceVertexCounts [4] != size of faceVertexIndices [3]."
        );

        let negative = Mesh::validate_topology(&[0, -1, 1], &[3], 3).expect_err("a negative index");
        assert_eq!(
            negative,
            MeshTopologyError::IndexOutOfRange {
                index: -1,
                num_points: 3
            }
        );
        assert_eq!(
            negative.to_string(),
            "Out of range face vertex index -1: Vertex must be in the range [0,3)."
        );

        let past_end = Mesh::validate_topology(&[1, 2, 3], &[3], 3).expect_err("index 3 of 3 points");
        assert_eq!(
            past_end,
            MeshTopologyError::IndexOutOfRange {
                index: 3,
                num_points: 3
            }
        );

        assert_eq!(Mesh::validate_topology(&[0, 1, 2, 3, 4, 5], &[3, 3], 6), Ok(()));
    }

    /// The sum is checked before the indices, and the first bad index is the
    /// one reported.
    #[test]
    fn topology_first_failure() {
        assert!(matches!(
            Mesh::validate_topology(&[9, -1], &[3], 1),
            Err(MeshTopologyError::CountMismatch { .. })
        ));
        assert_eq!(
            Mesh::validate_topology(&[0, 7, -1], &[3], 2),
            Err(MeshTopologyError::IndexOutOfRange {
                index: 7,
                num_points: 2
            })
        );
    }

    /// Negative counts are summed as they are: they cancel against positive
    /// ones, and a negative sum matches no number of indices.
    #[test]
    fn topology_negative_counts() {
        assert_eq!(Mesh::validate_topology(&[0, 1, 2], &[4, -1], 3), Ok(()));
        assert_eq!(
            Mesh::validate_topology(&[], &[-3], 3),
            Err(MeshTopologyError::CountMismatch {
                counts_sum: -3,
                indices: 0
            })
        );
        assert_eq!(Mesh::validate_topology(&[], &[], 0), Ok(()));
    }

    #[test]
    fn sharpness_infinite() {
        assert!(Mesh::is_sharpness_infinite(Mesh::SHARPNESS_INFINITE));
        assert!(Mesh::is_sharpness_infinite(11.0));
        assert!(!Mesh::is_sharpness_infinite(9.5));
    }

    /// C++ `testUsdGeomMesh.test_ComputeFaceCount`, over its `mesh.usda`.
    #[test]
    fn face_count() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Mesh "UnsetVertexCounts"
{
}

def Mesh "BlockedVertexCounts"
{
    int[] faceVertexCounts = None
}

def Mesh "EmptyVertexCounts"
{
    int[] faceVertexCounts = []
}

def Mesh "TimeSampledVertexCounts"
{
    int[] faceVertexCounts.timeSamples = {
        1: [4, 4, 4]
    }
}

def Mesh "TimeSampledAndDefaultVertexCounts"
{
    int[] faceVertexCounts = [4, 4, 4, 4]
    int[] faceVertexCounts.timeSamples = {
        1: [4, 4, 4, 4, 4]
    }
}
"#,
        )?;

        for (path, earliest, default) in [
            ("/UnsetVertexCounts", 0, 0),
            ("/BlockedVertexCounts", 0, 0),
            ("/EmptyVertexCounts", 0, 0),
            ("/TimeSampledVertexCounts", 3, 0),
            ("/TimeSampledAndDefaultVertexCounts", 5, 4),
        ] {
            let mesh = Mesh::get(&stage, path)?.expect("Mesh");
            assert_eq!(mesh.face_count(TimeCode::EARLIEST)?, earliest, "{path}");
            assert_eq!(mesh.face_count(None)?, default, "{path}");
        }
        Ok(())
    }

    /// The count follows the samples of an authored mesh.
    #[test]
    fn face_count_authored() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = Mesh::define(&stage, "/Mesh")?;
        mesh.create_face_vertex_counts_attr()?
            .set_at(vec![3, 3], TimeCode::new(1.0))?
            .set_at(vec![4], TimeCode::new(2.0))?;

        assert_eq!(mesh.face_count(TimeCode::new(1.0))?, 2);
        assert_eq!(mesh.face_count(TimeCode::new(2.0))?, 1);
        assert_eq!(mesh.face_count(None)?, 0);
        Ok(())
    }
}
