//! What `UsdGeomTetMesh` answers beyond its own properties.

use std::collections::HashMap;

use openusd::Result;
use openusd::usd::{self, SchemaBase};
use openusd::{gf, tf};

use super::{GprimSchema, PointBasedSchema, TetMesh, TetMeshSchema, tokens};
use crate::SchemaError;

impl TetMesh {
    /// The triangles on the surface of the mesh at `time`, where `None` is
    /// the default time (C++ `ComputeSurfaceFaces`):
    /// [`surface_faces_from`](Self::surface_faces_from) over
    /// `tetVertexIndices` there. A mesh that reads no tetrahedra has no
    /// surface faces.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::{gf, usd};
    /// use openusd_schemas::geom::{self, TetMeshSchema};
    ///
    /// let stage = usd::Stage::builder()
    ///     .schema_registry(openusd_schemas::schema_registry())
    ///     .in_memory("scene.usda")?;
    /// let mesh = geom::TetMesh::define(&stage, "/Tets")?;
    /// mesh.create_tet_vertex_indices_attr()?
    ///     .set(vec![gf::vec4i(0, 1, 2, 3)])?;
    ///
    /// // All four faces of a lone tetrahedron are on the surface.
    /// let faces = mesh.surface_faces(None)?;
    /// assert_eq!(faces.len(), 4);
    /// mesh.create_surface_face_vertex_indices_attr()?.set(faces)?;
    /// # Ok::<(), openusd_schemas::SchemaError>(())
    /// ```
    pub fn surface_faces(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Vec<gf::Vec3i>> {
        let tets = self.tet_vertex_indices_at(time)?.unwrap_or_default();
        Ok(Self::surface_faces_from(&tets))
    }

    /// The triangles on the surface of the tetrahedra `tet_vertex_indices`
    /// (C++ `UsdGeomTetMesh::ComputeSurfaceFaces`, over the indices it
    /// reads): each face that exactly one tetrahedron has, two faces being
    /// the same where they join the same three points in any order.
    ///
    /// A face keeps the winding its tetrahedron gives it, and the faces are
    /// sorted by their three indices in turn, so the same tetrahedra always
    /// yield the same list.
    pub fn surface_faces_from(tet_vertex_indices: &[gf::Vec4i]) -> Vec<gf::Vec3i> {
        // Keyed by the sorted corners, which is what two tetrahedra sharing a
        // face agree on; the winding is kept beside the count.
        let mut seen: HashMap<[i32; 3], (usize, [i32; 3])> =
            HashMap::with_capacity(TET_FACES.len() * tet_vertex_indices.len());
        for tet in tet_vertex_indices {
            for face in TET_FACES {
                let triangle = face.map(|corner| tet[corner]);
                let mut corners = triangle;
                corners.sort_unstable();
                seen.entry(corners).or_insert((0, triangle)).0 += 1;
            }
        }

        let mut faces: Vec<[i32; 3]> = seen
            .into_values()
            .filter_map(|(count, triangle)| (count == 1).then_some(triangle))
            .collect();
        faces.sort_unstable();
        faces.into_iter().map(gf::Vec3i::from).collect()
    }

    /// The tetrahedra that are inverted at `time`, where `None` is the
    /// default time, each as its position in `tetVertexIndices`, in ascending
    /// order (C++ `FindInvertedElements`).
    ///
    /// A tetrahedron is inverted where one of its faces is wound against the
    /// mesh's `orientation`, which is read at the default time and is
    /// right-handed unless it is the token `leftHanded`. An empty list says
    /// every tetrahedron is wound as the mesh is oriented.
    ///
    /// The list is also empty for a mesh that reads fewer than four points
    /// or no tetrahedra at `time`, where C++ reports failure. A tetrahedron
    /// naming a point the mesh does not have is
    /// [`SchemaError::TetVertexOutOfRange`].
    pub fn inverted_elements(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Vec<usize>, SchemaError> {
        let time = time.into();
        let points = self.points_at(time)?.unwrap_or_default();
        let tets = self.tet_vertex_indices_at(time)?.unwrap_or_default();
        if points.len() < 4 || tets.is_empty() {
            return Ok(Vec::new());
        }
        // The token is compared as authored, so any spelling but `leftHanded`
        // is right-handed, as in C++, including one no `Orientation` names.
        let orientation = self.orientation_attr().get::<tf::Token>()?;
        let left_handed = orientation.as_deref() == Some(tokens::LEFT_HANDED);

        inverted_elements(&points, &tets, left_handed).map_err(|(tet, index)| SchemaError::TetVertexOutOfRange {
            prim: self.path().clone(),
            tet,
            index,
            points: points.len(),
        })
    }
}

/// The four faces of a tetrahedron, each as the positions of its corners
/// among the tetrahedron's four indices, wound counter-clockwise seen from
/// outside a right-handed tetrahedron.
const TET_FACES: [[usize; 3]; 4] = [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]];

/// The positions in `tets` of the tetrahedra over `points` that have a face
/// wound against the orientation, or the first tetrahedron naming a point
/// outside `points`, as its position and the index it holds.
///
/// A face is wound with a right-handed orientation where its normal points
/// away from the tetrahedron's center, and with a left-handed one where it
/// points toward it.
///
// TODO(rayon): each tetrahedron is judged from `points` and its own indices
// alone, so the outer loop can run in parallel and collect in order.
fn inverted_elements(points: &[gf::Vec3f], tets: &[gf::Vec4i], left_handed: bool) -> Result<Vec<usize>, (usize, i32)> {
    let sign: f32 = if left_handed { 1.0 } else { -1.0 };
    let point = |index: i32| usize::try_from(index).ok().and_then(|index| points.get(index)).copied();

    let mut inverted = Vec::new();
    for (position, tet) in tets.iter().enumerate() {
        let mut corners = [gf::Vec3f::default(); 4];
        for (corner, slot) in corners.iter_mut().enumerate() {
            *slot = point(tet[corner]).ok_or((position, tet[corner]))?;
        }
        let center = (corners[0] + corners[1] + corners[2] + corners[3]) * 0.25;

        let is_inverted = TET_FACES.iter().any(|face| {
            let [v0, v1, v2] = face.map(|corner| corners[corner]);
            let normal = (v1 - v0).cross(v2 - v0);
            sign * normal.dot(center - v0) < 0.0
        });
        if is_inverted {
            inverted.push(position);
        }
    }
    Ok(inverted)
}

#[cfg(test)]
mod tests {
    use openusd::gf;
    use openusd::usd::{Stage, TimeCode};

    use crate::SchemaError;
    use crate::geom::{GprimSchema, Orientation, PointBasedSchema, TetMesh, TetMeshSchema};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    fn points(points: &[[f32; 3]]) -> Vec<gf::Vec3f> {
        points.iter().copied().map(gf::Vec3f::from).collect()
    }

    fn tets(tets: &[[i32; 4]]) -> Vec<gf::Vec4i> {
        tets.iter().copied().map(gf::Vec4i::from).collect()
    }

    fn faces(faces: &[[i32; 3]]) -> Vec<gf::Vec3i> {
        faces.iter().copied().map(gf::Vec3i::from).collect()
    }

    /// The mesh of the C++ surface-extraction tests: two tetrahedra sharing
    /// a face at time 0, and apart at time 10. `x` is the first coordinate of
    /// the point off the origin along that axis, 2 for the right-handed
    /// fixture and -2 for the left-handed one.
    fn two_tets(stage: &Stage, x: f32) -> Result<TetMesh> {
        let mesh = TetMesh::define(stage, "/tetMesh")?;
        let (start, end) = (TimeCode::new(0.0), TimeCode::new(10.0));
        mesh.create_points_attr()?
            .set_at(
                points(&[
                    [0.0, 0.0, 0.0],
                    [x, 0.0, 0.0],
                    [0.0, 2.0, 0.0],
                    [0.0, 0.0, 2.0],
                    [0.0, 0.0, -2.0],
                ]),
                start,
            )?
            .set_at(
                points(&[
                    [0.0, 0.0, 3.0],
                    [x, 0.0, 3.0],
                    [0.0, 2.0, 3.0],
                    [0.0, 0.0, 5.0],
                    [0.0, 0.0, -3.0],
                    [x, 0.0, -3.0],
                    [0.0, 2.0, -3.0],
                    [0.0, 0.0, -5.0],
                ]),
                end,
            )?;
        mesh.create_tet_vertex_indices_attr()?
            .set_at(tets(&[[0, 1, 2, 3], [0, 2, 1, 4]]), start)?
            .set_at(tets(&[[0, 1, 2, 3], [4, 6, 5, 7]]), end)?;
        Ok(mesh)
    }

    /// What both surface-extraction tests of C++ `testUsdGeomTetMesh` check
    /// of their fixture: nothing is inverted, the joined tetrahedra have six
    /// surface faces and the separate ones eight, and the faces author as
    /// `surfaceFaceVertexIndices`.
    fn check_surface(mesh: &TetMesh) -> Result {
        let (start, end) = (TimeCode::new(0.0), TimeCode::new(10.0));
        assert!(mesh.inverted_elements(start)?.is_empty());
        assert!(mesh.inverted_elements(end)?.is_empty());

        let joined = mesh.surface_faces(start)?;
        assert_eq!(
            joined,
            faces(&[[0, 1, 3], [0, 2, 4], [0, 3, 2], [0, 4, 1], [1, 2, 3], [2, 1, 4]])
        );
        let apart = mesh.surface_faces(end)?;
        assert_eq!(apart.len(), 8);

        mesh.create_surface_face_vertex_indices_attr()?
            .set_at(joined.clone(), start)?
            .set_at(apart.clone(), end)?;
        assert_eq!(mesh.surface_face_vertex_indices_at(start)?, Some(joined));
        assert_eq!(mesh.surface_face_vertex_indices_at(end)?, Some(apart));
        Ok(())
    }

    #[test]
    fn surface_right_handed() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        check_surface(&two_tets(&stage, 2.0)?)
    }

    #[test]
    fn surface_left_handed() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = two_tets(&stage, -2.0)?;
        mesh.create_orientation_attr()?.set(Orientation::LeftHanded)?;
        check_surface(&mesh)
    }

    /// A mesh with no tetrahedra at the time asked for has no surface.
    #[test]
    fn surface_no_tets() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = two_tets(&stage, 2.0)?;
        assert!(mesh.surface_faces(None)?.is_empty());
        assert!(TetMesh::surface_faces_from(&[]).is_empty());
        Ok(())
    }

    /// A face two tetrahedra share is interior however each winds it, and
    /// the result does not depend on the order the tetrahedra come in.
    #[test]
    fn surface_order_independent() {
        let forward = TetMesh::surface_faces_from(&tets(&[[0, 1, 2, 3], [0, 2, 1, 4]]));
        let backward = TetMesh::surface_faces_from(&tets(&[[0, 2, 1, 4], [0, 1, 2, 3]]));
        assert_eq!(forward, backward);
        assert!(!forward.contains(&gf::vec3i(0, 2, 1)));
        assert!(!forward.contains(&gf::vec3i(0, 1, 2)));
    }

    /// C++ `test_UsdGeomTetMeshFindInvertedElements`: one tetrahedron, wound
    /// each way, against each orientation.
    #[test]
    fn inverted_elements() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = TetMesh::define(&stage, "/tetMesh")?;
        let time = TimeCode::new(0.0);
        let set_points = |x: f32, y: f32| -> Result {
            mesh.create_points_attr()?.set_at(
                points(&[[0.0, 0.0, 0.0], [0.0, 0.0, 1.0], [x, 0.0, 0.0], [0.0, y, 0.0]]),
                time,
            )?;
            Ok(())
        };
        let orient = |orientation: Orientation| -> Result {
            mesh.create_orientation_attr()?.set(orientation)?;
            Ok(())
        };
        let inverted = || mesh.inverted_elements(time);

        // A right-handed element under the fallback orientation.
        set_points(-1.0, -1.0)?;
        mesh.create_tet_vertex_indices_attr()?
            .set_at(tets(&[[0, 1, 2, 3]]), time)?;
        assert_eq!(inverted()?, Vec::<usize>::new());

        orient(Orientation::LeftHanded)?;
        assert_eq!(inverted()?, vec![0]);

        // The mirrored element is left-handed.
        orient(Orientation::RightHanded)?;
        set_points(1.0, -1.0)?;
        assert_eq!(inverted()?, vec![0]);

        orient(Orientation::LeftHanded)?;
        assert_eq!(inverted()?, Vec::<usize>::new());

        orient(Orientation::RightHanded)?;
        assert_eq!(inverted()?, vec![0]);

        // Mirrored again, the element is right-handed under a left-handed mesh.
        orient(Orientation::LeftHanded)?;
        set_points(1.0, 1.0)?;
        assert_eq!(inverted()?, vec![0]);
        Ok(())
    }

    /// Only the inverted tetrahedra are listed, by position.
    #[test]
    fn inverted_positions() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = two_tets(&stage, 2.0)?;
        mesh.create_tet_vertex_indices_attr()?
            .set(tets(&[[0, 2, 1, 3], [0, 2, 1, 4], [0, 1, 2, 4]]))?;
        mesh.create_points_attr()?.set(points(&[
            [0.0, 0.0, 0.0],
            [2.0, 0.0, 0.0],
            [0.0, 2.0, 0.0],
            [0.0, 0.0, 2.0],
            [0.0, 0.0, -2.0],
        ]))?;
        assert_eq!(mesh.inverted_elements(None)?, vec![0, 2]);
        Ok(())
    }

    /// Fewer than four points, or no tetrahedra, leaves nothing to judge.
    #[test]
    fn inverted_needs_geometry() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = TetMesh::define(&stage, "/tetMesh")?;
        assert!(mesh.inverted_elements(None)?.is_empty());

        mesh.create_points_attr()?
            .set(points(&[[0.0, 0.0, 0.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0]]))?;
        mesh.create_tet_vertex_indices_attr()?.set(tets(&[[0, 1, 2, 3]]))?;
        assert!(mesh.inverted_elements(None)?.is_empty());
        Ok(())
    }

    /// A tetrahedron naming a point the mesh lacks is an error naming it.
    #[test]
    fn inverted_index_range() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = two_tets(&stage, 2.0)?;
        for bad in [5, -1] {
            mesh.create_tet_vertex_indices_attr()?
                .set_at(tets(&[[0, 1, 2, 3], [0, 2, bad, 4]]), TimeCode::new(0.0))?;
            let error = mesh
                .inverted_elements(TimeCode::new(0.0))
                .expect_err("an index outside the points");
            assert!(matches!(
                error,
                SchemaError::TetVertexOutOfRange { tet: 1, index, points: 5, .. } if index == bad
            ));
        }
        Ok(())
    }
}
