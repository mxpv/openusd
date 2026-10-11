//! What the curve schemas answer beyond their own properties: how many
//! curves a prim holds, how its `widths` lie on it, and how a `BasisCurves`'
//! topology sizes its primvar data and its segments.

use openusd::Result;
use openusd::{gf, tf, usd};

use super::points::{interpolation, set_interpolation};
use super::{BasisCurves, BasisCurvesSchema, CurveBasis, CurveType, CurveWrap, CurvesSchema, Interpolation, array_len};
use crate::SchemaError;

/// What every `UsdGeomCurves` answers about its curves and their `widths`.
///
/// Every [`CurvesSchema`] answers it, so a `BasisCurves`, `NurbsCurves` or
/// `HermiteCurves` view has these wherever the generated accessors are.
pub trait CurvesExt: CurvesSchema {
    /// How many curves the prim holds at `time`, where `None` is the default
    /// time (C++ `GetCurveCount`): the length of `curveVertexCounts`, and
    /// zero where it reads no value.
    fn curve_count(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        Ok(array_len(self.curve_vertex_counts_at(time)?))
    }

    /// How `widths` lie on the curves (C++ `GetWidthsInterpolation`),
    /// [`Interpolation::Vertex`] where none is authored.
    ///
    /// An authored token that names no interpolation is an error.
    fn widths_interpolation(&self) -> Result<Interpolation> {
        interpolation(&CurvesSchema::widths_attr(self))
    }

    /// Author the `interpolation` of `widths` (C++ `SetWidthsInterpolation`),
    /// declaring the attribute where no layer has yet.
    fn set_widths_interpolation(&self, interpolation: Interpolation) -> Result<()> {
        set_interpolation(CurvesSchema::widths_attr_builder(self), interpolation)
    }
}

impl<T: CurvesSchema> CurvesExt for T {}

impl BasisCurves {
    /// The interpolation a primvar of `n` values has on these curves at
    /// `time`, where `None` is the default time, or `None` where `n` fits no
    /// interpolation (C++ `ComputeInterpolationForSize`).
    ///
    /// The first fit wins, in the order constant, uniform, varying, vertex.
    /// The sizes `n` is measured against are the ones
    /// [`uniform_data_size`](Self::uniform_data_size),
    /// [`varying_data_size`](Self::varying_data_size) and
    /// [`vertex_data_size`](Self::vertex_data_size) answer,
    /// which is what C++ reports through its `ComputeInterpolationInfo`.
    pub fn interpolation_for_size(
        &self,
        n: usize,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<Option<Interpolation>> {
        let time = time.into();
        if n == 1 {
            return Ok(Some(Interpolation::Constant));
        }
        let counts = self.curve_vertex_counts_at(time)?.unwrap_or_default();
        if n == counts.len() {
            return Ok(Some(Interpolation::Uniform));
        }
        if n == self.varying_data_size_of(&counts, time)? {
            return Ok(Some(Interpolation::Varying));
        }
        Ok((n == vertex_data_size_of(&counts)).then_some(Interpolation::Vertex))
    }

    /// How many values a `uniform` primvar holds at `time`, where `None` is
    /// the default time: one for each curve (C++ `ComputeUniformDataSize`).
    pub fn uniform_data_size(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        self.curve_count(time)
    }

    /// How many values a `varying` primvar holds at `time`, where `None` is
    /// the default time: one for each segment end (C++
    /// `ComputeVaryingDataSize`).
    ///
    /// A linear curve of `n` vertices takes `n` values, and `n + 1` when it
    /// is periodic. A cubic curve takes `(n - 4) / vstep + 2`, or `n / vstep`
    /// when it is periodic, where `vstep` is 3 for a `bezier` basis and 1 for
    /// `bspline` and `catmullRom`; one with fewer than four vertices counts
    /// as a single segment, so it takes two. The size is zero for a curve
    /// type that is neither `linear` nor `cubic`, and for cubic curves of any
    /// other basis. A negative vertex count reads as zero.
    pub fn varying_data_size(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        let time = time.into();
        let counts = self.curve_vertex_counts_at(time)?.unwrap_or_default();
        self.varying_data_size_of(&counts, time)
    }

    /// How many values a `vertex` primvar holds at `time`, where `None` is
    /// the default time: one for each curve vertex (C++
    /// `ComputeVertexDataSize`). A negative vertex count reads as zero.
    pub fn vertex_data_size(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        let counts = self.curve_vertex_counts_at(time)?.unwrap_or_default();
        Ok(vertex_data_size_of(&counts))
    }

    /// How many segments each curve has at `time`, where `None` is the
    /// default time, in the order of `curveVertexCounts` (C++
    /// `ComputeSegmentCounts`).
    ///
    /// For a curve of `n` vertices:
    ///
    /// | type | basis | nonperiodic | periodic | pinned |
    /// |------|-------|-------------|----------|--------|
    /// | `linear` | any | `n - 1` | `n` | `n - 1` |
    /// | `cubic` | `bezier` | `(n - 4) / 3 + 1` | `n / 3` | `(n - 4) / 3 + 1` |
    /// | `cubic` | `bspline`, `catmullRom` | `n - 3` | `n` | `n - 1` |
    ///
    /// A curve with too few vertices for its type gets the count the formula
    /// gives, which may be zero or negative. The answer is empty where
    /// `curveVertexCounts`, `type`, `wrap` or `basis` reads no value, as on a
    /// prim that is not a `BasisCurves`, and for any combination outside the
    /// table.
    pub fn segment_counts(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Vec<i32>> {
        let time = time.into();
        match self.curve_vertex_counts_at(time)? {
            Some(counts) => self.segment_counts_of(&counts, time),
            None => Ok(Vec::new()),
        }
    }

    /// The segment counts of curves with the vertex `counts`, under the
    /// `type`, `wrap` and `basis` read at `time`: what
    /// [`segment_counts`](Self::segment_counts) answers for
    /// the `curveVertexCounts` it reads.
    pub(super) fn segment_counts_of(&self, counts: &[i32], time: Option<usd::TimeCode>) -> Result<Vec<i32>> {
        use CurveBasis::{Bezier, Bspline, CatmullRom};
        use CurveType::{Cubic, Linear};
        use CurveWrap::{Nonperiodic, Periodic, Pinned};

        let topology = self.topology(time)?;
        if !topology.complete {
            return Ok(Vec::new());
        }
        let segments: fn(i32) -> i32 = match (topology.curve_type, topology.wrap, topology.basis) {
            (Some(Linear), Some(Periodic), _) => |n| n,
            (Some(Linear), Some(Nonperiodic | Pinned), _) => |n| n.saturating_sub(1),
            (Some(Cubic), Some(Periodic), Some(Bezier)) => |n| n / BEZIER_VSTEP,
            (Some(Cubic), Some(Nonperiodic | Pinned), Some(Bezier)) => |n| n.saturating_sub(4) / BEZIER_VSTEP + 1,
            (Some(Cubic), Some(Periodic), Some(Bspline | CatmullRom)) => |n| n,
            (Some(Cubic), Some(Nonperiodic), Some(Bspline | CatmullRom)) => |n| n.saturating_sub(3),
            (Some(Cubic), Some(Pinned), Some(Bspline | CatmullRom)) => |n| n.saturating_sub(1),
            _ => return Ok(Vec::new()),
        };
        Ok(counts.iter().copied().map(segments).collect())
    }

    /// The `varying` data size of curves with the vertex `counts`, under the
    /// `type`, `wrap` and `basis` read at `time` (C++
    /// `_ComputeVaryingDataSize`).
    fn varying_data_size_of(&self, counts: &[i32], time: Option<usd::TimeCode>) -> Result<usize> {
        use CurveBasis::{Bezier, Bspline, CatmullRom};
        use CurveType::{Cubic, Linear};

        let topology = self.topology(time)?;
        // Pinned curves take no values for the segments pinning adds, so they
        // size as nonperiodic ones do, and any other wrap sizes as periodic.
        let open = matches!(topology.wrap, Some(CurveWrap::Nonperiodic | CurveWrap::Pinned));
        let values: fn(i32) -> i32 = match (topology.curve_type, open, topology.basis) {
            (Some(Linear), true, _) => |n| n,
            (Some(Linear), false, _) => |n| n.saturating_add(1),
            (Some(Cubic), true, Some(Bezier)) => |n| (n.saturating_sub(4) / BEZIER_VSTEP).max(0) + 2,
            (Some(Cubic), false, Some(Bezier)) => |n| n / BEZIER_VSTEP,
            (Some(Cubic), true, Some(Bspline | CatmullRom)) => |n| n.saturating_sub(4).max(0) + 2,
            (Some(Cubic), false, Some(Bspline | CatmullRom)) => |n| n,
            _ => return Ok(0),
        };
        Ok(counts.iter().map(|&n| non_negative(values(n))).sum())
    }

    /// The `type`, `wrap` and `basis` of the curves at `time`.
    fn topology(&self, time: Option<usd::TimeCode>) -> Result<Topology> {
        // Each is read as a token at `time`: one that names no type, wrap or
        // basis is topology no formula covers, which sizes as nothing.
        let curve_type = self.type_attr().get_at::<tf::Token>(time)?;
        let wrap = self.wrap_attr().get_at::<tf::Token>(time)?;
        let basis = self.basis_attr().get_at::<tf::Token>(time)?;
        Ok(Topology {
            complete: curve_type.is_some() && wrap.is_some() && basis.is_some(),
            curve_type: curve_type.and_then(CurveType::from_token),
            wrap: wrap.and_then(CurveWrap::from_token),
            basis: basis.and_then(CurveBasis::from_token),
        })
    }
}

/// The points and tangents of hermite curves as two arrays of one length
/// (C++ `UsdGeomHermiteCurves::PointAndTangentArrays`), which is how a
/// `HermiteCurves` prim stores them: in `points` and `tangents`.
///
/// [`separate`](Self::separate) and [`interleave`](Self::interleave) convert
/// from and to the single array that alternates each point with its tangent.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct PointAndTangentArrays {
    points: Vec<gf::Vec3f>,
    tangents: Vec<gf::Vec3f>,
}

impl PointAndTangentArrays {
    /// Pair `points` with `tangents` (C++ `PointAndTangentArrays(points,
    /// tangents)`).
    ///
    /// Arrays of different lengths are [`SchemaError::UnpairedHermiteData`].
    pub fn new(points: Vec<gf::Vec3f>, tangents: Vec<gf::Vec3f>) -> Result<Self, SchemaError> {
        if points.len() != tangents.len() {
            return Err(SchemaError::UnpairedHermiteData {
                points: points.len(),
                tangents: tangents.len(),
            });
        }
        Ok(PointAndTangentArrays { points, tangents })
    }

    /// Split an array that alternates each point with its tangent (C++
    /// `Separate`).
    ///
    /// An array of odd length is [`SchemaError::UnpairedHermiteData`].
    pub fn separate(interleaved: &[gf::Vec3f]) -> Result<Self, SchemaError> {
        let pairs = interleaved.chunks_exact(2);
        if !pairs.remainder().is_empty() {
            return Err(SchemaError::UnpairedHermiteData {
                points: interleaved.len().div_ceil(2),
                tangents: interleaved.len() / 2,
            });
        }
        let (points, tangents) = pairs.map(|pair| (pair[0], pair[1])).unzip();
        Ok(PointAndTangentArrays { points, tangents })
    }

    /// One array alternating each point with its tangent (C++ `Interleave`).
    pub fn interleave(&self) -> Vec<gf::Vec3f> {
        let mut interleaved = Vec::with_capacity(2 * self.points.len());
        for (&point, &tangent) in self.points.iter().zip(&self.tangents) {
            interleaved.extend([point, tangent]);
        }
        interleaved
    }

    /// `true` when there are no points, and so no tangents (C++ `IsEmpty`).
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// The points (C++ `GetPoints`).
    pub fn points(&self) -> &[gf::Vec3f] {
        &self.points
    }

    /// The tangents, one for each point (C++ `GetTangents`).
    pub fn tangents(&self) -> &[gf::Vec3f] {
        &self.tangents
    }
}

/// The topology attributes of a `BasisCurves` at one time, each `None`
/// where it reads no value or a token that names none of its values.
struct Topology {
    curve_type: Option<CurveType>,
    wrap: Option<CurveWrap>,
    basis: Option<CurveBasis>,
    /// Whether `type`, `wrap` and `basis` each read a value.
    complete: bool,
}

/// How many vertices apart consecutive segments of a cubic `bezier` curve
/// start (C++ `_GetVStepForBasis`).
const BEZIER_VSTEP: i32 = 3;

/// The `vertex` data size of curves with the vertex `counts` (C++
/// `_ComputeVertexDataSize`).
fn vertex_data_size_of(counts: &[i32]) -> usize {
    counts.iter().map(|&n| non_negative(n)).sum()
}

/// `n` as a size, where a negative count is zero.
pub(super) fn non_negative(n: i32) -> usize {
    usize::try_from(n).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, tf};

    use super::{CurvesExt, PointAndTangentArrays};
    use crate::SchemaError;
    use crate::geom::{BasisCurves, BasisCurvesSchema, CurveBasis, CurveType, CurveWrap, CurvesSchema, Interpolation};
    use crate::geom::{HermiteCurves, Mesh, PointBasedExt, PointBasedSchema};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// A `BasisCurves` at `path` with the topology given.
    fn curves(
        stage: &usd::Stage,
        path: &str,
        curve_type: CurveType,
        wrap: CurveWrap,
        basis: CurveBasis,
        counts: &[i32],
    ) -> Result<BasisCurves> {
        let curves = BasisCurves::define(stage, path)?;
        curves.create_type_attr()?.set(curve_type)?;
        curves.create_wrap_attr()?.set(wrap)?;
        curves.create_basis_attr()?.set(basis)?;
        curves.create_curve_vertex_counts_attr()?.set(counts.to_vec())?;
        Ok(curves)
    }

    /// The `/BezierCubic` prim of C++ `testUsdGeomBasisCurves`: each data
    /// size, and the interpolation a primvar of that size has.
    #[test]
    fn interpolation_for_size() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let c = BasisCurves::define(&stage, "/BezierCubic")?;
        c.create_basis_attr()?.set(CurveBasis::Bezier)?;
        c.create_type_attr()?.set(CurveType::Cubic)?;
        c.create_curve_vertex_counts_attr()?.set(vec![5, 5])?;

        assert_eq!(c.uniform_data_size(None)?, 2);
        assert_eq!(c.varying_data_size(None)?, 4);
        assert_eq!(c.vertex_data_size(None)?, 10);
        for (n, expected) in [
            (1, Some(Interpolation::Constant)),
            (2, Some(Interpolation::Uniform)),
            (4, Some(Interpolation::Varying)),
            (10, Some(Interpolation::Vertex)),
            (100, None),
            (0, None),
        ] {
            assert_eq!(c.interpolation_for_size(n, None)?, expected, "{n}");
        }
        Ok(())
    }

    /// Varying data is sized by segment ends, which the type, the wrap and
    /// the basis each change.
    #[test]
    fn varying_data_size() -> Result {
        use CurveBasis::{Bezier, Bspline, Hermite};
        use CurveType::{Cubic, Linear};
        use CurveWrap::{Nonperiodic, Periodic, Pinned};

        let stage = crate::tests::stage("anon.usda")?;
        for (index, (curve_type, wrap, basis, counts, expected)) in [
            (Linear, Nonperiodic, Bezier, &[2, 3][..], 5),
            (Linear, Pinned, Bezier, &[2, 3], 5),
            (Linear, Periodic, Bezier, &[2, 3], 7),
            (Cubic, Nonperiodic, Bezier, &[4, 7, 10], 9),
            (Cubic, Pinned, Bspline, &[4, 6], 6),
            (Cubic, Periodic, Bezier, &[6, 9], 5),
            (Cubic, Periodic, Bspline, &[6, 9], 15),
            // Fewer vertices than a cubic segment needs is one segment.
            (Cubic, Nonperiodic, Bspline, &[2, 0, -3], 6),
            (Cubic, Nonperiodic, Hermite, &[4, 4], 0),
        ]
        .into_iter()
        .enumerate()
        {
            let c = curves(&stage, &format!("/C{index}"), curve_type, wrap, basis, counts)?;
            assert_eq!(
                c.varying_data_size(None)?,
                expected,
                "{curve_type:?} {wrap:?} {basis:?} {counts:?}"
            );
        }
        Ok(())
    }

    /// The vertex-count cases of C++ `testUsdGeomBasisCurves`
    /// `test_ComputeCurveCount`: unset, blocked, empty, sampled, and sampled
    /// over a default.
    #[test]
    fn curve_count() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let unset = BasisCurves::define(&stage, "/Unset")?;
        let blocked = BasisCurves::define(&stage, "/Blocked")?;
        blocked.create_curve_vertex_counts_attr()?.block()?;
        let empty = BasisCurves::define(&stage, "/Empty")?;
        empty.create_curve_vertex_counts_attr()?.set(Vec::<i32>::new())?;
        let sampled = BasisCurves::define(&stage, "/Sampled")?;
        sampled
            .create_curve_vertex_counts_attr()?
            .set_at(vec![4, 4, 4], usd::TimeCode::new(1.0))?;
        let both = BasisCurves::define(&stage, "/Both")?;
        both.create_curve_vertex_counts_attr()?
            .set(vec![4, 4, 4, 4])?
            .set_at(vec![4, 4, 4, 4, 4], usd::TimeCode::new(1.0))?;

        for (schema, earliest, default) in [
            (&unset, 0, 0),
            (&blocked, 0, 0),
            (&empty, 0, 0),
            (&sampled, 3, 0),
            (&both, 5, 4),
        ] {
            assert_eq!(
                schema.curve_count(usd::TimeCode::EARLIEST)?,
                earliest,
                "{}",
                schema.path()
            );
            assert_eq!(schema.curve_count(None)?, default, "{}", schema.path());
        }
        Ok(())
    }

    /// The segment counts of C++ `testUsdGeomBasisCurves`
    /// `test_ComputeSegmentCount`.
    #[test]
    fn segment_counts() -> Result {
        use CurveBasis::{Bezier, Bspline, CatmullRom};
        use CurveType::{Cubic, Linear};
        use CurveWrap::{Nonperiodic, Periodic, Pinned};

        let stage = crate::tests::stage("anon.usda")?;
        for (index, (curve_type, wrap, basis, counts, expected)) in [
            (Linear, Nonperiodic, Bezier, &[2, 3, 2, 5][..], &[1, 2, 1, 4][..]),
            (Linear, Periodic, Bezier, &[3, 7], &[3, 7]),
            (Cubic, Nonperiodic, Bezier, &[4, 7, 10, 4, 7], &[1, 2, 3, 1, 2]),
            (Cubic, Nonperiodic, Bspline, &[5, 4, 6, 7], &[2, 1, 3, 4]),
            (Cubic, Periodic, Bezier, &[6, 9, 6], &[2, 3, 2]),
            (Cubic, Periodic, Bspline, &[6, 9, 6], &[6, 9, 6]),
            (Cubic, Pinned, CatmullRom, &[2, 3, 2, 5], &[1, 2, 1, 4]),
            (Cubic, Pinned, Bezier, &[4, 7, 10, 4, 7], &[1, 2, 3, 1, 2]),
        ]
        .into_iter()
        .enumerate()
        {
            let c = curves(&stage, &format!("/C{index}"), curve_type, wrap, basis, counts)?;
            assert_eq!(
                c.segment_counts(usd::TimeCode::EARLIEST)?,
                expected,
                "{curve_type:?} {wrap:?} {basis:?}"
            );
        }
        Ok(())
    }

    /// Topology the table has no row for, or that is not there to read,
    /// answers no segment counts.
    #[test]
    fn segment_counts_invalid() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let hermite = curves(
            &stage,
            "/Hermite",
            CurveType::Cubic,
            CurveWrap::Nonperiodic,
            CurveBasis::Hermite,
            &[4, 4],
        )?;
        assert!(hermite.segment_counts(None)?.is_empty());

        let bogus = curves(
            &stage,
            "/Bogus",
            CurveType::Linear,
            CurveWrap::Periodic,
            CurveBasis::Bezier,
            &[3],
        )?;
        bogus.wrap_attr().set(tf::Token::from("bogus"))?;
        assert!(bogus.segment_counts(None)?.is_empty());

        let unset = BasisCurves::define(&stage, "/Unset")?;
        assert!(unset.segment_counts(None)?.is_empty());

        // A mesh declares no curve topology, so there is nothing to read.
        let mesh = Mesh::define(&stage, "/Mesh")?;
        let as_curves = BasisCurves::from_prim_unchecked(mesh.prim().clone());
        as_curves.create_curve_vertex_counts_attr()?.set(vec![3])?;
        assert!(as_curves.segment_counts(None)?.is_empty());
        Ok(())
    }

    /// `normals` and `widths` are per vertex until a layer says otherwise
    /// (C++ `testUsdGeomSchemata`), and each setter is one edit.
    #[test]
    fn interpolation_fallback_vertex() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let curves = BasisCurves::define(&stage, "/Curves")?;
        assert_eq!(curves.normals_interpolation()?, Interpolation::Vertex);
        assert_eq!(curves.widths_interpolation()?, Interpolation::Vertex);

        curves.create_widths_attr()?.set(vec![1.0_f32])?;
        let commits = crate::tests::commits(&stage);
        curves.set_normals_interpolation(Interpolation::Uniform)?;
        curves.set_widths_interpolation(Interpolation::Constant)?;
        assert_eq!(commits.get(), 2);
        // The authored widths are left as they were.
        assert_eq!(CurvesSchema::widths(&curves)?, Some(vec![1.0]));
        assert_eq!(curves.normals_interpolation()?, Interpolation::Uniform);
        assert_eq!(curves.widths_interpolation()?, Interpolation::Constant);
        assert!(!curves.normals_attr().has_authored_value()?);

        // The setters reach every subclass view.
        let hermite = HermiteCurves::define(&stage, "/Hermite")?;
        hermite.set_widths_interpolation(Interpolation::Varying)?;
        assert_eq!(hermite.widths_interpolation()?, Interpolation::Varying);
        let mesh = Mesh::define(&stage, "/Mesh")?;
        mesh.set_normals_interpolation(Interpolation::FaceVarying)?;
        assert_eq!(mesh.normals_interpolation()?, Interpolation::FaceVarying);
        Ok(())
    }

    /// C++ `testUsdGeomHermiteCurves` `testPointAndTangents`.
    #[test]
    fn point_and_tangents() -> Result {
        let mismatched = PointAndTangentArrays::new(
            vec![gf::vec3f(1.0, 2.0, 3.0)],
            vec![gf::vec3f(1.0, 2.0, 3.0), gf::vec3f(4.0, 5.0, 6.0)],
        );
        assert!(matches!(
            mismatched,
            Err(SchemaError::UnpairedHermiteData { points: 1, tangents: 2 })
        ));

        let empty = PointAndTangentArrays::default();
        assert!(empty.is_empty() && empty.points().is_empty() && empty.tangents().is_empty());

        let points = vec![gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(-1.0, 0.0, 0.0)];
        let tangents = vec![gf::vec3f(1.0, 2.0, 3.0), gf::vec3f(4.0, 5.0, 6.0)];
        let arrays = PointAndTangentArrays::new(points.clone(), tangents.clone())?;
        assert!(!arrays.is_empty());
        assert_eq!(arrays.points(), points);
        assert_eq!(arrays.tangents(), tangents);

        assert_eq!(arrays, PointAndTangentArrays::new(points, tangents)?);
        assert_ne!(arrays, empty);
        Ok(())
    }

    /// C++ `testUsdGeomHermiteCurves` `testInterleave` and `testSeparate`.
    #[test]
    fn interleave_separate() -> Result {
        let arrays = PointAndTangentArrays::new(
            vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(2.0, 0.0, 0.0)],
            vec![gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 1.0, 0.0)],
        )?;
        let interleaved = [
            gf::vec3f(0.0, 0.0, 0.0),
            gf::vec3f(1.0, 0.0, 0.0),
            gf::vec3f(2.0, 0.0, 0.0),
            gf::vec3f(0.0, 1.0, 0.0),
        ];
        assert_eq!(arrays.interleave(), interleaved);
        assert!(PointAndTangentArrays::default().interleave().is_empty());

        assert_eq!(PointAndTangentArrays::separate(&interleaved)?, arrays);
        assert!(PointAndTangentArrays::separate(&[])?.is_empty());
        assert!(matches!(
            PointAndTangentArrays::separate(&interleaved[..3]),
            Err(SchemaError::UnpairedHermiteData { points: 2, tangents: 1 })
        ));
        Ok(())
    }
}
