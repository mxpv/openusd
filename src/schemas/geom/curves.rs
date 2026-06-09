//! Curve and NURBS-patch views — `BasisCurves`, `NurbsCurves`,
//! `HermiteCurves`, and `NurbsPatch`.
//!
//! The first three are [`Curves`] (a batch of curves sharing one prim, sized
//! by `curveVertexCounts`); `NurbsPatch` is a [`PointBased`] surface. Each is
//! a concrete view over a [`Prim`] mirroring the matching C++ `UsdGeom`
//! class. Attribute getters return a handle whose `get()` yields the authored
//! value (or `None`).

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, SchemaBase, SchemaKind, Stage};

use super::tokens as tok;
use super::{impl_geom_schema, Boundable, Gprim, Imageable, PointBased, Xformable};
use crate::schemas::common::get_typed;

/// A batch of curves sharing one prim (C++ `UsdGeomCurves`) — a
/// [`PointBased`] whose `points` are partitioned into individual curves by
/// `curveVertexCounts`. Adds the shared `curveVertexCounts` / `widths`
/// attributes; the basis / knot data lives on the concrete subclasses.
pub trait Curves: PointBased {
    /// The number of vertices in each curve in the batch; its length is the curve count and its
    /// sum is the total number of control points partitioning `points`.
    /// C++ `UsdGeomCurves::GetCurveVertexCountsAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    fn curve_vertex_counts_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_CURVE_VERTEX_COUNTS)
    }

    /// Author `curveVertexCounts` (`int[]`), returning its handle
    /// (C++ `CreateCurveVertexCountsAttr`).
    fn create_curve_vertex_counts_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_CURVE_VERTEX_COUNTS, "int[]")?
            .set_custom(false)?)
    }

    /// The width (diameter) of the curves, in object space; set its `interpolation` metadata
    /// (`constant` / `varying` / `vertex`) to describe how the values map to the curve.
    /// C++ `UsdGeomCurves::GetWidthsAttr`.
    ///
    /// Type `float[]`. Fetch with `get::<Vec<f32>>()?`.
    fn widths_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_WIDTHS)
    }

    /// Author `widths` (`float[]`), returning its handle
    /// (C++ `CreateWidthsAttr`).
    fn create_widths_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_WIDTHS, "float[]")?
            .set_custom(false)?)
    }
}

/// Piecewise-polynomial curves with a shared basis (C++ `UsdGeomBasisCurves`).
/// Intrinsic attributes: `type` (`linear` / `cubic`), `basis`, `wrap`.
#[derive(Clone, derive_more::Deref)]
pub struct BasisCurves(Prim);

impl BasisCurves {
    /// Author a `def BasisCurves` prim at `path`
    /// (C++ `UsdGeomBasisCurves::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_BASIS_CURVES)?))
    }

    /// Wrap `path` as a `BasisCurves` if it is typed `BasisCurves`
    /// (C++ `UsdGeomBasisCurves::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_BASIS_CURVES).map(|o| o.map(Self))
    }

    /// Whether the curves are `linear` (joining vertices with straight segments) or `cubic`
    /// (interpolated by the chosen `basis`).
    /// C++ `UsdGeomBasisCurves::GetTypeAttr`.
    ///
    /// Type `token` (see [`CurveType`](super::CurveType)). Fetch with `get::<Token>()?`.
    pub fn type_attr(&self) -> Attribute {
        self.attribute(tok::A_TYPE)
    }

    /// Author `type` (`uniform token`) (C++ `CreateTypeAttr`).
    pub fn create_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_TYPE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The basis matrix that interpolates the control points of `cubic` curves: `bezier`,
    /// `bspline`, `catmullRom`, or `hermite` (ignored when `type` is `linear`).
    /// C++ `UsdGeomBasisCurves::GetBasisAttr`.
    ///
    /// Type `token` (see [`CurveBasis`](super::CurveBasis)). Fetch with `get::<Token>()?`.
    pub fn basis_attr(&self) -> Attribute {
        self.attribute(tok::A_BASIS)
    }

    /// Author `basis` (`uniform token`) (C++ `CreateBasisAttr`).
    pub fn create_basis_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_BASIS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// How the curve's endpoints are treated: `nonperiodic` (open), `periodic` (the last vertices
    /// connect back to the first to close the loop), or `pinned` (the curve passes through its
    /// first and last control points).
    /// C++ `UsdGeomBasisCurves::GetWrapAttr`.
    ///
    /// Type `token` (see [`CurveWrap`](super::CurveWrap)). Fetch with `get::<Token>()?`.
    pub fn wrap_attr(&self) -> Attribute {
        self.attribute(tok::A_WRAP)
    }

    /// Author `wrap` (`uniform token`) (C++ `CreateWrapAttr`).
    pub fn create_wrap_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_WRAP, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_geom_schema!(curves BasisCurves);

/// NURBS curves (C++ `UsdGeomNurbsCurves`). Adds per-curve `order`, the
/// concatenated `knots`, parameter `ranges`, and rational `pointWeights`.
#[derive(Clone, derive_more::Deref)]
pub struct NurbsCurves(Prim);

impl NurbsCurves {
    /// Author a `def NurbsCurves` prim at `path`
    /// (C++ `UsdGeomNurbsCurves::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_NURBS_CURVES)?))
    }

    /// Wrap `path` as a `NurbsCurves` if it is typed `NurbsCurves`
    /// (C++ `UsdGeomNurbsCurves::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_NURBS_CURVES).map(|o| o.map(Self))
    }

    /// The order of each curve, where order equals degree plus one (e.g. 4 for a cubic curve); one
    /// value per curve in the batch.
    /// C++ `UsdGeomNurbsCurves::GetOrderAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn order_attr(&self) -> Attribute {
        self.attribute(tok::A_ORDER)
    }

    /// Author `order` (`int[]`) (C++ `CreateOrderAttr`).
    pub fn create_order_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_ORDER, "int[]")?.set_custom(false)?)
    }

    /// The knot vectors for all curves concatenated end to end; each curve contributes
    /// `curveVertexCount + order` knots in non-decreasing order.
    /// C++ `UsdGeomNurbsCurves::GetKnotsAttr`.
    ///
    /// Type `double[]`. Fetch with `get::<Vec<f64>>()?`.
    pub fn knots_attr(&self) -> Attribute {
        self.attribute(tok::A_KNOTS)
    }

    /// Author `knots` (`double[]`) (C++ `CreateKnotsAttr`).
    pub fn create_knots_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_KNOTS, "double[]")?.set_custom(false)?)
    }

    /// The parametric range `(uMin, uMax)` over which each curve is evaluated, one pair per curve;
    /// the curve is only valid over this subset of its knot range.
    /// C++ `UsdGeomNurbsCurves::GetRangesAttr`.
    ///
    /// Type `double2[]`. Fetch with `get::<Vec<f64>>()?`.
    pub fn ranges_attr(&self) -> Attribute {
        self.attribute(tok::A_RANGES)
    }

    /// Author `ranges` (`double2[]`) (C++ `CreateRangesAttr`).
    pub fn create_ranges_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_RANGES, "double2[]")?.set_custom(false)?)
    }

    /// The rational weight of each control point, making the geometry a rational NURBS; one value
    /// per point and parallel to `points`. Omit (or leave all 1.0) for a non-rational curve.
    /// C++ `UsdGeomNurbsCurves::GetPointWeightsAttr`.
    ///
    /// Type `double[]`. Fetch with `get::<Vec<f64>>()?`.
    pub fn point_weights_attr(&self) -> Attribute {
        self.attribute(tok::A_POINT_WEIGHTS)
    }

    /// Author `pointWeights` (`double[]`) (C++ `CreatePointWeightsAttr`).
    pub fn create_point_weights_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_POINT_WEIGHTS, "double[]")?
            .set_custom(false)?)
    }
}

impl_geom_schema!(curves NurbsCurves);

/// Cubic-Hermite curves (C++ `UsdGeomHermiteCurves`). Each CV carries both a
/// position (`points`, from [`PointBased`]) and a `tangents` vector.
#[derive(Clone, derive_more::Deref)]
pub struct HermiteCurves(Prim);

impl HermiteCurves {
    /// Author a `def HermiteCurves` prim at `path`
    /// (C++ `UsdGeomHermiteCurves::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_HERMITE_CURVES)?))
    }

    /// Wrap `path` as a `HermiteCurves` if it is typed `HermiteCurves`
    /// (C++ `UsdGeomHermiteCurves::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_HERMITE_CURVES).map(|o| o.map(Self))
    }

    /// The outgoing tangent vector at each control point, parallel to `points`; together a point
    /// and its tangent define the cubic-Hermite segment leaving that vertex.
    /// C++ `UsdGeomHermiteCurves::GetTangentsAttr`.
    ///
    /// Type `vector3f[]`. Fetch with `get::<Vec<gf::Vec3f>>()?`.
    pub fn tangents_attr(&self) -> Attribute {
        self.attribute(tok::A_TANGENTS)
    }

    /// Author `tangents` (`vector3f[]`) (C++ `CreateTangentsAttr`).
    pub fn create_tangents_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_TANGENTS, "vector3f[]")?
            .set_custom(false)?)
    }
}

impl_geom_schema!(curves HermiteCurves);

/// A NURBS surface patch (C++ `UsdGeomNurbsPatch`). A [`PointBased`] control
/// net laid out row-major (`P[i, j] = points[i * vVertexCount + j]`) with
/// independent U / V order, knot vectors, parameter ranges, and forms.
#[derive(Clone, derive_more::Deref)]
pub struct NurbsPatch(Prim);

impl NurbsPatch {
    /// Author a `def NurbsPatch` prim at `path`
    /// (C++ `UsdGeomNurbsPatch::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_NURBS_PATCH)?))
    }

    /// Wrap `path` as a `NurbsPatch` if it is typed `NurbsPatch`
    /// (C++ `UsdGeomNurbsPatch::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_NURBS_PATCH).map(|o| o.map(Self))
    }

    /// The number of control points along the U (row) direction of the control net; `points` is
    /// laid out row-major as `P[i, j] = points[i * vVertexCount + j]`.
    /// C++ `UsdGeomNurbsPatch::GetUVertexCountAttr`.
    ///
    /// Type `int`. Fetch with `get::<i32>()?`.
    pub fn u_vertex_count_attr(&self) -> Attribute {
        self.attribute(tok::A_U_VERTEX_COUNT)
    }

    /// Author `uVertexCount` (`int`) (C++ `CreateUVertexCountAttr`).
    pub fn create_u_vertex_count_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_U_VERTEX_COUNT, "int")?.set_custom(false)?)
    }

    /// The number of control points along the V (column) direction of the control net; the inner
    /// stride of the row-major `points` layout.
    /// C++ `UsdGeomNurbsPatch::GetVVertexCountAttr`.
    ///
    /// Type `int`. Fetch with `get::<i32>()?`.
    pub fn v_vertex_count_attr(&self) -> Attribute {
        self.attribute(tok::A_V_VERTEX_COUNT)
    }

    /// Author `vVertexCount` (`int`) (C++ `CreateVVertexCountAttr`).
    pub fn create_v_vertex_count_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_V_VERTEX_COUNT, "int")?.set_custom(false)?)
    }

    /// The order of the surface in the U direction, equal to degree plus one (e.g. 4 for bicubic
    /// in U).
    /// C++ `UsdGeomNurbsPatch::GetUOrderAttr`.
    ///
    /// Type `int`. Fetch with `get::<i32>()?`.
    pub fn u_order_attr(&self) -> Attribute {
        self.attribute(tok::A_U_ORDER)
    }

    /// Author `uOrder` (`int`) (C++ `CreateUOrderAttr`).
    pub fn create_u_order_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_U_ORDER, "int")?.set_custom(false)?)
    }

    /// The order of the surface in the V direction, equal to degree plus one.
    /// C++ `UsdGeomNurbsPatch::GetVOrderAttr`.
    ///
    /// Type `int`. Fetch with `get::<i32>()?`.
    pub fn v_order_attr(&self) -> Attribute {
        self.attribute(tok::A_V_ORDER)
    }

    /// Author `vOrder` (`int`) (C++ `CreateVOrderAttr`).
    pub fn create_v_order_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_V_ORDER, "int")?.set_custom(false)?)
    }

    /// The knot vector along the U direction; its length must be `uVertexCount + uOrder` and its
    /// values must be non-decreasing.
    /// C++ `UsdGeomNurbsPatch::GetUKnotsAttr`.
    ///
    /// Type `double[]`. Fetch with `get::<Vec<f64>>()?`.
    pub fn u_knots_attr(&self) -> Attribute {
        self.attribute(tok::A_U_KNOTS)
    }

    /// Author `uKnots` (`double[]`) (C++ `CreateUKnotsAttr`).
    pub fn create_u_knots_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_U_KNOTS, "double[]")?.set_custom(false)?)
    }

    /// The knot vector along the V direction; its length must be `vVertexCount + vOrder` and its
    /// values must be non-decreasing.
    /// C++ `UsdGeomNurbsPatch::GetVKnotsAttr`.
    ///
    /// Type `double[]`. Fetch with `get::<Vec<f64>>()?`.
    pub fn v_knots_attr(&self) -> Attribute {
        self.attribute(tok::A_V_KNOTS)
    }

    /// Author `vKnots` (`double[]`) (C++ `CreateVKnotsAttr`).
    pub fn create_v_knots_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_V_KNOTS, "double[]")?.set_custom(false)?)
    }

    /// The topological form of the surface in the U direction: `open`, `closed` (the surface
    /// meets itself), or `periodic` (it wraps around smoothly).
    /// C++ `UsdGeomNurbsPatch::GetUFormAttr`.
    ///
    /// Type `token` (see [`PatchForm`](super::PatchForm)). Fetch with `get::<Token>()?`.
    pub fn u_form_attr(&self) -> Attribute {
        self.attribute(tok::A_U_FORM)
    }

    /// Author `uForm` (`uniform token`) (C++ `CreateUFormAttr`).
    pub fn create_u_form_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_U_FORM, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The topological form of the surface in the V direction: `open`, `closed`, or `periodic`.
    /// C++ `UsdGeomNurbsPatch::GetVFormAttr`.
    ///
    /// Type `token` (see [`PatchForm`](super::PatchForm)). Fetch with `get::<Token>()?`.
    pub fn v_form_attr(&self) -> Attribute {
        self.attribute(tok::A_V_FORM)
    }

    /// Author `vForm` (`uniform token`) (C++ `CreateVFormAttr`).
    pub fn create_v_form_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_V_FORM, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The parametric range `(uMin, uMax)` over which the surface is evaluated in U; the patch is
    /// only valid over this subset of the `uKnots` range.
    /// C++ `UsdGeomNurbsPatch::GetURangeAttr`.
    ///
    /// Type `double2`. Fetch with `get::<Vec<f64>>()?`.
    pub fn u_range_attr(&self) -> Attribute {
        self.attribute(tok::A_U_RANGE)
    }

    /// Author `uRange` (`double2`) (C++ `CreateURangeAttr`).
    pub fn create_u_range_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_U_RANGE, "double2")?.set_custom(false)?)
    }

    /// The parametric range `(vMin, vMax)` over which the surface is evaluated in V; the patch is
    /// only valid over this subset of the `vKnots` range.
    /// C++ `UsdGeomNurbsPatch::GetVRangeAttr`.
    ///
    /// Type `double2`. Fetch with `get::<Vec<f64>>()?`.
    pub fn v_range_attr(&self) -> Attribute {
        self.attribute(tok::A_V_RANGE)
    }

    /// Author `vRange` (`double2`) (C++ `CreateVRangeAttr`).
    pub fn create_v_range_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_V_RANGE, "double2")?.set_custom(false)?)
    }

    /// The rational weight of each control point, making the surface a rational NURBS; one value
    /// per point and parallel to `points`. Omit (or leave all 1.0) for a non-rational patch.
    /// C++ `UsdGeomNurbsPatch::GetPointWeightsAttr`.
    ///
    /// Type `double[]`. Fetch with `get::<Vec<f64>>()?`.
    pub fn point_weights_attr(&self) -> Attribute {
        self.attribute(tok::A_POINT_WEIGHTS)
    }

    /// Author `pointWeights` (`double[]`) (C++ `CreatePointWeightsAttr`).
    pub fn create_point_weights_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_POINT_WEIGHTS, "double[]")?
            .set_custom(false)?)
    }
}

impl_geom_schema!(pointbased NurbsPatch);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basis_curves_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let c = BasisCurves::define(&stage, "/C")?;
        c.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
            [0.0_f32, 0.0, 0.0].into(),
            [1.0, 0.0, 0.0].into(),
        ]))?;
        c.create_curve_vertex_counts_attr()?.set(sdf::Value::IntVec(vec![2]))?;
        c.create_type_attr()?.set(sdf::Value::Token("linear".into()))?;
        c.create_widths_attr()?
            .set_metadata(tok::META_INTERPOLATION, sdf::Value::Token("vertex".into()))?
            .set(sdf::Value::FloatVec(vec![0.1, 0.1]))?;

        let c = BasisCurves::get(&stage, "/C")?.expect("BasisCurves");
        assert_eq!(c.curve_vertex_counts_attr().get()?, Some(sdf::Value::IntVec(vec![2])));
        assert_eq!(c.type_attr().get()?, Some(sdf::Value::Token("linear".into())));
        assert_eq!(
            c.widths_attr().get_metadata(tok::META_INTERPOLATION)?,
            Some(sdf::Value::Token("vertex".into()))
        );
        assert!(BasisCurves::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    #[test]
    fn nurbs_curves_attrs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let c = NurbsCurves::define(&stage, "/N")?;
        c.create_order_attr()?.set(vec![4])?;
        c.create_knots_attr()?
            .set(sdf::Value::DoubleVec(vec![0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0]))?;
        c.create_point_weights_attr()?.set(vec![1.0_f64, 1.0, 1.0, 1.0])?;

        let c = NurbsCurves::get(&stage, "/N")?.expect("NurbsCurves");
        assert_eq!(c.order_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
        assert_eq!(
            c.point_weights_attr()
                .get::<sdf::Value>()?
                .and_then(|v| v.try_as_double_vec())
                .map(|v| v.len()),
            Some(4)
        );
        Ok(())
    }

    #[test]
    fn hermite_curves_tangents() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let c = HermiteCurves::define(&stage, "/H")?;
        c.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
            [0.0_f32, 0.0, 0.0].into(),
            [1.0, 0.0, 0.0].into(),
        ]))?;
        c.create_curve_vertex_counts_attr()?.set(sdf::Value::IntVec(vec![2]))?;
        c.create_tangents_attr()?.set(sdf::Value::Vec3fVec(vec![
            [1.0_f32, 0.0, 0.0].into(),
            [1.0, 0.0, 0.0].into(),
        ]))?;

        let c = HermiteCurves::get(&stage, "/H")?.expect("HermiteCurves");
        assert_eq!(
            c.tangents_attr()
                .get::<sdf::Value>()?
                .and_then(|v| v.try_as_vec_3f_vec())
                .map(|v| v.len()),
            Some(2)
        );
        Ok(())
    }

    #[test]
    fn nurbs_patch_grid() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let p = NurbsPatch::define(&stage, "/P")?;
        p.create_u_vertex_count_attr()?.set(4_i32)?;
        p.create_v_vertex_count_attr()?.set(4_i32)?;
        p.create_u_form_attr()?.set(sdf::Value::Token("periodic".into()))?;

        let p = NurbsPatch::get(&stage, "/P")?.expect("NurbsPatch");
        assert_eq!(p.u_vertex_count_attr().get()?, Some(sdf::Value::Int(4)));
        assert_eq!(p.u_form_attr().get()?, Some(sdf::Value::Token("periodic".into())));
        Ok(())
    }
}
