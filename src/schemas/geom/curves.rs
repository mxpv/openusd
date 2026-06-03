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

use super::internal::{create, create_uniform_token, get_typed};
use super::tokens as tok;
use super::{impl_geom_schema, Boundable, Gprim, Imageable, PointBased, Xformable};

/// A batch of curves sharing one prim (C++ `UsdGeomCurves`) — a
/// [`PointBased`] whose `points` are partitioned into individual curves by
/// `curveVertexCounts`. Adds the shared `curveVertexCounts` / `widths`
/// attributes; the basis / knot data lives on the concrete subclasses.
pub trait Curves: PointBased {
    /// `curveVertexCounts` attribute handle — CV count per curve, `int[]`
    /// (C++ `GetCurveVertexCountsAttr`).
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

    /// `widths` attribute handle — per-CV width, `float[]`
    /// (C++ `GetWidthsAttr`). Set its `interpolation` metadata (`vertex` /
    /// `varying` / `constant`) to describe how the values map to the curve.
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

    /// `type` attribute handle — `linear` / `cubic` (C++ `GetTypeAttr`).
    pub fn type_attr(&self) -> Attribute {
        self.attribute(tok::A_TYPE)
    }

    /// Author `type` (`uniform token`) (C++ `CreateTypeAttr`).
    pub fn create_type_attr(&self) -> Result<Attribute> {
        create_uniform_token(self, tok::A_TYPE)
    }

    /// `basis` attribute handle — `bezier` / `bspline` / `catmullRom` /
    /// `hermite` (C++ `GetBasisAttr`).
    pub fn basis_attr(&self) -> Attribute {
        self.attribute(tok::A_BASIS)
    }

    /// Author `basis` (`uniform token`) (C++ `CreateBasisAttr`).
    pub fn create_basis_attr(&self) -> Result<Attribute> {
        create_uniform_token(self, tok::A_BASIS)
    }

    /// `wrap` attribute handle — `nonperiodic` / `periodic` / `pinned`
    /// (C++ `GetWrapAttr`).
    pub fn wrap_attr(&self) -> Attribute {
        self.attribute(tok::A_WRAP)
    }

    /// Author `wrap` (`uniform token`) (C++ `CreateWrapAttr`).
    pub fn create_wrap_attr(&self) -> Result<Attribute> {
        create_uniform_token(self, tok::A_WRAP)
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

    /// `order` attribute handle — per-curve order (degree + 1), `int[]`
    /// (C++ `GetOrderAttr`).
    pub fn order_attr(&self) -> Attribute {
        self.attribute(tok::A_ORDER)
    }

    /// Author `order` (`int[]`) (C++ `CreateOrderAttr`).
    pub fn create_order_attr(&self) -> Result<Attribute> {
        create(self, tok::A_ORDER, "int[]")
    }

    /// `knots` attribute handle — concatenated knot vectors, `double[]`
    /// (C++ `GetKnotsAttr`).
    pub fn knots_attr(&self) -> Attribute {
        self.attribute(tok::A_KNOTS)
    }

    /// Author `knots` (`double[]`) (C++ `CreateKnotsAttr`).
    pub fn create_knots_attr(&self) -> Result<Attribute> {
        create(self, tok::A_KNOTS, "double[]")
    }

    /// `ranges` attribute handle — per-curve `(uMin, uMax)`, `double2[]`
    /// (C++ `GetRangesAttr`).
    pub fn ranges_attr(&self) -> Attribute {
        self.attribute(tok::A_RANGES)
    }

    /// Author `ranges` (`double2[]`) (C++ `CreateRangesAttr`).
    pub fn create_ranges_attr(&self) -> Result<Attribute> {
        create(self, tok::A_RANGES, "double2[]")
    }

    /// `pointWeights` attribute handle — rational CV weights, `double[]`
    /// (C++ `GetPointWeightsAttr`).
    pub fn point_weights_attr(&self) -> Attribute {
        self.attribute(tok::A_POINT_WEIGHTS)
    }

    /// Author `pointWeights` (`double[]`) (C++ `CreatePointWeightsAttr`).
    pub fn create_point_weights_attr(&self) -> Result<Attribute> {
        create(self, tok::A_POINT_WEIGHTS, "double[]")
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

    /// `tangents` attribute handle — per-CV tangent, `vector3f[]`
    /// (C++ `GetTangentsAttr`).
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

    /// `uVertexCount` attribute handle (C++ `GetUVertexCountAttr`).
    pub fn u_vertex_count_attr(&self) -> Attribute {
        self.attribute(tok::A_U_VERTEX_COUNT)
    }

    /// Author `uVertexCount` (`int`) (C++ `CreateUVertexCountAttr`).
    pub fn create_u_vertex_count_attr(&self) -> Result<Attribute> {
        create(self, tok::A_U_VERTEX_COUNT, "int")
    }

    /// `vVertexCount` attribute handle (C++ `GetVVertexCountAttr`).
    pub fn v_vertex_count_attr(&self) -> Attribute {
        self.attribute(tok::A_V_VERTEX_COUNT)
    }

    /// Author `vVertexCount` (`int`) (C++ `CreateVVertexCountAttr`).
    pub fn create_v_vertex_count_attr(&self) -> Result<Attribute> {
        create(self, tok::A_V_VERTEX_COUNT, "int")
    }

    /// `uOrder` attribute handle (C++ `GetUOrderAttr`).
    pub fn u_order_attr(&self) -> Attribute {
        self.attribute(tok::A_U_ORDER)
    }

    /// Author `uOrder` (`int`) (C++ `CreateUOrderAttr`).
    pub fn create_u_order_attr(&self) -> Result<Attribute> {
        create(self, tok::A_U_ORDER, "int")
    }

    /// `vOrder` attribute handle (C++ `GetVOrderAttr`).
    pub fn v_order_attr(&self) -> Attribute {
        self.attribute(tok::A_V_ORDER)
    }

    /// Author `vOrder` (`int`) (C++ `CreateVOrderAttr`).
    pub fn create_v_order_attr(&self) -> Result<Attribute> {
        create(self, tok::A_V_ORDER, "int")
    }

    /// `uKnots` attribute handle — `double[]` (C++ `GetUKnotsAttr`).
    pub fn u_knots_attr(&self) -> Attribute {
        self.attribute(tok::A_U_KNOTS)
    }

    /// Author `uKnots` (`double[]`) (C++ `CreateUKnotsAttr`).
    pub fn create_u_knots_attr(&self) -> Result<Attribute> {
        create(self, tok::A_U_KNOTS, "double[]")
    }

    /// `vKnots` attribute handle — `double[]` (C++ `GetVKnotsAttr`).
    pub fn v_knots_attr(&self) -> Attribute {
        self.attribute(tok::A_V_KNOTS)
    }

    /// Author `vKnots` (`double[]`) (C++ `CreateVKnotsAttr`).
    pub fn create_v_knots_attr(&self) -> Result<Attribute> {
        create(self, tok::A_V_KNOTS, "double[]")
    }

    /// `uForm` attribute handle — `open` / `closed` / `periodic`
    /// (C++ `GetUFormAttr`).
    pub fn u_form_attr(&self) -> Attribute {
        self.attribute(tok::A_U_FORM)
    }

    /// Author `uForm` (`uniform token`) (C++ `CreateUFormAttr`).
    pub fn create_u_form_attr(&self) -> Result<Attribute> {
        create_uniform_token(self, tok::A_U_FORM)
    }

    /// `vForm` attribute handle — `open` / `closed` / `periodic`
    /// (C++ `GetVFormAttr`).
    pub fn v_form_attr(&self) -> Attribute {
        self.attribute(tok::A_V_FORM)
    }

    /// Author `vForm` (`uniform token`) (C++ `CreateVFormAttr`).
    pub fn create_v_form_attr(&self) -> Result<Attribute> {
        create_uniform_token(self, tok::A_V_FORM)
    }

    /// `uRange` attribute handle — `(uMin, uMax)`, `double2`
    /// (C++ `GetURangeAttr`).
    pub fn u_range_attr(&self) -> Attribute {
        self.attribute(tok::A_U_RANGE)
    }

    /// Author `uRange` (`double2`) (C++ `CreateURangeAttr`).
    pub fn create_u_range_attr(&self) -> Result<Attribute> {
        create(self, tok::A_U_RANGE, "double2")
    }

    /// `vRange` attribute handle — `(vMin, vMax)`, `double2`
    /// (C++ `GetVRangeAttr`).
    pub fn v_range_attr(&self) -> Attribute {
        self.attribute(tok::A_V_RANGE)
    }

    /// Author `vRange` (`double2`) (C++ `CreateVRangeAttr`).
    pub fn create_v_range_attr(&self) -> Result<Attribute> {
        create(self, tok::A_V_RANGE, "double2")
    }

    /// `pointWeights` attribute handle — rational CV weights, `double[]`
    /// (C++ `GetPointWeightsAttr`).
    pub fn point_weights_attr(&self) -> Attribute {
        self.attribute(tok::A_POINT_WEIGHTS)
    }

    /// Author `pointWeights` (`double[]`) (C++ `CreatePointWeightsAttr`).
    pub fn create_point_weights_attr(&self) -> Result<Attribute> {
        create(self, tok::A_POINT_WEIGHTS, "double[]")
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
        c.create_points_attr()?
            .set(sdf::Value::Vec3fVec(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0]]))?;
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
        c.create_order_attr()?.set(sdf::Value::IntVec(vec![4]))?;
        c.create_knots_attr()?
            .set(sdf::Value::DoubleVec(vec![0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0]))?;
        c.create_point_weights_attr()?
            .set(sdf::Value::DoubleVec(vec![1.0, 1.0, 1.0, 1.0]))?;

        let c = NurbsCurves::get(&stage, "/N")?.expect("NurbsCurves");
        assert_eq!(c.order_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
        assert_eq!(
            c.point_weights_attr()
                .get()?
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
        c.create_points_attr()?
            .set(sdf::Value::Vec3fVec(vec![[0.0, 0.0, 0.0], [1.0, 0.0, 0.0]]))?;
        c.create_curve_vertex_counts_attr()?.set(sdf::Value::IntVec(vec![2]))?;
        c.create_tangents_attr()?
            .set(sdf::Value::Vec3fVec(vec![[1.0, 0.0, 0.0], [1.0, 0.0, 0.0]]))?;

        let c = HermiteCurves::get(&stage, "/H")?.expect("HermiteCurves");
        assert_eq!(
            c.tangents_attr()
                .get()?
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
