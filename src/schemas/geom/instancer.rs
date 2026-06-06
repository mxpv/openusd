//! `UsdGeomPointInstancer` — vectorized instancing.
//!
//! A [`PointInstancer`] instances the prims targeted by its `prototypes`
//! relationship once per entry of the per-instance arrays (`protoIndices`
//! selects the prototype, `positions` / `orientations` / `scales` place it).
//! It is a [`Boundable`] (it has an `extent` and a transform) but not a
//! [`Gprim`], mirroring the C++ `UsdGeomPointInstancer : UsdGeomBoundable`.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, Relationship, SchemaBase, SchemaKind, Stage};

use super::tokens as tok;
use super::{impl_geom_schema, Boundable, Imageable, Xformable};
use crate::schemas::common::get_typed;

/// A vectorized-instancing prim (C++ `UsdGeomPointInstancer`).
#[derive(Clone, derive_more::Deref)]
pub struct PointInstancer(Prim);

impl PointInstancer {
    /// Author a `def PointInstancer` prim at `path`
    /// (C++ `UsdGeomPointInstancer::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_POINT_INSTANCER)?))
    }

    /// Wrap `path` as a `PointInstancer` if it is typed `PointInstancer`
    /// (C++ `UsdGeomPointInstancer::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_POINT_INSTANCER).map(|o| o.map(Self))
    }

    /// The relationship targeting the prototype prims to be instanced; its
    /// ordered targets are the prototypes that `protoIndices` selects per
    /// instance. Read the targets via `relationship_targets`.
    /// C++ `UsdGeomPointInstancer::GetPrototypesRel`.
    pub fn prototypes_rel(&self) -> Relationship {
        self.relationship(tok::REL_PROTOTYPES)
    }

    /// Author the `prototypes` relationship (C++ `CreatePrototypesRel`).
    pub fn create_prototypes_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_PROTOTYPES)?.set_custom(false)?)
    }

    /// For each instance, the index into the `prototypes` relationship's
    /// targets selecting which prototype to draw; its length defines the
    /// number of instances.
    /// C++ `UsdGeomPointInstancer::GetProtoIndicesAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::IntVec`).
    pub fn proto_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_PROTO_INDICES)
    }

    /// Author `protoIndices` (`int[]`) (C++ `CreateProtoIndicesAttr`).
    pub fn create_proto_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_PROTO_INDICES, "int[]")?
            .set_custom(false)?)
    }

    /// The position of each instance in the instancer's local space, forming
    /// the translation part of every instance transform.
    /// C++ `UsdGeomPointInstancer::GetPositionsAttr`.
    ///
    /// Type `point3f[]`. Fetch with `get::<Vec<gf::Vec3f>>()?`.
    pub fn positions_attr(&self) -> Attribute {
        self.attribute(tok::A_POSITIONS)
    }

    /// Author `positions` (`point3f[]`) (C++ `CreatePositionsAttr`).
    pub fn create_positions_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_POSITIONS, "point3f[]")?
            .set_custom(false)?)
    }

    /// The orientation of each instance as a half-precision unit quaternion,
    /// supplying the rotation part of every instance transform.
    /// C++ `UsdGeomPointInstancer::GetOrientationsAttr`.
    ///
    /// Type `quath[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::QuathVec`).
    pub fn orientations_attr(&self) -> Attribute {
        self.attribute(tok::A_ORIENTATIONS)
    }

    /// Author `orientations` (`quath[]`) (C++ `CreateOrientationsAttr`).
    pub fn create_orientations_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_ORIENTATIONS, "quath[]")?
            .set_custom(false)?)
    }

    /// The orientation of each instance as a single-precision unit quaternion;
    /// when authored it takes precedence over the half-precision
    /// `orientations`.
    /// C++ `UsdGeomPointInstancer::GetOrientationsfAttr`.
    ///
    /// Type `quatf[]`. Fetch with `get::<Vec<gf::Quatf>>()?`.
    pub fn orientationsf_attr(&self) -> Attribute {
        self.attribute(tok::A_ORIENTATIONS_F)
    }

    /// Author `orientationsf` (`quatf[]`) (C++ `CreateOrientationsfAttr`).
    pub fn create_orientationsf_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_ORIENTATIONS_F, "quatf[]")?
            .set_custom(false)?)
    }

    /// The per-axis scale of each instance, supplying the scaling part of
    /// every instance transform.
    /// C++ `UsdGeomPointInstancer::GetScalesAttr`.
    ///
    /// Type `float3[]`. Fetch with `get::<Vec<gf::Vec3f>>()?`.
    pub fn scales_attr(&self) -> Attribute {
        self.attribute(tok::A_SCALES)
    }

    /// Author `scales` (`float3[]`) (C++ `CreateScalesAttr`).
    pub fn create_scales_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_SCALES, "float3[]")?.set_custom(false)?)
    }

    /// The linear velocity of each instance in units per second, used to
    /// interpolate (motion-blur) positions between time samples instead of
    /// linearly blending `positions`.
    /// C++ `UsdGeomPointInstancer::GetVelocitiesAttr`.
    ///
    /// Type `vector3f[]`. Fetch with `get::<Vec<gf::Vec3f>>()?`.
    pub fn velocities_attr(&self) -> Attribute {
        self.attribute(tok::A_VELOCITIES)
    }

    /// Author `velocities` (`vector3f[]`) (C++ `CreateVelocitiesAttr`).
    pub fn create_velocities_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_VELOCITIES, "vector3f[]")?
            .set_custom(false)?)
    }

    /// The linear acceleration of each instance, refining velocity-based
    /// position interpolation into a quadratic motion model.
    /// C++ `UsdGeomPointInstancer::GetAccelerationsAttr`.
    ///
    /// Type `vector3f[]`. Fetch with `get::<Vec<gf::Vec3f>>()?`.
    pub fn accelerations_attr(&self) -> Attribute {
        self.attribute(tok::A_ACCELERATIONS)
    }

    /// Author `accelerations` (`vector3f[]`) (C++ `CreateAccelerationsAttr`).
    pub fn create_accelerations_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_ACCELERATIONS, "vector3f[]")?
            .set_custom(false)?)
    }

    /// The angular velocity of each instance in degrees per second, used to
    /// interpolate orientations between time samples for rotational motion
    /// blur.
    /// C++ `UsdGeomPointInstancer::GetAngularVelocitiesAttr`.
    ///
    /// Type `vector3f[]`. Fetch with `get::<Vec<gf::Vec3f>>()?`.
    pub fn angular_velocities_attr(&self) -> Attribute {
        self.attribute(tok::A_ANGULAR_VELOCITIES)
    }

    /// Author `angularVelocities` (`vector3f[]`)
    /// (C++ `CreateAngularVelocitiesAttr`).
    pub fn create_angular_velocities_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_ANGULAR_VELOCITIES, "vector3f[]")?
            .set_custom(false)?)
    }

    /// An optional stable identifier for each instance, letting `invisibleIds`
    /// and downstream consumers track instances across time even as array
    /// order changes.
    /// C++ `UsdGeomPointInstancer::GetIdsAttr`.
    ///
    /// Type `int64[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::Int64Vec`).
    pub fn ids_attr(&self) -> Attribute {
        self.attribute(tok::A_IDS)
    }

    /// Author `ids` (`int64[]`) (C++ `CreateIdsAttr`).
    pub fn create_ids_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_IDS, "int64[]")?.set_custom(false)?)
    }

    /// The `ids` of instances to hide at a given time; typically time-sampled
    /// to prune instances on a per-frame basis without resizing the other
    /// per-instance arrays.
    /// C++ `UsdGeomPointInstancer::GetInvisibleIdsAttr`.
    ///
    /// Type `int64[]`. Fetch with `get::<sdf::Value>()?` (a `sdf::Value::Int64Vec`).
    pub fn invisible_ids_attr(&self) -> Attribute {
        self.attribute(tok::A_INVISIBLE_IDS)
    }

    /// Author `invisibleIds` (`int64[]`) (C++ `CreateInvisibleIdsAttr`).
    pub fn create_invisible_ids_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_INVISIBLE_IDS, "int64[]")?
            .set_custom(false)?)
    }
}

impl_geom_schema!(boundable PointInstancer);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::geom::Cube;

    #[test]
    fn point_instancer_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Cube::define(&stage, "/Proto/Marker")?
            .create_size_attr()?
            .set(0.1_f64)?;

        let pi = PointInstancer::define(&stage, "/Instances")?;
        pi.create_prototypes_rel()?.set_targets([sdf::path("/Proto/Marker")?])?;
        pi.create_proto_indices_attr()?.set(sdf::Value::IntVec(vec![0, 0, 0]))?;
        pi.create_positions_attr()?.set(sdf::Value::Vec3fVec(vec![
            [0.0_f32, 0.0, 0.0].into(),
            [1.0, 0.0, 0.0].into(),
            [2.0, 0.0, 0.0].into(),
        ]))?;
        pi.create_ids_attr()?.set(sdf::Value::Int64Vec(vec![100, 200, 300]))?;
        pi.create_invisible_ids_attr()?.set(sdf::Value::Int64Vec(vec![200]))?;

        let pi = PointInstancer::get(&stage, "/Instances")?.expect("PointInstancer");
        assert_eq!(pi.proto_indices_attr().get()?, Some(sdf::Value::IntVec(vec![0, 0, 0])));
        assert_eq!(pi.invisible_ids_attr().get()?, Some(sdf::Value::Int64Vec(vec![200])));
        assert_eq!(pi.prototypes_rel().targets()?, vec![sdf::path("/Proto/Marker")?]);
        // Inherited Boundable / Xformable accessors are available.
        assert_eq!(pi.extent_attr().get::<sdf::Value>()?, None);
        assert!(PointInstancer::get(&stage, "/Proto/Marker")?.is_none());
        Ok(())
    }
}
