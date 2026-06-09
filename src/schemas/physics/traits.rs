//! The shared `UsdPhysicsJoint` attribute interface.
//!
//! [`JointBase`] carries the attributes every joint exposes (the two attached
//! bodies, their local attachment frames, and the break / enable flags). It is
//! implemented by the generic [`Joint`](super::Joint) and by every concrete
//! joint view ([`FixedJoint`](super::FixedJoint),
//! [`RevoluteJoint`](super::RevoluteJoint), …) through the
//! `impl_physics_schema!(joint ...)` macro arm.

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Relationship};

use super::tokens as tok;

/// The `UsdPhysicsJoint` attribute surface shared by every joint. A joint
/// constrains the relative motion of two bodies; `body0`/`body1` name them and
/// `localPos*`/`localRot*` place the joint frame in each body's local space.
pub trait JointBase: crate::usd::SchemaBase {
    /// The first body the joint attaches to; an empty target means the joint is
    /// anchored to the world frame. C++ `UsdPhysicsJoint::GetBody0Rel`.
    fn body0_rel(&self) -> Relationship {
        self.prim().relationship(tok::A_BODY0)
    }

    /// Author the `physics:body0` relationship (C++ `CreateBody0Rel`).
    fn create_body0_rel(&self) -> Result<Relationship> {
        Ok(self.prim().create_relationship(tok::A_BODY0)?.set_custom(false)?)
    }

    /// The second body the joint attaches to; an empty target anchors it to the
    /// world frame. C++ `UsdPhysicsJoint::GetBody1Rel`.
    fn body1_rel(&self) -> Relationship {
        self.prim().relationship(tok::A_BODY1)
    }

    /// Author the `physics:body1` relationship (C++ `CreateBody1Rel`).
    fn create_body1_rel(&self) -> Result<Relationship> {
        Ok(self.prim().create_relationship(tok::A_BODY1)?.set_custom(false)?)
    }

    /// The joint frame's position in `body0`'s local space, scaled by the body's
    /// world scale. C++ `UsdPhysicsJoint::GetLocalPos0Attr`.
    ///
    /// Type `point3f`. Fetch with `get::<[f32; 3]>()?`.
    fn local_pos0_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_LOCAL_POS_0)
    }

    /// Author `localPos0` (`point3f`) (C++ `CreateLocalPos0Attr`).
    fn create_local_pos0_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_LOCAL_POS_0, "point3f")?
            .set_custom(false)?)
    }

    /// The joint frame's orientation in `body0`'s local space, as a quaternion.
    /// C++ `UsdPhysicsJoint::GetLocalRot0Attr`.
    ///
    /// Type `quatf`. Fetch with `get::<gf::Quatf>()?` (a `(w, x, y, z)` quat).
    fn local_rot0_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_LOCAL_ROT_0)
    }

    /// Author `localRot0` (`quatf`) (C++ `CreateLocalRot0Attr`).
    fn create_local_rot0_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_LOCAL_ROT_0, "quatf")?
            .set_custom(false)?)
    }

    /// The joint frame's position in `body1`'s local space, scaled by the body's
    /// world scale. C++ `UsdPhysicsJoint::GetLocalPos1Attr`.
    ///
    /// Type `point3f`. Fetch with `get::<[f32; 3]>()?`.
    fn local_pos1_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_LOCAL_POS_1)
    }

    /// Author `localPos1` (`point3f`) (C++ `CreateLocalPos1Attr`).
    fn create_local_pos1_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_LOCAL_POS_1, "point3f")?
            .set_custom(false)?)
    }

    /// The joint frame's orientation in `body1`'s local space, as a quaternion.
    /// C++ `UsdPhysicsJoint::GetLocalRot1Attr`.
    ///
    /// Type `quatf`. Fetch with `get::<gf::Quatf>()?` (a `(w, x, y, z)` quat).
    fn local_rot1_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_LOCAL_ROT_1)
    }

    /// Author `localRot1` (`quatf`) (C++ `CreateLocalRot1Attr`).
    fn create_local_rot1_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_LOCAL_ROT_1, "quatf")?
            .set_custom(false)?)
    }

    /// Whether the joint is active; a disabled joint imposes no constraint but
    /// stays in the scene. C++ `UsdPhysicsJoint::GetJointEnabledAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    fn joint_enabled_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_JOINT_ENABLED)
    }

    /// Author `jointEnabled` (`bool`) (C++ `CreateJointEnabledAttr`).
    fn create_joint_enabled_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_JOINT_ENABLED, "bool")?
            .set_custom(false)?)
    }

    /// Whether the two jointed bodies are allowed to collide with each other
    /// (default `false`). C++ `UsdPhysicsJoint::GetCollisionEnabledAttr`.
    ///
    /// Type `bool`. Fetch with `get::<bool>()?`.
    fn collision_enabled_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_JOINT_COLLISION_ENABLED)
    }

    /// Author `collisionEnabled` (`bool`) (C++ `CreateCollisionEnabledAttr`).
    fn create_collision_enabled_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_JOINT_COLLISION_ENABLED, "bool")?
            .set_custom(false)?)
    }

    /// Whether this joint is left out of any articulation the simulator would
    /// otherwise build through it. C++ `UsdPhysicsJoint::GetExcludeFromArticulationAttr`.
    ///
    /// Type `uniform bool`. Fetch with `get::<bool>()?`.
    fn exclude_from_articulation_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_EXCLUDE_FROM_ARTICULATION)
    }

    /// Author `excludeFromArticulation` (`uniform bool`)
    /// (C++ `CreateExcludeFromArticulationAttr`).
    fn create_exclude_from_articulation_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_EXCLUDE_FROM_ARTICULATION, "bool")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The force threshold above which the joint breaks and stops constraining
    /// (default infinity — unbreakable). C++ `UsdPhysicsJoint::GetBreakForceAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    fn break_force_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_BREAK_FORCE)
    }

    /// Author `breakForce` (`float`) (C++ `CreateBreakForceAttr`).
    fn create_break_force_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_BREAK_FORCE, "float")?
            .set_custom(false)?)
    }

    /// The torque threshold above which the joint breaks (default infinity —
    /// unbreakable). C++ `UsdPhysicsJoint::GetBreakTorqueAttr`.
    ///
    /// Type `float`. Fetch with `get::<f32>()?`.
    fn break_torque_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_BREAK_TORQUE)
    }

    /// Author `breakTorque` (`float`) (C++ `CreateBreakTorqueAttr`).
    fn create_break_torque_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_BREAK_TORQUE, "float")?
            .set_custom(false)?)
    }
}
