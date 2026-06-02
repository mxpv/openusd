//! Authoring helpers for `PhysicsJoint` and its 5 typed subclasses:
//! `PhysicsFixedJoint`, `PhysicsRevoluteJoint`, `PhysicsPrismaticJoint`,
//! `PhysicsSphericalJoint`, `PhysicsDistanceJoint`.
//!
//! The base [`JointSetters`] trait exposes the 11 attrs every joint
//! type inherits from `PhysicsJoint`. Concrete joint authors layer
//! their own attrs on top via inherent methods.

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::physics::tokens::{
    AXIS_X, AXIS_Y, AXIS_Z, A_AXIS, A_BODY0, A_BODY1, A_BREAK_FORCE, A_BREAK_TORQUE, A_CONE_ANGLE_0_LIMIT,
    A_CONE_ANGLE_1_LIMIT, A_EXCLUDE_FROM_ARTICULATION, A_JOINT_COLLISION_ENABLED, A_JOINT_ENABLED, A_LOCAL_POS_0,
    A_LOCAL_POS_1, A_LOCAL_ROT_0, A_LOCAL_ROT_1, A_LOWER_LIMIT, A_MAX_DISTANCE, A_MIN_DISTANCE, A_UPPER_LIMIT,
    T_PHYSICS_DISTANCE_JOINT, T_PHYSICS_FIXED_JOINT, T_PHYSICS_JOINT, T_PHYSICS_PRISMATIC_JOINT,
    T_PHYSICS_REVOLUTE_JOINT, T_PHYSICS_SPHERICAL_JOINT,
};

use super::common::{
    author_bool, author_float, author_point3f, author_quatf, author_rel_targets, author_uniform_bool,
    author_uniform_token,
};

/// Axis token for single-axis joints (`PhysicsRevoluteJoint`,
/// `PhysicsPrismaticJoint`, `PhysicsSphericalJoint`). Mirrors the
/// schema's `allowedTokens = ["X", "Y", "Z"]`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JointAxis {
    X,
    Y,
    Z,
}

impl JointAxis {
    fn as_token(self) -> &'static str {
        match self {
            JointAxis::X => AXIS_X,
            JointAxis::Y => AXIS_Y,
            JointAxis::Z => AXIS_Z,
        }
    }
}

/// Setters shared by every `PhysicsJoint` subclass.
///
/// Each implementor exposes a `prim()` accessor; the trait's default
/// methods route through the shared free functions so the
/// attribute-name choices live in one place.
pub trait JointSetters: Sized {
    fn prim(&self) -> &Prim;

    /// Set `physics:body0` rel target (UsdGeomXformable).
    fn set_body0(self, body: impl Into<Path>) -> Result<Self> {
        author_rel_targets(self.prim().stage(), self.prim().path(), A_BODY0, [body.into()])?;
        Ok(self)
    }

    /// Set `physics:body1` rel target (UsdGeomXformable).
    fn set_body1(self, body: impl Into<Path>) -> Result<Self> {
        author_rel_targets(self.prim().stage(), self.prim().path(), A_BODY1, [body.into()])?;
        Ok(self)
    }

    /// Set `physics:localPos0` — joint frame in body0's local space.
    fn set_local_pos0(self, pos: [f32; 3]) -> Result<Self> {
        author_point3f(self.prim().stage(), self.prim().path(), A_LOCAL_POS_0, pos)?;
        Ok(self)
    }

    /// Set `physics:localRot0` — joint frame rotation in body0's
    /// local space. Quat order `(w, x, y, z)`.
    fn set_local_rot0(self, rot: [f32; 4]) -> Result<Self> {
        author_quatf(self.prim().stage(), self.prim().path(), A_LOCAL_ROT_0, rot)?;
        Ok(self)
    }

    /// Set `physics:localPos1`.
    fn set_local_pos1(self, pos: [f32; 3]) -> Result<Self> {
        author_point3f(self.prim().stage(), self.prim().path(), A_LOCAL_POS_1, pos)?;
        Ok(self)
    }

    /// Set `physics:localRot1`.
    fn set_local_rot1(self, rot: [f32; 4]) -> Result<Self> {
        author_quatf(self.prim().stage(), self.prim().path(), A_LOCAL_ROT_1, rot)?;
        Ok(self)
    }

    /// Set `physics:jointEnabled` (spec default true).
    fn set_enabled(self, enabled: bool) -> Result<Self> {
        author_bool(self.prim().stage(), self.prim().path(), A_JOINT_ENABLED, enabled)?;
        Ok(self)
    }

    /// Set `physics:collisionEnabled` on the joint (spec default
    /// false — jointed bodies typically don't collide).
    fn set_collision_enabled(self, enabled: bool) -> Result<Self> {
        author_bool(
            self.prim().stage(),
            self.prim().path(),
            A_JOINT_COLLISION_ENABLED,
            enabled,
        )?;
        Ok(self)
    }

    /// Set `physics:excludeFromArticulation` (uniform bool, spec
    /// default false).
    fn set_exclude_from_articulation(self, exclude: bool) -> Result<Self> {
        author_uniform_bool(
            self.prim().stage(),
            self.prim().path(),
            A_EXCLUDE_FROM_ARTICULATION,
            exclude,
        )?;
        Ok(self)
    }

    /// Set `physics:breakForce` (spec default +inf).
    fn set_break_force(self, force: f32) -> Result<Self> {
        author_float(self.prim().stage(), self.prim().path(), A_BREAK_FORCE, force)?;
        Ok(self)
    }

    /// Set `physics:breakTorque` (spec default +inf).
    fn set_break_torque(self, torque: f32) -> Result<Self> {
        author_float(self.prim().stage(), self.prim().path(), A_BREAK_TORQUE, torque)?;
        Ok(self)
    }
}

// ── PhysicsJoint (base / D6) ────────────────────────────────────────

/// Author a `def PhysicsJoint` prim — generic 6-DOF joint base. All
/// degrees of freedom are free until a [`super::apply_limit`] /
/// [`super::apply_drive`] caller restricts them.
pub fn define_joint(stage: &Stage, path: impl Into<Path>) -> Result<JointAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_JOINT)?;
    Ok(JointAuthor { prim })
}

pub struct JointAuthor {
    prim: Prim,
}

impl JointAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }
}

impl JointSetters for JointAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── PhysicsFixedJoint ───────────────────────────────────────────────

/// Author a `def PhysicsFixedJoint` prim — all DOFs locked.
pub fn define_fixed_joint(stage: &Stage, path: impl Into<Path>) -> Result<FixedJointAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_FIXED_JOINT)?;
    Ok(FixedJointAuthor { prim })
}

pub struct FixedJointAuthor {
    prim: Prim,
}

impl FixedJointAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }
}

impl JointSetters for FixedJointAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── PhysicsRevoluteJoint ────────────────────────────────────────────

/// Author a `def PhysicsRevoluteJoint` prim — single rotational axis.
pub fn define_revolute_joint(stage: &Stage, path: impl Into<Path>) -> Result<RevoluteJointAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_REVOLUTE_JOINT)?;
    Ok(RevoluteJointAuthor { prim })
}

pub struct RevoluteJointAuthor {
    prim: Prim,
}

impl RevoluteJointAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:axis` (uniform token, `X` / `Y` / `Z`).
    pub fn set_axis(self, axis: JointAxis) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_AXIS, axis.as_token())?;
        Ok(self)
    }

    /// Set `physics:lowerLimit` in degrees (spec default -inf).
    pub fn set_lower_limit_deg(self, deg: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_LOWER_LIMIT, deg)?;
        Ok(self)
    }

    /// Set `physics:upperLimit` in degrees (spec default +inf).
    pub fn set_upper_limit_deg(self, deg: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_UPPER_LIMIT, deg)?;
        Ok(self)
    }
}

impl JointSetters for RevoluteJointAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── PhysicsPrismaticJoint ───────────────────────────────────────────

/// Author a `def PhysicsPrismaticJoint` prim — single translational axis.
pub fn define_prismatic_joint(stage: &Stage, path: impl Into<Path>) -> Result<PrismaticJointAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_PRISMATIC_JOINT)?;
    Ok(PrismaticJointAuthor { prim })
}

pub struct PrismaticJointAuthor {
    prim: Prim,
}

impl PrismaticJointAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:axis` (uniform token, `X` / `Y` / `Z`).
    pub fn set_axis(self, axis: JointAxis) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_AXIS, axis.as_token())?;
        Ok(self)
    }

    /// Set `physics:lowerLimit` in distance units.
    pub fn set_lower_limit(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_LOWER_LIMIT, value)?;
        Ok(self)
    }

    /// Set `physics:upperLimit` in distance units.
    pub fn set_upper_limit(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_UPPER_LIMIT, value)?;
        Ok(self)
    }
}

impl JointSetters for PrismaticJointAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── PhysicsSphericalJoint ───────────────────────────────────────────

/// Author a `def PhysicsSphericalJoint` prim — ball joint with cone
/// limits around `axis`.
pub fn define_spherical_joint(stage: &Stage, path: impl Into<Path>) -> Result<SphericalJointAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_SPHERICAL_JOINT)?;
    Ok(SphericalJointAuthor { prim })
}

pub struct SphericalJointAuthor {
    prim: Prim,
}

impl SphericalJointAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:axis` — cone limit axis.
    pub fn set_axis(self, axis: JointAxis) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_AXIS, axis.as_token())?;
        Ok(self)
    }

    /// Set `physics:coneAngle0Limit` in degrees (spec default -1 — no limit).
    pub fn set_cone_angle_0_limit_deg(self, deg: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_CONE_ANGLE_0_LIMIT, deg)?;
        Ok(self)
    }

    /// Set `physics:coneAngle1Limit` in degrees (spec default -1 — no limit).
    pub fn set_cone_angle_1_limit_deg(self, deg: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_CONE_ANGLE_1_LIMIT, deg)?;
        Ok(self)
    }
}

impl JointSetters for SphericalJointAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

// ── PhysicsDistanceJoint ────────────────────────────────────────────

/// Author a `def PhysicsDistanceJoint` prim — min/max distance constraint.
pub fn define_distance_joint(stage: &Stage, path: impl Into<Path>) -> Result<DistanceJointAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_PHYSICS_DISTANCE_JOINT)?;
    Ok(DistanceJointAuthor { prim })
}

pub struct DistanceJointAuthor {
    prim: Prim,
}

impl DistanceJointAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `physics:minDistance` (negative = unlimited).
    pub fn set_min_distance(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_MIN_DISTANCE, value)?;
        Ok(self)
    }

    /// Set `physics:maxDistance` (negative = unlimited).
    pub fn set_max_distance(self, value: f32) -> Result<Self> {
        author_float(self.prim.stage(), self.prim.path(), A_MAX_DISTANCE, value)?;
        Ok(self)
    }
}

impl JointSetters for DistanceJointAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::physics::types::JointKind;
    use crate::sdf;

    #[test]
    fn revolute_joint_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/A")?.set_type_name("Xform")?;
        stage.define_prim("/B")?.set_type_name("Xform")?;
        define_revolute_joint(&stage, sdf::path("/Hinge")?)?
            .set_body0(sdf::path("/A")?)?
            .set_body1(sdf::path("/B")?)?
            .set_axis(JointAxis::Y)?
            .set_lower_limit_deg(-90.0)?
            .set_upper_limit_deg(90.0)?
            .set_enabled(true)?;

        let joint = crate::schemas::physics::read_joint(&stage, &sdf::path("/Hinge")?)?.expect("RevoluteJoint");
        assert_eq!(joint.kind, JointKind::Revolute);
        assert_eq!(joint.body0.as_deref(), Some("/A"));
        assert_eq!(joint.body1.as_deref(), Some("/B"));
        assert_eq!(joint.axis.as_deref(), Some("Y"));
        assert!((joint.lower_limit.unwrap() - -90.0).abs() < 1e-3);
        assert!((joint.upper_limit.unwrap() - 90.0).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn fixed_joint_locks_all_dofs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_fixed_joint(&stage, sdf::path("/Weld")?)?.set_enabled(true)?;

        let joint = crate::schemas::physics::read_joint(&stage, &sdf::path("/Weld")?)?.expect("FixedJoint");
        assert_eq!(joint.kind, JointKind::Fixed);
        Ok(())
    }

    #[test]
    fn prismatic_joint_with_translation_limits() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_prismatic_joint(&stage, sdf::path("/Slider")?)?
            .set_axis(JointAxis::X)?
            .set_lower_limit(0.0)?
            .set_upper_limit(2.5)?;

        let joint = crate::schemas::physics::read_joint(&stage, &sdf::path("/Slider")?)?.expect("PrismaticJoint");
        assert_eq!(joint.kind, JointKind::Prismatic);
        assert_eq!(joint.axis.as_deref(), Some("X"));
        assert!((joint.upper_limit.unwrap() - 2.5).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn spherical_joint_cone_limits() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_spherical_joint(&stage, sdf::path("/Ball")?)?
            .set_axis(JointAxis::Z)?
            .set_cone_angle_0_limit_deg(30.0)?
            .set_cone_angle_1_limit_deg(45.0)?;

        let joint = crate::schemas::physics::read_joint(&stage, &sdf::path("/Ball")?)?.expect("SphericalJoint");
        assert_eq!(joint.kind, JointKind::Spherical);
        assert!((joint.cone_angle_0.unwrap() - 30.0).abs() < 1e-3);
        assert!((joint.cone_angle_1.unwrap() - 45.0).abs() < 1e-3);
        Ok(())
    }

    #[test]
    fn distance_joint_range() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_distance_joint(&stage, sdf::path("/Rope")?)?
            .set_min_distance(0.5)?
            .set_max_distance(2.0)?;

        let joint = crate::schemas::physics::read_joint(&stage, &sdf::path("/Rope")?)?.expect("DistanceJoint");
        assert_eq!(joint.kind, JointKind::Distance);
        assert!((joint.min_distance.unwrap() - 0.5).abs() < 1e-3);
        assert!((joint.max_distance.unwrap() - 2.0).abs() < 1e-3);
        Ok(())
    }
}
