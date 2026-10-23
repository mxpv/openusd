//! Joints (C++ `_ParseCommonJointDesc`, the per-kind joint parsers,
//! `_FinalizeJoint`, `_GetLocalPose`, `_GetBodyPrim`, `_ParseLimit` and
//! `_ParseDrive`).

use openusd::gf;
use openusd::sdf::Path;
use openusd::tf;
use openusd::usd::{self, SchemaRegistry};

use super::{Parser, SENTINEL, read, token_or};
use crate::SchemaError;
use crate::physics::tokens::{
    ACCELERATION, ANGULAR, LINEAR, PHYSICS_COLLISION_API, PHYSICS_DRIVE_API, PHYSICS_LIMIT_API, PHYSICS_RIGID_BODY_API,
};
use crate::physics::{
    DistanceJoint, DistanceJointSchema, Dof, DriveAPI, Joint, JointAxis, JointSchema, LimitAPI, PrismaticJoint,
    PrismaticJointSchema, RevoluteJoint, RevoluteJointSchema, SphericalJoint, SphericalJointSchema, desc,
};

/// The joint kinds the classifier tells apart (the joint values of C++
/// `UsdPhysicsObjectType`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum JointType {
    Fixed,
    Revolute,
    Prismatic,
    Spherical,
    Distance,
    D6,
    Custom,
}

impl Parser<'_> {
    /// `prim`'s joint of `kind` (C++ `_ParseCommonJointDesc` and the kind's
    /// parser).
    pub(super) fn joint(&mut self, prim: &usd::Prim, kind: JointType) -> Result<desc::Joint, SchemaError> {
        let joint = Joint::from_prim_unchecked(prim.clone());
        // C++ `_GetRel`: the first target of each body rel.
        let rel0 = joint.body0_rel().targets()?.into_iter().next();
        let rel1 = joint.body1_rel().targets()?.into_iter().next();
        // C++ `_FinalizeJoint`: the anchors, in their bodies' frames.
        let rot0: gf::Quatf = read(&joint.local_rot0_attr())?;
        let rot1: gf::Quatf = read(&joint.local_rot1_attr())?;
        let (body0, local_pos0, local_rot0) =
            self.anchor(rel0.as_ref(), read(&joint.local_pos0_attr())?, rot0.normalize())?;
        let (body1, local_pos1, local_rot1) =
            self.anchor(rel1.as_ref(), read(&joint.local_pos1_attr())?, rot1.normalize())?;
        Ok(desc::Joint {
            path: prim.path().clone(),
            rel0,
            rel1,
            body0,
            body1,
            local_pos0,
            local_rot0,
            local_pos1,
            local_rot1,
            enabled: read(&joint.joint_enabled_attr())?,
            collision_enabled: read(&joint.collision_enabled_attr())?,
            break_force: read(&joint.break_force_attr())?,
            break_torque: read(&joint.break_torque_attr())?,
            exclude_from_articulation: read(&joint.exclude_from_articulation_attr())?,
            kind: joint_kind(prim, kind)?,
        })
    }

    /// The body `rel` reaches and the anchor `(pos, rot)` in that body's frame,
    /// scaled by its world scale (C++ `_GetLocalPose`).
    ///
    /// Where the target is the body, the anchor is scaled and kept. Where it
    /// is another prim, the anchor is carried through the target's world
    /// transform into the body's frame, the world's where there is no body.
    /// A target that composes nothing, or no target, leaves the anchor and
    /// gives no body.
    fn anchor(
        &mut self,
        rel: Option<&Path>,
        pos: gf::Vec3f,
        rot: gf::Quatf,
    ) -> Result<(Option<Path>, gf::Vec3f, gf::Quatf), SchemaError> {
        let Some(rel) = rel else {
            return Ok((None, pos, rot));
        };
        let target = self.stage.prim(rel.clone())?;
        if !target.is_valid()? {
            return Ok((None, pos, rot));
        }
        let body = body_of(&target)?;
        let body_path = body.as_ref().map(|body| body.path().clone());
        if body_path.as_ref() == Some(target.path()) {
            let scale = self.world_scale(&target)?;
            return Ok((body_path, gf::Vec3d::from(pos).comp_mult(scale).to_f32(), rot));
        }
        let target_world = self.xform.local_to_world_transform(&target)?;
        let body_world = match &body {
            Some(body) => self.xform.local_to_world_transform(body)?,
            None => gf::Mat4d::IDENTITY,
        };
        let anchor = gf::Mat4d::from_trs(pos, rot, gf::vec3f(1.0, 1.0, 1.0));
        let local = (anchor * target_world * body_world.inverse_or_max()).remove_scale_shear();
        let scale = body_world.factor(gf::Mat4d::FACTOR_EPSILON).scale;
        Ok((
            body_path,
            local.extract_translation().comp_mult(scale).to_f32(),
            local.extract_rotation_quat().normalize().to_f32(),
        ))
    }
}

/// The per-kind part of `prim`'s joint.
fn joint_kind(prim: &usd::Prim, kind: JointType) -> Result<desc::JointKind, SchemaError> {
    Ok(match kind {
        JointType::Fixed => desc::JointKind::Fixed,
        JointType::Revolute => {
            let joint = RevoluteJoint::from_prim_unchecked(prim.clone());
            let lower: f32 = read(&joint.lower_limit_attr())?;
            let upper: f32 = read(&joint.upper_limit_attr())?;
            let (lower_set, upper_set) = bounded(lower, upper);
            desc::JointKind::Revolute {
                axis: token_or(&joint.axis_attr(), JointAxis::from_token, JointAxis::X)?,
                limit: desc::Limit {
                    enabled: lower_set && upper_set,
                    lower,
                    upper,
                },
                drive: DriveAPI::from_prim(prim, ANGULAR)?.map(|api| drive(&api)).transpose()?,
            }
        }
        JointType::Prismatic => {
            let joint = PrismaticJoint::from_prim_unchecked(prim.clone());
            let lower: f32 = read(&joint.lower_limit_attr())?;
            let upper: f32 = read(&joint.upper_limit_attr())?;
            let (lower_set, upper_set) = bounded(lower, upper);
            desc::JointKind::Prismatic {
                axis: token_or(&joint.axis_attr(), JointAxis::from_token, JointAxis::X)?,
                limit: desc::Limit {
                    enabled: lower_set || upper_set,
                    lower,
                    upper,
                },
                drive: DriveAPI::from_prim(prim, LINEAR)?.map(|api| drive(&api)).transpose()?,
            }
        }
        JointType::Spherical => {
            let joint = SphericalJoint::from_prim_unchecked(prim.clone());
            let lower: f32 = read(&joint.cone_angle0_limit_attr())?;
            let upper: f32 = read(&joint.cone_angle1_limit_attr())?;
            desc::JointKind::Spherical {
                axis: token_or(&joint.axis_attr(), JointAxis::from_token, JointAxis::X)?,
                limit: desc::Limit {
                    enabled: lower.is_finite() && upper.is_finite() && lower >= 0.0 && upper >= 0.0,
                    lower,
                    upper,
                },
            }
        }
        JointType::Distance => {
            let joint = DistanceJoint::from_prim_unchecked(prim.clone());
            let lower: f32 = read(&joint.min_distance_attr())?;
            let upper: f32 = read(&joint.max_distance_attr())?;
            desc::JointKind::Distance {
                min_enabled: lower >= 0.0,
                max_enabled: upper >= 0.0,
                limit: desc::Limit {
                    enabled: false,
                    lower,
                    upper,
                },
            }
        }
        JointType::D6 => {
            // One read of the applied schemas tells which instances exist.
            let applied = prim.api_schemas()?;
            let mut limits = Vec::new();
            let mut drives = Vec::new();
            for dof in Dof::ALL {
                if applied.contains(&SchemaRegistry::make_applied_name(PHYSICS_LIMIT_API, dof.as_token())) {
                    limits.push((
                        dof,
                        limit(&LimitAPI::from_prim_unchecked(prim.clone(), dof.as_token()))?,
                    ));
                }
                if applied.contains(&SchemaRegistry::make_applied_name(PHYSICS_DRIVE_API, dof.as_token())) {
                    drives.push((
                        dof,
                        drive(&DriveAPI::from_prim_unchecked(prim.clone(), dof.as_token()))?,
                    ));
                }
            }
            desc::JointKind::D6 { limits, drives }
        }
        JointType::Custom => desc::JointKind::Custom,
    })
}

/// The body the rel target `prim` stands for (C++ `_GetBodyPrim`): the
/// nearest ancestor-or-self with `PhysicsRigidBodyAPI`, else the topmost
/// ancestor-or-self with `PhysicsCollisionAPI`, else none.
fn body_of(prim: &usd::Prim) -> Result<Option<usd::Prim>, SchemaError> {
    let mut collision = None;
    for prim in prim.ancestors() {
        let schemas = prim.api_schemas()?;
        if schemas.iter().any(|schema| schema == PHYSICS_RIGID_BODY_API) {
            return Ok(Some(prim));
        }
        if schemas.iter().any(|schema| schema == PHYSICS_COLLISION_API) {
            collision = Some(prim);
        }
    }
    Ok(collision)
}

/// A `PhysicsDriveAPI` instance's drive (C++ `_ParseDrive`).
fn drive(api: &DriveAPI) -> Result<desc::Drive, SchemaError> {
    let kind: tf::Token = read(&api.type_attr())?;
    Ok(desc::Drive {
        target_position: read(&api.target_position_attr())?,
        target_velocity: read(&api.target_velocity_attr())?,
        force_limit: read(&api.max_force_attr())?,
        stiffness: read(&api.stiffness_attr())?,
        damping: read(&api.damping_attr())?,
        acceleration: kind == ACCELERATION,
    })
}

/// A `PhysicsLimitAPI` instance's limit (C++ `_ParseLimit`), in force when
/// either bound is.
fn limit(api: &LimitAPI) -> Result<desc::Limit, SchemaError> {
    let lower: f32 = read(&api.low_attr())?;
    let upper: f32 = read(&api.high_attr())?;
    let (lower_set, upper_set) = bounded(lower, upper);
    Ok(desc::Limit {
        enabled: lower_set || upper_set,
        lower,
        upper,
    })
}

/// Whether each bound is a bound: finite and within the sentinel.
fn bounded(lower: f32, upper: f32) -> (bool, bool) {
    (
        lower.is_finite() && lower > -SENTINEL,
        upper.is_finite() && upper < SENTINEL,
    )
}
