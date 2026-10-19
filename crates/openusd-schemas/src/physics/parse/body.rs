//! Rigid bodies and the colliders' attachment to them (C++
//! `_ParseRigidBodyDesc`, `_GetRigidBody`, `_GetCollisionShapeLocalTransfrom`,
//! `_FinalizeCollisionDescs`).

use std::collections::BTreeMap;

use openusd::gf;
use openusd::sdf::{self, Path, PathSet};
use openusd::usd;

use super::{Parser, filtered_pairs, read};
use crate::SchemaError;
use crate::physics::{RigidBodyAPI, desc};

/// What a body's colliders are placed against: the inverse of its world
/// matrix and its world scale.
#[derive(Debug, Clone, Copy)]
pub(super) struct BodyFrame {
    inverse: gf::Mat4d,
    scale: gf::Vec3d,
}

impl BodyFrame {
    /// The world's frame, which a static collider is placed against.
    const WORLD: Self = Self {
        inverse: gf::Mat4d::IDENTITY,
        scale: gf::Vec3d { x: 1.0, y: 1.0, z: 1.0 },
    };
}

impl Parser<'_> {
    /// `prim`'s body (C++ `_ParseRigidBodyDesc`), with no colliders yet, and
    /// the frame its colliders are placed against.
    pub(super) fn rigid_body(&mut self, prim: &usd::Prim) -> Result<(desc::RigidBody, BodyFrame), SchemaError> {
        let api = RigidBodyAPI::from_prim_unchecked(prim.clone());
        let world = self.xform.local_to_world_transform(prim)?;
        let factors = world.factor(gf::Mat4d::FACTOR_EPSILON);
        let body = desc::RigidBody {
            path: prim.path().clone(),
            collisions: Vec::new(),
            filtered_collisions: filtered_pairs(prim)?,
            simulation_owners: api.simulation_owner_rel().targets()?,
            position: factors.translation.to_f32(),
            rotation: factors.rotation.extract_rotation_quat().to_f32(),
            scale: factors.scale.to_f32(),
            enabled: read(&api.rigid_body_enabled_attr())?,
            kinematic: read(&api.kinematic_enabled_attr())?,
            starts_asleep: read(&api.starts_asleep_attr())?,
            linear_velocity: read(&api.velocity_attr())?,
            angular_velocity: read(&api.angular_velocity_attr())?,
        };
        let frame = BodyFrame {
            inverse: world.inverse_or_max(),
            scale: factors.scale,
        };
        Ok((body, frame))
    }

    /// Each shape's body, pose in the body's frame and collision groups, and
    /// each body's colliders (C++ `_FinalizeCollisionDescs`); `frames` are the
    /// bodies' frames, in the bodies' order.
    ///
    /// A shape's body is the nearest ancestor-or-self among `bodies`, enabled
    /// or not (C++ `_GetRigidBody`); without one the shape is static and its
    /// pose is its world pose. A body's colliders come by shape kind in the
    /// order C++ reports kinds, and by path within a kind, as the per-kind
    /// passes of `_FinalizeCollisionDescs` each sort theirs.
    pub(super) fn attach_collisions(
        &mut self,
        shapes: &mut [desc::Shape],
        bodies: &mut [desc::RigidBody],
        frames: &[BodyFrame],
        groups: &BTreeMap<Path, PathSet>,
    ) -> Result<(), SchemaError> {
        let mut body_at = sdf::PathTable::new();
        for (i, body) in bodies.iter().enumerate() {
            body_at.insert(body.path.clone(), i);
        }
        // The groups each collider is in, in group path order.
        let mut groups_of: sdf::PathMap<Vec<Path>> = sdf::PathMap::default();
        for (group, colliders) in groups {
            for collider in colliders {
                groups_of.entry(collider.clone()).or_default().push(group.clone());
            }
        }
        let mut collisions: Vec<Vec<(u8, Path)>> = vec![Vec::new(); bodies.len()];
        // TODO(rayon): each shape's pose and groups depend on the shape and its
        // body alone; C++ computes them in parallel batches of ten and merges
        // the body-collider pairs afterwards.
        for shape in shapes.iter_mut() {
            shape.collision_groups = groups_of.remove(&shape.path).unwrap_or_default();
            let frame = match body_at.nearest_ancestor(&shape.path) {
                Some((body, &i)) => {
                    shape.rigid_body = Some(body.clone());
                    collisions[i].push((kind_rank(&shape.geometry), shape.path.clone()));
                    frames[i]
                }
                None => BodyFrame::WORLD,
            };

            // C++ `_GetCollisionShapeLocalTransfrom`: the shape in the body's
            // frame, the position scaled by the body's world scale.
            let (position, rotation, scale) = if shape.rigid_body.as_ref() == Some(&shape.path) {
                (gf::Vec3d::default(), gf::Quatd::IDENTITY, gf::vec3d(1.0, 1.0, 1.0))
            } else {
                let world = self
                    .xform
                    .local_to_world_transform(&self.stage.prim(shape.path.clone())?)?;
                let local = (world * frame.inverse).factor(gf::Mat4d::FACTOR_EPSILON);
                (local.translation, local.rotation.extract_rotation_quat(), local.scale)
            };
            shape.local_pos = position.comp_mult(frame.scale).to_f32();
            shape.local_rot = rotation.to_f32();
            shape.local_scale = scale.to_f32();
        }
        for (body, mut found) in bodies.iter_mut().zip(collisions) {
            found.sort();
            body.collisions = found.into_iter().map(|(_, path)| path).collect();
        }
        Ok(())
    }
}

/// Where a shape's kind comes in the C++ report: the order the collider
/// passes run in.
fn kind_rank(geometry: &desc::Geometry) -> u8 {
    match geometry {
        desc::Geometry::Sphere { .. } => 0,
        desc::Geometry::Cube { .. } => 1,
        desc::Geometry::Capsule { .. } => 2,
        desc::Geometry::Capsule1 { .. } => 3,
        desc::Geometry::Cylinder { .. } => 4,
        desc::Geometry::Cylinder1 { .. } => 5,
        desc::Geometry::Cone { .. } => 6,
        desc::Geometry::Plane { .. } => 7,
        desc::Geometry::Mesh { .. } => 8,
        desc::Geometry::SpherePoints(_) => 9,
        desc::Geometry::Custom(_) => 10,
    }
}
