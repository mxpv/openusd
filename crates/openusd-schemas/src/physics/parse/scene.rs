//! Scenes, physics materials and collision groups (C++ `_ParseSceneDesc`,
//! `_ParseRigidBodyMaterialDesc`, `_ParseCollisionGroupDesc`, and the group
//! merging and collider sets of the entry point).

use std::collections::{BTreeMap, HashMap};
use std::slice;

use openusd::gf;
use openusd::sdf::{Path, PathSet};
use openusd::usd::{self, PrimPredicate};

use super::{Parser, SENTINEL, read};
use crate::SchemaError;
use crate::geom::{self, UpAxis};
use crate::physics::{CollisionGroup, CollisionGroupSchema, MaterialAPI, Scene, SceneSchema, desc};

/// Earth's gravity in m/s² (C++ `defaultGravity`).
const DEFAULT_GRAVITY: f32 = 9.81;

impl Parser<'_> {
    /// `prim`'s scene (C++ `_ParseSceneDesc`): an unauthored gravity
    /// direction is the negative stage up axis, an unauthored magnitude
    /// Earth's in stage units.
    pub(super) fn scene(&self, prim: &usd::Prim) -> Result<desc::Scene, SchemaError> {
        let scene = Scene::from_prim_unchecked(prim.clone());
        let mut direction: gf::Vec3f = read(&scene.gravity_direction_attr())?;
        if direction == gf::Vec3f::default() {
            direction = match geom::stage_up_axis(self.stage)? {
                UpAxis::Y => gf::vec3f(0.0, -1.0, 0.0),
                UpAxis::Z => gf::vec3f(0.0, 0.0, -1.0),
            };
        } else {
            direction = direction.normalize();
        }
        let mut magnitude: f32 = read(&scene.gravity_magnitude_attr())?;
        if magnitude < -SENTINEL {
            let meters_per_unit = geom::stage_meters_per_unit(self.stage)? as f32;
            magnitude = DEFAULT_GRAVITY / meters_per_unit;
        }
        Ok(desc::Scene {
            path: prim.path().clone(),
            gravity_direction: direction,
            gravity_magnitude: magnitude,
        })
    }

    /// The groups among `prims` after merging, with the colliders each
    /// reported group's collection holds (the entry point's merge loop and
    /// `collisionGroupSets`).
    ///
    /// The merge loop is the C++ one: a group with a merge name either
    /// represents that name from then on or is folded into its representative
    /// and swap-removed, which moves the last group into its slot to be
    /// visited next. The representative keeps its own path and
    /// `invertFilteredGroups`. The loop's order therefore decides the
    /// filtering and is kept.
    pub(super) fn collision_groups(
        &self,
        prims: &[usd::Prim],
    ) -> Result<(Vec<desc::CollisionGroup>, BTreeMap<Path, PathSet>), SchemaError> {
        let mut groups = prims.iter().map(collision_group).collect::<Result<Vec<_>, _>>()?;
        let mut representative: HashMap<String, usize> = HashMap::new();
        let mut i = 0;
        while i < groups.len() {
            let name = &groups[i].merge_group_name;
            if name.is_empty() {
                i += 1;
            } else if let Some(&index) = representative.get(name) {
                let merged = groups.swap_remove(i);
                groups[index].merged_groups.push(merged.path);
                groups[index].filtered_groups.extend(merged.filtered_groups);
            } else {
                representative.insert(name.clone(), i);
                let path = groups[i].path.clone();
                groups[i].merged_groups.push(path);
                i += 1;
            }
        }

        // TODO(rayon): each group's set is independent; C++ computes them in
        // parallel batches of ten.
        let mut sets = BTreeMap::new();
        for group in &groups {
            let mut colliders = PathSet::default();
            let members = if group.merged_groups.is_empty() {
                slice::from_ref(&group.path)
            } else {
                &group.merged_groups
            };
            // Every member is one of `prims`, a classified collision group.
            for member in members {
                // TODO(perf): C++ computes the collection's full included set,
                // as here; asking the membership query about each collider's
                // path answers the same for a collider the walk reached under
                // the same predicate, without a traversal per group.
                let group = CollisionGroup::from_prim_unchecked(self.stage.prim(member.clone())?);
                let query = group.colliders_collection().membership_query()?;
                colliders.extend(usd::included_paths(self.stage, &query, PrimPredicate::DEFAULT_PROXIES)?);
            }
            sets.insert(group.path.clone(), colliders);
        }
        Ok((groups, sets))
    }
}

/// `prim`'s material (C++ `_ParseRigidBodyMaterialDesc`).
pub(super) fn material(prim: &usd::Prim) -> Result<desc::Material, SchemaError> {
    let api = MaterialAPI::from_prim_unchecked(prim.clone());
    Ok(desc::Material {
        path: prim.path().clone(),
        static_friction: read(&api.static_friction_attr())?,
        dynamic_friction: read(&api.dynamic_friction_attr())?,
        restitution: read(&api.restitution_attr())?,
        density: read(&api.density_attr())?,
    })
}

/// `prim`'s group before merging (C++ `_ParseCollisionGroupDesc`).
///
/// `physics:mergeGroup` declares no fallback, and the merge name is its value
/// where authored and empty otherwise (C++ `Get` into a `std::string`); the
/// collision group table decides merging by whether the attribute is
/// authored, which is a different rule.
fn collision_group(prim: &usd::Prim) -> Result<desc::CollisionGroup, SchemaError> {
    let group = CollisionGroup::from_prim_unchecked(prim.clone());
    Ok(desc::CollisionGroup {
        path: prim.path().clone(),
        invert_filtered_groups: group.inverts_filtering()?,
        filtered_groups: group.filtered_groups_rel().targets()?,
        merge_group_name: group.merge_group_name()?.unwrap_or_default(),
        merged_groups: Vec::new(),
    })
}
