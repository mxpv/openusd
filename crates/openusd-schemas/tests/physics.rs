//! Integration tests for the `UsdPhysics` schema views against a fixture
//! that exercises every schema family.

use openusd::Result;
use openusd::gf;
use openusd::sdf;
use openusd::usd;
use openusd::usd::{PrimPredicate, SchemaBase, Stage};
use openusd_schemas::physics::{
    self, CollisionAPI, CollisionApprox, CollisionGroupSchema, DistanceJointSchema, DriveAPI, DriveType, Joint,
    JointAxis, JointSchema, LimitAPI, MassAPI, MeshCollisionAPI, PrismaticJointSchema, RevoluteJoint,
    RevoluteJointSchema, RigidBodyAPI, Scene, SceneSchema, SphericalJointSchema,
};

const FIXTURE: &str = "fixtures/usdPhysics_scene.usda";

fn open() -> Result<usd::Stage> {
    usd::Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)
}

/// A stage opened from `usda` source, for the scenes a fixture does not carry.
fn from_usda(usda: &str) -> Result<Stage> {
    // Persist the tempdir so it outlives the stage; the process exits at test
    // end, so the OS reclaims it.
    let path = tempfile::tempdir()?.keep().join("scene.usda");
    std::fs::write(&path, usda)?;
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(path.to_str().unwrap())
}

#[test]
fn scene_material_and_apis() -> Result<()> {
    let stage = open()?;

    let scene = physics::Scene::get(&stage, sdf::path("/World/PhysicsScene")?)?.expect("Scene");
    assert_eq!(
        scene.gravity_direction_attr().get::<[f32; 3]>()?,
        Some([0.0, -1.0, 0.0])
    );
    assert_eq!(scene.gravity_magnitude_attr().get::<f32>()?, Some(9.81));

    let mat = physics::MaterialAPI::get(&stage, sdf::path("/World/Rubber")?)?.expect("MaterialAPI");
    assert_eq!(mat.dynamic_friction_attr().get::<f32>()?, Some(0.8));
    assert_eq!(mat.static_friction_attr().get::<f32>()?, Some(0.9));
    assert_eq!(mat.restitution_attr().get::<f32>()?, Some(0.6));
    assert_eq!(mat.density_attr().get::<f32>()?, Some(1100.0));

    Ok(())
}

#[test]
fn rigid_body_mass_and_articulation() -> Result<()> {
    let stage = open()?;
    let base = sdf::path("/World/Base")?;

    let body = physics::RigidBodyAPI::get(&stage, base.clone())?.expect("RigidBodyAPI");
    assert_eq!(body.kinematic_enabled_attr().get::<bool>()?, Some(true));
    assert_eq!(body.velocity_attr().get::<[f32; 3]>()?, Some([0.0, 0.0, 0.0]));

    let mass = physics::MassAPI::get(&stage, base.clone())?.expect("MassAPI");
    assert_eq!(mass.mass_attr().get::<f32>()?, Some(2.5));
    assert_eq!(mass.center_of_mass_attr().get::<[f32; 3]>()?, Some([0.0, 0.0, 0.0]));
    assert_eq!(mass.diagonal_inertia_attr().get::<[f32; 3]>()?, Some([0.1, 0.1, 0.1]));
    assert_eq!(
        mass.principal_axes_attr().get::<gf::Quatf>()?,
        Some(gf::quatf(1.0, 0.0, 0.0, 0.0))
    );

    assert!(physics::CollisionAPI::get(&stage, base.clone())?.is_some());
    assert!(physics::ArticulationRootAPI::get(&stage, base)?.is_some());

    // The mesh-approximation API isn't applied here.
    assert!(physics::MeshCollisionAPI::get(&stage, sdf::path("/World/Base")?)?.is_none());
    Ok(())
}

#[test]
fn filtered_pairs_relationship() -> Result<()> {
    let stage = open()?;
    let arm = physics::FilteredPairsAPI::get(&stage, sdf::path("/World/Arm")?)?.expect("FilteredPairsAPI");
    let targets = arm.filtered_pairs_rel().targets()?;
    assert_eq!(targets, vec![sdf::path("/World/Base")?]);
    Ok(())
}

#[test]
fn every_joint_kind() -> Result<()> {
    let stage = open()?;

    let hinge = physics::RevoluteJoint::get(&stage, sdf::path("/World/Hinge")?)?.expect("RevoluteJoint");
    assert_eq!(hinge.axis_attr().get::<JointAxis>()?, Some(JointAxis::Z));
    assert_eq!(hinge.lower_limit_attr().get::<f32>()?, Some(-45.0));
    assert_eq!(hinge.upper_limit_attr().get::<f32>()?, Some(45.0));
    // Inherited JointBase attributes.
    assert_eq!(hinge.break_force_attr().get::<f32>()?, Some(1000.0));
    assert_eq!(hinge.break_torque_attr().get::<f32>()?, Some(500.0));
    assert_eq!(hinge.body0_rel().targets()?, vec![sdf::path("/World/Base")?]);

    let slider = physics::PrismaticJoint::get(&stage, sdf::path("/World/Slider")?)?.expect("PrismaticJoint");
    assert_eq!(slider.axis_attr().get::<JointAxis>()?, Some(JointAxis::X));
    assert_eq!(slider.upper_limit_attr().get::<f32>()?, Some(1.0));

    let ball = physics::SphericalJoint::get(&stage, sdf::path("/World/Ball")?)?.expect("SphericalJoint");
    assert_eq!(ball.axis_attr().get::<JointAxis>()?, Some(JointAxis::Y));
    assert_eq!(ball.cone_angle0_limit_attr().get::<f32>()?, Some(30.0));
    assert_eq!(ball.cone_angle1_limit_attr().get::<f32>()?, Some(45.0));

    let tether = physics::DistanceJoint::get(&stage, sdf::path("/World/Tether")?)?.expect("DistanceJoint");
    assert_eq!(tether.min_distance_attr().get::<f32>()?, Some(0.5));
    assert_eq!(tether.max_distance_attr().get::<f32>()?, Some(2.0));

    let lock = physics::FixedJoint::get(&stage, sdf::path("/World/Lock")?)?.expect("FixedJoint");
    assert_eq!(lock.joint_enabled_attr().get::<bool>()?, Some(false));

    // A RevoluteJoint is a Joint: the registry answers `is_a` along the
    // inheritance the schema declares, so the base view sees the derived prim.
    assert!(physics::Joint::get(&stage, sdf::path("/World/Hinge")?)?.is_some());
    Ok(())
}

#[test]
fn multi_apply_limits_and_drive() -> Result<()> {
    let stage = open()?;
    let generic = sdf::path("/World/Generic")?;

    assert!(physics::Joint::get(&stage, generic.clone())?.is_some());

    let lim_x = physics::LimitAPI::get_instance(&stage.prim(generic.clone())?, "transX")?.expect("LimitAPI:transX");
    // low > high encodes a locked DOF.
    assert_eq!(lim_x.low_attr().get::<f32>()?, Some(1.0));
    assert_eq!(lim_x.high_attr().get::<f32>()?, Some(0.0));

    let lim_z = physics::LimitAPI::get_instance(&stage.prim(generic.clone())?, "rotZ")?.expect("LimitAPI:rotZ");
    assert_eq!(lim_z.low_attr().get::<f32>()?, Some(-30.0));
    assert_eq!(lim_z.high_attr().get::<f32>()?, Some(30.0));

    // `get_all` enumerates the applied instances: two limits, one drive.
    let mut limit_dofs: Vec<String> = physics::LimitAPI::get_all(&stage.prim(generic.clone())?)?
        .iter()
        .map(|l| l.name().to_string())
        .collect();
    limit_dofs.sort();
    assert_eq!(limit_dofs, vec!["rotZ".to_string(), "transX".to_string()]);
    assert_eq!(physics::DriveAPI::get_all(&stage.prim(generic.clone())?)?.len(), 1);

    let drive = physics::DriveAPI::get_instance(&stage.prim(generic.clone())?, "rotZ")?.expect("DriveAPI:rotZ");
    assert_eq!(drive.name(), "rotZ");
    assert_eq!(drive.type_attr().get::<DriveType>()?, Some(DriveType::Force));
    assert_eq!(drive.target_velocity_attr().get::<f32>()?, Some(90.0));
    assert_eq!(drive.stiffness_attr().get::<f32>()?, Some(100.0));
    assert_eq!(drive.damping_attr().get::<f32>()?, Some(10.0));
    assert_eq!(drive.max_force_attr().get::<f32>()?, Some(50.0));

    // A DOF instance that wasn't applied is absent.
    assert!(physics::DriveAPI::get_instance(&stage.prim(generic)?, "transX")?.is_none());
    Ok(())
}

#[test]
fn collision_group() -> Result<()> {
    let stage = open()?;
    let group = physics::CollisionGroup::get(&stage, sdf::path("/World/Group")?)?.expect("CollisionGroup");
    assert_eq!(
        group.merge_group_name_attr().get::<String>()?.as_deref(),
        Some("default")
    );
    Ok(())
}

/// A group's colliders are the members of its built-in collection, which
/// expands as any collection does — the group targets two prims and both are
/// members.
#[test]
fn group_colliders_collection() -> Result<()> {
    let stage = open()?;
    let group = physics::CollisionGroup::get(&stage, sdf::path("/World/Group")?)?.expect("CollisionGroup");

    let query = group.colliders_collection().compute_membership_query()?;
    assert!(query.is_path_included(&sdf::path("/World/Base")?));
    assert!(query.is_path_included(&sdf::path("/World/Arm")?));
    assert!(!query.is_path_included(&sdf::path("/World/Ball")?));

    let mut colliders = usd::compute_included_paths(&stage, &query, PrimPredicate::DEFAULT_PROXIES)?;
    colliders.sort();
    assert_eq!(colliders, vec![sdf::path("/World/Arm")?, sdf::path("/World/Base")?]);
    Ok(())
}

/// A collection reaches into instanced content, so a collider inside an
/// instance is a member — which is why enumerating them asks for instance
/// proxies. The walk behind the group table does not, and so cannot see a
/// group inside a prototype.
#[test]
fn colliders_reach_instance_proxies() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0

class Xform "Proto"
{
    def Cube "Body" (prepend apiSchemas = ["PhysicsCollisionAPI"])
    {
    }

    def PhysicsCollisionGroup "Inner"
    {
    }
}

def Xform "World"
{
    def Xform "Inst" (
        instanceable = true
        prepend references = </Proto>
    )
    {
    }

    def PhysicsCollisionGroup "Group"
    {
        rel collection:colliders:includes = [</World/Inst>]
    }
}
"#,
    )?;

    let group = physics::CollisionGroup::get(&stage, "/World/Group")?.expect("CollisionGroup");
    let query = group.colliders_collection().compute_membership_query()?;

    let proxies = usd::compute_included_paths(&stage, &query, PrimPredicate::DEFAULT_PROXIES)?;
    assert!(
        proxies.contains(&sdf::path("/World/Inst/Body")?),
        "the collider inside the instance is a member: {proxies:?}"
    );
    let plain = usd::compute_included_paths(&stage, &query, PrimPredicate::DEFAULT)?;
    assert!(!plain.contains(&sdf::path("/World/Inst/Body")?));

    // The group inside the prototype is not one the table knows.
    let table = physics::compute_collision_group_table(&stage)?;
    assert_eq!(table.groups(), [sdf::path("/World/Group")?]);
    Ok(())
}

/// Every pair answers the same both ways round, and by path as by index.
fn assert_symmetric(table: &physics::CollisionGroupTable) {
    for (ia, a) in table.groups().iter().enumerate() {
        for (ib, b) in table.groups().iter().enumerate() {
            assert_eq!(
                table.is_collision_enabled_at(ia, ib),
                table.is_collision_enabled_at(ib, ia),
                "{a} vs {b} by index"
            );
            assert_eq!(
                table.is_collision_enabled(a, b),
                table.is_collision_enabled(b, a),
                "{a} vs {b}"
            );
            assert_eq!(table.is_collision_enabled(a, b), table.is_collision_enabled_at(ia, ib));
        }
    }
}

/// Define collision groups at `paths`, in order.
fn groups(stage: &Stage, paths: &[&str]) -> Result<Vec<physics::CollisionGroup>> {
    paths
        .iter()
        .map(|path| physics::CollisionGroup::define(stage, *path))
        .collect()
}

/// A group filtering another disables the pair both ways, and one filtering
/// itself disables its own (C++ `test_collision_group_table`).
#[test]
fn group_table_filters() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/a", "/b", "/c"])?;
    let (a, b, c) = (&all[0], &all[1], &all[2]);
    b.create_filtered_groups_rel()?.add_target(c.path().clone())?;
    c.create_filtered_groups_rel()?.add_target(c.path().clone())?;

    let table = physics::compute_collision_group_table(&stage)?;
    assert_eq!(table.groups().len(), 3);
    assert!(table.is_collision_enabled(a.path(), a.path()));
    assert!(table.is_collision_enabled(a.path(), b.path()));
    assert!(table.is_collision_enabled(a.path(), c.path()));
    assert!(table.is_collision_enabled(b.path(), b.path()));
    assert!(!table.is_collision_enabled(b.path(), c.path()));
    assert!(
        !table.is_collision_enabled(c.path(), c.path()),
        "a group filtering itself"
    );
    assert_symmetric(&table);
    Ok(())
}

/// An inverted filter disables everything it does not name — its own pair
/// included, since it did not name itself (C++
/// `test_collision_group_inversion`).
#[test]
fn group_table_inversion() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/a", "/b", "/c"])?;
    let (a, b, c) = (&all[0], &all[1], &all[2]);
    a.create_filtered_groups_rel()?.add_target(c.path().clone())?;
    a.create_invert_filtered_groups_attr()?.set(true)?;

    let table = physics::compute_collision_group_table(&stage)?;
    assert!(!table.is_collision_enabled(a.path(), a.path()));
    assert!(!table.is_collision_enabled(a.path(), b.path()));
    assert!(table.is_collision_enabled(a.path(), c.path()));
    assert!(table.is_collision_enabled(b.path(), b.path()));
    assert!(table.is_collision_enabled(b.path(), c.path()));
    assert!(table.is_collision_enabled(c.path(), c.path()));
    assert_symmetric(&table);
    Ok(())
}

/// Merging a plain filter into an inverted group disables every pair either
/// of them had: rules combine, and combining only ever disables. The C++
/// documentation warns about exactly this.
#[test]
fn inverted_merge_disables_all() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/allOthers", "/grpXCollider", "/grpX", "/grpA"])?;
    let (others, collider, x, a) = (&all[0], &all[1], &all[2], &all[3]);
    x.create_filtered_groups_rel()?.add_target(collider.path().clone())?;
    x.create_invert_filtered_groups_attr()?.set(true)?;
    a.create_filtered_groups_rel()?.add_target(collider.path().clone())?;

    // Apart, each group keeps its own rules.
    let table = physics::compute_collision_group_table(&stage)?;
    assert!(table.is_collision_enabled(x.path(), collider.path()));
    assert!(!table.is_collision_enabled(x.path(), others.path()));
    assert!(!table.is_collision_enabled(a.path(), collider.path()));

    // Merged, `grpA`'s filter and `grpX`'s inversion together leave nothing.
    x.create_merge_group_name_attr()?.set("mergeTest".to_string())?;
    a.create_merge_group_name_attr()?.set("mergeTest".to_string())?;
    let table = physics::compute_collision_group_table(&stage)?;
    assert!(!table.is_collision_enabled(x.path(), collider.path()));
    assert!(!table.is_collision_enabled(x.path(), others.path()));
    assert!(!table.is_collision_enabled(a.path(), collider.path()));
    assert!(!table.is_collision_enabled(a.path(), others.path()));
    assert_symmetric(&table);
    Ok(())
}

/// A merged group's filters are every member's (C++
/// `test_collision_group_simple_merging`).
#[test]
fn group_table_simple_merge() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/a", "/b", "/c"])?;
    let (a, b, c) = (&all[0], &all[1], &all[2]);
    a.create_filtered_groups_rel()?.add_target(c.path().clone())?;
    a.create_merge_group_name_attr()?.set("mergeTest".to_string())?;
    b.create_merge_group_name_attr()?.set("mergeTest".to_string())?;

    let table = physics::compute_collision_group_table(&stage)?;
    assert!(table.is_collision_enabled(a.path(), a.path()));
    assert!(table.is_collision_enabled(a.path(), b.path()));
    assert!(!table.is_collision_enabled(a.path(), c.path()));
    assert!(!table.is_collision_enabled(b.path(), c.path()), "b inherits a's filter");
    assert!(table.is_collision_enabled(c.path(), c.path()));
    assert_symmetric(&table);
    Ok(())
}

/// A filter between two merge groups applies to every member on both sides
/// (C++ `test_collision_group_complex_merging`).
#[test]
fn group_table_complex_merge() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/a", "/b", "/c", "/d"])?;
    let (a, b, c, d) = (&all[0], &all[1], &all[2], &all[3]);
    a.create_filtered_groups_rel()?.add_target(c.path().clone())?;
    for (group, name) in [(a, "mergeAB"), (b, "mergeAB"), (c, "mergeCD"), (d, "mergeCD")] {
        group.create_merge_group_name_attr()?.set(name.to_string())?;
    }

    let table = physics::compute_collision_group_table(&stage)?;
    for near in [a, b] {
        assert!(table.is_collision_enabled(near.path(), a.path()));
        assert!(table.is_collision_enabled(near.path(), b.path()));
        assert!(!table.is_collision_enabled(near.path(), c.path()));
        assert!(!table.is_collision_enabled(near.path(), d.path()));
    }
    assert!(table.is_collision_enabled(c.path(), d.path()));
    assert!(table.is_collision_enabled(d.path(), d.path()));
    assert_symmetric(&table);
    Ok(())
}

/// Both members of a merge group answer alike, whichever order their indices
/// fall in.
///
/// Merge names `a, b, c, a` give the four groups merged indices `0, 1, 2, 0`,
/// so the last group's index is below the third's — the case where reading a
/// pair without putting it in order first lands on `(1, 1)`, the second
/// group's own pair, which is left enabled here precisely so that a wrong
/// read shows up. Symmetry does not catch it: the wrong value reaches both
/// halves of the pair.
#[test]
fn merged_index_stays_ordered() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/p0", "/p1", "/p2", "/p3"])?;
    for (group, name) in [(&all[0], "a"), (&all[1], "b"), (&all[2], "c"), (&all[3], "a")] {
        group.create_merge_group_name_attr()?.set(name.to_string())?;
    }
    all[0].create_filtered_groups_rel()?.add_target(all[2].path().clone())?;

    let table = physics::compute_collision_group_table(&stage)?;
    assert!(
        table.is_collision_enabled(all[1].path(), all[1].path()),
        "the cell a wrong read lands on"
    );
    assert!(!table.is_collision_enabled(all[0].path(), all[2].path()));
    assert!(
        !table.is_collision_enabled(all[3].path(), all[2].path()),
        "the other member of the same merge group answers alike"
    );
    assert_symmetric(&table);
    Ok(())
}

/// A filter target naming no collision group filters nothing, rather than
/// filtering against whichever group came first.
#[test]
fn unknown_filter_target_ignored() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/a", "/b"])?;
    let (a, b) = (&all[0], &all[1]);
    stage.define_prim("/NotAGroup")?.set_type_name("Cube")?;
    b.create_filtered_groups_rel()?.add_target(sdf::path("/NotAGroup")?)?;

    let table = physics::compute_collision_group_table(&stage)?;
    assert!(table.is_collision_enabled(a.path(), a.path()));
    assert!(table.is_collision_enabled(a.path(), b.path()));
    assert!(table.is_collision_enabled(b.path(), b.path()));

    // Inverted, an unknown target is not among what stays enabled either, so
    // the group is left colliding with nothing.
    b.create_invert_filtered_groups_attr()?.set(true)?;
    let table = physics::compute_collision_group_table(&stage)?;
    assert!(!table.is_collision_enabled(b.path(), b.path()));
    assert!(!table.is_collision_enabled(a.path(), b.path()));
    assert!(table.is_collision_enabled(a.path(), a.path()));
    Ok(())
}

/// Merging turns on whether anything authors `mergeGroup`, not on whether a
/// value comes back: a declaration alone and a block both merge the group
/// under the empty name, as C++ does, while an unauthored one merges with
/// nothing.
#[test]
fn merge_name_authorship() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/absent", "/empty", "/declared", "/blocked", "/other"])?;
    all[1].create_merge_group_name_attr()?.set(String::new())?;
    all[2].create_merge_group_name_attr()?;
    all[3].create_merge_group_name_attr()?.block()?;
    all[4].create_filtered_groups_rel()?.add_target(all[1].path().clone())?;

    // The filter against `/empty` reaches every group merged under the empty
    // name, and no further.
    let table = physics::compute_collision_group_table(&stage)?;
    for merged in [&all[1], &all[2], &all[3]] {
        assert!(
            !table.is_collision_enabled(merged.path(), all[4].path()),
            "{} merges under the empty name",
            merged.path()
        );
    }
    assert!(
        table.is_collision_enabled(all[0].path(), all[4].path()),
        "an unauthored name merges with nothing"
    );
    assert_symmetric(&table);
    Ok(())
}

/// Inversion turns on a value rather than on authorship: a declaration with
/// no value, and a blocked one, leave filtering the usual way round.
#[test]
fn inversion_missing_values() -> Result<()> {
    let stage = memory()?;
    let all = groups(&stage, &["/a", "/b"])?;
    let (a, b) = (&all[0], &all[1]);
    a.create_filtered_groups_rel()?.add_target(b.path().clone())?;

    for author in [0, 1, 2] {
        match author {
            1 => {
                a.create_invert_filtered_groups_attr()?;
            }
            2 => {
                a.create_invert_filtered_groups_attr()?.block()?;
            }
            _ => {}
        }
        let table = physics::compute_collision_group_table(&stage)?;
        assert!(
            !table.is_collision_enabled(a.path(), b.path()),
            "the named pair is filtered"
        );
        assert!(table.is_collision_enabled(a.path(), a.path()), "nothing else is");
    }
    Ok(())
}

/// A value of the wrong type is an error, not a group quietly left unmerged.
/// A stage carrying a recoverable composition diagnostic still computes.
#[test]
fn malformed_merge_name_errors() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0

def PhysicsCollisionGroup "Group"
{
    uniform token physics:mergeGroup = "wrongType"
}
"#,
    )?;
    assert!(physics::compute_collision_group_table(&stage).is_err());

    let stage = from_usda(
        r#"#usda 1.0
(
    subLayers = [
        @nowhere.usda@
    ]
)

def PhysicsCollisionGroup "Group"
{
}
"#,
    )?;
    assert!(!stage.composition_errors().is_empty(), "the sublayer is unresolvable");
    let table = physics::compute_collision_group_table(&stage)?;
    assert_eq!(table.groups(), [sdf::path("/Group")?]);
    Ok(())
}

/// An in-memory stage carrying the schema data, which is what makes a prim its
/// type and resolves the fallbacks its schema declares.
fn memory() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")
}

#[test]
fn applied_apis_roundtrip() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/World/Box")?.set_type_name("Cube")?;

    let body = RigidBodyAPI::apply(&stage.prim("/World/Box")?)?;
    body.create_rigid_body_enabled_attr()?.set(true)?;
    MassAPI::apply(&stage.prim("/World/Box")?)?
        .create_mass_attr()?
        .set(2.5_f32)?;
    MeshCollisionAPI::apply(&stage.prim("/World/Box")?)?
        .create_approximation_attr()?
        .set(CollisionApprox::ConvexHull)?;

    let body = RigidBodyAPI::get(&stage, "/World/Box")?.expect("RigidBodyAPI");
    assert_eq!(body.rigid_body_enabled_attr().get::<bool>()?, Some(true));
    assert_eq!(
        MassAPI::get(&stage, "/World/Box")?
            .expect("MassAPI")
            .mass_attr()
            .get::<f32>()?,
        Some(2.5)
    );
    assert_eq!(
        MeshCollisionAPI::get(&stage, "/World/Box")?
            .expect("MeshCollisionAPI")
            .approximation_attr()
            .get::<CollisionApprox>()?,
        Some(CollisionApprox::ConvexHull)
    );

    // Not applied â†’ None.
    assert!(CollisionAPI::get(&stage, "/World/Box")?.is_none());
    Ok(())
}

#[test]
fn multi_apply_drive_and_limit() -> Result<()> {
    let stage = memory()?;
    let joint = Joint::define(&stage, "/World/D6")?;

    DriveAPI::apply(&stage.prim(joint.path().clone())?, "rotX")?
        .create_type_attr()?
        .set(DriveType::Acceleration)?;
    DriveAPI::apply(&stage.prim("/World/D6")?, "rotY")?
        .create_target_position_attr()?
        .set(45.0_f32)?;

    let limit = LimitAPI::apply(&stage.prim("/World/D6")?, "rotX")?;
    limit.create_low_attr()?.set(-30.0_f32)?;
    limit.create_high_attr()?.set(30.0_f32)?;

    let drive = DriveAPI::get_instance(&stage.prim("/World/D6")?, "rotX")?.expect("DriveAPI:rotX");
    assert_eq!(drive.name(), "rotX");
    assert_eq!(drive.type_attr().get::<DriveType>()?, Some(DriveType::Acceleration));

    let limit = LimitAPI::get_instance(&stage.prim("/World/D6")?, "rotX")?.expect("LimitAPI:rotX");
    assert_eq!(limit.low_attr().get::<f32>()?, Some(-30.0));
    assert_eq!(limit.high_attr().get::<f32>()?, Some(30.0));

    // `get_all` enumerates every applied instance.
    let mut drives: Vec<String> = DriveAPI::get_all(&stage.prim("/World/D6")?)?
        .iter()
        .map(|d| d.name().to_string())
        .collect();
    drives.sort();
    assert_eq!(drives, vec!["rotX".to_string(), "rotY".to_string()]);
    assert_eq!(LimitAPI::get_all(&stage.prim("/World/D6")?)?.len(), 1);

    // A different DOF instance is absent.
    assert!(DriveAPI::get_instance(&stage.prim("/World/D6")?, "rotZ")?.is_none());
    Ok(())
}

#[test]
fn scene_and_joint_roundtrip() -> Result<()> {
    let stage = memory()?;

    let scene = Scene::define(&stage, "/World/Scene")?;
    scene.create_gravity_magnitude_attr()?.set(981.0_f32)?;

    let hinge = RevoluteJoint::define(&stage, "/World/Hinge")?;
    hinge.create_axis_attr()?.set(JointAxis::Z)?;
    // Inherited from JointBase.
    hinge.create_break_force_attr()?.set(500.0_f32)?;

    let scene = Scene::get(&stage, "/World/Scene")?.expect("Scene");
    assert_eq!(scene.gravity_magnitude_attr().get::<f32>()?, Some(981.0));

    let hinge = RevoluteJoint::get(&stage, "/World/Hinge")?.expect("RevoluteJoint");
    assert_eq!(hinge.axis_attr().get::<JointAxis>()?, Some(JointAxis::Z));
    assert_eq!(hinge.break_force_attr().get::<f32>()?, Some(500.0));

    // `RevoluteJoint` derives from `Joint`, so the base view resolves once a
    // registry knows the physics family. This stage has none, leaving the
    // gate on the authored name alone.
    // A RevoluteJoint is a Joint: the registry answers `is_a` along the
    // inheritance the schema declares.
    assert!(Joint::get(&stage, "/World/Hinge")?.is_some());
    Ok(())
}
