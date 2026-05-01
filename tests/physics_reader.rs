//! Integration tests for `physics::read::*` against a fixture
//! that exercises every schema family the reader covers.

use anyhow::Result;
use openusd::sdf;
use openusd::physics::{
    self, CollisionApprox, Dof, DriveType, JointKind,
};
use openusd::Stage;

const FIXTURE: &str = "fixtures/usdPhysics_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

#[test]
fn finds_every_physics_prim_family() -> Result<()> {
    let stage = open()?;
    let prims = physics::find_physics_prims(&stage)?;

    assert_eq!(prims.scenes, vec!["/World/PhysicsScene".to_string()]);
    assert_eq!(prims.articulation_roots, vec!["/World/Base".to_string()]);
    assert_eq!(prims.materials, vec!["/World/Rubber".to_string()]);
    assert_eq!(prims.collision_groups, vec!["/World/Group".to_string()]);
    assert_eq!(prims.filtered_pairs, vec!["/World/Arm".to_string()]);

    assert!(prims.rigid_bodies.contains(&"/World/Base".to_string()));
    assert!(prims.rigid_bodies.contains(&"/World/Arm".to_string()));
    assert_eq!(prims.rigid_bodies.len(), 2);

    assert!(prims.colliders.contains(&"/World/Base".to_string()));
    assert!(prims.colliders.contains(&"/World/Arm".to_string()));
    assert_eq!(prims.colliders.len(), 2);

    // 6 joints: Hinge, Slider, Ball, Tether, Lock, Generic.
    assert_eq!(prims.joints.len(), 6);

    Ok(())
}

#[test]
fn reads_physics_scene_gravity() -> Result<()> {
    let stage = open()?;
    let scene = physics::read_physics_scene(&stage, &sdf::path("/World/PhysicsScene")?)?
        .expect("PhysicsScene present");
    assert_eq!(scene.path, "/World/PhysicsScene");
    assert_eq!(scene.gravity_direction, Some([0.0, -1.0, 0.0]));
    assert_eq!(scene.gravity_magnitude, Some(9.81));
    Ok(())
}

#[test]
fn reads_rigid_body_state() -> Result<()> {
    let stage = open()?;
    let rb = physics::read_rigid_body(&stage, &sdf::path("/World/Base")?)?
        .expect("RigidBodyAPI on Base");
    assert!(rb.kinematic_enabled);
    assert!(rb.rigid_body_enabled);
    assert_eq!(rb.velocity, Some([0.0, 0.0, 0.0]));

    // Arm authors RigidBodyAPI but no kinematic/velocity attrs.
    let arm = physics::read_rigid_body(&stage, &sdf::path("/World/Arm")?)?
        .expect("RigidBodyAPI on Arm");
    assert!(!arm.kinematic_enabled);
    assert!(arm.velocity.is_none());
    Ok(())
}

#[test]
fn reads_mass_inertia_density() -> Result<()> {
    let stage = open()?;
    let mass = physics::read_mass(&stage, &sdf::path("/World/Base")?)?
        .expect("MassAPI on Base");
    assert_eq!(mass.mass, Some(2.5));
    assert_eq!(mass.center_of_mass, Some([0.0, 0.0, 0.0]));
    assert_eq!(mass.diagonal_inertia, Some([0.1, 0.1, 0.1]));
    assert_eq!(mass.principal_axes, Some([1.0, 0.0, 0.0, 0.0]));

    // Arm has no MassAPI applied.
    assert!(physics::read_mass(&stage, &sdf::path("/World/Arm")?)?.is_none());
    Ok(())
}

#[test]
fn reads_collision_shape_with_material_binding() -> Result<()> {
    let stage = open()?;
    let arm = physics::read_collision_shape(&stage, &sdf::path("/World/Arm")?)?
        .expect("CollisionAPI on Arm");
    assert!(arm.has_collision_api);
    assert!(!arm.has_mesh_collision_api);
    assert!(arm.collision_enabled);
    assert!(arm.approximation.is_none()); // no MeshCollisionAPI applied
    assert_eq!(
        arm.physics_material_path,
        Some("/World/Rubber".to_string()),
        "material:binding:physics rel should resolve"
    );
    Ok(())
}

#[test]
fn reads_physics_material_friction_and_restitution() -> Result<()> {
    let stage = open()?;
    let m = physics::read_physics_material(&stage, &sdf::path("/World/Rubber")?)?
        .expect("PhysicsMaterialAPI on Rubber");
    assert_eq!(m.dynamic_friction, Some(0.8));
    assert_eq!(m.static_friction, Some(0.9));
    assert_eq!(m.restitution, Some(0.6));
    assert_eq!(m.density, Some(1100.0));
    Ok(())
}

#[test]
fn reads_revolute_joint_with_built_in_limits_and_break() -> Result<()> {
    let stage = open()?;
    let hinge = physics::read_joint(&stage, &sdf::path("/World/Hinge")?)?
        .expect("Hinge is a known joint");
    assert_eq!(hinge.kind, JointKind::Revolute);
    assert_eq!(hinge.body0.as_deref(), Some("/World/Base"));
    assert_eq!(hinge.body1.as_deref(), Some("/World/Arm"));
    assert_eq!(hinge.axis.as_deref(), Some("Z"));
    assert_eq!(hinge.lower_limit, Some(-45.0));
    assert_eq!(hinge.upper_limit, Some(45.0));
    assert_eq!(hinge.break_force, Some(1000.0));
    assert_eq!(hinge.break_torque, Some(500.0));
    assert!((hinge.local_pos0[0] - 0.5).abs() < 1e-5);
    assert!(hinge.joint_enabled);
    Ok(())
}

#[test]
fn reads_every_specialised_joint_kind() -> Result<()> {
    let stage = open()?;
    for (path, kind) in [
        ("/World/Hinge", JointKind::Revolute),
        ("/World/Slider", JointKind::Prismatic),
        ("/World/Ball", JointKind::Spherical),
        ("/World/Tether", JointKind::Distance),
        ("/World/Lock", JointKind::Fixed),
        ("/World/Generic", JointKind::Generic),
    ] {
        let j = physics::read_joint(&stage, &sdf::path(path)?)?
            .unwrap_or_else(|| panic!("joint {path} missing"));
        assert_eq!(j.kind, kind, "{path}");
    }
    Ok(())
}

#[test]
fn reads_spherical_cone_and_distance_min_max() -> Result<()> {
    let stage = open()?;
    let ball = physics::read_joint(&stage, &sdf::path("/World/Ball")?)?.unwrap();
    assert_eq!(ball.cone_angle_0, Some(30.0));
    assert_eq!(ball.cone_angle_1, Some(45.0));

    let tether = physics::read_joint(&stage, &sdf::path("/World/Tether")?)?.unwrap();
    assert_eq!(tether.min_distance, Some(0.5));
    assert_eq!(tether.max_distance, Some(2.0));
    Ok(())
}

#[test]
fn reads_disabled_joint_flag() -> Result<()> {
    let stage = open()?;
    let lock = physics::read_joint(&stage, &sdf::path("/World/Lock")?)?.unwrap();
    assert!(!lock.joint_enabled, "Lock authors physics:jointEnabled = 0");
    Ok(())
}

#[test]
fn reads_multi_apply_limit_and_drive_on_generic_joint() -> Result<()> {
    let stage = open()?;
    let g = physics::read_joint(&stage, &sdf::path("/World/Generic")?)?.unwrap();
    assert_eq!(g.kind, JointKind::Generic);

    assert_eq!(g.limits.len(), 2);
    let trans_x = g.limits.iter().find(|l| l.dof == Dof::TransX).unwrap();
    assert_eq!(trans_x.low, 1.0);
    assert_eq!(trans_x.high, 0.0); // low > high → locked
    let rot_z = g.limits.iter().find(|l| l.dof == Dof::RotZ).unwrap();
    assert_eq!(rot_z.low, -30.0);
    assert_eq!(rot_z.high, 30.0);

    assert_eq!(g.drives.len(), 1);
    let d = &g.drives[0];
    assert_eq!(d.dof, Dof::RotZ);
    assert_eq!(d.drive_type, DriveType::Force);
    assert_eq!(d.target_velocity, Some(90.0));
    assert_eq!(d.stiffness, 100.0);
    assert_eq!(d.damping, 10.0);
    assert_eq!(d.max_force, Some(50.0));
    Ok(())
}

#[test]
fn reads_collision_group_members_and_merge_name() -> Result<()> {
    let stage = open()?;
    let g = physics::read_collision_group(&stage, &sdf::path("/World/Group")?)?
        .expect("CollisionGroup present");
    assert!(g.members.contains(&"/World/Base".to_string()));
    assert!(g.members.contains(&"/World/Arm".to_string()));
    assert_eq!(g.merge_group.as_deref(), Some("default"));
    Ok(())
}

#[test]
fn reads_filtered_pairs_targets() -> Result<()> {
    let stage = open()?;
    let f = physics::read_filtered_pairs(&stage, &sdf::path("/World/Arm")?)?
        .expect("FilteredPairsAPI on Arm");
    assert_eq!(f.filtered, vec!["/World/Base".to_string()]);
    Ok(())
}

#[test]
fn approx_token_round_trip() {
    for tok in [
        CollisionApprox::None,
        CollisionApprox::ConvexHull,
        CollisionApprox::ConvexDecomposition,
        CollisionApprox::BoundingSphere,
        CollisionApprox::BoundingCube,
        CollisionApprox::MeshSimplification,
    ] {
        assert_eq!(CollisionApprox::from_token(tok.as_token()), Some(tok));
    }
}

#[test]
fn dof_token_round_trip() {
    for tok in [
        Dof::TransX, Dof::TransY, Dof::TransZ,
        Dof::RotX, Dof::RotY, Dof::RotZ,
        Dof::Linear, Dof::Angular, Dof::Distance,
    ] {
        assert_eq!(Dof::from_token(tok.as_token()), Some(tok));
    }
}
