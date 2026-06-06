//! Integration tests for the `UsdPhysics` schema views against a fixture
//! that exercises every schema family.

use anyhow::Result;
use openusd::schemas::physics::{self, DriveType, JointAxis, JointBase};
use openusd::sdf;
use openusd::usd;

const FIXTURE: &str = "fixtures/usdPhysics_scene.usda";

fn open() -> Result<usd::Stage> {
    usd::Stage::open(FIXTURE)
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
        mass.principal_axes_attr().get::<[f32; 4]>()?,
        Some([1.0, 0.0, 0.0, 0.0])
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

    // A RevoluteJoint isn't a generic Joint.
    assert!(physics::Joint::get(&stage, sdf::path("/World/Hinge")?)?.is_none());
    Ok(())
}

#[test]
fn multi_apply_limits_and_drive() -> Result<()> {
    let stage = open()?;
    let generic = sdf::path("/World/Generic")?;

    assert!(physics::Joint::get(&stage, generic.clone())?.is_some());

    let lim_x = physics::LimitAPI::get(&stage, generic.clone(), "transX")?.expect("LimitAPI:transX");
    // low > high encodes a locked DOF.
    assert_eq!(lim_x.low_attr().get::<f32>()?, Some(1.0));
    assert_eq!(lim_x.high_attr().get::<f32>()?, Some(0.0));

    let lim_z = physics::LimitAPI::get(&stage, generic.clone(), "rotZ")?.expect("LimitAPI:rotZ");
    assert_eq!(lim_z.low_attr().get::<f32>()?, Some(-30.0));
    assert_eq!(lim_z.high_attr().get::<f32>()?, Some(30.0));

    // `get_all` enumerates the applied instances: two limits, one drive.
    let mut limit_dofs: Vec<String> = physics::LimitAPI::get_all(&stage, generic.clone())?
        .iter()
        .map(|l| l.name().to_string())
        .collect();
    limit_dofs.sort();
    assert_eq!(limit_dofs, vec!["rotZ".to_string(), "transX".to_string()]);
    assert_eq!(physics::DriveAPI::get_all(&stage, generic.clone())?.len(), 1);

    let drive = physics::DriveAPI::get(&stage, generic.clone(), "rotZ")?.expect("DriveAPI:rotZ");
    assert_eq!(drive.name(), "rotZ");
    assert_eq!(drive.type_attr().get::<DriveType>()?, Some(DriveType::Force));
    assert_eq!(drive.target_velocity_attr().get::<f32>()?, Some(90.0));
    assert_eq!(drive.stiffness_attr().get::<f32>()?, Some(100.0));
    assert_eq!(drive.damping_attr().get::<f32>()?, Some(10.0));
    assert_eq!(drive.max_force_attr().get::<f32>()?, Some(50.0));

    // A DOF instance that wasn't applied is absent.
    assert!(physics::DriveAPI::get(&stage, generic, "transX")?.is_none());
    Ok(())
}

#[test]
fn collision_group() -> Result<()> {
    let stage = open()?;
    let group = physics::CollisionGroup::get(&stage, sdf::path("/World/Group")?)?.expect("CollisionGroup");
    assert_eq!(group.merge_group_attr().get::<String>()?.as_deref(), Some("default"));
    Ok(())
}
