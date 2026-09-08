//! Integration tests for the `UsdPhysics` schema views against a fixture
//! that exercises every schema family.

use openusd::Result;
use openusd::gf;
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd;
use openusd::usd::Stage;
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
        group.merge_group_name_attr().get::<Token>()?.as_deref(),
        Some("default")
    );
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
