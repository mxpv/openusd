//! The physics parser against in-memory stages (C++ `testUsdPhysicsParsing.py`,
//! with the cases a port adds).

use std::slice;

use openusd::gf;
use openusd::sdf::{self, Path};
use openusd::tf;
use openusd::usd::{self, FamilySource, SchemaBase, SchemaRegistry, Stage};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::{
    self, Capsule, Capsule_1, Capsule_1Schema, CapsuleSchema, Cone, ConeSchema, Cube, Cylinder, Cylinder_1,
    Cylinder_1Schema, CylinderSchema, GprimSchema, Mesh, MeshSchema, Plane, PlaneSchema, PointBasedSchema,
    PointInstancer, Points, PointsSchema, Sphere, SphereSchema, Subset, SubsetSchema, Xform, XformableExt,
};
use openusd_schemas::physics::{
    self, ArticulationRootAPI, CollisionAPI, CollisionGroup, CollisionGroupSchema, CustomTokens, DistanceJoint,
    DistanceJointSchema, Dof, DriveAPI, FilteredPairsAPI, FixedJoint, Joint, JointAxis, JointSchema, LimitAPI,
    MATERIAL_PURPOSE, MaterialAPI, MeshCollisionAPI, ParseDiagnostic, ParseOptions, Parsed, PrismaticJoint,
    PrismaticJointSchema, RevoluteJoint, RevoluteJointSchema, RigidBodyAPI, Scene, SceneSchema, SphericalJoint,
    SphericalJointSchema, desc, tokens,
};
use openusd_schemas::shade::{Material, MaterialBindingAPI};

type Result<T = ()> = std::result::Result<T, SchemaError>;

/// The Python tests' `toleranceEpsilon`.
const TOLERANCE: f32 = 0.01;

fn new_stage() -> Result<Stage> {
    Ok(Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("physics_parse.usda")?)
}

/// The whole stage parsed.
fn parse(stage: &Stage) -> Result<Parsed> {
    physics::parse(stage, &from_root(ParseOptions::default()))
}

/// The whole stage parsed for `owners`.
fn parse_owned(stage: &Stage, owners: Vec<Path>) -> Result<Parsed> {
    physics::parse(
        stage,
        &from_root(ParseOptions {
            simulation_owners: Some(owners),
            ..ParseOptions::default()
        }),
    )
}

fn from_root(options: ParseOptions) -> ParseOptions {
    ParseOptions {
        include: vec![Path::abs_root()],
        ..options
    }
}

fn path(text: &str) -> Path {
    sdf::path(text).expect("a valid path")
}

fn close(a: gf::Vec3f, b: gf::Vec3f) -> bool {
    gf::Vec3d::from(a).is_close(gf::Vec3d::from(b), f64::from(TOLERANCE))
}

/// The XYZ Euler angles of `q`, in degrees (the Python `Gf.Rotation.Decompose`).
fn euler_xyz(q: gf::Quatf) -> gf::Vec3f {
    gf::Rotation::from_quat(gf::Quatd::from(q))
        .decompose(gf::Vec3d::X_AXIS, gf::Vec3d::Y_AXIS, gf::Vec3d::Z_AXIS)
        .to_f32()
}

/// A scene at `/physicsScene`.
fn define_scene(stage: &Stage) -> Result<Scene> {
    Ok(Scene::define(stage, "/physicsScene")?)
}

/// An `Xform` body at `path`.
fn body(stage: &Stage, path: &str) -> Result<(Xform, RigidBodyAPI)> {
    let xform = Xform::define(stage, path)?;
    let api = RigidBodyAPI::apply(xform.prim())?;
    Ok((xform, api))
}

/// A cube collider at `path`.
fn collider(stage: &Stage, path: &str) -> Result<(Cube, CollisionAPI)> {
    let cube = Cube::define(stage, path)?;
    let api = CollisionAPI::apply(cube.prim())?;
    Ok((cube, api))
}

const POSITION: gf::Vec3f = gf::Vec3f {
    x: 100.0,
    y: 20.0,
    z: 10.0,
};
const ROTATE_XYZ: gf::Vec3f = gf::Vec3f {
    x: 0.0,
    y: 0.0,
    z: 45.0,
};
const SCALE: gf::Vec3f = gf::Vec3f { x: 3.0, y: 3.0, z: 3.0 };

/// `xformable` translated, rotated and scaled by the constants above.
fn placed<X: XformableExt>(xformable: X) -> Result<X> {
    xformable
        .set_translate(gf::Vec3d::from(POSITION))?
        .set_rotate_xyz(ROTATE_XYZ)?
        .set_scale(SCALE)
}

/// The physics material at `path`, with `PhysicsMaterialAPI`.
fn physics_material(stage: &Stage, path: &str) -> Result<Material> {
    let material = Material::define(stage, path)?;
    MaterialAPI::apply(material.prim())?;
    Ok(material)
}

/// `material` bound to `prim` for the physics purpose.
fn bind(prim: &usd::Prim, material: &Material) -> Result {
    MaterialBindingAPI::apply(prim)?.bind_for_purpose(MATERIAL_PURPOSE, material.path().clone(), None)?;
    Ok(())
}

/// The one shape parsed.
fn only_shape(parsed: &Parsed) -> &desc::Shape {
    assert_eq!(parsed.shapes.len(), 1, "{:?}", parsed.shapes);
    &parsed.shapes[0]
}

/// `apiSchemas` authored directly on `prim`, which may name schemas the
/// registry does not know.
fn author_api_schemas(prim: &usd::Prim, names: &[&str]) -> Result {
    for name in names {
        prim.clone().add_applied_schema(*name)?;
    }
    Ok(())
}

fn paths<'a>(items: impl IntoIterator<Item = &'a Path>) -> Vec<String> {
    items.into_iter().map(ToString::to_string).collect()
}

/// A gravity magnitude below the negated sentinel takes Earth's gravity, and
/// one at it is kept as authored.
#[test]
fn gravity_sentinel() -> Result {
    let magnitude = |authored: f32| -> Result<f32> {
        let stage = new_stage()?;
        define_scene(&stage)?.create_gravity_magnitude_attr()?.set(authored)?;
        Ok(parse(&stage)?.scenes[0].gravity_magnitude)
    };
    assert!((magnitude(-1e38)? - 981.0).abs() < TOLERANCE);
    assert_eq!(magnitude(-0.5e38)?, -0.5e38);
    Ok(())
}

/// A scene with nothing authored has Earth's gravity along the negative up
/// axis, in stage units (C++ `test_scene_parse`).
#[test]
fn scene_defaults() -> Result {
    let stage = new_stage()?;
    let scene = define_scene(&stage)?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    let desc = &parsed.scenes[0];
    assert_eq!(&desc.path, scene.path());
    assert!(close(desc.gravity_direction, gf::vec3f(0.0, -1.0, 0.0)));
    assert!((desc.gravity_magnitude - 981.0).abs() < TOLERANCE);
    Ok(())
}

/// The nine gprim kinds as colliders, each placed, scaled and alone on its
/// stage (C++ `test_collision_parse`).
#[test]
fn collision_shapes() -> Result {
    let shared = |shape: &desc::Shape, prim: &usd::Prim| {
        assert_eq!(&shape.path, prim.path());
        assert_eq!(shape.rigid_body, None);
        assert!(shape.collision_enabled);
        assert!(shape.materials.is_empty());
        assert!(shape.simulation_owners.is_empty());
        assert!(shape.filtered_collisions.is_empty());
        assert!(close(shape.local_pos, POSITION), "{:?}", shape.local_pos);
        assert!(close(euler_xyz(shape.local_rot), ROTATE_XYZ), "{:?}", shape.local_rot);
        assert!(close(shape.local_scale, SCALE), "{:?}", shape.local_scale);
    };
    let s = SCALE.x;
    let y = tf::Token::from(tokens::Y);
    let z = tf::Token::from(tokens::Z);

    let stage = new_stage()?;
    define_scene(&stage)?;
    let sphere = placed(Sphere::define(&stage, "/Shape")?)?;
    sphere.create_radius_attr()?.set(30.0_f64)?;
    CollisionAPI::apply(sphere.prim())?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    let shape = only_shape(&parsed);
    shared(shape, sphere.prim());
    assert_eq!(shape.geometry, desc::Geometry::Sphere { radius: 30.0 * s });

    let stage = new_stage()?;
    let capsule = placed(Capsule::define(&stage, "/Shape")?)?;
    capsule.create_radius_attr()?.set(30.0_f64)?;
    capsule.create_height_attr()?.set(10.0_f64)?;
    capsule.create_axis_attr()?.set(y.clone())?;
    CollisionAPI::apply(capsule.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, capsule.prim());
    assert_eq!(
        shape.geometry,
        desc::Geometry::Capsule {
            radius: 30.0 * s,
            half_height: 10.0 * 0.5 * s,
            axis: geom::Axis::Y,
        }
    );

    let stage = new_stage()?;
    let capsule = placed(Capsule_1::define(&stage, "/Shape")?)?;
    capsule.create_radius_top_attr()?.set(30.0_f64)?;
    capsule.create_radius_bottom_attr()?.set(20.0_f64)?;
    capsule.create_height_attr()?.set(10.0_f64)?;
    capsule.create_axis_attr()?.set(y.clone())?;
    CollisionAPI::apply(capsule.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, capsule.prim());
    assert_eq!(
        shape.geometry,
        desc::Geometry::Capsule1 {
            top_radius: 30.0 * s,
            bottom_radius: 20.0 * s,
            half_height: 10.0 * 0.5 * s,
            axis: geom::Axis::Y,
        }
    );

    let stage = new_stage()?;
    let cone = placed(Cone::define(&stage, "/Shape")?)?;
    cone.create_radius_attr()?.set(30.0_f64)?;
    cone.create_height_attr()?.set(10.0_f64)?;
    cone.create_axis_attr()?.set(z.clone())?;
    CollisionAPI::apply(cone.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, cone.prim());
    assert_eq!(
        shape.geometry,
        desc::Geometry::Cone {
            radius: 30.0 * s,
            half_height: 10.0 * 0.5 * s,
            axis: geom::Axis::Z,
        }
    );

    let stage = new_stage()?;
    let cylinder = placed(Cylinder::define(&stage, "/Shape")?)?;
    cylinder.create_radius_attr()?.set(30.0_f64)?;
    cylinder.create_height_attr()?.set(10.0_f64)?;
    cylinder.create_axis_attr()?.set(y.clone())?;
    CollisionAPI::apply(cylinder.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, cylinder.prim());
    assert_eq!(
        shape.geometry,
        desc::Geometry::Cylinder {
            radius: 30.0 * s,
            half_height: 10.0 * 0.5 * s,
            axis: geom::Axis::Y,
        }
    );

    let stage = new_stage()?;
    let cylinder = placed(Cylinder_1::define(&stage, "/Shape")?)?;
    cylinder.create_radius_top_attr()?.set(30.0_f64)?;
    cylinder.create_radius_bottom_attr()?.set(20.0_f64)?;
    cylinder.create_height_attr()?.set(10.0_f64)?;
    cylinder.create_axis_attr()?.set(y)?;
    CollisionAPI::apply(cylinder.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, cylinder.prim());
    assert_eq!(
        shape.geometry,
        desc::Geometry::Cylinder1 {
            top_radius: 30.0 * s,
            bottom_radius: 20.0 * s,
            half_height: 10.0 * 0.5 * s,
            axis: geom::Axis::Y,
        }
    );

    let stage = new_stage()?;
    let plane = placed(Plane::define(&stage, "/Shape")?)?;
    plane.create_axis_attr()?.set(z)?;
    CollisionAPI::apply(plane.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, plane.prim());
    assert_eq!(shape.geometry, desc::Geometry::Plane { axis: geom::Axis::Z });

    let stage = new_stage()?;
    let mesh = placed(Mesh::define(&stage, "/Shape")?)?;
    MeshCollisionAPI::apply(mesh.prim())?
        .create_approximation_attr()?
        .set(tf::Token::from(tokens::CONVEX_HULL))?;
    CollisionAPI::apply(mesh.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, mesh.prim());
    let desc::Geometry::Mesh {
        approximation,
        scale,
        double_sided,
    } = &shape.geometry
    else {
        panic!("a mesh, got {:?}", shape.geometry);
    };
    assert_eq!(approximation, tokens::CONVEX_HULL);
    assert!(close(*scale, SCALE));
    assert!(!double_sided);

    let stage = new_stage()?;
    let points = placed(Points::define(&stage, "/Shape")?)?;
    points.create_widths_attr()?.set(vec![5.0_f32, 10.0])?;
    points
        .create_points_attr()?
        .set(vec![gf::vec3f(1.0, 1.0, 1.0), gf::vec3f(2.0, 2.0, 2.0)])?;
    CollisionAPI::apply(points.prim())?;
    let parsed = parse(&stage)?;
    let shape = only_shape(&parsed);
    shared(shape, points.prim());
    assert_eq!(
        shape.geometry,
        desc::Geometry::SpherePoints(vec![
            desc::SpherePoint {
                center: gf::vec3f(1.0, 1.0, 1.0),
                radius: 7.5,
            },
            desc::SpherePoint {
                center: gf::vec3f(2.0, 2.0, 2.0),
                radius: 15.0,
            },
        ])
    );
    Ok(())
}

/// A body's world pose, flags and velocities (C++ `test_rigidbody_parse`).
#[test]
fn rigid_body() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let (xform, api) = body(&stage, "/rigidBody")?;
    placed(xform.clone())?;
    api.create_velocity_attr()?.set(gf::vec3f(20.0, 10.0, 5.0))?;
    api.create_angular_velocity_attr()?.set(gf::vec3f(10.0, 1.0, 2.0))?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(parsed.rigid_bodies.len(), 1);
    let desc = &parsed.rigid_bodies[0];
    assert_eq!(&desc.path, xform.path());
    assert!(desc.collisions.is_empty());
    assert!(desc.filtered_collisions.is_empty());
    assert!(desc.simulation_owners.is_empty());
    assert!(close(desc.position, POSITION));
    assert!(close(euler_xyz(desc.rotation), ROTATE_XYZ));
    assert!(close(desc.scale, SCALE));
    assert!(desc.enabled);
    assert!(!desc.kinematic);
    assert!(!desc.starts_asleep);
    assert!(close(desc.linear_velocity, gf::vec3f(20.0, 10.0, 5.0)));
    assert!(close(desc.angular_velocity, gf::vec3f(10.0, 1.0, 2.0)));
    Ok(())
}

/// C++ `test_rigidbody_kinematic_parse`.
#[test]
fn kinematic_body() -> Result {
    let stage = new_stage()?;
    let (xform, api) = body(&stage, "/rigidBody")?;
    api.create_kinematic_enabled_attr()?.set(true)?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.rigid_bodies.len(), 1);
    assert_eq!(&parsed.rigid_bodies[0].path, xform.path());
    assert!(parsed.rigid_bodies[0].enabled);
    assert!(parsed.rigid_bodies[0].kinematic);
    Ok(())
}

/// A collider under a body belongs to it and is reported in the body's
/// frame (C++ `test_rigidbody_collision_parse`).
#[test]
fn body_collision() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let (xform, _) = body(&stage, "/rigidBody")?;
    xform
        .clone()
        .set_translate(gf::vec3d(100.0, 0.0, 0.0))?
        .set_rotate_xyz(gf::Vec3f::default())?
        .set_scale(SCALE)?;
    let (cube, _) = collider(&stage, "/rigidBody/cube")?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    let body = &parsed.rigid_bodies[0];
    assert_eq!(&body.path, xform.path());
    assert_eq!(paths(&body.collisions), [cube.path().to_string()]);
    assert!(close(body.position, gf::vec3f(100.0, 0.0, 0.0)));
    assert!(close(euler_xyz(body.rotation), gf::Vec3f::default()));
    assert!(close(body.scale, SCALE));
    let shape = only_shape(&parsed);
    assert_eq!(&shape.path, cube.path());
    assert_eq!(shape.rigid_body.as_ref(), Some(xform.path()));
    assert!(close(shape.local_pos, gf::Vec3f::default()));
    assert!(close(euler_xyz(shape.local_rot), gf::Vec3f::default()));
    assert!(close(shape.local_scale, gf::vec3f(1.0, 1.0, 1.0)));
    Ok(())
}

/// Every collider under a body with many is attached, and the body lists
/// them sorted (C++ `test_rigidbody_collision_multithreading_parse`).
#[test]
fn many_colliders() -> Result {
    const COLLIDERS: usize = 1000;
    let stage = new_stage()?;
    let (xform, _) = body(&stage, "/Body")?;
    for k in 0..COLLIDERS {
        let sphere = Sphere::define(&stage, format!("/Body/SphereCollider_{k}"))?;
        CollisionAPI::apply(sphere.prim())?;
    }
    let parsed = parse(&stage)?;
    assert_eq!(parsed.shapes.len(), COLLIDERS);
    assert!(
        parsed
            .shapes
            .iter()
            .all(|shape| shape.rigid_body.as_ref() == Some(xform.path()))
    );
    let collisions = &parsed.rigid_bodies[0].collisions;
    assert_eq!(collisions.len(), COLLIDERS);
    assert!(collisions.windows(2).all(|pair| pair[0] < pair[1]));
    Ok(())
}

/// Filtered pairs on a body and on a collider (C++ `test_filtering_pairs_parse`).
#[test]
fn filtered_pairs() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let (body0, _) = body(&stage, "/rigidBody0")?;
    let (cube0, _) = collider(&stage, "/rigidBody0/cube")?;
    let (body1, _) = body(&stage, "/rigidBody1")?;
    FilteredPairsAPI::apply(body1.prim())?
        .create_filtered_pairs_rel()?
        .add_target(body0.path().clone())?;
    let (cube1, _) = collider(&stage, "/rigidBody1/cube")?;
    FilteredPairsAPI::apply(cube1.prim())?
        .create_filtered_pairs_rel()?
        .add_target(cube0.path().clone())?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(parsed.rigid_bodies.len(), 2);
    assert_eq!(parsed.shapes.len(), 2);
    let filtered = parsed
        .rigid_bodies
        .iter()
        .find(|body| &body.path == body1.path())
        .expect("body1");
    assert_eq!(filtered.filtered_collisions, [body0.path().clone()]);
    let filtered = parsed
        .shapes
        .iter()
        .find(|shape| &shape.path == cube1.path())
        .expect("cube1");
    assert_eq!(filtered.filtered_collisions, [cube0.path().clone()]);
    Ok(())
}

/// A collider's bound physics material, and the material's own descriptor
/// (C++ `test_collision_material_parse`).
#[test]
fn collision_material() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let (cube, _) = collider(&stage, "/cube")?;
    let material = physics_material(&stage, "/physicsMaterial")?;
    bind(cube.prim(), &material)?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(only_shape(&parsed).materials, [material.path().clone()]);
    assert_eq!(parsed.materials.len(), 1);
    let desc = &parsed.materials[0];
    assert_eq!(&desc.path, material.path());
    assert_eq!(
        (
            desc.static_friction,
            desc.dynamic_friction,
            desc.restitution,
            desc.density
        ),
        (0.0, 0.0, 0.0, 0.0)
    );
    Ok(())
}

/// A mesh's materials come from its face subsets, in order (C++
/// `test_collision_multi_material_parse`).
#[test]
fn subset_materials() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let mesh = Mesh::define(&stage, "/mesh")?;
    CollisionAPI::apply(mesh.prim())?;
    MeshCollisionAPI::apply(mesh.prim())?
        .create_approximation_attr()?
        .set(tf::Token::from(tokens::NONE))?;
    let materials = [
        physics_material(&stage, "/physicsMaterial0")?,
        physics_material(&stage, "/physicsMaterial1")?,
    ];
    let mut points = Vec::new();
    let mut normals = Vec::new();
    let mut indices = Vec::new();
    let mut counts = Vec::new();
    let (strip, half) = (100.0_f32, 500.0_f32);
    for (i, material) in materials.iter().enumerate() {
        let subset = Subset::define(&stage, format!("/mesh/subset{i}"))?;
        subset
            .create_element_type_attr()?
            .set(tf::Token::from(geom::tokens::FACE))?;
        bind(subset.prim(), material)?;
        let i = i as i32;
        let x = |k: i32| -strip / 2.0 + strip * k as f32;
        points.extend([
            gf::vec3f(x(i), -half, 0.0),
            gf::vec3f(x(i + 1), -half, 0.0),
            gf::vec3f(x(i + 1), half, 0.0),
            gf::vec3f(x(i), half, 0.0),
        ]);
        for j in 0..4 {
            normals.push(gf::vec3f(0.0, 0.0, 1.0));
            indices.push(j + i * 4);
        }
        subset.create_indices_attr()?.set(vec![i])?;
        counts.push(4_i32);
    }
    mesh.create_face_vertex_counts_attr()?.set(counts)?;
    mesh.create_face_vertex_indices_attr()?.set(indices)?;
    mesh.create_points_attr()?.set(points)?;
    mesh.create_double_sided_attr()?.set(false)?;
    mesh.create_normals_attr()?.set(normals)?;
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(
        only_shape(&parsed).materials,
        [materials[0].path().clone(), materials[1].path().clone()]
    );
    assert_eq!(parsed.materials.len(), 2);
    Ok(())
}

/// Every joint kind between two bodies, each alone on its stage (C++
/// `test_joint_parse`).
#[test]
fn joints() -> Result {
    fn jointed() -> Result<(Stage, Xform, Xform)> {
        let stage = new_stage()?;
        define_scene(&stage)?;
        let (body0, _) = body(&stage, "/rigidBody0")?;
        let (body1, _) = body(&stage, "/rigidBody1")?;
        Ok((stage, body0, body1))
    }
    fn common<J: JointSchema>(joint: &J, body0: &Xform, body1: &Xform) -> Result {
        joint.create_body0_rel()?.add_target(body0.path().clone())?;
        joint.create_body1_rel()?.add_target(body1.path().clone())?;
        joint.create_break_force_attr()?.set(500.0_f32)?;
        joint.create_break_torque_attr()?.set(1500.0_f32)?;
        joint.create_local_pos0_attr()?.set(gf::vec3f(1.0, 1.0, 1.0))?;
        joint.create_local_pos1_attr()?.set(gf::vec3f(-1.0, -1.0, -1.0))?;
        Ok(())
    }
    fn only_joint<'a>(parsed: &'a Parsed, body0: &Xform, body1: &Xform) -> &'a desc::Joint {
        assert_eq!(parsed.scenes.len(), 1);
        assert_eq!(parsed.joints.len(), 1, "{:?}", parsed.joints);
        let joint = &parsed.joints[0];
        assert_eq!(joint.path, path("/joint"));
        assert_eq!(joint.rel0.as_ref(), Some(body0.path()));
        assert_eq!(joint.body0.as_ref(), Some(body0.path()));
        assert_eq!(joint.rel1.as_ref(), Some(body1.path()));
        assert_eq!(joint.body1.as_ref(), Some(body1.path()));
        assert!(close(joint.local_pos0, gf::vec3f(1.0, 1.0, 1.0)));
        assert!(close(joint.local_pos1, gf::vec3f(-1.0, -1.0, -1.0)));
        assert!(joint.enabled);
        assert!(!joint.collision_enabled);
        assert!(!joint.exclude_from_articulation);
        assert_eq!((joint.break_force, joint.break_torque), (500.0, 1500.0));
        joint
    }
    fn drive(prim: &usd::Prim, instance: &str) -> Result {
        let drive = DriveAPI::apply(prim, instance)?;
        drive.create_target_position_attr()?.set(10.0_f32)?;
        drive.create_target_velocity_attr()?.set(20.0_f32)?;
        drive.create_stiffness_attr()?.set(30.0_f32)?;
        drive.create_damping_attr()?.set(40.0_f32)?;
        Ok(())
    }
    const DRIVEN: desc::Drive = desc::Drive {
        target_position: 10.0,
        target_velocity: 20.0,
        force_limit: f32::INFINITY,
        stiffness: 30.0,
        damping: 40.0,
        acceleration: false,
    };

    let (stage, body0, body1) = jointed()?;
    let joint = FixedJoint::define(&stage, "/joint")?;
    common(&joint, &body0, &body1)?;
    let parsed = parse(&stage)?;
    assert_eq!(only_joint(&parsed, &body0, &body1).kind, desc::JointKind::Fixed);

    for limited in [true, false] {
        let (stage, body0, body1) = jointed()?;
        let joint = RevoluteJoint::define(&stage, "/joint")?;
        common(&joint, &body0, &body1)?;
        joint.create_axis_attr()?.set(tf::Token::from(tokens::Y))?;
        if limited {
            joint.create_lower_limit_attr()?.set(0.0_f32)?;
            joint.create_upper_limit_attr()?.set(90.0_f32)?;
            drive(joint.prim(), tokens::ANGULAR)?;
        }
        let parsed = parse(&stage)?;
        let desc::JointKind::Revolute { axis, limit, drive } = &only_joint(&parsed, &body0, &body1).kind else {
            panic!("a revolute joint");
        };
        assert_eq!(*axis, JointAxis::Y);
        if limited {
            assert_eq!(
                *limit,
                desc::Limit {
                    enabled: true,
                    lower: 0.0,
                    upper: 90.0
                }
            );
            assert_eq!(*drive, Some(DRIVEN));
        } else {
            assert!(!limit.enabled);
            assert_eq!(*drive, None);
        }
    }

    for limited in [true, false] {
        let (stage, body0, body1) = jointed()?;
        let joint = PrismaticJoint::define(&stage, "/joint")?;
        common(&joint, &body0, &body1)?;
        joint.create_axis_attr()?.set(tf::Token::from(tokens::Z))?;
        if limited {
            joint.create_lower_limit_attr()?.set(10.0_f32)?;
            joint.create_upper_limit_attr()?.set(80.0_f32)?;
            drive(joint.prim(), tokens::LINEAR)?;
        }
        let parsed = parse(&stage)?;
        let desc::JointKind::Prismatic { axis, limit, drive } = &only_joint(&parsed, &body0, &body1).kind else {
            panic!("a prismatic joint");
        };
        assert_eq!(*axis, JointAxis::Z);
        if limited {
            assert_eq!(
                *limit,
                desc::Limit {
                    enabled: true,
                    lower: 10.0,
                    upper: 80.0
                }
            );
            assert_eq!(*drive, Some(DRIVEN));
        } else {
            assert!(!limit.enabled);
            assert_eq!(*drive, None);
        }
    }

    let (stage, body0, body1) = jointed()?;
    let joint = SphericalJoint::define(&stage, "/joint")?;
    common(&joint, &body0, &body1)?;
    joint.create_axis_attr()?.set(tf::Token::from(tokens::Z))?;
    joint.create_cone_angle0_limit_attr()?.set(20.0_f32)?;
    joint.create_cone_angle1_limit_attr()?.set(30.0_f32)?;
    let parsed = parse(&stage)?;
    assert_eq!(
        only_joint(&parsed, &body0, &body1).kind,
        desc::JointKind::Spherical {
            axis: JointAxis::Z,
            limit: desc::Limit {
                enabled: true,
                lower: 20.0,
                upper: 30.0,
            },
        }
    );

    let (stage, body0, body1) = jointed()?;
    let joint = DistanceJoint::define(&stage, "/joint")?;
    common(&joint, &body0, &body1)?;
    joint.create_min_distance_attr()?.set(0.0_f32)?;
    joint.create_max_distance_attr()?.set(10.0_f32)?;
    let parsed = parse(&stage)?;
    assert_eq!(
        only_joint(&parsed, &body0, &body1).kind,
        desc::JointKind::Distance {
            min_enabled: true,
            max_enabled: true,
            limit: desc::Limit {
                enabled: false,
                lower: 0.0,
                upper: 10.0,
            },
        }
    );

    let (stage, body0, body1) = jointed()?;
    let joint = Joint::define(&stage, "/joint")?;
    common(&joint, &body0, &body1)?;
    for (instance, low, high) in [
        (tokens::TRANS_X, -10.0_f32, 10.0_f32),
        (tokens::TRANS_Y, -20.0, 20.0),
        (tokens::ROT_X, -30.0, 30.0),
        (tokens::ROT_Y, 30.0, -30.0),
    ] {
        let limit = LimitAPI::apply(joint.prim(), instance)?;
        limit.create_low_attr()?.set(low)?;
        limit.create_high_attr()?.set(high)?;
    }
    drive(joint.prim(), tokens::ROT_X)?;
    let parsed = parse(&stage)?;
    let desc::JointKind::D6 { limits, drives } = &only_joint(&parsed, &body0, &body1).kind else {
        panic!("a D6 joint");
    };
    let limit = |lower, upper| desc::Limit {
        enabled: true,
        lower,
        upper,
    };
    assert_eq!(
        *limits,
        [
            (Dof::TransX, limit(-10.0, 10.0)),
            (Dof::TransY, limit(-20.0, 20.0)),
            (Dof::RotX, limit(-30.0, 30.0)),
            // A lower bound above the upper locks the degree of freedom.
            (Dof::RotY, limit(30.0, -30.0)),
        ]
    );
    assert_eq!(*drives, [(Dof::RotX, DRIVEN)]);
    Ok(())
}

/// Where the articulation API sits in the articulation tests over three
/// bodies in a chain: on the body at an index (`Floating`), on the bodies'
/// parent (`Auto`), on a fixed joint holding the first body (`Fixed`), or on
/// the parent with that joint present (`AutoFixed`).
#[derive(Clone, Copy, PartialEq)]
enum Variant {
    Floating(usize),
    Auto,
    Fixed,
    AutoFixed,
}

/// Three bodies at `bodies` under `/xform`, joined in a chain by two revolute
/// joints, with the articulation API placed by `variant`; `kinematic` makes
/// the bodies kinematic.
fn articulated(
    variant: Variant,
    bodies: [&str; 3],
    kinematic: bool,
) -> Result<(Stage, [Xform; 3], Option<FixedJoint>)> {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let top = Xform::define(&stage, "/xform")?;
    let mut xforms = Vec::new();
    for path in bodies {
        let (xform, api) = body(&stage, path)?;
        if kinematic {
            api.create_kinematic_enabled_attr()?.set(true)?;
        }
        xforms.push(xform);
    }
    let xforms = <[Xform; 3]>::try_from(xforms).expect("three bodies");
    for (name, (a, b)) in [("/xform/revoluteJoint0", (0, 1)), ("/xform/revoluteJoint1", (1, 2))] {
        let joint = RevoluteJoint::define(&stage, name)?;
        joint.create_body0_rel()?.add_target(xforms[a].path().clone())?;
        joint.create_body1_rel()?.add_target(xforms[b].path().clone())?;
    }
    let fixed = match variant {
        Variant::Fixed | Variant::AutoFixed => {
            let fixed = FixedJoint::define(&stage, "/xform/fixedJoint")?;
            fixed.create_body1_rel()?.add_target(xforms[0].path().clone())?;
            Some(fixed)
        }
        Variant::Floating(_) | Variant::Auto => None,
    };
    let api_prim = match variant {
        Variant::Floating(index) => xforms[index].prim(),
        Variant::Auto | Variant::AutoFixed => top.prim(),
        Variant::Fixed => fixed.as_ref().expect("the fixed joint").prim(),
    };
    ArticulationRootAPI::apply(api_prim)?;
    Ok((stage, xforms, fixed))
}

/// The one articulation parsed, with the counts and root the variant gives.
fn check_articulation(parsed: &Parsed, variant: Variant, root_body: &Xform, fixed: Option<&FixedJoint>) {
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(parsed.articulations.len(), 1, "{:?}", parsed.diagnostics);
    let articulation = &parsed.articulations[0];
    match variant {
        Variant::Floating(_) | Variant::Auto => {
            assert_eq!(articulation.joints.len(), 2);
            assert_eq!(articulation.bodies.len(), 3);
            assert_eq!(articulation.roots, slice::from_ref(root_body.path()));
        }
        Variant::Fixed | Variant::AutoFixed => {
            assert_eq!(articulation.joints.len(), 3);
            // The world counts among the bodies.
            assert_eq!(articulation.bodies.len(), 4);
            assert_eq!(articulation.bodies[0], None);
            assert_eq!(
                articulation.roots,
                slice::from_ref(fixed.expect("the fixed joint").path())
            );
        }
    }
}

const SIBLINGS: [&str; 3] = ["/xform/rigidBody0", "/xform/rigidBody1", "/xform/rigidBody2"];
const NESTED: [&str; 3] = [
    "/xform/rigidBody0",
    "/xform/rigidBody0/rigidBody1",
    "/xform/rigidBody0/rigidBody1/rigidBody2",
];

/// Sibling bodies in a chain: the middle body is the root of a floating
/// articulation, the fixed joint of an anchored one (C++
/// `test_articulation_parse`).
#[test]
fn articulation() -> Result {
    for variant in [Variant::Floating(1), Variant::Auto, Variant::Fixed, Variant::AutoFixed] {
        let (stage, bodies, fixed) = articulated(variant, SIBLINGS, false)?;
        check_articulation(&parse(&stage)?, variant, &bodies[1], fixed.as_ref());
    }
    Ok(())
}

/// Bodies nested in namespace: the top body is the root of a floating
/// articulation (C++ `test_nested_bodies_articulation_parse`).
#[test]
fn nested_articulation() -> Result {
    for variant in [Variant::Floating(0), Variant::Auto, Variant::Fixed] {
        let (stage, bodies, fixed) = articulated(variant, NESTED, false)?;
        check_articulation(&parse(&stage)?, variant, &bodies[0], fixed.as_ref());
    }
    Ok(())
}

/// Kinematic bodies articulate as dynamic ones do (C++
/// `test_articulation_kinematic_parse`).
#[test]
fn kinematic_articulation() -> Result {
    for variant in [Variant::Floating(1), Variant::Auto, Variant::Fixed, Variant::AutoFixed] {
        let (stage, bodies, fixed) = articulated(variant, SIBLINGS, true)?;
        check_articulation(&parse(&stage)?, variant, &bodies[1], fixed.as_ref());
    }
    Ok(())
}

/// Ten groups in a ring of filters, merged by name into seven (C++
/// `test_collision_groups_parse`).
#[test]
fn collision_groups() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let mut groups = Vec::new();
    for i in 0..10 {
        let group = CollisionGroup::define(&stage, format!("/collision_group{i}"))?;
        group.create_invert_filtered_groups_attr()?.set(false)?;
        let filtered = if i == 0 { 9 } else { i - 1 };
        group
            .create_filtered_groups_rel()?
            .add_target(format!("/collision_group{filtered}"))?;
        if i > 0 && i % 3 == 0 {
            group.create_merge_group_name_attr()?.set("three".to_string())?;
        }
        if i > 0 && i % 4 == 0 {
            group.create_merge_group_name_attr()?.set("four".to_string())?;
        }
        groups.push(group);
    }
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(parsed.collision_groups.len(), 7);
    for group in &parsed.collision_groups {
        assert!(!group.invert_filtered_groups);
        match group.merge_group_name.as_str() {
            "three" => {
                assert_eq!(&group.path, groups[3].path());
                assert_eq!(group.merged_groups.len(), 3);
                assert_eq!(
                    paths(&group.filtered_groups),
                    ["/collision_group2", "/collision_group5", "/collision_group8"]
                );
            }
            "four" => {
                assert_eq!(&group.path, groups[4].path());
                assert_eq!(group.merged_groups.len(), 2);
                assert_eq!(
                    paths(&group.filtered_groups),
                    ["/collision_group3", "/collision_group7"]
                );
            }
            "" => {
                assert!(group.merged_groups.is_empty());
                assert_eq!(group.filtered_groups.len(), 1);
            }
            other => panic!("unexpected merge name {other}"),
        }
    }
    Ok(())
}

/// A collider in two groups' collections lists both, in path order (C++
/// `test_collision_groups_collider_parse`).
#[test]
fn group_colliders() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let group0 = CollisionGroup::define(&stage, "/collision_group_0")?;
    let group1 = CollisionGroup::define(&stage, "/collision_group_1")?;
    let (cube, _) = collider(&stage, "/cube")?;
    for group in [&group0, &group1] {
        group
            .colliders_collection()
            .create_includes_rel()?
            .add_target(cube.path().clone())?;
    }
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(parsed.collision_groups.len(), 2);
    assert_eq!(
        only_shape(&parsed).collision_groups,
        [group0.path().clone(), group1.path().clone()]
    );
    Ok(())
}

/// A collider whose authored API schemas name a custom shape token, one the
/// registry does not know (C++ `test_custom_geometry_parse`).
#[test]
fn custom_shape() -> Result {
    let stage = new_stage()?;
    define_scene(&stage)?;
    let cube = Cube::define(&stage, "/cube")?;
    author_api_schemas(cube.prim(), &["MyCustomGeometryAPI", tokens::PHYSICS_COLLISION_API])?;
    let custom = CustomTokens {
        shapes: vec![tf::Token::from("MyCustomGeometryAPI")],
        ..CustomTokens::default()
    };
    let parsed = physics::parse(
        &stage,
        &from_root(ParseOptions {
            custom,
            ..ParseOptions::default()
        }),
    )?;
    assert_eq!(parsed.scenes.len(), 1);
    assert_eq!(
        only_shape(&parsed).geometry,
        desc::Geometry::Custom(tf::Token::from("MyCustomGeometryAPI"))
    );
    Ok(())
}

/// Each of many custom colliders reports the token that matched it (C++
/// `test_custom_geometry_multithreading_parse`).
#[test]
fn custom_shape_tokens() -> Result {
    const COLLIDERS: usize = 500;
    let stage = new_stage()?;
    define_scene(&stage)?;
    body(&stage, "/Body")?;
    let names = ["CustomGeomA_API", "CustomGeomB_API"];
    for k in 0..COLLIDERS {
        let cube = Cube::define(&stage, format!("/Body/CustomCollider_{k}"))?;
        author_api_schemas(cube.prim(), &[names[k % 2], tokens::PHYSICS_COLLISION_API])?;
    }
    let custom = CustomTokens {
        shapes: names.iter().map(|name| tf::Token::from(*name)).collect(),
        ..CustomTokens::default()
    };
    let parsed = physics::parse(
        &stage,
        &from_root(ParseOptions {
            custom,
            ..ParseOptions::default()
        }),
    )?;
    assert_eq!(parsed.shapes.len(), COLLIDERS);
    for shape in &parsed.shapes {
        let k: usize = shape
            .path
            .name()
            .and_then(|name| name.strip_prefix("CustomCollider_"))
            .and_then(|k| k.parse().ok())
            .expect("a collider path");
        assert_eq!(
            shape.geometry,
            desc::Geometry::Custom(tf::Token::from(names[k % 2])),
            "{}",
            shape.path
        );
    }
    Ok(())
}

/// Which bodies and scenes `simulation_owners` keeps (the body half of C++
/// `test_rigid_body_simulation_owner_parse`).
#[test]
fn body_owner() -> Result {
    let stage = new_stage()?;
    let scene = define_scene(&stage)?;
    let cube = Cube::define(&stage, "/cube")?;
    let api = RigidBodyAPI::apply(cube.prim())?;
    let found = |parsed: &Parsed| (parsed.scenes.len(), parsed.rigid_bodies.len());

    assert_eq!(found(&parse_owned(&stage, vec![scene.path().clone()])?), (1, 0));
    assert_eq!(found(&parse_owned(&stage, vec![Path::default()])?), (0, 1));
    api.create_simulation_owner_rel()?.add_target(scene.path().clone())?;
    assert_eq!(found(&parse_owned(&stage, vec![scene.path().clone()])?), (1, 1));
    Ok(())
}

/// Which scenes `simulation_owners` keeps: those listed, whatever else the
/// list says. An empty list drops them all and filters nothing else.
#[test]
fn scene_owners() -> Result {
    let stage = new_stage()?;
    let scene = define_scene(&stage)?;
    Scene::define(&stage, "/otherScene")?;
    body(&stage, "/body")?;
    let parsed = parse_owned(&stage, vec![scene.path().clone()])?;
    assert_eq!(
        paths(parsed.scenes.iter().map(|scene| &scene.path)),
        [scene.path().to_string()]
    );
    let parsed = parse_owned(&stage, vec![])?;
    assert!(parsed.scenes.is_empty());
    assert_eq!(parsed.rigid_bodies.len(), 1);
    assert_eq!(parse(&stage)?.scenes.len(), 2);
    Ok(())
}

/// A collider follows its body's fate under `simulation_owners`; a static
/// collider has owners of its own (C++ `test_collision_simulation_owner_parse`).
#[test]
fn collision_owner() -> Result {
    let found = |parsed: &Parsed| (parsed.scenes.len(), parsed.rigid_bodies.len(), parsed.shapes.len());

    let stage = new_stage()?;
    let scene = define_scene(&stage)?;
    let (_, api) = body(&stage, "/xform")?;
    collider(&stage, "/xform/cube")?;
    assert_eq!(found(&parse_owned(&stage, vec![scene.path().clone()])?), (1, 0, 0));
    assert_eq!(found(&parse_owned(&stage, vec![Path::default()])?), (0, 1, 1));
    api.create_simulation_owner_rel()?.add_target(scene.path().clone())?;
    assert_eq!(found(&parse_owned(&stage, vec![scene.path().clone()])?), (1, 1, 1));

    // The same scene without the body's API (the C++ test removes it).
    let stage = new_stage()?;
    let scene = define_scene(&stage)?;
    Xform::define(&stage, "/xform")?;
    let (_, collision) = collider(&stage, "/xform/cube")?;
    assert_eq!(found(&parse_owned(&stage, vec![Path::default()])?), (0, 0, 1));
    assert_eq!(found(&parse_owned(&stage, vec![scene.path().clone()])?), (1, 0, 0));
    collision
        .create_simulation_owner_rel()?
        .add_target(scene.path().clone())?;
    assert_eq!(found(&parse_owned(&stage, vec![scene.path().clone()])?), (1, 0, 1));
    Ok(())
}

/// A joint is kept when each of its bodies is missing or kept (C++
/// `test_joint_simulation_owner_parse`).
#[test]
fn joint_owner() -> Result {
    let stage = new_stage()?;
    let scene = define_scene(&stage)?;
    let (xform0, api0) = body(&stage, "/xform0")?;
    let (xform1, api1) = body(&stage, "/xform1")?;
    let joint = FixedJoint::define(&stage, "/fixedJoint")?;
    let found = |parsed: &Parsed| (parsed.scenes.len(), parsed.rigid_bodies.len(), parsed.joints.len());
    let owner = scene.path().clone();

    // The C++ cases accumulate on one stage: body0 first, then body1, then
    // both again.
    for case in ["body0", "body1", "both"] {
        api0.create_simulation_owner_rel()?.clear_targets()?;
        api1.create_simulation_owner_rel()?.clear_targets()?;
        if case != "body1" {
            joint.create_body0_rel()?.add_target(xform0.path().clone())?;
        }
        if case != "body0" {
            joint.create_body1_rel()?.add_target(xform1.path().clone())?;
        }
        assert_eq!(found(&parse_owned(&stage, vec![owner.clone()])?), (1, 0, 0), "{case}");
        assert_eq!(found(&parse_owned(&stage, vec![Path::default()])?), (0, 2, 1), "{case}");
        api0.create_simulation_owner_rel()?.add_target(owner.clone())?;
        api1.create_simulation_owner_rel()?.add_target(owner.clone())?;
        assert_eq!(found(&parse_owned(&stage, vec![owner.clone()])?), (1, 2, 1), "{case}");
        api0.create_simulation_owner_rel()?.clear_targets()?;
        api1.create_simulation_owner_rel()?.add_target(owner.clone())?;
        assert_eq!(found(&parse_owned(&stage, vec![owner.clone()])?), (1, 1, 0), "{case}");
        assert_eq!(
            found(&parse_owned(&stage, vec![Path::default(), owner.clone()])?),
            (1, 2, 1),
            "{case}"
        );
    }
    Ok(())
}

/// An articulation is kept when every body of it is (C++
/// `test_articulation_simulation_owner_parse`).
#[test]
fn articulation_owner() -> Result {
    let stage = new_stage()?;
    let scene = define_scene(&stage)?;
    let xform = Xform::define(&stage, "/xform")?;
    ArticulationRootAPI::apply(xform.prim())?;
    let mut cubes = Vec::new();
    for i in 0..3 {
        let cube = Cube::define(&stage, format!("/xform/cube{i}"))?;
        cubes.push((cube.path().clone(), RigidBodyAPI::apply(cube.prim())?));
    }
    for (name, (a, b)) in [("/xform/revoluteJoint0", (0, 1)), ("/xform/revoluteJoint1", (1, 2))] {
        let joint = RevoluteJoint::define(&stage, name)?;
        joint.create_body0_rel()?.add_target(cubes[a].0.clone())?;
        joint.create_body1_rel()?.add_target(cubes[b].0.clone())?;
    }
    let found = |parsed: &Parsed| {
        (
            parsed.scenes.len(),
            parsed.rigid_bodies.len(),
            parsed.joints.len(),
            parsed.articulations.len(),
        )
    };
    let owner = scene.path().clone();
    assert_eq!(found(&parse_owned(&stage, vec![owner.clone()])?), (1, 0, 0, 0));
    assert_eq!(found(&parse_owned(&stage, vec![Path::default()])?), (0, 3, 2, 1));
    cubes[0].1.create_simulation_owner_rel()?.add_target(owner.clone())?;
    cubes[1].1.create_simulation_owner_rel()?.add_target(owner.clone())?;
    assert_eq!(found(&parse_owned(&stage, vec![owner.clone()])?), (1, 2, 1, 0));
    cubes[2].1.create_simulation_owner_rel()?.add_target(owner.clone())?;
    assert_eq!(found(&parse_owned(&stage, vec![owner])?), (1, 3, 2, 1));
    Ok(())
}

/// An API schema that builds in `PhysicsCollisionAPI` makes its prim a
/// collider (C++ `test_SimpleTypedSchemaPrimDefinition`, over the test
/// schema under `testUsdPhysicsParsing/resources`).
#[test]
fn nested_api_schema() -> Result {
    const MANIFEST: &str = r#"#usda 1.0

def "TestNestedPhysicsCollisionAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
}
"#;
    const SCHEMATICS: &str = r#"#usda 1.0
(
)

class TestNestedPhysicsCollisionAPI "TestNestedPhysicsCollisionAPI" (
    apiSchemas = ["PhysicsCollisionAPI"]
)
{
}
"#;
    let manifest = sdf::Layer::from_bytes("manifest.usda", MANIFEST.as_bytes().to_vec()).expect("the manifest parses");
    let schematics =
        sdf::Layer::from_bytes("generatedSchema.usda", SCHEMATICS.as_bytes().to_vec()).expect("the schematics parse");
    let registry = openusd_schemas::ALL
        .iter()
        .fold(SchemaRegistry::builder(), |builder, family| builder.register(family))
        .family(FamilySource {
            name: "testUsdPhysicsParsing",
            manifest: &manifest,
            schematics: &schematics,
        })
        .build()
        .expect("the test family registers");
    let stage = Stage::builder().schema_registry(registry).in_memory("nested.usda")?;
    define_scene(&stage)?;
    let cube = Cube::define(&stage, "/cube")?;
    cube.prim().clone().apply_api("TestNestedPhysicsCollisionAPI")?;
    assert!(cube.prim().has_api_schema("TestNestedPhysicsCollisionAPI")?);
    assert!(cube.prim().has_api_schema(tokens::PHYSICS_COLLISION_API)?);
    let parsed = parse(&stage)?;
    assert_eq!(parsed.scenes.len(), 1);
    assert!(matches!(only_shape(&parsed).geometry, desc::Geometry::Cube { .. }));
    Ok(())
}

// The cases below are the port's own.

#[test]
fn empty_includes() -> Result {
    let stage = new_stage()?;
    assert!(matches!(
        physics::parse(&stage, &ParseOptions::default()),
        Err(SchemaError::EmptyIncludePaths)
    ));
    Ok(())
}

/// An excluded prim and its subtree are left out.
#[test]
fn exclude_prunes() -> Result {
    let stage = new_stage()?;
    body(&stage, "/a")?;
    body(&stage, "/a/b")?;
    let (c, _) = body(&stage, "/c")?;
    let parsed = physics::parse(
        &stage,
        &from_root(ParseOptions {
            exclude: vec![path("/a")],
            ..ParseOptions::default()
        }),
    )?;
    assert_eq!(
        paths(parsed.rigid_bodies.iter().map(|body| &body.path)),
        [c.path().to_string()]
    );
    Ok(())
}

/// A point instancer is classified itself but nothing under it is.
#[test]
fn instancer_pruned() -> Result {
    let stage = new_stage()?;
    let instancer = PointInstancer::define(&stage, "/inst")?;
    RigidBodyAPI::apply(instancer.prim())?;
    body(&stage, "/inst/body")?;
    let parsed = parse(&stage)?;
    assert_eq!(
        paths(parsed.rigid_bodies.iter().map(|body| &body.path)),
        [instancer.path().to_string()]
    );
    Ok(())
}

/// A prim of a custom instancer type prunes its subtree as a point instancer
/// does.
#[test]
fn custom_instancer_pruned() -> Result {
    let stage = new_stage()?;
    stage.define_prim("/custom")?.set_type_name("MyInstancer")?;
    body(&stage, "/custom/body")?;
    assert_eq!(parse(&stage)?.rigid_bodies.len(), 1);
    let parsed = physics::parse(
        &stage,
        &from_root(ParseOptions {
            custom: CustomTokens {
                instancers: vec![tf::Token::from("MyInstancer")],
                ..CustomTokens::default()
            },
            ..ParseOptions::default()
        }),
    )?;
    assert!(parsed.rigid_bodies.is_empty());
    Ok(())
}

/// A prim with both `PhysicsMaterialAPI` and `PhysicsCollisionAPI` is a
/// material only where the material comes first in `apiSchemas`, as the C++
/// flag loop has it. A low-level compatibility case.
#[test]
fn material_flag_order() -> Result {
    let stage = new_stage()?;
    let first = Cube::define(&stage, "/materialFirst")?;
    author_api_schemas(
        first.prim(),
        &[tokens::PHYSICS_MATERIAL_API, tokens::PHYSICS_COLLISION_API],
    )?;
    let second = Cube::define(&stage, "/collisionFirst")?;
    author_api_schemas(
        second.prim(),
        &[tokens::PHYSICS_COLLISION_API, tokens::PHYSICS_MATERIAL_API],
    )?;
    let parsed = parse(&stage)?;
    assert_eq!(
        paths(parsed.materials.iter().map(|material| &material.path)),
        [first.path().to_string()]
    );
    assert_eq!(
        paths(parsed.shapes.iter().map(|shape| &shape.path)),
        [second.path().to_string()]
    );
    Ok(())
}

/// A prim under two include paths is reported once.
#[test]
fn include_twice() -> Result {
    let stage = new_stage()?;
    Xform::define(&stage, "/World")?;
    body(&stage, "/World/Body")?;
    collider(&stage, "/World/Body/cube")?;
    let parsed = physics::parse(
        &stage,
        &ParseOptions {
            include: vec![path("/World"), path("/World/Body")],
            ..ParseOptions::default()
        },
    )?;
    assert_eq!(parsed.rigid_bodies.len(), 1);
    assert_eq!(parsed.shapes.len(), 1);
    assert_eq!(parsed.rigid_bodies[0].collisions.len(), 1);
    Ok(())
}

/// Merging a group moves the last group into its slot. For A1, A2, B1, B2
/// the representative of B is therefore B2, with its own flag, as in C++.
#[test]
fn merge_representative() -> Result {
    let stage = new_stage()?;
    for (name, merge, invert) in [
        ("/A1", "A", false),
        ("/A2", "A", false),
        ("/B1", "B", false),
        ("/B2", "B", true),
    ] {
        let group = CollisionGroup::define(&stage, name)?;
        group.create_merge_group_name_attr()?.set(merge.to_string())?;
        group.create_invert_filtered_groups_attr()?.set(invert)?;
    }
    let parsed = parse(&stage)?;
    assert_eq!(parsed.collision_groups.len(), 2);
    let b = parsed
        .collision_groups
        .iter()
        .find(|group| group.merge_group_name == "B")
        .expect("the B group");
    assert_eq!(b.path, path("/B2"));
    assert!(b.invert_filtered_groups);
    assert_eq!(paths(&b.merged_groups), ["/B2", "/B1"]);
    Ok(())
}

/// `PhysicsCollisionAPI` on a prim of no supported shape is a diagnostic.
#[test]
fn unknown_shape() -> Result {
    let stage = new_stage()?;
    let xform = Xform::define(&stage, "/thing")?;
    CollisionAPI::apply(xform.prim())?;
    let parsed = parse(&stage)?;
    assert!(parsed.shapes.is_empty());
    assert_eq!(
        parsed.diagnostics,
        [ParseDiagnostic::UnknownShape(xform.path().clone())]
    );
    Ok(())
}

/// A `Points` collider without widths, with blocked widths, or with a count
/// mismatch is a diagnostic.
#[test]
fn points_diagnostics() -> Result {
    let stage = new_stage()?;
    let bare = Points::define(&stage, "/bare")?;
    CollisionAPI::apply(bare.prim())?;
    let blocked = Points::define(&stage, "/blocked")?;
    blocked.create_widths_attr()?.set(vec![1.0_f32])?.block()?;
    CollisionAPI::apply(blocked.prim())?;
    let mismatch = Points::define(&stage, "/mismatch")?;
    mismatch.create_widths_attr()?.set(vec![1.0_f32, 2.0])?;
    mismatch.create_points_attr()?.set(vec![gf::Vec3f::default()])?;
    CollisionAPI::apply(mismatch.prim())?;
    let parsed = parse(&stage)?;
    assert!(parsed.shapes.is_empty());
    assert_eq!(
        parsed.diagnostics,
        [
            ParseDiagnostic::PointsWithoutWidths(bare.path().clone()),
            ParseDiagnostic::PointsWithoutWidths(blocked.path().clone()),
            ParseDiagnostic::PointsWidthCount {
                path: mismatch.path().clone(),
                points: 1,
                widths: 2,
            },
        ]
    );
    Ok(())
}

/// A physics binding authored without `MaterialBindingAPI` applied binds no
/// material to a collider, as the C++ binding view is invalid there.
#[test]
fn binding_without_api() -> Result {
    let stage = new_stage()?;
    let (cube, _) = collider(&stage, "/cube")?;
    let material = physics_material(&stage, "/physicsMaterial")?;
    MaterialBindingAPI::from_prim_unchecked(cube.prim().clone()).bind_for_purpose(
        MATERIAL_PURPOSE,
        material.path().clone(),
        None,
    )?;
    let parsed = parse(&stage)?;
    assert!(only_shape(&parsed).materials.is_empty());
    assert_eq!(parsed.materials.len(), 1);
    Ok(())
}

/// A blocked shape attribute reads as its fallback.
#[test]
fn blocked_shape() -> Result {
    let stage = new_stage()?;
    let sphere = placed(Sphere::define(&stage, "/sphere")?)?;
    sphere.create_radius_attr()?.set(30.0_f64)?.block()?;
    CollisionAPI::apply(sphere.prim())?;
    let parsed = parse(&stage)?;
    assert_eq!(only_shape(&parsed).geometry, desc::Geometry::Sphere { radius: SCALE.x });
    Ok(())
}

/// A collider under a disabled body still names that body.
#[test]
fn disabled_body_collider() -> Result {
    let stage = new_stage()?;
    let (xform, api) = body(&stage, "/static")?;
    api.create_rigid_body_enabled_attr()?.set(false)?;
    collider(&stage, "/static/cube")?;
    let parsed = parse(&stage)?;
    assert!(!parsed.rigid_bodies[0].enabled);
    assert_eq!(only_shape(&parsed).rigid_body.as_ref(), Some(xform.path()));
    assert_eq!(parsed.rigid_bodies[0].collisions.len(), 1);
    Ok(())
}

/// A body above the include path is no body of the parse. Its collider is
/// static.
#[test]
fn body_outside_range() -> Result {
    let stage = new_stage()?;
    body(&stage, "/World")?;
    collider(&stage, "/World/cube")?;
    let parsed = physics::parse(
        &stage,
        &ParseOptions {
            include: vec![path("/World/cube")],
            ..ParseOptions::default()
        },
    )?;
    assert!(parsed.rigid_bodies.is_empty());
    assert_eq!(only_shape(&parsed).rigid_body, None);
    Ok(())
}

/// A joint rel to a collider under a body reaches the body, and the anchor
/// is re-expressed in the body's frame.
#[test]
fn joint_rel_collider() -> Result {
    let stage = new_stage()?;
    let (xform, _) = body(&stage, "/body")?;
    xform.clone().set_translate(gf::vec3d(10.0, 0.0, 0.0))?;
    let (cube, _) = collider(&stage, "/body/cube")?;
    cube.clone().set_translate(gf::vec3d(0.0, 5.0, 0.0))?;
    let joint = FixedJoint::define(&stage, "/joint")?;
    joint.create_body0_rel()?.add_target(cube.path().clone())?;
    let parsed = parse(&stage)?;
    let desc = &parsed.joints[0];
    assert_eq!(desc.rel0.as_ref(), Some(cube.path()));
    assert_eq!(desc.body0.as_ref(), Some(xform.path()));
    assert!(
        close(desc.local_pos0, gf::vec3f(0.0, 5.0, 0.0)),
        "{:?}",
        desc.local_pos0
    );
    assert!(close(euler_xyz(desc.local_rot0), gf::Vec3f::default()));
    Ok(())
}

/// A joint rel to a path where nothing composes gives no body and keeps the
/// authored anchor.
#[test]
fn joint_rel_missing() -> Result {
    let stage = new_stage()?;
    let joint = FixedJoint::define(&stage, "/joint")?;
    joint.create_body0_rel()?.add_target(path("/nothing"))?;
    joint.create_local_pos0_attr()?.set(gf::vec3f(1.0, 2.0, 3.0))?;
    let parsed = parse(&stage)?;
    let desc = &parsed.joints[0];
    assert_eq!(desc.rel0, Some(path("/nothing")));
    assert_eq!(desc.body0, None);
    assert_eq!(desc.local_pos0, gf::vec3f(1.0, 2.0, 3.0));
    Ok(())
}

/// A joint's body is found on the stage, even above the include path.
#[test]
fn joint_body_outside_range() -> Result {
    let stage = new_stage()?;
    let (world, _) = body(&stage, "/World")?;
    let joint = FixedJoint::define(&stage, "/World/joint")?;
    joint.create_body0_rel()?.add_target(world.path().clone())?;
    let parsed = physics::parse(
        &stage,
        &ParseOptions {
            include: vec![joint.path().clone()],
            ..ParseOptions::default()
        },
    )?;
    assert!(parsed.rigid_bodies.is_empty());
    assert_eq!(parsed.joints[0].body0.as_ref(), Some(world.path()));
    Ok(())
}

/// Blocked limits read as their infinite fallbacks, which disable the limit.
#[test]
fn blocked_limit() -> Result {
    let stage = new_stage()?;
    let joint = RevoluteJoint::define(&stage, "/joint")?;
    joint.create_lower_limit_attr()?.set(0.0_f32)?.block()?;
    joint.create_upper_limit_attr()?.set(90.0_f32)?.block()?;
    let parsed = parse(&stage)?;
    let desc::JointKind::Revolute { limit, .. } = &parsed.joints[0].kind else {
        panic!("a revolute joint");
    };
    assert!(!limit.enabled);
    assert_eq!((limit.lower, limit.upper), (f32::NEG_INFINITY, f32::INFINITY));
    Ok(())
}

/// A finite bound at the sentinel is no bound, and one just inside it is:
/// either bound of a prismatic joint enables its limit.
#[test]
fn sentinel_limit() -> Result {
    let enabled = |lower: f32, upper: f32| -> Result<bool> {
        let stage = new_stage()?;
        let joint = PrismaticJoint::define(&stage, "/joint")?;
        joint.create_lower_limit_attr()?.set(lower)?;
        joint.create_upper_limit_attr()?.set(upper)?;
        let parsed = parse(&stage)?;
        let desc::JointKind::Prismatic { limit, .. } = &parsed.joints[0].kind else {
            panic!("a prismatic joint");
        };
        Ok(limit.enabled)
    };
    let sentinel = desc::Limit::SENTINEL;
    let inside = sentinel * 0.5;
    assert!(!enabled(-sentinel, sentinel)?);
    assert!(enabled(-inside, sentinel)?);
    assert!(enabled(-sentinel, inside)?);
    Ok(())
}

/// A blocked `maxForce` reads as its infinite fallback.
#[test]
fn blocked_drive() -> Result {
    let stage = new_stage()?;
    let joint = RevoluteJoint::define(&stage, "/joint")?;
    DriveAPI::apply(joint.prim(), tokens::ANGULAR)?
        .create_max_force_attr()?
        .set(5.0_f32)?
        .block()?;
    let parsed = parse(&stage)?;
    let desc::JointKind::Revolute { drive, .. } = &parsed.joints[0].kind else {
        panic!("a revolute joint");
    };
    assert_eq!(drive.map(|drive| drive.force_limit), Some(f32::INFINITY));
    Ok(())
}

/// An articulation prim with no body under it has no root.
#[test]
fn articulation_no_root() -> Result {
    let stage = new_stage()?;
    let xform = Xform::define(&stage, "/xform")?;
    ArticulationRootAPI::apply(xform.prim())?;
    let parsed = parse(&stage)?;
    assert!(parsed.articulations.is_empty());
    assert_eq!(
        parsed.diagnostics,
        [ParseDiagnostic::ArticulationWithoutRoot(xform.path().clone())]
    );
    Ok(())
}

/// Of a link's joints to the world, the last in joint path order is its root
/// joint, whatever the order they were defined in.
#[test]
fn articulation_root_joint_order() -> Result {
    let stage = new_stage()?;
    let xform = Xform::define(&stage, "/xform")?;
    ArticulationRootAPI::apply(xform.prim())?;
    let (link, _) = body(&stage, "/xform/body")?;
    for name in ["/xform/zJoint", "/xform/aJoint"] {
        let joint = FixedJoint::define(&stage, name)?;
        joint.create_body1_rel()?.add_target(link.path().clone())?;
    }
    let parsed = parse(&stage)?;
    assert_eq!(parsed.articulations[0].roots, [path("/xform/zJoint")]);
    assert_eq!(parsed.articulations[0].bodies, [None]);
    Ok(())
}

/// An articulation over two disjoint chains chooses a root per chain.
#[test]
fn articulation_two_chains() -> Result {
    let stage = new_stage()?;
    let xform = Xform::define(&stage, "/xform")?;
    ArticulationRootAPI::apply(xform.prim())?;
    let mut roots = Vec::new();
    for chain in ["a", "b"] {
        let (first, _) = body(&stage, &format!("/xform/{chain}0"))?;
        let (second, _) = body(&stage, &format!("/xform/{chain}1"))?;
        let joint = RevoluteJoint::define(&stage, format!("/xform/{chain}Joint"))?;
        joint.create_body0_rel()?.add_target(first.path().clone())?;
        joint.create_body1_rel()?.add_target(second.path().clone())?;
        // A two-link chain's center is the link the walk reached first.
        roots.push(first.path().clone());
    }
    let parsed = parse(&stage)?;
    let articulation = &parsed.articulations[0];
    assert_eq!(articulation.roots, roots);
    assert_eq!(articulation.joints.len(), 2);
    assert_eq!(articulation.bodies.len(), 4);
    Ok(())
}

/// A body's colliders come kind by kind in the C++ report order, by path
/// within a kind.
#[test]
fn body_collision_order() -> Result {
    let stage = new_stage()?;
    body(&stage, "/B")?;
    collider(&stage, "/B/a_cube")?;
    let sphere = Sphere::define(&stage, "/B/z_sphere")?;
    CollisionAPI::apply(sphere.prim())?;
    let parsed = parse(&stage)?;
    assert_eq!(paths(&parsed.rigid_bodies[0].collisions), ["/B/z_sphere", "/B/a_cube"]);
    Ok(())
}

/// The API on a joint with neither body roots the articulation at the joint
/// and finds nothing else.
#[test]
fn articulation_joint_no_bodies() -> Result {
    let stage = new_stage()?;
    let joint = FixedJoint::define(&stage, "/joint")?;
    ArticulationRootAPI::apply(joint.prim())?;
    let parsed = parse(&stage)?;
    assert!(parsed.diagnostics.is_empty());
    let articulation = &parsed.articulations[0];
    assert_eq!(articulation.roots, [joint.path().clone()]);
    assert!(articulation.joints.is_empty());
    assert!(articulation.bodies.is_empty());
    Ok(())
}

// The example scenes the C++ library ships under `usdPhysics/examples`, kept
// under `fixtures/usdPhysics_examples`. The expectations are read off the
// files; real OpenUSD's `UsdPhysics.UsdPhysicsLoadStageFromPrimRange` is the
// cross-check.

/// The example `name` parsed from the root, with nothing left unreported.
fn example(name: &str) -> Result<Parsed> {
    let stage = Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(&format!("fixtures/usdPhysics_examples/{name}.usda"))?;
    let parsed = physics::parse(&stage, &from_root(ParseOptions::default()))?;
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    Ok(parsed)
}

/// How many of each kind `parsed` holds, in field order.
fn counts(parsed: &Parsed) -> [usize; 7] {
    [
        parsed.scenes.len(),
        parsed.collision_groups.len(),
        parsed.materials.len(),
        parsed.shapes.len(),
        parsed.articulations.len(),
        parsed.rigid_bodies.len(),
        parsed.joints.len(),
    ]
}

fn shape_at<'a>(parsed: &'a Parsed, path: &str) -> &'a desc::Shape {
    parsed
        .shapes
        .iter()
        .find(|shape| shape.path.as_str() == path)
        .unwrap_or_else(|| panic!("no shape at {path}"))
}

fn body_at<'a>(parsed: &'a Parsed, path: &str) -> &'a desc::RigidBody {
    parsed
        .rigid_bodies
        .iter()
        .find(|body| body.path.as_str() == path)
        .unwrap_or_else(|| panic!("no body at {path}"))
}

fn joint_at<'a>(parsed: &'a Parsed, path: &str) -> &'a desc::Joint {
    parsed
        .joints
        .iter()
        .find(|joint| joint.path.as_str() == path)
        .unwrap_or_else(|| panic!("no joint at {path}"))
}

/// A body falling on a static box; Earth's gravity along the negative Z up
/// axis in centimeters.
#[test]
fn example_box_on_box() -> Result {
    let parsed = example("usdPhysicsBoxOnBox")?;
    assert_eq!(counts(&parsed), [1, 0, 0, 2, 0, 1, 0]);
    let scene = &parsed.scenes[0];
    assert!(close(scene.gravity_direction, gf::vec3f(0.0, 0.0, -1.0)));
    assert!((scene.gravity_magnitude - 981.0).abs() < TOLERANCE);
    let actor = body_at(&parsed, "/World/BoxActor");
    assert_eq!(actor.collisions, [path("/World/BoxActor")]);
    assert!(close(actor.linear_velocity, gf::vec3f(2.0, 1.0, 2.0)));
    assert!(close(actor.angular_velocity, gf::vec3f(1.0, 0.0, 0.0)));
    assert_eq!(
        shape_at(&parsed, "/World/BoxActor").rigid_body,
        Some(path("/World/BoxActor"))
    );
    assert_eq!(shape_at(&parsed, "/World/Ground").rigid_body, None);
    Ok(())
}

/// A body on a convex-hull mesh ground.
#[test]
fn example_box_on_quad() -> Result {
    let parsed = example("usdPhysicsBoxOnQuad")?;
    assert_eq!(counts(&parsed), [1, 0, 0, 2, 0, 1, 0]);
    let desc::Geometry::Mesh {
        approximation,
        double_sided,
        ..
    } = &shape_at(&parsed, "/World/Ground").geometry
    else {
        panic!("a mesh ground");
    };
    assert_eq!(approximation, tokens::CONVEX_HULL);
    assert!(double_sided);
    assert_eq!(
        shape_at(&parsed, "/World/BoxActor").rigid_body,
        Some(path("/World/BoxActor"))
    );
    Ok(())
}

/// The file's `DistancePhysicsJoint` names no schema type. The parser reports
/// no joint for it, as C++ does.
#[test]
fn example_distance_joint() -> Result {
    let parsed = example("usdPhysicsDistanceJoint")?;
    assert_eq!(counts(&parsed), [1, 0, 0, 2, 0, 1, 0]);
    Ok(())
}

/// Two bodies in one collision group that filters itself.
#[test]
fn example_group_filtering() -> Result {
    let parsed = example("usdPhysicsGroupFiltering")?;
    assert_eq!(counts(&parsed), [1, 1, 0, 3, 0, 2, 0]);
    let group = &parsed.collision_groups[0];
    assert_eq!(group.path, path("/World/DynamicGroup"));
    assert_eq!(group.filtered_groups, [path("/World/DynamicGroup")]);
    assert!(group.merged_groups.is_empty());
    for box_ in ["/World/Box1", "/World/Box2"] {
        assert_eq!(shape_at(&parsed, box_).collision_groups, slice::from_ref(&group.path));
    }
    assert!(shape_at(&parsed, "/World/Ground").collision_groups.is_empty());
    Ok(())
}

/// A D6 joint locking five degrees of freedom and driving the sixth; its
/// static side is a collider, which stands in for a body.
#[test]
fn example_joints() -> Result {
    let parsed = example("usdPhysicsJoints")?;
    assert_eq!(counts(&parsed), [1, 0, 0, 2, 0, 1, 1]);
    let joint = joint_at(&parsed, "/World/D6Joint");
    assert_eq!(joint.body0, Some(path("/World/StaticBox")));
    assert_eq!(joint.body1, Some(path("/World/DynamicBox")));
    let desc::JointKind::D6 { limits, drives } = &joint.kind else {
        panic!("a D6 joint");
    };
    let locked = desc::Limit {
        enabled: true,
        lower: 1.0,
        upper: -1.0,
    };
    assert_eq!(
        *limits,
        [
            (Dof::TransX, locked),
            (Dof::TransY, locked),
            (Dof::TransZ, locked),
            (Dof::RotX, locked),
            (Dof::RotY, locked),
        ]
    );
    assert_eq!(
        *drives,
        [(
            Dof::RotZ,
            desc::Drive {
                target_position: 0.0,
                target_velocity: 10.0,
                force_limit: f32::INFINITY,
                stiffness: 0.0,
                damping: 9999.0,
                acceleration: false,
            },
        )]
    );
    Ok(())
}

/// A two-body hinge fixed to the world, its bodies nested in namespace and
/// the API on the first.
#[test]
fn example_nested_articulation() -> Result {
    let parsed = example("usdPhysicsNestedArticulation")?;
    assert_eq!(counts(&parsed), [1, 0, 0, 2, 1, 2, 2]);
    let scene = &parsed.scenes[0];
    assert!(close(scene.gravity_direction, gf::vec3f(0.0, 0.0, -1.0)));
    assert!((scene.gravity_magnitude - 9.81).abs() < TOLERANCE);
    let (body1, body2) = (path("/Hinge/Body1"), path("/Hinge/Body1/Body2"));
    assert_eq!(shape_at(&parsed, "/Hinge/Body1/Box1").rigid_body, Some(body1.clone()));
    assert_eq!(
        shape_at(&parsed, "/Hinge/Body1/Body2/Box2").rigid_body,
        Some(body2.clone())
    );
    let hinge = joint_at(&parsed, "/Hinge/Body1/Body2/PhysicsRevoluteJoint");
    assert_eq!(
        (&hinge.body0, &hinge.body1),
        (&Some(body1.clone()), &Some(body2.clone()))
    );
    let desc::JointKind::Revolute { axis, limit, drive } = &hinge.kind else {
        panic!("a revolute joint");
    };
    assert_eq!(*axis, JointAxis::X);
    assert_eq!(
        *limit,
        desc::Limit {
            enabled: true,
            lower: -90.0,
            upper: 10.0,
        }
    );
    assert_eq!(*drive, None);
    // The fixed joint's first rel names `/Hinge`, which is no body and has no
    // collider above it.
    let anchor = joint_at(&parsed, "/Hinge/Body1/PhysicsFixedJoint");
    assert_eq!((&anchor.body0, &anchor.body1), (&None, &Some(body1.clone())));
    let articulation = &parsed.articulations[0];
    assert_eq!(articulation.roots, slice::from_ref(&body1));
    assert_eq!(articulation.joints.len(), 2);
    assert_eq!(articulation.bodies, [None, Some(body1), Some(body2)]);
    Ok(())
}

/// A filtered pair authored on a body that is also a collider shows on both.
#[test]
fn example_pair_filtering() -> Result {
    let parsed = example("usdPhysicsPairFiltering")?;
    assert_eq!(counts(&parsed), [1, 0, 0, 3, 0, 2, 0]);
    let filtered = [path("/World/Box1")];
    assert_eq!(body_at(&parsed, "/World/Box2").filtered_collisions, filtered);
    assert_eq!(shape_at(&parsed, "/World/Box2").filtered_collisions, filtered);
    assert!(body_at(&parsed, "/World/Box1").filtered_collisions.is_empty());
    Ok(())
}

/// Two physics materials; the spheres author their bindings without
/// `MaterialBindingAPI` applied. Neither C++ nor the port binds them.
#[test]
fn example_spheres_with_material() -> Result {
    let parsed = example("usdPhysicsSpheresWithMaterial")?;
    assert_eq!(counts(&parsed), [1, 0, 2, 3, 0, 2, 0]);
    let restitution: Vec<(String, f32)> = parsed
        .materials
        .iter()
        .map(|material| (material.path.to_string(), material.restitution))
        .collect();
    assert_eq!(
        restitution,
        [
            ("/World/Looks/RegularMaterial".to_string(), 0.1),
            ("/World/Looks/BouncyMaterial".to_string(), 0.8),
        ]
    );
    for sphere in ["/World/RegularSphere", "/World/BouncySphere"] {
        let shape = shape_at(&parsed, sphere);
        assert!(shape.materials.is_empty());
        assert_eq!(shape.rigid_body, Some(path(sphere)));
    }
    Ok(())
}
