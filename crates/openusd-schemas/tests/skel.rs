//! Integration tests for the UsdSkel views against a fixture that exercises
//! every schema family, plus the time-independent object-model layer
//! (topology, AnimMapper, SkeletonResolver, SkinningResolver, binding
//! discovery).

use openusd::Result;
use openusd::gf::{self, Mat4d, Quatf, Vec3f};
use openusd::sdf::{self, Value};
use openusd::usd::{PrimPredicate, SchemaBase, Stage, TimeCode};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::BoundableSchema;
use openusd_schemas::skel::{
    AnimMapper, AnimQuery, Animation, BindingAPI, BlendShape, BlendShapeSchema, NO_PARENT, Root, SkelBinding, Skeleton,
    SkeletonResolver, SkeletonSchema, SkinningMethod, SkinningResolver, Topology, discover_bindings,
};

mod common;
use common::from_usda;

const FIXTURE: &str = "fixtures/usdSkel_scene.usda";

fn open() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)
}

/// Traverse `stage` and collect the prims that `get` resolves to a view —
/// the C++-style `prim.IsA<T>()` filter.
fn typed<S>(stage: &Stage, get: impl Fn(&Stage, sdf::Path) -> Result<Option<S>>) -> Result<Vec<S>> {
    let mut paths = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT_PROXIES, |p| paths.push(p.clone()))?;
    paths.into_iter().filter_map(|p| get(stage, p).transpose()).collect()
}

fn paths_of<S: SchemaBase>(views: &[S]) -> Vec<String> {
    views.iter().map(|v| v.path().as_str().to_string()).collect()
}

#[test]
fn finds_every_skel_prim_family() -> Result<()> {
    let stage = open()?;
    assert_eq!(paths_of(&typed(&stage, Root::get)?), vec!["/World/Character"]);
    assert_eq!(paths_of(&typed(&stage, Skeleton::get)?), vec!["/World/Character/Rig"]);
    assert_eq!(paths_of(&typed(&stage, Animation::get)?), vec!["/World/Character/Anim"]);
    assert_eq!(
        paths_of(&typed(&stage, BlendShape::get)?),
        vec!["/World/Character/Smile"]
    );
    let bindings = paths_of(&typed(&stage, BindingAPI::get)?);
    assert!(bindings.contains(&"/World/Character".to_string()));
    assert!(bindings.contains(&"/World/Character/Body".to_string()));
    Ok(())
}

#[test]
fn reads_skel_root_extent() -> Result<()> {
    let stage = open()?;
    let root = Root::get(&stage, "/World/Character")?.expect("Root");
    assert_eq!(
        root.extent_attr().get::<Value>()?.and_then(|v| v.try_as_vec_3f_vec()),
        Some(vec![
            openusd::gf::Vec3f {
                x: -1.0,
                y: 0.0,
                z: -1.0
            },
            openusd::gf::Vec3f { x: 1.0, y: 2.0, z: 1.0 },
        ])
    );
    Ok(())
}

#[test]
fn reads_skeleton_joints_and_transforms() -> Result<()> {
    let stage = open()?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.expect("Skeleton");
    assert_eq!(skl.joint_paths()?, vec!["Root", "Root/Hip", "Root/Hip/Knee"]);
    let bind = skl.bind_transforms()?.expect("authored");
    assert_eq!(bind.len(), 3);
    assert_eq!(skl.rest_transforms()?.expect("authored").len(), 3);

    // bindTransforms world-space: Hip is at (0, 1, 0), Knee at (0, 2, 0).
    assert_eq!(bind[1].0[12..16], [0.0, 1.0, 0.0, 1.0]);
    assert_eq!(bind[2].0[12..16], [0.0, 2.0, 0.0, 1.0]);

    // Parent indices derive from the path encoding.
    assert_eq!(skl.joint_parent_indices()?, vec![None, Some(0), Some(1)]);
    // Short names strip everything but the leaf segment.
    assert_eq!(skl.joint_short_names()?, vec!["Root", "Hip", "Knee"]);
    Ok(())
}

#[test]
fn maps_anim_joints_to_skeleton_indices() -> Result<()> {
    let stage = open()?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let anim = Animation::get(&stage, "/World/Character/Anim")?.unwrap();
    assert_eq!(
        skl.map_anim_joints(&anim.joint_paths()?)?,
        vec![Some(0), Some(1), Some(2)]
    );
    Ok(())
}

#[test]
fn reads_blend_shape_with_inbetween() -> Result<()> {
    let stage = open()?;
    let bs = BlendShape::get(&stage, "/World/Character/Smile")?.expect("BlendShape");
    assert_eq!(
        bs.offsets()?,
        Some(vec![Vec3f { x: 0.0, y: 0.1, z: 0.0 }, Vec3f { x: 0.0, y: 0.1, z: 0.0 }])
    );
    assert_eq!(bs.normal_offsets()?.map(|offsets| offsets.len()), Some(2));
    assert_eq!(bs.point_indices()?, Some(vec![0, 1]));

    let inbetweens = bs.inbetweens()?;
    assert_eq!(inbetweens.len(), 1);
    let inb = &inbetweens[0];
    assert_eq!(inb.name, "half");
    assert_eq!(inb.weight, Some(0.5));
    assert_eq!(
        inb.offsets,
        vec![
            Vec3f {
                x: 0.0,
                y: 0.04,
                z: 0.0
            },
            Vec3f {
                x: 0.0,
                y: 0.04,
                z: 0.0
            }
        ]
    );
    Ok(())
}

#[test]
fn reads_skel_binding_on_mesh() -> Result<()> {
    let stage = open()?;
    let bind = BindingAPI::get(&stage, "/World/Character/Body")?.expect("BindingAPI");

    // skel:skeleton / skel:animationSource are NOT authored on the mesh itself —
    // they're inherited from the Root.
    assert!(bind.skeleton()?.is_none());
    assert!(bind.animation_source()?.is_none());

    assert_eq!(bind.joint_subset()?, vec!["Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(bind.joint_indices()?, Some(vec![0, 0, 1, 1]));
    assert_eq!(bind.joint_weights()?, Some(vec![1.0, 1.0, 1.0, 1.0]));
    assert_eq!(bind.blend_shapes()?.expect("authored"), vec!["smile"]);
    assert_eq!(bind.blend_shape_targets()?, vec![sdf::path("/World/Character/Smile")?]);
    assert!(bind.geom_bind_transform()?.is_some());
    assert_eq!(bind.skinning_method()?, Some(SkinningMethod::ClassicLinear));
    Ok(())
}

#[test]
fn resolves_inherited_skeleton_and_animation_source() -> Result<()> {
    let stage = open()?;
    let bind = BindingAPI::get(&stage, "/World/Character/Body")?.expect("BindingAPI");

    assert_eq!(
        bind.inherited_skeleton()?.map(|s| s.path().clone()),
        Some(sdf::path("/World/Character/Rig")?)
    );
    assert_eq!(
        bind.inherited_animation_source()?.map(|a| a.path().clone()),
        Some(sdf::path("/World/Character/Anim")?)
    );
    Ok(())
}

#[test]
fn finds_skel_roots_on_stage() -> Result<()> {
    let stage = open()?;
    assert_eq!(paths_of(&typed(&stage, Root::get)?), vec!["/World/Character"]);
    Ok(())
}

#[test]
fn discover_bindings_walks_skel_root_subtree() -> Result<()> {
    let stage = open()?;
    let bindings = discover_bindings(&root(&stage, "/World/Character")?)?;
    // The Root carries BindingAPI too, but only the Body mesh is skinnable.
    assert_eq!(bindings.len(), 1);
    let body = &bindings[0];
    assert_eq!(body.prim.path().as_str(), "/World/Character/Body");
    // The Body doesn't author skel:skeleton; it's inherited from the Root.
    assert_eq!(body.skeleton.path().as_str(), "/World/Character/Rig");
    assert_eq!(
        body.animation_source.as_ref().map(|a| a.path().as_str()),
        Some("/World/Character/Anim")
    );
    Ok(())
}

fn root(stage: &Stage, path: &str) -> Result<Root> {
    Ok(Root::get(stage, path)?.expect("Root"))
}

/// The binding `discover_bindings` finds for `prim` beneath the Root at
/// `root_path`.
fn binding_of(stage: &Stage, root_path: &str, prim: &str) -> Result<Option<SkelBinding>> {
    let bindings = discover_bindings(&root(stage, root_path)?)?;
    Ok(bindings.into_iter().find(|b| b.prim.path().as_str() == prim))
}

#[test]
fn skeleton_resolver_pre_computes_inverse_bind() -> Result<()> {
    let stage = open()?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let resolver = SkeletonResolver::from_skeleton(&skl)?.expect("valid topology");

    assert_eq!(resolver.topology().joint_count(), 3);
    assert_eq!(resolver.topology().parents(), &[NO_PARENT, 0, 1]);
    assert!(resolver.has_bind_pose() && resolver.has_rest_pose());
    assert_eq!(resolver.inverse_bind_transforms().map(<[_]>::len), Some(3));

    // rest_pose composed into skel-space: identity rests with the chain
    // (0,0,0) → (0,1,0) → (0,2,0) should produce skel-space translations
    // matching the bind transforms.
    let skel_space = resolver.rest_pose_skel_space().expect("rest pose");
    assert_eq!(skel_space[1].0[12..16], [0.0, 1.0, 0.0, 1.0]);
    assert_eq!(skel_space[2].0[12..16], [0.0, 2.0, 0.0, 1.0]);
    Ok(())
}

#[test]
fn skinning_resolver_remaps_through_skel_joints_subset() -> Result<(), SchemaError> {
    let stage = open()?;
    let binding = binding_of(&stage, "/World/Character", "/World/Character/Body")?.expect("Body binding");
    let resolver = SkinningResolver::new(&binding)?;

    assert!(!resolver.is_rigidly_deformed());
    assert!(resolver.has_joint_influences());
    assert_eq!(resolver.influences_per_component(), 1);
    // skel:joints subset = ["Root/Hip", "Root/Hip/Knee"] — two mesh-effective
    // joints out of the skeleton's three.
    assert_eq!(resolver.joint_order_len(), 2);
    assert_eq!(resolver.skinning_method(), SkinningMethod::ClassicLinear);

    // Skeleton joints 1 and 2 land at mesh joints 0 and 1.
    let skel_xforms: Vec<_> = (0..3).map(|i| Mat4d::translation([f64::from(i), 0.0, 0.0])).collect();
    let mesh_xforms = resolver
        .remap_transforms(&skel_xforms)
        .expect("one transform per joint");
    assert_eq!(mesh_xforms, skel_xforms[1..]);
    // Too few skeleton transforms are rejected.
    assert!(resolver.remap_transforms(&[]).is_none());
    assert!(resolver.skinned_points(&[Vec3f::default(); 4], &[]).is_none());
    Ok(())
}

#[test]
fn skinning_resolver_with_identity_xforms_returns_bind_pose_points() -> Result<(), SchemaError> {
    let stage = open()?;
    let binding = binding_of(&stage, "/World/Character", "/World/Character/Body")?.expect("Body binding");
    let resolver = SkinningResolver::new(&binding)?;

    let pts = [
        Vec3f {
            x: -0.5,
            y: 0.0,
            z: -0.5,
        },
        Vec3f {
            x: 0.5,
            y: 0.0,
            z: -0.5,
        },
        Vec3f { x: 0.5, y: 0.0, z: 0.5 },
        Vec3f {
            x: -0.5,
            y: 0.0,
            z: 0.5,
        },
    ];
    let identity = Mat4d::IDENTITY;
    let skel_xforms = vec![identity; 3];
    let out = resolver
        .skinned_points(&pts, &skel_xforms)
        .expect("per-vertex influences");
    // Identity geom-bind + identity joints + weight 1.0 = no movement.
    for (i, p) in out.iter().enumerate() {
        let want = pts[i];
        assert!((p.x - want.x).abs() < 1e-6, "point {i}: got {p:?}, want {want:?}");
        assert!((p.y - want.y).abs() < 1e-6, "point {i}: got {p:?}, want {want:?}");
        assert!((p.z - want.z).abs() < 1e-6, "point {i}: got {p:?}, want {want:?}");
    }
    Ok(())
}

#[test]
fn topology_unit_methods() {
    let topo = Topology::from_joint_paths(&["Root".to_string(), "Root/Hip".to_string(), "Root/Hip/Knee".to_string()]);
    assert_eq!(topo.joint_count(), 3);
    assert!(topo.is_root(0));
    assert!(!topo.is_root(1));
    assert_eq!(topo.parent(2), Some(1));
    topo.validate().expect("valid");
}

#[test]
fn anim_mapper_remap_with_missing_joints() {
    let m = AnimMapper::new(
        &["Root".to_string(), "Hip".to_string()],
        &["Hip".to_string(), "Missing".to_string(), "Root".to_string()],
    );
    assert!(m.is_sparse());
    assert_eq!(m.target_len(), 3);
    let out = m.remap(&[10, 20], -1);
    assert_eq!(out, vec![20, -1, 10]);
}

/// The query over the fixture's animation.
fn anim_query(stage: &Stage) -> Result<AnimQuery> {
    let anim = Animation::get(stage, "/World/Character/Anim")?.expect("Animation");
    Ok(AnimQuery::new(anim)?.expect("joints and blend shapes"))
}

#[test]
fn skel_anim_query_orderings() -> Result<()> {
    let stage = open()?;
    let q = anim_query(&stage)?;
    assert_eq!(q.animation().path().as_str(), "/World/Character/Anim");
    assert_eq!(q.joint_order(), &["Root", "Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(q.blend_shape_order(), &["smile"]);
    assert!(q.joint_transforms_might_be_time_varying()?);
    assert!(q.blend_shape_weights_might_be_time_varying()?);
    Ok(())
}

/// The times an animation is authored at: the joint transform samples are the
/// union over translations, rotations and the default-only scales, and the
/// blend-shape weights have their own.
#[test]
fn skel_anim_query_time_samples() -> Result<()> {
    let stage = open()?;
    let q = anim_query(&stage)?;

    assert_eq!(q.joint_transform_time_samples()?, vec![0.0, 10.0]);
    assert_eq!(q.joint_transform_time_samples_in(0.0..=5.0)?, vec![0.0]);
    assert_eq!(q.joint_transform_time_samples_in(0.0..10.0)?, vec![0.0]);
    assert_eq!(q.blend_shape_weight_time_samples()?, vec![0.0, 10.0]);
    assert_eq!(q.blend_shape_weight_time_samples_in(5.0..=10.0)?, vec![10.0]);
    Ok(())
}

#[test]
fn skel_anim_query_components_at_start_frame() -> Result<()> {
    let stage = open()?;
    let q = anim_query(&stage)?;
    let (t, r, s) = q
        .joint_transform_components(TimeCode::new(0.0))?
        .expect("authored components");
    // Authored at t=0: hip is at (0, 1, 0), all rotations identity, and the
    // default-only scales are unit.
    assert_eq!(t[1], Vec3f { x: 0.0, y: 1.0, z: 0.0 });
    assert_eq!(r[1], Quatf::IDENTITY);
    assert_eq!(s[1], Vec3f { x: 1.0, y: 1.0, z: 1.0 });
    Ok(())
}

#[test]
fn skel_anim_query_components_lerp_at_midframe() -> Result<()> {
    let stage = open()?;
    let q = anim_query(&stage)?;
    let (t, r, _) = q
        .joint_transform_components(TimeCode::new(5.0))?
        .expect("authored components");
    // Hip translation lerps from (0,1,0) at t=0 to (0,1.5,0) at t=10.
    assert!((t[1].y - 1.25).abs() < 1e-5, "hip y at t=5: got {}", t[1].y);
    // Hip rotation slerps from identity to ~45° about +Z; at t=5 ~22.5°.
    let w_expected = (std::f32::consts::PI / 8.0).cos();
    let z_expected = (std::f32::consts::PI / 8.0).sin();
    assert!((r[1].w - w_expected).abs() < 1e-3, "w: {}", r[1].w);
    assert!((r[1].z - z_expected).abs() < 1e-3, "z: {}", r[1].z);
    Ok(())
}

#[test]
fn skel_anim_query_blend_shape_weights_lerp() -> Result<()> {
    let stage = open()?;
    let q = anim_query(&stage)?;
    assert_eq!(q.blend_shape_weights(TimeCode::new(0.0))?, Some(vec![0.0]));
    let w_mid = q.blend_shape_weights(TimeCode::new(5.0))?.expect("authored weights");
    assert!((w_mid[0] - 0.5).abs() < 1e-5, "midpoint weight: {}", w_mid[0]);
    assert_eq!(q.blend_shape_weights(TimeCode::new(10.0))?, Some(vec![1.0]));
    Ok(())
}

#[test]
fn skel_anim_query_joint_local_matrices_drive_skeleton_resolver() -> Result<()> {
    let stage = open()?;
    let q = anim_query(&stage)?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let resolver = SkeletonResolver::from_skeleton(&skl)?.expect("valid topology");

    let locals = q
        .joint_local_transforms(TimeCode::new(0.0))?
        .expect("authored components");
    assert_eq!(locals.len(), 3);
    // Hip's local at t=0 carries the (0,1,0) translation (row-major [12..15]).
    assert_eq!(locals[1].0[12..15], [0.0, 1.0, 0.0]);

    // At t=0 the animated pose matches the bind pose, so every skinning
    // transform is the identity.
    let mapper = AnimMapper::new(q.joint_order(), resolver.joint_order());
    let locals = resolver
        .joint_local_transforms(&mapper, &locals)
        .expect("covered joints");
    let skinning = resolver.skinning_transforms_from_local(&locals);
    assert_eq!(skinning, Some(vec![Mat4d::IDENTITY; 3]));
    Ok(())
}

/// An animation naming neither joints nor blend shapes has nothing to
/// animate, so no query is built over it.
#[test]
fn skel_anim_query_none_when_empty() -> Result<()> {
    let stage = memory()?;
    let empty = Animation::define(&stage, "/Empty")?;
    assert!(AnimQuery::new(empty)?.is_none());
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
fn skel_root_is_boundable() -> Result<()> {
    let stage = memory()?;
    let root = Root::define(&stage, "/Char")?;
    root.create_extent_attr()?.set(Value::Vec3fVec(vec![
        [-1.0_f32, 0.0, -1.0].into(),
        [1.0, 2.0, 1.0].into(),
    ]))?;
    let root = Root::get(&stage, "/Char")?.expect("Root");
    assert_eq!(
        root.extent_attr().get::<Value>()?.and_then(|v| v.try_as_vec_3f_vec()),
        Some(vec![gf::vec3f(-1.0, 0.0, -1.0), gf::vec3f(1.0, 2.0, 1.0)])
    );
    Ok(())
}

#[test]
fn skeleton_roundtrip_and_topology() -> Result<()> {
    let stage = memory()?;
    let skel = Skeleton::define(&stage, "/Rig")?;
    skel.create_joints_attr()?.set(Value::TokenVec(vec![
        "Root".into(),
        "Root/Hip".into(),
        "Root/Hip/Knee".into(),
    ]))?;

    let skel = Skeleton::get(&stage, "/Rig")?.expect("Skeleton");
    assert_eq!(skel.joint_paths()?, vec!["Root", "Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(skel.joint_parent_indices()?, vec![None, Some(0), Some(1)]);
    assert_eq!(skel.joint_short_names()?, vec!["Root", "Hip", "Knee"]);
    assert_eq!(skel.map_anim_joints(&["Root/Hip".to_string()])?, vec![Some(1)]);
    Ok(())
}

#[test]
fn binding_props_inherit() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "A/B"]
    }
    def Xform "G" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = ["A/B"]
        matrix4d primvars:skel:geomBindTransform = ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (1, 0, 0, 1) )
        int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
        def Mesh "M" {}
    }
}
"#,
    )?;
    let binding = binding_of(&stage, "/R", "/R/G/M")?.expect("M binding");
    assert_eq!(binding.skeleton.path().as_str(), "/R/Rig");
    let resolver = SkinningResolver::new(&binding)?;
    assert!(resolver.has_joint_influences());
    assert!(resolver.is_rigidly_deformed());
    assert_eq!(resolver.joint_order_len(), 1);
    assert_eq!(resolver.geom_bind_transform(), Mat4d::translation([1.0, 0.0, 0.0]));

    // Joint `A/B` is skeleton joint 1; the constant influence applies to every
    // point, after the geom bind transform.
    let xforms = [Mat4d::IDENTITY, Mat4d::translation([0.0, 2.0, 0.0])];
    let rigid = resolver.rigid_transform(&xforms).expect("constant influences");
    assert_eq!(rigid, Mat4d::translation([1.0, 2.0, 0.0]));
    let points = resolver
        .skinned_points(&[Vec3f::default(), gf::vec3f(1.0, 0.0, 0.0)], &xforms)
        .expect("constant influences");
    assert_eq!(points, vec![gf::vec3f(1.0, 2.0, 0.0), gf::vec3f(2.0, 2.0, 0.0)]);
    Ok(())
}

#[test]
fn binding_above_root_ignored() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def Xform "W" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:skeleton = </W/Rig>
    def Skeleton "Rig" {}
    def SkelRoot "R" {
        def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {}
    }
}
"#,
    )?;
    // The inherited lookup walks to the pseudo-root; discovery starts at the
    // Root.
    let mesh = BindingAPI::get(&stage, "/W/R/M")?.expect("BindingAPI");
    assert_eq!(
        mesh.inherited_skeleton()?.map(|s| s.path().clone()),
        Some(sdf::path("/W/Rig")?)
    );
    assert!(discover_bindings(&root(&stage, "/W/R")?)?.is_empty());
    Ok(())
}

#[test]
fn empty_skeleton_rel_blocks() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:skeleton = </R/Rig>
    def Skeleton "Rig" {}
    def Xform "G" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = []
        def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {}
    }
}
"#,
    )?;
    let mesh = BindingAPI::get(&stage, "/R/G/M")?.expect("BindingAPI");
    assert!(mesh.inherited_skeleton()?.is_none());
    assert!(discover_bindings(&root(&stage, "/R")?)?.is_empty());
    Ok(())
}

#[test]
fn non_api_rel_ignored() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:skeleton = </R/Rig>
    def Skeleton "Rig" {}
    def Skeleton "Other" {}
    def Xform "G" {
        rel skel:skeleton = </R/Other>
        def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {}
    }
}
"#,
    )?;
    let mesh = BindingAPI::get(&stage, "/R/G/M")?.expect("BindingAPI");
    assert_eq!(
        mesh.inherited_skeleton()?.map(|s| s.path().clone()),
        Some(sdf::path("/R/Rig")?)
    );
    let binding = binding_of(&stage, "/R", "/R/G/M")?.expect("M binding");
    assert_eq!(binding.skeleton.path().as_str(), "/R/Rig");
    Ok(())
}

#[test]
fn discovery_prunes_subtrees() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:skeleton = </R/Rig>
    def Skeleton "Rig" {}
    def Mesh "M" {
        def Mesh "Nested" {}
    }
    def "Untyped" {
        def Mesh "Hidden" {}
    }
    def Scope "S" {
        def Mesh "Found" {}
    }
}
"#,
    )?;
    let bindings = discover_bindings(&root(&stage, "/R")?)?;
    let prims: Vec<_> = bindings.iter().map(|b| b.prim.path().as_str().to_string()).collect();
    assert_eq!(prims, vec!["/R/M", "/R/S/Found"]);
    Ok(())
}

#[test]
fn inactive_skeleton_skipped() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:skeleton = </R/Rig>
    def Skeleton "Rig" (active = false) {}
    def Mesh "M" {}
}
"#,
    )?;
    assert!(discover_bindings(&root(&stage, "/R")?)?.is_empty());
    Ok(())
}

#[test]
fn mismatched_influences_rejected() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A"]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        int[] primvars:skel:jointIndices = [0, 0] (interpolation = "vertex" elementSize = 1)
        float[] primvars:skel:jointWeights = [1, 0] (interpolation = "vertex" elementSize = 2)
    }
}
"#,
    )?;
    let binding = binding_of(&stage, "/R", "/R/M")?.expect("M binding");
    let resolver = SkinningResolver::new(&binding)?;
    assert!(!resolver.has_joint_influences());
    assert!(resolver.is_rigidly_deformed());
    assert!(resolver.rigid_transform(&[Mat4d::IDENTITY]).is_none());
    assert!(
        resolver
            .skinned_points(&[Vec3f::default(); 2], &[Mat4d::IDENTITY])
            .is_none()
    );
    Ok(())
}

#[test]
fn unknown_interpolation_rejected() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A"]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        int[] primvars:skel:jointIndices = [0] (interpolation = "bogus")
        float[] primvars:skel:jointWeights = [1] (interpolation = "bogus")
    }
}
"#,
    )?;
    let binding = binding_of(&stage, "/R", "/R/M")?.expect("M binding");
    assert!(!SkinningResolver::new(&binding)?.has_joint_influences());
    Ok(())
}

#[test]
fn bad_joint_index_skips() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A"]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        int[] primvars:skel:jointIndices = [0, 3] (interpolation = "vertex")
        float[] primvars:skel:jointWeights = [1, 1] (interpolation = "vertex")
    }
}
"#,
    )?;
    let binding = binding_of(&stage, "/R", "/R/M")?.expect("M binding");
    let resolver = SkinningResolver::new(&binding)?;
    assert!(resolver.has_joint_influences());
    assert!(
        resolver
            .skinned_points(&[Vec3f::default(); 2], &[Mat4d::IDENTITY])
            .is_none()
    );
    // The influences fit three points no better than they name joints.
    assert!(
        resolver
            .skinned_points(&[Vec3f::default(); 3], &[Mat4d::IDENTITY; 4])
            .is_none()
    );
    Ok(())
}

#[test]
fn anim_source_from_skeleton() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:skeleton = </R/Rig>
    rel skel:animationSource = </R/MeshAnim>
    def Skeleton "Rig" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:animationSource = </R/RigAnim>
    }
    def SkelAnimation "MeshAnim" {}
    def SkelAnimation "RigAnim" {}
    def Mesh "M" {}
}
"#,
    )?;
    let binding = binding_of(&stage, "/R", "/R/M")?.expect("M binding");
    assert_eq!(
        binding.animation_source.as_ref().map(|a| a.path().as_str()),
        Some("/R/RigAnim")
    );
    Ok(())
}

#[test]
fn sparse_anim_fills_rest() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def Skeleton "Rig" {
    uniform token[] joints = ["A", "A/B"]
    uniform matrix4d[] restTransforms = [
        ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (1, 0, 0, 1) ),
        ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 1, 0, 1) ),
    ]
}
def Skeleton "Bare" {
    uniform token[] joints = ["A", "A/B"]
}
"#,
    )?;
    let anim_joints = ["A/B".to_string()];
    let anim_local = [Mat4d::translation([0.0, 5.0, 0.0])];

    let rig = Skeleton::get(&stage, "/Rig")?.expect("Skeleton");
    let rig = SkeletonResolver::from_skeleton(&rig)?.expect("valid topology");
    let mapper = AnimMapper::new(&anim_joints, rig.joint_order());
    assert_eq!(
        rig.joint_local_transforms(&mapper, &anim_local),
        Some(vec![
            Mat4d::translation([1.0, 0.0, 0.0]),
            Mat4d::translation([0.0, 5.0, 0.0])
        ])
    );
    // The animation's arrays must match its own joint order.
    assert!(rig.joint_local_transforms(&mapper, &[]).is_none());

    // Without a rest pose the uncovered joint has no transform.
    let bare = Skeleton::get(&stage, "/Bare")?.expect("Skeleton");
    let bare = SkeletonResolver::from_skeleton(&bare)?.expect("valid topology");
    assert!(bare.joint_local_transforms(&mapper, &anim_local).is_none());
    Ok(())
}

#[test]
fn mismatched_bind_ignored() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def Skeleton "Rig" {
    uniform token[] joints = ["A", "A/B"]
    uniform matrix4d[] bindTransforms = [( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) )]
    uniform matrix4d[] restTransforms = [( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) )]
}
"#,
    )?;
    let rig = Skeleton::get(&stage, "/Rig")?.expect("Skeleton");
    let rig = SkeletonResolver::from_skeleton(&rig)?.expect("valid topology");
    assert!(!rig.has_bind_pose());
    assert!(!rig.has_rest_pose());
    assert!(rig.skinning_transforms(&[Mat4d::IDENTITY; 2]).is_none());
    assert!(rig.rest_pose_skel_space().is_none());
    Ok(())
}

#[test]
fn invalid_topology_rejected() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def Skeleton "Rig" {
    uniform token[] joints = ["A/B", "A"]
}
"#,
    )?;
    let rig = Skeleton::get(&stage, "/Rig")?.expect("Skeleton");
    assert!(SkeletonResolver::from_skeleton(&rig)?.is_none());
    Ok(())
}

#[test]
fn empty_joint_subset_maps_none() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A"]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = []
        int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
    }
}
"#,
    )?;
    let binding = binding_of(&stage, "/R", "/R/M")?.expect("M binding");
    let resolver = SkinningResolver::new(&binding)?;
    assert_eq!(resolver.joint_order_len(), 0);
    assert!(resolver.rigid_transform(&[Mat4d::IDENTITY]).is_none());
    Ok(())
}

/// The animation's arrays have no fallbacks, so a component with no value,
/// one of the wrong type, or arrays that do not hold one entry per joint
/// leave nothing to compose.
#[test]
fn anim_query_missing_components() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelAnimation "NoScales" {
    uniform token[] joints = ["A", "A/B"]
    float3[] translations = [(0, 0, 0), (0, 1, 0)]
    quatf[] rotations = [(1, 0, 0, 0), (1, 0, 0, 0)]
}
def SkelAnimation "Blocked" {
    uniform token[] joints = ["A", "A/B"]
    float3[] translations = [(0, 0, 0), (0, 1, 0)]
    quatf[] rotations = None
    half3[] scales = [(1, 1, 1), (1, 1, 1)]
}
def SkelAnimation "Short" {
    uniform token[] joints = ["A", "A/B"]
    float3[] translations = [(0, 0, 0)]
    quatf[] rotations = [(1, 0, 0, 0)]
    half3[] scales = [(1, 1, 1)]
}
def SkelAnimation "Mismatched" {
    uniform token[] joints = ["A", "A/B"]
    float3[] translations = [(0, 0, 0), (0, 1, 0)]
    quatf[] rotations = [(1, 0, 0, 0), (1, 0, 0, 0)]
    half3[] scales = [(1, 1, 1)]
    float[] blendShapeWeights = [0.5, 0.25, 1]
}
"#,
    )?;
    let query = |path: &str| -> Result<AnimQuery> {
        let anim = Animation::get(&stage, path)?.expect("SkelAnimation");
        Ok(AnimQuery::new(anim)?.expect("joints authored"))
    };
    for path in ["/NoScales", "/Blocked"] {
        let q = query(path)?;
        assert!(q.joint_transform_components(None)?.is_none(), "{path}");
        assert!(q.joint_local_transforms(None)?.is_none(), "{path}");
    }
    // Components that read but do not hold one entry per joint compose
    // nothing, though they are answered as authored.
    let short = query("/Short")?;
    assert!(short.joint_transform_components(None)?.is_some());
    assert!(short.joint_local_transforms(None)?.is_none());
    let mismatched = query("/Mismatched")?;
    assert!(mismatched.joint_local_transforms(None)?.is_none());
    // Weights are answered as authored; unauthored weights are `None`.
    assert_eq!(mismatched.blend_shape_weights(None)?, Some(vec![0.5, 0.25, 1.0]));
    assert!(short.blend_shape_weights(None)?.is_none());
    Ok(())
}
