//! Integration tests for the UsdSkel views against a fixture that exercises
//! every schema family, plus the time-independent object-model layer
//! (topology, AnimMapper, SkeletonResolver, SkinningResolver, binding
//! discovery).

use anyhow::Result;
use openusd::gf::{Matrix4d, Quatf, Vec3f};
use openusd::schemas::geom::Boundable;
use openusd::schemas::skel::{
    discover_bindings, AnimMapper, BlendShape, InfluenceInterpolation, SkelAnimQuery, SkelAnimation, SkelBindingAPI,
    SkelRoot, Skeleton, SkeletonResolver, SkinningMethod, SkinningResolver, Topology, NO_PARENT,
};
use openusd::sdf::{self, Value};
use openusd::usd::{PrimPredicate, SchemaBase, Stage};

const FIXTURE: &str = "fixtures/usdSkel_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
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
    assert_eq!(paths_of(&typed(&stage, SkelRoot::get)?), vec!["/World/Character"]);
    assert_eq!(paths_of(&typed(&stage, Skeleton::get)?), vec!["/World/Character/Rig"]);
    assert_eq!(
        paths_of(&typed(&stage, SkelAnimation::get)?),
        vec!["/World/Character/Anim"]
    );
    assert_eq!(
        paths_of(&typed(&stage, BlendShape::get)?),
        vec!["/World/Character/Smile"]
    );
    let bindings = paths_of(&typed(&stage, SkelBindingAPI::get)?);
    assert!(bindings.contains(&"/World/Character".to_string()));
    assert!(bindings.contains(&"/World/Character/Body".to_string()));
    Ok(())
}

#[test]
fn reads_skel_root_extent() -> Result<()> {
    let stage = open()?;
    let root = SkelRoot::get(&stage, "/World/Character")?.expect("SkelRoot");
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
    assert_eq!(skl.joints()?, vec!["Root", "Root/Hip", "Root/Hip/Knee"]);
    let bind = skl.bind_transforms()?;
    assert_eq!(bind.len(), 3);
    assert_eq!(skl.rest_transforms()?.len(), 3);

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
    let anim = SkelAnimation::get(&stage, "/World/Character/Anim")?.unwrap();
    assert_eq!(skl.map_anim_joints(&anim.joints()?)?, vec![Some(0), Some(1), Some(2)]);
    Ok(())
}

#[test]
fn reads_blend_shape_with_inbetween() -> Result<()> {
    let stage = open()?;
    let bs = BlendShape::get(&stage, "/World/Character/Smile")?.expect("BlendShape");
    assert_eq!(
        bs.offsets()?,
        vec![Vec3f { x: 0.0, y: 0.1, z: 0.0 }, Vec3f { x: 0.0, y: 0.1, z: 0.0 }]
    );
    assert_eq!(bs.normal_offsets()?.len(), 2);
    assert_eq!(bs.point_indices()?, vec![0, 1]);

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
    let bind = SkelBindingAPI::get(&stage, "/World/Character/Body")?.expect("SkelBindingAPI");

    // skel:skeleton / skel:animationSource are NOT authored on the mesh itself —
    // they're inherited from the SkelRoot.
    assert!(bind.skeleton()?.is_none());
    assert!(bind.animation_source()?.is_none());

    assert_eq!(bind.joint_subset()?, vec!["Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(bind.joint_indices()?, vec![0, 0, 1, 1]);
    assert_eq!(bind.joint_weights()?, vec![1.0, 1.0, 1.0, 1.0]);
    assert_eq!(bind.elements_per_element()?, 1);
    assert_eq!(bind.interpolation()?, InfluenceInterpolation::Vertex);
    assert_eq!(bind.blend_shapes()?, vec!["smile"]);
    assert_eq!(bind.blend_shape_targets()?, vec![sdf::path("/World/Character/Smile")?]);
    assert!(bind.geom_bind_transform()?.is_some());
    assert_eq!(bind.skinning_method()?, SkinningMethod::ClassicLinear);
    Ok(())
}

#[test]
fn resolves_inherited_skeleton_and_animation_source() -> Result<()> {
    let stage = open()?;
    let bind = SkelBindingAPI::get(&stage, "/World/Character/Body")?.expect("SkelBindingAPI");

    assert_eq!(
        bind.inherited_skeleton()?.map(|p| p.as_str().to_string()),
        Some("/World/Character/Rig".to_string())
    );
    assert_eq!(
        bind.inherited_animation_source()?.map(|p| p.as_str().to_string()),
        Some("/World/Character/Anim".to_string())
    );
    Ok(())
}

#[test]
fn finds_skel_roots_on_stage() -> Result<()> {
    let stage = open()?;
    assert_eq!(paths_of(&typed(&stage, SkelRoot::get)?), vec!["/World/Character"]);
    Ok(())
}

#[test]
fn discover_bindings_walks_skel_root_subtree() -> Result<()> {
    let stage = open()?;
    let bindings = discover_bindings(&stage, &sdf::path("/World/Character")?)?;
    // The SkelRoot itself + the Body mesh both carry SkelBindingAPI.
    assert_eq!(bindings.len(), 2);

    let body = bindings
        .iter()
        .find(|b| b.prim == "/World/Character/Body")
        .expect("Body binding");
    // The Body itself doesn't author skel:skeleton — it's inherited from the
    // SkelRoot.
    assert!(body.binding.skeleton()?.is_none());
    assert_eq!(body.skeleton.as_ref().map(|p| p.as_str()), Some("/World/Character/Rig"));
    assert_eq!(
        body.animation_source.as_ref().map(|p| p.as_str()),
        Some("/World/Character/Anim")
    );
    Ok(())
}

#[test]
fn skeleton_resolver_pre_computes_inverse_bind() -> Result<()> {
    let stage = open()?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let resolver = SkeletonResolver::from_skeleton(&skl)?;

    assert_eq!(resolver.topology().num_joints(), 3);
    assert_eq!(resolver.topology().parents(), &[NO_PARENT, 0, 1]);
    assert_eq!(resolver.inverse_bind_transforms().len(), 3);

    // rest_pose composed into skel-space: identity rests with the chain
    // (0,0,0) → (0,1,0) → (0,2,0) should produce skel-space translations
    // matching the bind transforms.
    let skel_space = resolver.rest_pose_skel_space();
    assert_eq!(skel_space[1].0[12..16], [0.0, 1.0, 0.0, 1.0]);
    assert_eq!(skel_space[2].0[12..16], [0.0, 2.0, 0.0, 1.0]);
    Ok(())
}

#[test]
fn skinning_resolver_remaps_through_skel_joints_subset() -> Result<()> {
    let stage = open()?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let binding = SkelBindingAPI::get(&stage, "/World/Character/Body")?.unwrap();
    let resolver = SkinningResolver::from_binding(&binding, &skl.joints()?)?;

    assert!(!resolver.is_rigidly_deformed());
    assert!(resolver.has_joint_influences());
    assert_eq!(resolver.num_influences_per_component(), 1);
    // skel:joints subset = ["Root/Hip", "Root/Hip/Knee"] — two mesh-effective
    // joints out of the skeleton's three.
    assert_eq!(resolver.joint_order_len(), 2);
    assert_eq!(resolver.skinning_method(), SkinningMethod::ClassicLinear);

    let identity = Matrix4d::IDENTITY;
    let skel_xforms = vec![identity; 3];
    let mesh_xforms = resolver.remap_skinning_xforms(&skel_xforms);
    assert_eq!(mesh_xforms.len(), 2);
    assert_eq!(mesh_xforms[0], identity);
    Ok(())
}

#[test]
fn skinning_resolver_with_identity_xforms_returns_bind_pose_points() -> Result<()> {
    let stage = open()?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let binding = SkelBindingAPI::get(&stage, "/World/Character/Body")?.unwrap();
    let resolver = SkinningResolver::from_binding(&binding, &skl.joints()?)?;

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
    let identity = Matrix4d::IDENTITY;
    let skel_xforms = vec![identity; 3];
    let out = resolver.compute_skinned_points(&pts, &skel_xforms);
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
    assert_eq!(topo.num_joints(), 3);
    assert!(topo.is_root(0));
    assert!(!topo.is_root(1));
    assert_eq!(topo.parent(2), 1);
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

#[test]
fn skel_anim_query_orderings() -> Result<()> {
    let stage = open()?;
    let q = SkelAnimQuery::new(&stage, sdf::path("/World/Character/Anim")?)?.expect("SkelAnimation");
    assert_eq!(q.prim_path(), "/World/Character/Anim");
    assert_eq!(q.joint_order(), &["Root", "Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(q.blend_shape_order(), &["smile"]);
    assert!(q.joint_transforms_might_be_time_varying());
    assert!(q.blend_shape_weights_might_be_time_varying());
    Ok(())
}

#[test]
fn skel_anim_query_components_at_start_frame() -> Result<()> {
    let stage = open()?;
    let q = SkelAnimQuery::new(&stage, sdf::path("/World/Character/Anim")?)?.unwrap();
    let (t, r, s) = q.compute_joint_local_transform_components(&stage, 0.0)?;
    // Authored at t=0: hip is at (0, 1, 0), all rotations identity, scales
    // unauthored so they default to unit.
    assert_eq!(t[1], Vec3f { x: 0.0, y: 1.0, z: 0.0 });
    assert_eq!(r[1], Quatf::IDENTITY);
    assert_eq!(s[1], Vec3f { x: 1.0, y: 1.0, z: 1.0 });
    Ok(())
}

#[test]
fn skel_anim_query_components_lerp_at_midframe() -> Result<()> {
    let stage = open()?;
    let q = SkelAnimQuery::new(&stage, sdf::path("/World/Character/Anim")?)?.unwrap();
    let (t, r, _) = q.compute_joint_local_transform_components(&stage, 5.0)?;
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
    let q = SkelAnimQuery::new(&stage, sdf::path("/World/Character/Anim")?)?.unwrap();
    assert_eq!(q.compute_blend_shape_weights(&stage, 0.0)?, vec![0.0]);
    let w_mid = q.compute_blend_shape_weights(&stage, 5.0)?;
    assert!((w_mid[0] - 0.5).abs() < 1e-5, "midpoint weight: {}", w_mid[0]);
    assert_eq!(q.compute_blend_shape_weights(&stage, 10.0)?, vec![1.0]);
    Ok(())
}

#[test]
fn skel_anim_query_joint_local_matrices_drive_skeleton_resolver() -> Result<()> {
    let stage = open()?;
    let q = SkelAnimQuery::new(&stage, sdf::path("/World/Character/Anim")?)?.unwrap();
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let resolver = SkeletonResolver::from_skeleton(&skl)?;

    let locals = q.compute_joint_local_transforms(&stage, 0.0)?;
    assert_eq!(locals.len(), 3);
    // Hip's local at t=0 carries the (0,1,0) translation (row-major [12..15]).
    assert_eq!(locals[1].0[12..15], [0.0, 1.0, 0.0]);

    let identity_world = Matrix4d::IDENTITY;
    let skinning = resolver.compute_skinning_transforms_from_local(&locals, identity_world);
    assert_eq!(skinning.len(), 3);
    Ok(())
}

#[test]
fn skel_anim_query_returns_none_on_non_skel_animation() -> Result<()> {
    let stage = open()?;
    // /World is an Xform, not a SkelAnimation.
    assert!(SkelAnimQuery::new(&stage, sdf::path("/World")?)?.is_none());
    Ok(())
}
