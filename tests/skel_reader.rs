//! Integration tests for the UsdSkel module against a fixture that
//! exercises every schema family the reader covers, plus the
//! time-independent object-model layer (topology, AnimMapper,
//! SkeletonResolver, SkinningResolver, binding discovery).

use anyhow::Result;
use openusd::schemas::skel::{
    self, discover_bindings, find_skel_roots, AnimMapper, InfluenceInterpolation, SkeletonResolver, SkinningMethod,
    SkinningResolver, Topology, NO_PARENT,
};
use openusd::sdf;
use openusd::Stage;

const FIXTURE: &str = "fixtures/usdSkel_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

#[test]
fn finds_every_skel_prim_family() -> Result<()> {
    let stage = open()?;
    let prims = skel::find_skel_prims(&stage)?;

    assert_eq!(prims.skel_roots, vec!["/World/Character".to_string()]);
    assert_eq!(prims.skeletons, vec!["/World/Character/Rig".to_string()]);
    assert_eq!(prims.animations, vec!["/World/Character/Anim".to_string()]);
    assert_eq!(prims.blend_shapes, vec!["/World/Character/Smile".to_string()]);
    assert!(prims.bindings.contains(&"/World/Character".to_string()));
    assert!(prims.bindings.contains(&"/World/Character/Body".to_string()));

    Ok(())
}

#[test]
fn reads_skel_root_extent() -> Result<()> {
    let stage = open()?;
    let root = skel::read_skel_root(&stage, &sdf::path("/World/Character")?)?.expect("SkelRoot");
    assert_eq!(root.path, "/World/Character");
    let extent = root.extent.expect("extent authored");
    assert_eq!(extent, [[-1.0, 0.0, -1.0], [1.0, 2.0, 1.0]]);
    Ok(())
}

#[test]
fn reads_skeleton_joints_and_transforms() -> Result<()> {
    let stage = open()?;
    let skl = skel::read_skeleton(&stage, &sdf::path("/World/Character/Rig")?)?.expect("Skeleton");
    assert_eq!(skl.joints, vec!["Root", "Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(skl.bind_transforms.len(), 3);
    assert_eq!(skl.rest_transforms.len(), 3);

    // bindTransforms world-space: Hip is at (0, 1, 0), Knee at (0, 2, 0).
    assert_eq!(skl.bind_transforms[1][12..16], [0.0, 1.0, 0.0, 1.0]);
    assert_eq!(skl.bind_transforms[2][12..16], [0.0, 2.0, 0.0, 1.0]);

    // Parent indices derive from the path encoding.
    let parents = skl.joint_parent_indices();
    assert_eq!(parents, vec![None, Some(0), Some(1)]);

    // Short names strip everything but the leaf segment.
    assert_eq!(skl.joint_short_names(), vec!["Root", "Hip", "Knee"]);
    Ok(())
}

#[test]
fn reads_skel_animation_time_samples() -> Result<()> {
    let stage = open()?;
    let anim = skel::read_skel_animation(&stage, &sdf::path("/World/Character/Anim")?)?.expect("SkelAnimation");
    assert_eq!(anim.joints, vec!["Root", "Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(anim.blend_shapes, vec!["smile"]);

    assert_eq!(anim.translations.len(), 2);
    assert_eq!(anim.translations[0].0, 0.0);
    assert_eq!(anim.translations[1].0, 10.0);
    assert_eq!(anim.translations[1].1[1], [0.0, 1.5, 0.0]);

    assert_eq!(anim.rotations.len(), 2);
    assert_eq!(anim.rotations[1].1[1][0], 0.707);

    assert_eq!(anim.blend_shape_weights.len(), 2);
    assert_eq!(anim.blend_shape_weights[1].1, vec![1.0]);
    Ok(())
}

#[test]
fn maps_anim_joints_to_skeleton_indices() -> Result<()> {
    let stage = open()?;
    let skl = skel::read_skeleton(&stage, &sdf::path("/World/Character/Rig")?)?.unwrap();
    let anim = skel::read_skel_animation(&stage, &sdf::path("/World/Character/Anim")?)?.unwrap();
    let map = skl.map_anim_joints(&anim.joints);
    assert_eq!(map, vec![Some(0), Some(1), Some(2)]);
    Ok(())
}

#[test]
fn reads_blend_shape_with_inbetween() -> Result<()> {
    let stage = open()?;
    let bs = skel::read_blend_shape(&stage, &sdf::path("/World/Character/Smile")?)?.expect("BlendShape");
    assert_eq!(bs.offsets, vec![[0.0, 0.1, 0.0], [0.0, 0.1, 0.0]]);
    assert_eq!(bs.normal_offsets.len(), 2);
    assert_eq!(bs.point_indices, vec![0, 1]);

    assert_eq!(bs.inbetweens.len(), 1);
    let inb = &bs.inbetweens[0];
    assert_eq!(inb.name, "half");
    assert_eq!(inb.weight, Some(0.5));
    assert_eq!(inb.offsets, vec![[0.0, 0.04, 0.0], [0.0, 0.04, 0.0]]);
    Ok(())
}

#[test]
fn reads_skel_binding_on_mesh() -> Result<()> {
    let stage = open()?;
    let bind = skel::read_skel_binding(&stage, &sdf::path("/World/Character/Body")?)?.expect("SkelBindingAPI");
    assert_eq!(bind.path, "/World/Character/Body");

    // skel:skeleton / skel:animationSource are NOT authored on the mesh
    // itself — they're inherited from the SkelRoot.
    assert!(bind.skeleton.is_none());
    assert!(bind.animation_source.is_none());

    assert_eq!(bind.joint_subset, vec!["Root/Hip", "Root/Hip/Knee"]);
    assert_eq!(bind.joint_indices, vec![0, 0, 1, 1]);
    assert_eq!(bind.joint_weights, vec![1.0, 1.0, 1.0, 1.0]);
    assert_eq!(bind.elements_per_element, 1);
    assert_eq!(bind.interpolation, InfluenceInterpolation::Vertex);
    assert_eq!(bind.blend_shapes, vec!["smile"]);
    assert_eq!(bind.blend_shape_targets, vec!["/World/Character/Smile".to_string()]);
    assert!(bind.geom_bind_transform.is_some());
    assert_eq!(bind.skinning_method, SkinningMethod::ClassicLinear);
    Ok(())
}

#[test]
fn resolves_inherited_skeleton_and_animation_source() -> Result<()> {
    let stage = open()?;
    let mesh = sdf::path("/World/Character/Body")?;

    let skeleton = skel::read_inherited_skeleton(&stage, &mesh)?.expect("inherited skel:skeleton");
    assert_eq!(skeleton, "/World/Character/Rig");

    let anim = skel::read_inherited_animation_source(&stage, &mesh)?.expect("inherited skel:animationSource");
    assert_eq!(anim, "/World/Character/Anim");
    Ok(())
}

#[test]
fn finds_skel_roots_on_stage() -> Result<()> {
    let stage = open()?;
    let roots = find_skel_roots(&stage)?;
    assert_eq!(roots, vec!["/World/Character".to_string()]);
    Ok(())
}

#[test]
fn discover_bindings_walks_skel_root_subtree() -> Result<()> {
    let stage = open()?;
    let root = sdf::path("/World/Character")?;
    let bindings = discover_bindings(&stage, &root)?;
    // The SkelRoot itself + the Body mesh both carry SkelBindingAPI.
    assert_eq!(bindings.len(), 2);

    let body = bindings
        .iter()
        .find(|b| b.prim == "/World/Character/Body")
        .expect("Body binding");
    // The Body itself doesn't author skel:skeleton — it's inherited
    // from the SkelRoot.
    assert!(body.binding.skeleton.is_none());
    assert_eq!(body.skeleton.as_deref(), Some("/World/Character/Rig"));
    assert_eq!(body.animation_source.as_deref(), Some("/World/Character/Anim"));
    Ok(())
}

#[test]
fn skeleton_resolver_pre_computes_inverse_bind() -> Result<()> {
    let stage = open()?;
    let skl = skel::read_skeleton(&stage, &sdf::path("/World/Character/Rig")?)?.unwrap();
    let resolver = SkeletonResolver::new(skl);

    assert_eq!(resolver.topology().num_joints(), 3);
    assert_eq!(resolver.topology().parents(), &[NO_PARENT, 0, 1]);
    assert_eq!(resolver.inverse_bind_transforms().len(), 3);

    // rest_pose composed into skel-space: identity rests with the
    // chain (0, 0, 0) → (0, 1, 0) → (0, 2, 0) should produce
    // skel-space translations matching the bind transforms.
    let skel_space = resolver.rest_pose_skel_space();
    assert_eq!(skel_space[1][12..16], [0.0, 1.0, 0.0, 1.0]);
    assert_eq!(skel_space[2][12..16], [0.0, 2.0, 0.0, 1.0]);
    Ok(())
}

#[test]
fn skinning_resolver_remaps_through_skel_joints_subset() -> Result<()> {
    let stage = open()?;
    let skl = skel::read_skeleton(&stage, &sdf::path("/World/Character/Rig")?)?.unwrap();
    let binding = skel::read_skel_binding(&stage, &sdf::path("/World/Character/Body")?)?.unwrap();
    let resolver = SkinningResolver::new(binding, &skl.joints);

    assert!(!resolver.is_rigidly_deformed());
    assert!(resolver.has_joint_influences());
    assert_eq!(resolver.num_influences_per_component(), 1);
    // skel:joints subset = ["Root/Hip", "Root/Hip/Knee"] — two
    // mesh-effective joints out of the skeleton's three.
    assert_eq!(resolver.joint_order_len(), 2);
    assert_eq!(resolver.skinning_method(), SkinningMethod::ClassicLinear);

    // Author identity skinning transforms for every skeleton joint.
    // After remapping, the mesh-side array should still be length 2
    // (since the subset selects 2 joints).
    let identity = openusd::schemas::skel::skinning::IDENTITY_MAT4;
    let skel_xforms = vec![identity; 3];
    let mesh_xforms = resolver.remap_skinning_xforms(&skel_xforms);
    assert_eq!(mesh_xforms.len(), 2);
    assert_eq!(mesh_xforms[0], identity);
    Ok(())
}

#[test]
fn skinning_resolver_with_identity_xforms_returns_bind_pose_points() -> Result<()> {
    let stage = open()?;
    let skl = skel::read_skeleton(&stage, &sdf::path("/World/Character/Rig")?)?.unwrap();
    let binding = skel::read_skel_binding(&stage, &sdf::path("/World/Character/Body")?)?.unwrap();
    let resolver = SkinningResolver::new(binding, &skl.joints);

    let pts = [
        [-0.5_f32, 0.0, -0.5],
        [0.5, 0.0, -0.5],
        [0.5, 0.0, 0.5],
        [-0.5, 0.0, 0.5],
    ];
    let identity = openusd::schemas::skel::skinning::IDENTITY_MAT4;
    let skel_xforms = vec![identity; 3];
    let out = resolver.compute_skinned_points(&pts, &skel_xforms);
    // Identity geom-bind + identity joints + weight 1.0 = no movement.
    for (i, p) in out.iter().enumerate() {
        for k in 0..3 {
            assert!(
                (p[k] - pts[i][k]).abs() < 1e-6,
                "point {i}: got {p:?}, want {:?}",
                pts[i]
            );
        }
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
