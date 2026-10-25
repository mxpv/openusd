//! Integration tests for the UsdSkel views against a fixture that exercises
//! every schema family, plus the object-model layer (topology, AnimMapper,
//! SkeletonQuery, SkinningQuery, binding discovery).

use std::f64::consts::{FRAC_PI_2, FRAC_PI_4};

use openusd::Result;
use openusd::gf::{self, Mat4d, Quatf, Vec3f};
use openusd::sdf::{self, Value};
use openusd::usd::{Attribute, PrimPredicate, SchemaBase, Stage, TimeCode};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::{
    BBoxCache, BoundableExt, BoundableSchema, Extent, Interpolation, Mesh, Primvar, Purpose, XformCache, XformableExt,
};
use openusd_schemas::skel::{
    AnimMapper, AnimQuery, Animation, AnimationSchema, Binding, BindingAPI, BindingProperties, BlendShape,
    BlendShapeQuery, BlendShapeSchema, Cache, IndexError, NO_PARENT, Pose, Root, Skeleton, SkeletonQuery,
    SkeletonSchema, SkinningMethod, SkinningQuery, Topology, skinning, validate_indices,
};

mod common;
use common::{from_usda, vendor};

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
    assert_eq!(inb.attribute().name(), "inbetweens:half");
    assert_eq!(inb.weight()?, Some(0.5));
    assert_eq!(inb.offsets()?, Some(vec![gf::vec3f(0.0, 0.04, 0.0); 2]));
    assert_eq!(inb.normal_offsets()?, None);
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
fn cache_groups_bindings() -> Result<(), SchemaError> {
    let stage = open()?;
    let mut cache = populated(&stage, "/World/Character")?;
    let bindings = cache.skel_bindings(&root(&stage, "/World/Character")?, PrimPredicate::DEFAULT_PROXIES)?;
    // The Root carries BindingAPI too, but only the Body mesh is skinnable.
    assert_eq!(bindings.len(), 1);
    // The Body doesn't author skel:skeleton; it's inherited from the Root.
    let rig = &bindings[0];
    assert_eq!(rig.skeleton().path().as_str(), "/World/Character/Rig");
    assert_eq!(target_paths(rig), ["/World/Character/Body"]);
    let query = cache.skel_query(rig.skeleton())?.expect("valid topology");
    assert_eq!(
        query.anim_query().map(|anim| anim.animation().path().as_str()),
        Some("/World/Character/Anim")
    );
    Ok(())
}

fn root(stage: &Stage, path: &str) -> Result<Root> {
    Ok(Root::get(stage, path)?.expect("Root"))
}

/// A cache populated from the Root at `root_path`, through instance proxies.
fn populated(stage: &Stage, root_path: &str) -> Result<Cache, SchemaError> {
    let mut cache = Cache::new();
    cache.populate(&root(stage, root_path)?, PrimPredicate::DEFAULT_PROXIES)?;
    Ok(cache)
}

/// The skinning query a cache populated from the Root at `root_path` holds
/// for `prim`.
fn skinning_query(stage: &Stage, root_path: &str, prim: &str) -> Result<Option<SkinningQuery>, SchemaError> {
    Ok(populated(stage, root_path)?.skinning_query(&stage.prim(prim)?).cloned())
}

/// The bindings beneath the Root at `root_path`, through instance proxies.
fn bindings(stage: &Stage, root_path: &str) -> Result<Vec<Binding>, SchemaError> {
    let root = root(stage, root_path)?;
    let mut cache = Cache::new();
    cache.populate(&root, PrimPredicate::DEFAULT_PROXIES)?;
    cache.skel_bindings(&root, PrimPredicate::DEFAULT_PROXIES)
}

/// The paths of the prims bound in `binding`.
fn target_paths(binding: &Binding) -> Vec<&str> {
    binding
        .skinning_targets()
        .iter()
        .map(|query| query.prim().path().as_str())
        .collect()
}

#[test]
fn skeleton_query_rest_pose() -> Result<()> {
    let stage = open()?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let query = SkeletonQuery::new(&skl)?.expect("valid topology");

    assert_eq!(query.topology().joint_count(), 3);
    assert_eq!(query.topology().parents(), &[NO_PARENT, 0, 1]);
    assert!(query.has_bind_pose() && query.has_rest_pose());
    assert_eq!(query.bind_transforms().map(<[_]>::len), Some(3));
    assert_eq!(query.inverse_bind_transforms().map(<[_]>::len), Some(3));
    assert_eq!(
        query.anim_query().map(|q| q.animation().path().as_str()),
        Some("/World/Character/Anim")
    );

    // rest_pose composed into skel-space: identity rests with the chain
    // (0,0,0) → (0,1,0) → (0,2,0) should produce skel-space translations
    // matching the bind transforms.
    let skel_space = query.rest_skel_transforms().expect("rest pose");
    assert_eq!(skel_space[1].0[12..16], [0.0, 1.0, 0.0, 1.0]);
    assert_eq!(skel_space[2].0[12..16], [0.0, 2.0, 0.0, 1.0]);
    Ok(())
}

#[test]
fn skinning_query_remaps_subset() -> Result<(), SchemaError> {
    let stage = open()?;
    let query = skinning_query(&stage, "/World/Character", "/World/Character/Body")?.expect("Body query");

    assert!(!query.is_rigidly_deformed());
    assert!(query.has_joint_influences());
    assert_eq!(query.influences_per_component(), 1);
    // skel:joints subset = ["Root/Hip", "Root/Hip/Knee"] — two mesh-effective
    // joints out of the skeleton's three.
    assert_eq!(query.joint_order().map(<[_]>::len), Some(2));
    assert_eq!(query.skinning_method()?, Some(SkinningMethod::ClassicLinear));
    assert_eq!(query.blend_shape_order(), Some(&["smile".to_string()][..]));
    assert!(query.has_blend_shapes());

    // Skeleton joints 1 and 2 land at mesh joints 0 and 1: the Body's points
    // 0 and 1 follow joint 1, points 2 and 3 joint 2.
    let skel_xforms = Pose::from(
        (0..3)
            .map(|i| Mat4d::translation([f64::from(i), 0.0, 0.0]))
            .collect::<Vec<_>>(),
    );
    let points = [Vec3f::default(); 4];
    let skinned = query
        .skinned_points(&skel_xforms, &points, None)?
        .expect("per-vertex influences");
    assert_eq!(
        skinned,
        vec![
            gf::vec3f(1.0, 0.0, 0.0),
            gf::vec3f(1.0, 0.0, 0.0),
            gf::vec3f(2.0, 0.0, 0.0),
            gf::vec3f(2.0, 0.0, 0.0)
        ]
    );
    // Too few skeleton transforms are rejected, and so is a point count the
    // vertex influences do not fit.
    assert!(query.skinned_points(&Pose::default(), &points, None)?.is_none());
    assert!(query.skinned_points(&skel_xforms, &points[..3], None)?.is_none());
    Ok(())
}

#[test]
fn identity_xforms_keep_points() -> Result<(), SchemaError> {
    let stage = open()?;
    let query = skinning_query(&stage, "/World/Character", "/World/Character/Body")?.expect("Body query");

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
    let skel_xforms = Pose::from(vec![identity; 3]);
    let out = query
        .skinned_points(&skel_xforms, &pts, None)?
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
    AnimQuery::new(anim)
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
fn anim_drives_skinning() -> Result<()> {
    let stage = open()?;
    let q = anim_query(&stage)?;
    let skl = Skeleton::get(&stage, "/World/Character/Rig")?.unwrap();
    let query = SkeletonQuery::new(&skl)?.expect("valid topology");

    let locals = q
        .joint_local_transforms(TimeCode::new(0.0))?
        .expect("authored components");
    assert_eq!(locals.len(), 3);
    // Hip's local at t=0 carries the (0,1,0) translation (row-major [12..15]).
    assert_eq!(locals[1].0[12..15], [0.0, 1.0, 0.0]);

    // At t=0 the animated pose matches the bind pose, so every skinning
    // transform is the identity.
    let skinning = query.skinning_transforms(TimeCode::new(0.0))?;
    assert_eq!(skinning, Some(vec![Mat4d::IDENTITY; 3]));
    Ok(())
}

/// An animation naming neither joints nor blend shapes has a query with empty
/// orders, as in C++.
#[test]
fn anim_query_when_empty() -> Result<()> {
    let stage = memory()?;
    let empty = AnimQuery::new(Animation::define(&stage, "/Empty")?)?;
    assert!(empty.joint_order().is_empty());
    assert!(empty.blend_shape_order().is_empty());
    assert!(empty.joint_local_transforms(None)?.is_none());
    Ok(())
}

/// The query names the attributes it reads, authored or not.
#[test]
fn anim_query_attributes() -> Result<()> {
    let stage = memory()?;
    let query = AnimQuery::new(Animation::define(&stage, "/Anim")?)?;
    let names = |attrs: &[Attribute]| attrs.iter().map(|attr| attr.name().to_owned()).collect::<Vec<_>>();
    assert_eq!(
        names(&query.joint_transform_attributes()),
        ["translations", "rotations", "scales"]
    );
    assert_eq!(names(&query.blend_shape_weight_attributes()), ["blendShapeWeights"]);
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
    let bound = bindings(&stage, "/R")?;
    assert_eq!(bound[0].skeleton().path().as_str(), "/R/Rig");
    let query = skinning_query(&stage, "/R", "/R/G/M")?.expect("M query");
    assert!(query.has_joint_influences());
    assert!(query.is_rigidly_deformed());
    assert_eq!(query.joint_order().map(<[_]>::len), Some(1));
    assert_eq!(query.geom_bind_transform(None)?, Mat4d::translation([1.0, 0.0, 0.0]));

    // Joint `A/B` is skeleton joint 1; the constant influence applies to every
    // point, after the geom bind transform.
    let xforms = Pose::from(vec![Mat4d::IDENTITY, Mat4d::translation([0.0, 2.0, 0.0])]);
    let rigid = query.skinned_transform(&xforms, None)?.expect("constant influences");
    assert_eq!(rigid, Mat4d::translation([1.0, 2.0, 0.0]));
    let points = query
        .skinned_points(&xforms, &[Vec3f::default(), gf::vec3f(1.0, 0.0, 0.0)], None)?
        .expect("constant influences");
    assert_eq!(points, vec![gf::vec3f(1.0, 2.0, 0.0), gf::vec3f(2.0, 2.0, 0.0)]);
    Ok(())
}

#[test]
fn binding_above_root_ignored() -> Result<(), SchemaError> {
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
    assert!(bindings(&stage, "/W/R")?.is_empty());
    Ok(())
}

#[test]
fn empty_skeleton_rel_blocks() -> Result<(), SchemaError> {
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
    assert!(bindings(&stage, "/R")?.is_empty());
    Ok(())
}

#[test]
fn non_api_rel_ignored() -> Result<(), SchemaError> {
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
    let bound = bindings(&stage, "/R")?;
    assert_eq!(bound[0].skeleton().path().as_str(), "/R/Rig");
    assert_eq!(target_paths(&bound[0]), ["/R/G/M"]);
    Ok(())
}

#[test]
fn discovery_prunes_subtrees() -> Result<(), SchemaError> {
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
    let bound = bindings(&stage, "/R")?;
    assert_eq!(target_paths(&bound[0]), ["/R/M", "/R/S/Found"]);
    Ok(())
}

#[test]
fn inactive_skeleton_skipped() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:skeleton = </R/Rig>
    def Skeleton "Rig" (active = false) {}
    def Mesh "M" {}
}
"#,
    )?;
    assert!(bindings(&stage, "/R")?.is_empty());
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
    let query = skinning_query(&stage, "/R", "/R/M")?.expect("M query");
    assert!(!query.has_joint_influences());
    assert!(query.is_rigidly_deformed());
    assert!(
        query
            .skinned_transform(&Pose::from(vec![Mat4d::IDENTITY]), None)?
            .is_none()
    );
    assert!(
        query
            .skinned_points(&Pose::from(vec![Mat4d::IDENTITY]), &[Vec3f::default(); 2], None)?
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
    let query = skinning_query(&stage, "/R", "/R/M")?.expect("M query");
    assert!(!query.has_joint_influences());
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
    let query = skinning_query(&stage, "/R", "/R/M")?.expect("M query");
    assert!(query.has_joint_influences());
    assert!(
        query
            .skinned_points(&Pose::from(vec![Mat4d::IDENTITY]), &[Vec3f::default(); 2], None)?
            .is_none()
    );
    Ok(())
}

#[test]
fn anim_source_from_skeleton() -> Result<(), SchemaError> {
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
    let bound = bindings(&stage, "/R")?;
    assert_eq!(
        bound[0].skeleton().animation_source()?.map(|anim| anim.path().clone()),
        Some(sdf::path("/R/RigAnim")?)
    );
    Ok(())
}

#[test]
fn sparse_anim_fills_rest() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelAnimation "Anim" {
    uniform token[] joints = ["A/B"]
    float3[] translations = [(0, 5, 0)]
    quatf[] rotations = [(1, 0, 0, 0)]
    half3[] scales = [(1, 1, 1)]
}
def Skeleton "Rig" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:animationSource = </Anim>
    uniform token[] joints = ["A", "A/B"]
    uniform matrix4d[] restTransforms = [
        ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (1, 0, 0, 1) ),
        ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 1, 0, 1) ),
    ]
}
def Skeleton "Bare" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:animationSource = </Anim>
    uniform token[] joints = ["A", "A/B"]
}
"#,
    )?;
    let rig = Skeleton::get(&stage, "/Rig")?.expect("Skeleton");
    let rig = SkeletonQuery::new(&rig)?.expect("valid topology");
    assert!(rig.mapper().is_some_and(AnimMapper::is_sparse));
    assert_eq!(
        rig.joint_local_transforms(None)?,
        Some(vec![
            Mat4d::translation([1.0, 0.0, 0.0]),
            Mat4d::translation([0.0, 5.0, 0.0])
        ])
    );
    assert_eq!(
        rig.joint_skel_transforms(None)?,
        Some(vec![
            Mat4d::translation([1.0, 0.0, 0.0]),
            Mat4d::translation([1.0, 5.0, 0.0])
        ])
    );

    // Without a rest pose the uncovered joint has no transform.
    let bare = Skeleton::get(&stage, "/Bare")?.expect("Skeleton");
    let bare = SkeletonQuery::new(&bare)?.expect("valid topology");
    assert!(bare.joint_local_transforms(None)?.is_none());
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
    let rig = SkeletonQuery::new(&rig)?.expect("valid topology");
    assert!(!rig.has_bind_pose());
    assert!(!rig.has_rest_pose());
    assert!(rig.skinning_transforms(None)?.is_none());
    assert!(rig.rest_skel_transforms().is_none());
    // Without an animation or a rest pose there is no pose at all.
    assert!(rig.joint_local_transforms(None)?.is_none());
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
    assert!(SkeletonQuery::new(&rig)?.is_none());
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
    let query = skinning_query(&stage, "/R", "/R/M")?.expect("M query");
    assert_eq!(query.joint_order().map(<[_]>::len), Some(0));
    assert!(
        query
            .skinned_transform(&Pose::from(vec![Mat4d::IDENTITY]), None)?
            .is_none()
    );
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
        AnimQuery::new(anim)
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

/// A deterministic stand-in for the C++ test's `random.random()`.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> f64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 11) as f64 / (1u64 << 53) as f64
    }

    /// A rotation about each axis and a translation, with unit scale, as the
    /// C++ test's `_RandomXf` builds: the components and the matrix.
    fn transform(&mut self) -> (Vec3f, Quatf, Mat4d) {
        let rotation = Mat4d::rotation_x(self.next() * 6.0)
            * Mat4d::rotation_y(self.next() * 6.0)
            * Mat4d::rotation_z(self.next() * 6.0);
        let translation = gf::vec3f(
            ((self.next() - 0.5) * 10.0) as f32,
            ((self.next() - 0.5) * 10.0) as f32,
            ((self.next() - 0.5) * 10.0) as f32,
        );
        let rotation = rotation.extract_rotation_quat().to_f32();
        (
            translation,
            rotation,
            Mat4d::from_trs(translation, rotation, gf::vec3f(1.0, 1.0, 1.0)),
        )
    }
}

fn tokens(names: &[&str]) -> Value {
    Value::TokenVec(names.iter().map(|name| (*name).into()).collect())
}

fn assert_close(a: &[Mat4d], b: &[Mat4d]) {
    assert_eq!(a.len(), b.len());
    for (a, b) in a.iter().zip(b) {
        assert!(
            a.0.iter().zip(b.0.iter()).all(|(x, y)| (x - y).abs() < 1e-4),
            "{a:?} != {b:?}"
        );
    }
}

/// Port of C++ `testUsdSkelSkeletonQuery.py`: a skeleton under an animated
/// root, bound to an animation that leaves its last joint out.
#[test]
fn skeleton_query_poses() -> Result<(), SchemaError> {
    let mut random = Lcg(0);
    let frames: u32 = 10;
    let stage = memory()?;
    let root = Root::define(&stage, "/SkelRoot")?;
    let anim = Animation::define(&stage, "/SkelRoot/Anim")?;
    let skel = Skeleton::define(&stage, "/SkelRoot/Skel")?;
    let binding = BindingAPI::apply(&stage.prim("/SkelRoot")?)?;
    binding.create_skeleton_rel()?.add_target("/SkelRoot/Skel")?;
    binding.create_animation_source_rel()?.add_target("/SkelRoot/Anim")?;

    let joints = ["A", "A/B", "A/B/C", "D", "D/E/F"];
    let (a, ab, abc, d, def) = (0, 1, 2, 3, 4);
    skel.create_joints_attr()?.set(tokens(&joints))?;
    let rest: Vec<Mat4d> = joints.iter().map(|_| random.transform().2).collect();
    let topology = Topology::from_joint_paths(&joints.map(String::from));
    let bind = skinning::joint_local_to_skel_space(&rest, &topology, None).expect("ordered joints");
    skel.create_bind_transforms_attr()?.set(Value::Matrix4dVec(bind))?;
    skel.create_rest_transforms_attr()?
        .set(Value::Matrix4dVec(rest.clone()))?;

    let root_op = root.make_matrix_xform()?;
    let mut root_xforms = Vec::new();
    for frame in 0..frames {
        let xform = random.transform().2;
        root_op.set_at(xform, TimeCode::new(f64::from(frame)))?;
        root_xforms.push(xform);
    }

    // The animation leaves the last joint out.
    anim.create_joints_attr()?.set(tokens(&joints[..4]))?;
    let (translations, rotations, scales) = (
        anim.create_translations_attr()?,
        anim.create_rotations_attr()?,
        anim.create_scales_attr()?,
    );
    scales.set(Value::Vec3hVec(vec![gf::Vec3h::from([gf::f16::from_f32(1.0); 3]); 4]))?;
    let mut anim_xforms = Vec::new();
    for frame in 0..frames {
        let (t, r): (Vec<Vec3f>, Vec<Quatf>) = (0..4)
            .map(|_| {
                let (t, r, _) = random.transform();
                (t, r)
            })
            .unzip();
        let time = TimeCode::new(f64::from(frame));
        translations.clone().set_at(Value::Vec3fVec(t.clone()), time)?;
        rotations.clone().set_at(Value::QuatfVec(r.clone()), time)?;
        anim_xforms.push(skinning::make_transforms(&t, &r, &[gf::vec3f(1.0, 1.0, 1.0); 4]).expect("one of each"));
    }

    let query = SkeletonQuery::new(&skel)?.expect("valid topology");
    assert_close(query.rest_local_transforms().expect("rest pose"), &rest);
    let rest_skel = vec![
        rest[a],
        rest[ab] * rest[a],
        rest[abc] * rest[ab] * rest[a],
        rest[d],
        rest[def] * rest[d],
    ];
    assert_close(query.rest_skel_transforms().expect("rest pose"), &rest_skel);

    for frame in 0..frames {
        let time = TimeCode::new(f64::from(frame));
        let xforms = &anim_xforms[frame as usize];
        let root = root_xforms[frame as usize];
        let mut cache = XformCache::new(time);

        let local: Vec<Mat4d> = xforms.iter().copied().chain([rest[def]]).collect();
        assert_close(&query.joint_local_transforms(time)?.expect("posed"), &local);

        let skel_space = vec![
            xforms[a],
            xforms[ab] * xforms[a],
            xforms[abc] * xforms[ab] * xforms[a],
            xforms[d],
            rest[def] * xforms[d],
        ];
        assert_close(&query.joint_skel_transforms(time)?.expect("posed"), &skel_space);

        let world: Vec<Mat4d> = skel_space.iter().map(|&xform| xform * root).collect();
        assert_close(&query.joint_world_transforms(&mut cache)?.expect("posed"), &world);

        let rest_relative: Vec<Mat4d> = local
            .iter()
            .zip(&rest)
            .map(|(&local, rest)| local * rest.inverse().expect("rigid"))
            .collect();
        assert_close(
            &query.joint_rest_relative_transforms(time)?.expect("rest pose"),
            &rest_relative,
        );

        let rest_world: Vec<Mat4d> = rest_skel.iter().map(|&xform| xform * root).collect();
        assert_close(
            &query.rest_world_transforms(&mut cache)?.expect("rest pose"),
            &rest_world,
        );
    }

    // An inactive animation binds nothing, so the pose is the rest pose.
    stage.prim("/SkelRoot/Anim")?.set_active(false)?;
    let query = SkeletonQuery::new(&skel)?.expect("valid topology");
    assert!(query.anim_query().is_none());
    assert_close(
        &query.joint_local_transforms(TimeCode::new(5.0))?.expect("rest pose"),
        &rest,
    );
    assert_eq!(
        query.joint_rest_relative_transforms(None)?,
        Some(vec![Mat4d::IDENTITY; 5])
    );
    stage.prim("/SkelRoot/Anim")?.set_active(true)?;

    // Blocked translations leave the animation nothing to compose.
    translations.block()?;
    let query = SkeletonQuery::new(&skel)?.expect("valid topology");
    assert_close(
        &query.joint_local_transforms(TimeCode::new(5.0))?.expect("rest pose"),
        &rest,
    );

    // An inactive skeleton has no query.
    stage.prim("/SkelRoot/Skel")?.set_active(false)?;
    assert!(SkeletonQuery::new(&skel)?.is_none());
    Ok(())
}

/// A non-identity rest pose survives an animation that cannot compute,
/// rather than being overwritten with identity components.
#[test]
fn rest_on_bad_anim() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelAnimation "NoTranslations" {
    uniform token[] joints = ["A", "A/B"]
    quatf[] rotations = [(1, 0, 0, 0), (1, 0, 0, 0)]
    half3[] scales = [(1, 1, 1), (1, 1, 1)]
}
def SkelAnimation "BlockedRotations" {
    uniform token[] joints = ["A", "A/B"]
    float3[] translations = [(0, 0, 0), (0, 0, 0)]
    quatf[] rotations = None
    half3[] scales = [(1, 1, 1), (1, 1, 1)]
}
def SkelAnimation "ShortScales" {
    uniform token[] joints = ["A", "A/B"]
    float3[] translations = [(0, 0, 0), (0, 0, 0)]
    quatf[] rotations = [(1, 0, 0, 0), (1, 0, 0, 0)]
    half3[] scales = [(1, 1, 1)]
}
class Skeleton "Rig" {
    uniform token[] joints = ["A", "A/B"]
    uniform matrix4d[] restTransforms = [
        ( (2, 0, 0, 0), (0, 2, 0, 0), (0, 0, 2, 0), (1, 2, 3, 1) ),
        ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 4, 0, 1) ),
    ]
}
def Skeleton "NoTranslationsRig" (inherits = </Rig> prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:animationSource = </NoTranslations>
}
def Skeleton "BlockedRotationsRig" (inherits = </Rig> prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:animationSource = </BlockedRotations>
}
def Skeleton "ShortScalesRig" (inherits = </Rig> prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:animationSource = </ShortScales>
}
"#,
    )?;
    let rest = vec![
        Mat4d::scale([2.0, 2.0, 2.0]) * Mat4d::translation([1.0, 2.0, 3.0]),
        Mat4d::translation([0.0, 4.0, 0.0]),
    ];
    for rig in ["/NoTranslationsRig", "/BlockedRotationsRig", "/ShortScalesRig"] {
        let skel = Skeleton::get(&stage, rig)?.expect("Skeleton");
        let query = SkeletonQuery::new(&skel)?.expect("valid topology");
        assert!(query.anim_query().is_some(), "{rig}");
        assert_eq!(query.joint_local_transforms(None)?, Some(rest.clone()), "{rig}");
    }
    Ok(())
}

/// The query reads the influences and the geom bind transform at the time
/// it is asked for, and an indexed primvar's indices count among its samples.
#[test]
fn skinning_query_time_varying() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "B"]
        uniform matrix4d[] bindTransforms = [
            ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) ),
            ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) ),
        ]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        int[] primvars:skel:jointIndices = [0, 1] (interpolation = "constant")
        int[] primvars:skel:jointIndices:indices.timeSamples = {
            2: [0],
            7: [1],
        }
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
        matrix4d primvars:skel:geomBindTransform.timeSamples = {
            1: ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) ),
            4: ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (3, 0, 0, 1) ),
        }
    }
}
"#,
    )?;
    let query = skinning_query(&stage, "/R", "/R/M")?.expect("M query");
    assert_eq!(query.time_samples()?, vec![1.0, 2.0, 4.0, 7.0]);
    assert_eq!(query.time_samples_in(3.0..=7.0)?, vec![4.0, 7.0]);

    // The indexed indices select joint A before frame 7 and joint B after.
    assert_eq!(query.joint_influences(TimeCode::new(2.0))?, Some((vec![0], vec![1.0])));
    assert_eq!(query.joint_influences(TimeCode::new(7.0))?, Some((vec![1], vec![1.0])));

    let xforms = Pose::from(vec![Mat4d::IDENTITY, Mat4d::translation([0.0, 5.0, 0.0])]);
    assert_eq!(
        query.geom_bind_transform(TimeCode::new(4.0))?,
        Mat4d::translation([3.0, 0.0, 0.0])
    );
    assert_eq!(
        query.skinned_transform(&xforms, TimeCode::new(7.0))?,
        Some(Mat4d::translation([3.0, 5.0, 0.0]))
    );
    // Without `skel:joints` the transforms still need one per skeleton joint.
    let short = Pose::from(vec![Mat4d::IDENTITY]);
    assert!(query.skinned_transform(&short, TimeCode::new(7.0))?.is_none());
    Ok(())
}

/// An unknown skinning method token constructs a query whose skinning methods
/// answer nothing, and `dualQuaternion` skins by dual quaternions: halfway
/// through a quarter-turn twist, a point turns by an eighth and keeps its
/// length.
#[test]
fn skinning_method_dispatch() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "A/B"]
        uniform matrix4d[] bindTransforms = [
            ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) ),
            ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) )
        ]
    }
    def Mesh "Bogus" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
        uniform token primvars:skel:skinningMethod = "bogus"
    }
    def Mesh "Dual" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        int[] primvars:skel:jointIndices = [0, 1] (interpolation = "constant", elementSize = 2)
        float[] primvars:skel:jointWeights = [0.5, 0.5] (interpolation = "constant", elementSize = 2)
        uniform token primvars:skel:skinningMethod = "dualQuaternion"
    }
}
"#,
    )?;
    let xforms = Pose::from(vec![Mat4d::IDENTITY; 2]);
    let points = [Vec3f::default()];
    let bogus = skinning_query(&stage, "/R", "/R/Bogus")?.expect("Bogus query");
    assert_eq!(bogus.skinning_method()?, None);
    assert!(bogus.has_joint_influences());
    assert!(bogus.skinned_points(&xforms, &points, None)?.is_none());
    assert!(bogus.skinned_normals(&xforms, &points, None)?.is_none());
    assert!(bogus.skinned_transform(&xforms, None)?.is_none());

    let dual = skinning_query(&stage, "/R", "/R/Dual")?.expect("Dual query");
    assert_eq!(dual.skinning_method()?, Some(SkinningMethod::DualQuaternion));
    let twist = Pose::from(vec![Mat4d::IDENTITY, Mat4d::rotation_x(FRAC_PI_2)]);
    let eighth = Mat4d::rotation_x(FRAC_PI_4);
    let skinned = dual
        .skinned_points(&twist, &[gf::vec3f(0.0, 1.0, 0.0)], None)?
        .expect("constant influences");
    let expected = eighth.transform_dir(gf::Vec3d::Y_AXIS);
    assert!((gf::Vec3d::from(skinned[0]) - expected).length() < 1e-6, "{skinned:?}");
    let xform = dual.skinned_transform(&twist, None)?.expect("rigid influences");
    assert!(xform.is_close(eighth, 1e-6), "{xform:?}");
    Ok(())
}

/// The prim path of `attribute`, where it is bound.
fn owner(attribute: Option<&Attribute>) -> Option<String> {
    attribute.map(|attribute| attribute.path().prim_path().to_string())
}

/// A query hands back the binding properties it was built from, each on the
/// prim that authors it (C++ `testUsdSkelCache.py`'s
/// `test_InheritedSkeletonBinding`).
#[test]
fn inherited_attr_paths() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def Skeleton "Skel" {}
def SkelRoot "R" {
    def Scope "Scope" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Skel>
        int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
        uniform token[] skel:blendShapes = ["ignored"]
        def Mesh "Inherit" {}
        def Mesh "Override" (prepend apiSchemas = ["SkelBindingAPI"]) {
            int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
            uniform token[] skel:blendShapes = ["shape"]
        }
    }
}
"#,
    )?;
    let cache = populated(&stage, "/R")?;
    let query = |path: &str| -> Result<SkinningQuery> {
        Ok(cache.skinning_query(&stage.prim(path)?).expect("a query").clone())
    };

    let inherit = query("/R/Scope/Inherit")?;
    assert_eq!(
        owner(inherit.joint_indices_primvar().map(Primvar::attribute)),
        Some("/R/Scope".to_string())
    );
    assert_eq!(
        owner(inherit.joint_weights_primvar().map(Primvar::attribute)),
        Some("/R/Scope".to_string())
    );
    assert!(inherit.blend_shapes_attr().is_none());
    assert!(inherit.blend_shape_targets_rel().is_none());
    assert!(inherit.geom_bind_transform_attr().is_none());
    assert!(inherit.skinning_method_attr().is_none());

    let overridden = query("/R/Scope/Override")?;
    assert_eq!(
        owner(overridden.joint_indices_primvar().map(Primvar::attribute)),
        Some("/R/Scope/Override".to_string())
    );
    assert_eq!(
        owner(overridden.joint_weights_primvar().map(Primvar::attribute)),
        Some("/R/Scope".to_string())
    );
    assert_eq!(
        owner(overridden.blend_shapes_attr()),
        Some("/R/Scope/Override".to_string())
    );
    Ok(())
}

/// Under an instance proxy the binding properties are the prototype prim's,
/// all but the skinning method, which stays the proxy's (C++
/// `testUsdSkelCache.py`'s `test_InstancedSkeletonBinding`).
#[test]
fn instanced_attr_paths() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def Skeleton "Skel" {}
def Scope "Model" (instanceable = true) {
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
        uniform token primvars:skel:skinningMethod = "dualQuaternion"
    }
}
def SkelRoot "R" {
    def Scope "Instance" (prepend references = </Model> prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Skel>
    }
}
"#,
    )?;
    let query = skinning_query(&stage, "/R", "/R/Instance/M")?.expect("a query");
    let indices = query.joint_indices_primvar().expect("bound joint indices");
    let prototype = stage
        .prim("/R/Instance/M")?
        .prim_in_prototype()?
        .expect("an instance proxy");
    assert_eq!(indices.attribute().path().prim_path(), *prototype.path());
    assert_eq!(owner(query.skinning_method_attr()), Some("/R/Instance/M".to_string()));
    assert_eq!(query.skinning_method()?, Some(SkinningMethod::DualQuaternion));
    Ok(())
}

/// Unauthored, the method has no attribute and reads `classicLinear`;
/// authored, it reads back (C++ `testUsdSkelSkinningQuery.py`).
#[test]
fn skinning_method_attr() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Mesh "Plain" (prepend apiSchemas = ["SkelBindingAPI"]) {
        int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
    }
    def Mesh "Dual" (prepend apiSchemas = ["SkelBindingAPI"]) {
        uniform token primvars:skel:skinningMethod = "dualQuaternion"
    }
}
"#,
    )?;
    let plain = skinning_query(&stage, "/R", "/R/Plain")?.expect("Plain query");
    assert!(plain.skinning_method_attr().is_none());
    assert_eq!(plain.skinning_method()?, Some(SkinningMethod::ClassicLinear));
    let dual = skinning_query(&stage, "/R", "/R/Dual")?.expect("Dual query");
    assert_eq!(owner(dual.skinning_method_attr()), Some("/R/Dual".to_string()));
    assert_eq!(dual.skinning_method()?, Some(SkinningMethod::DualQuaternion));
    Ok(())
}

/// The method is read on each call, so an edit after the cache is populated
/// shows.
#[test]
fn skinning_method_live() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        uniform token primvars:skel:skinningMethod = "classicLinear"
    }
}
"#,
    )?;
    let query = skinning_query(&stage, "/R", "/R/M")?.expect("a query");
    assert_eq!(query.skinning_method()?, Some(SkinningMethod::ClassicLinear));
    query
        .skinning_method_attr()
        .expect("a bound method")
        .clone()
        .set(Value::token("dualQuaternion"))?;
    assert_eq!(query.skinning_method()?, Some(SkinningMethod::DualQuaternion));
    Ok(())
}

/// A pose shared by prims whose `skel:joints` reorders the skeleton's joints,
/// drops one and names one the skeleton lacks skins each prim as its own
/// remapped transforms do. The dropped joint scales, and no joint in the
/// subset does, so no point is carried through the leftover scales: under
/// weights that sum to 0.8 a point turned by pure rotations keeps its length.
#[test]
fn pose_remaps_subset() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "A/B", "A/B/C"]
    }
    def Mesh "Dual" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = ["A/B/C", "A", "Missing"]
        int[] primvars:skel:jointIndices = [0, 1, 1, 2] (interpolation = "vertex", elementSize = 2)
        float[] primvars:skel:jointWeights = [0.5, 0.3, 0.5, 0.3] (interpolation = "vertex", elementSize = 2)
        uniform token primvars:skel:skinningMethod = "dualQuaternion"
    }
    def Mesh "Linear" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = ["A/B/C", "A", "Missing"]
        int[] primvars:skel:jointIndices = [0, 1, 1, 2] (interpolation = "vertex", elementSize = 2)
        float[] primvars:skel:jointWeights = [0.5, 0.3, 0.5, 0.3] (interpolation = "vertex", elementSize = 2)
    }
    def Mesh "Rigid" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = ["A/B/C", "A", "Missing"]
        int[] primvars:skel:jointIndices = [0, 1] (interpolation = "constant", elementSize = 2)
        float[] primvars:skel:jointWeights = [0.5, 0.3] (interpolation = "constant", elementSize = 2)
        uniform token primvars:skel:skinningMethod = "dualQuaternion"
    }
}
"#,
    )?;
    let xforms = vec![
        Mat4d::rotation_x(FRAC_PI_2),
        Mat4d::scale([2.0, 3.0, 4.0]),
        Mat4d::rotation_z(FRAC_PI_4),
    ];
    let remapped = [xforms[2], xforms[0], Mat4d::IDENTITY];
    let pose = Pose::from(xforms);
    let points = [gf::vec3f(1.0, 2.0, 3.0), gf::vec3f(0.0, 1.0, 0.0)];
    let (indices, weights) = ([0, 1, 1, 2], [0.5, 0.3, 0.5, 0.3]);
    let near = |a: &[Vec3f], b: &[Vec3f]| a.iter().zip(b).all(|(a, b)| (*a - *b).length() < 1e-6);
    let bind = Mat4d::IDENTITY;

    let dual = skinning_query(&stage, "/R", "/R/Dual")?.expect("Dual query");
    let method = SkinningMethod::DualQuaternion;
    let skinned = dual.skinned_points(&pose, &points, None)?.expect("vertex influences");
    let expected = skinning::skin_points(method, &points, &indices, &weights, 2, bind, &remapped).expect("valid");
    assert!(near(&skinned, &expected), "{skinned:?} != {expected:?}");
    for (skinned, point) in skinned.iter().zip(points) {
        assert!((skinned.length() - point.length()).abs() < 1e-5, "{skinned:?}");
    }
    let skinned = dual.skinned_normals(&pose, &points, None)?.expect("vertex influences");
    let expected = skinning::skin_normals(method, &points, &indices, &weights, 2, bind, &remapped).expect("valid");
    assert!(near(&skinned, &expected), "{skinned:?} != {expected:?}");

    let linear = skinning_query(&stage, "/R", "/R/Linear")?.expect("Linear query");
    let method = SkinningMethod::ClassicLinear;
    let skinned = linear.skinned_points(&pose, &points, None)?.expect("vertex influences");
    let expected = skinning::skin_points(method, &points, &indices, &weights, 2, bind, &remapped).expect("valid");
    assert!(near(&skinned, &expected), "{skinned:?} != {expected:?}");
    let skinned = linear
        .skinned_normals(&pose, &points, None)?
        .expect("vertex influences");
    let expected = skinning::skin_normals(method, &points, &indices, &weights, 2, bind, &remapped).expect("valid");
    assert!(near(&skinned, &expected), "{skinned:?} != {expected:?}");

    let rigid = skinning_query(&stage, "/R", "/R/Rigid")?.expect("Rigid query");
    let skinned = rigid.skinned_transform(&pose, None)?.expect("constant influences");
    let expected =
        skinning::skin_transform(SkinningMethod::DualQuaternion, &[0, 1], &[0.5, 0.3], bind, &remapped).expect("valid");
    assert!(skinned.is_close(expected, 1e-9), "{skinned:?} != {expected:?}");
    // Through pure rotations the frame stays orthonormal.
    assert!(
        (skinned.extract_rotation_matrix().determinant() - 1.0).abs() < 1e-9,
        "{skinned:?}"
    );
    Ok(())
}

/// A prim whose skeleton has no query still gets one, with empty skeleton
/// and animation orders: its joint subset and blend shapes map nothing.
#[test]
fn skinning_without_skeleton() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A/B", "A"]
    }
    def BlendShape "Smile" {
        uniform vector3f[] offsets = [(0, 1, 0)]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = ["A"]
        uniform token[] skel:blendShapes = ["smile"]
        rel skel:blendShapeTargets = </R/Smile>
    }
}
"#,
    )?;
    let mut cache = populated(&stage, "/R")?;
    // The skeleton's joints are misordered, so it has no query.
    let rig = Skeleton::get(&stage, "/R/Rig")?.expect("Skeleton");
    assert!(cache.skel_query(&rig)?.is_none());
    let query = cache.skinning_query(&stage.prim("/R/M")?).expect("M query");
    assert!(query.has_blend_shapes());
    assert_eq!(query.blend_shape_order(), Some(&["smile".to_string()][..]));
    assert!(query.blend_shape_mapper().is_some_and(AnimMapper::is_null));
    assert!(query.joint_mapper().is_some_and(AnimMapper::is_null));
    assert_eq!(
        query.blend_shape_targets_rel().map(|rel| rel.targets()).transpose()?,
        Some(vec![sdf::path("/R/Smile")?])
    );
    Ok(())
}

/// The padding is how far the prim's bound, carried through its geom bind
/// transform, reaches past the box around the rest pose's joints.
#[test]
fn extents_padding_reach() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "A/B"]
        uniform matrix4d[] restTransforms = [
            ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) ),
            ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 2, 0, 1) ),
        ]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        float3[] extent = [(-1, 0, -0.5), (1, 2, 0.5)]
        matrix4d primvars:skel:geomBindTransform = ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0.5, 0, 1) )
    }
    def Mesh "Bare" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
    }
}
"#,
    )?;
    let mut cache = populated(&stage, "/R")?;
    let rig = Skeleton::get(&stage, "/R/Rig")?.expect("Skeleton");
    let skeleton = cache.skel_query(&rig)?.expect("valid topology");
    let query = cache.skinning_query(&stage.prim("/R/M")?).expect("M query");
    let rest = skeleton.rest_skel_transforms().expect("rest pose");
    let mesh = Mesh::get(&stage, "/R/M")?.expect("Mesh");
    // The joints span (0, 0, 0) to (0, 2, 0); the bound, raised by 0.5,
    // spans (-1, 0.5, -0.5) to (1, 2.5, 0.5), reaching 1 past them in x.
    assert_eq!(query.extents_padding(rest, &mesh)?, 1.0);
    let bare = Mesh::get(&stage, "/R/Bare")?.expect("Mesh");
    assert_eq!(query.extents_padding(rest, &bare)?, 0.0);
    Ok(())
}

/// The fixture's Body binds the Smile blend shape, whose sub-shapes are the
/// rest shape, its `half` inbetween at 0.5 and the primary shape.
#[test]
fn blend_shape_query_layout() -> Result<()> {
    let stage = open()?;
    let body = BindingAPI::get(&stage, "/World/Character/Body")?.expect("BindingAPI");
    let query = BlendShapeQuery::new(&body)?;
    assert_eq!(query.num_blend_shapes(), 1);
    assert_eq!(query.num_sub_shapes(), 3);
    assert_eq!(
        query.blend_shape(0).map(|shape| shape.path().as_str()),
        Some("/World/Character/Smile")
    );
    assert_eq!(
        query.inbetween(1).map(|inbetween| inbetween.attribute().name()),
        Some("inbetweens:half")
    );
    assert!(query.inbetween(2).is_none());
    assert_eq!(query.blend_shape_index(2), 0);

    // Between the inbetween and the primary shape, halfway.
    let weights = query.sub_shape_weights(&[0.75]).expect("one weight per shape");
    assert_eq!(weights.iter().map(|w| w.sub_shape).collect::<Vec<_>>(), vec![1, 2]);
    assert_eq!(weights.iter().map(|w| w.weight).collect::<Vec<_>>(), vec![0.5, 0.5]);
    assert_eq!(query.flattened_sub_shape_weights(&[0.75]), Some(vec![0.0, 0.5, 0.5]));
    assert!(query.sub_shape_weights(&[]).is_none());

    let indices = query.blend_shape_point_indices()?;
    assert_eq!(indices, vec![vec![0, 1]]);
    let offsets = query.sub_shape_point_offsets()?;
    assert_eq!(
        offsets,
        vec![
            vec![],
            vec![gf::vec3f(0.0, 0.04, 0.0); 2],
            vec![gf::vec3f(0.0, 0.1, 0.0); 2]
        ]
    );
    assert_eq!(query.sub_shape_normal_offsets()?[2], vec![Vec3f::default(); 2]);

    // At full weight only the primary shape applies, to points 0 and 1.
    let full = query.sub_shape_weights(&[1.0]).expect("one weight per shape");
    let points = vec![Vec3f::default(); 4];
    let deformed = BlendShapeQuery::deformed_points(&full, &indices, &offsets, &points).expect("offsets fit");
    assert_eq!(
        deformed,
        vec![
            gf::vec3f(0.0, 0.1, 0.0),
            gf::vec3f(0.0, 0.1, 0.0),
            Vec3f::default(),
            Vec3f::default()
        ]
    );
    // A sub-shape index past the offsets is rejected.
    assert!(BlendShapeQuery::deformed_points(&full, &indices, &offsets[..1], &points).is_none());
    Ok(())
}

/// A target that is not a blend shape, or is inactive, keeps its place in
/// the layout with no sub-shapes, so its weight applies nothing.
#[test]
fn blend_shape_query_skips() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def BlendShape "Up" {
    uniform vector3f[] offsets = [(0, 1, 0), (0, 2, 0)]
    uniform vector3f[] normalOffsets = [(0, 1, 0), (0, 1, 0)]
}
def BlendShape "Off" (active = false) {
    uniform vector3f[] offsets = [(1, 0, 0), (1, 0, 0)]
}
def Xform "NotAShape" {}
def BlendShape "Side" {
    uniform vector3f[] offsets = [(0, 0, 3)]
    uniform int[] pointIndices = [1]
    uniform vector3f[] inbetweens:bad (weight = 1) = [(0, 0, 9)]
}
def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:blendShapeTargets = [</Up>, </Off>, </NotAShape>, </Side>, </Up.offsets>]
}
"#,
    )?;
    let mesh = BindingAPI::get(&stage, "/M")?.expect("BindingAPI");
    let query = BlendShapeQuery::new(&mesh)?;
    // The property-path target keeps its place as no blend shape.
    assert_eq!(query.num_blend_shapes(), 5);
    assert!(query.blend_shape(4).is_none());
    // Up and Side each have a rest and a primary shape; Side's inbetween at
    // weight 1 is left out.
    assert_eq!(query.num_sub_shapes(), 4);
    assert!(query.blend_shape(1).is_some());
    assert!(query.blend_shape(2).is_none());

    let weights = query
        .sub_shape_weights(&[0.5, 1.0, 1.0, 2.0, 1.0])
        .expect("one weight per shape");
    assert_eq!(weights.iter().map(|w| w.blend_shape).collect::<Vec<_>>(), vec![0, 3]);
    assert_eq!(weights.iter().map(|w| w.weight).collect::<Vec<_>>(), vec![0.5, 2.0]);

    // Up's primary shape, sub-shape 1, is dense over points 0 and 1; Side's,
    // sub-shape 3, adds to point 1 alone. The table covers one point past the
    // largest offset count, as C++ lays it out.
    let (table, ranges) = query.packed_shape_table()?.expect("valid indices");
    assert_eq!(ranges, vec![gf::vec2i(0, 1), gf::vec2i(1, 3), gf::vec2i(3, 4)]);
    assert_eq!(
        table,
        vec![
            gf::vec4f(0.0, 1.0, 0.0, 1.0),
            gf::vec4f(0.0, 2.0, 0.0, 1.0),
            gf::vec4f(0.0, 0.0, 3.0, 3.0),
            gf::Vec4f::default(),
        ]
    );

    // Normals deform by the normal offsets, which only Up authors, and come
    // back normalized.
    let indices = query.blend_shape_point_indices()?;
    let offsets = query.sub_shape_normal_offsets()?;
    let normals = BlendShapeQuery::deformed_normals(&weights, &indices, &offsets, &[gf::vec3f(1.0, 0.0, 0.0); 2])
        .expect("offsets fit");
    assert!(
        (normals[1] - gf::vec3f(1.0, 0.5, 0.0).normalize()).length() < 1e-6,
        "{normals:?}"
    );
    Ok(())
}

/// A negative point index has no slot in the packed table.
#[test]
fn packed_table_negative_index() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def BlendShape "Bad" {
    uniform vector3f[] offsets = [(0, 1, 0)]
    uniform int[] pointIndices = [-1]
}
def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:blendShapeTargets = </Bad>
}
"#,
    )?;
    let mesh = BindingAPI::get(&stage, "/M")?.expect("BindingAPI");
    assert!(BlendShapeQuery::new(&mesh)?.packed_shape_table()?.is_none());
    Ok(())
}

/// The asset's skinned meshes declare `skel:blendShapes`, with no value, and
/// no `skel:blendShapeTargets`, so their queries lay out no blend shapes, and
/// weigh and pack nothing.
#[test]
fn blend_shapes_on_asset() -> Result<()> {
    let stage = vendor("usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc")?;
    let mut paths = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT_PROXIES, |path| paths.push(path.clone()))?;
    let mut named = 0;
    for path in paths {
        let Some(binding) = BindingAPI::get(&stage, path)? else {
            continue;
        };
        if binding
            .authored_property_names()?
            .iter()
            .any(|name| name == "skel:blendShapes")
        {
            named += 1;
        }
        let query = BlendShapeQuery::new(&binding)?;
        assert_eq!(query.num_blend_shapes(), 0);
        assert_eq!(query.sub_shape_weights(&[]), Some(Vec::new()));
        assert_eq!(query.packed_shape_table()?, Some((Vec::new(), Vec::new())));
    }
    assert_eq!(named, 2, "the elephant and the monochord author skel:blendShapes");
    Ok(())
}

/// A target that is another relationship stands for the blend shapes that
/// relationship forwards to.
#[test]
fn forwarded_blend_shape_targets() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def BlendShape "Up" {
    uniform vector3f[] offsets = [(0, 1, 0)]
}
def BlendShape "Side" {
    uniform vector3f[] offsets = [(1, 0, 0)]
}
def Scope "Shapes" {
    custom rel all = [</Up>, </Side>]
}
def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:blendShapeTargets = </Shapes.all>
}
"#,
    )?;
    let mesh = BindingAPI::get(&stage, "/M")?.expect("BindingAPI");
    let query = BlendShapeQuery::new(&mesh)?;
    assert_eq!(query.num_blend_shapes(), 2);
    assert_eq!(query.blend_shape(0).map(|shape| shape.path().as_str()), Some("/Up"));
    assert_eq!(query.blend_shape(1).map(|shape| shape.path().as_str()), Some("/Side"));
    Ok(())
}

/// A skeleton binds the animation it inherits, across instancing too (the
/// cases of C++ `testUsdSkelCache.py`'s `test_InheritedAnimBinding`).
#[test]
fn cache_inherited_anim() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelAnimation "Anim1" {}
def SkelAnimation "Anim2" {}
def SkelAnimation "Off" (active = false) {}
def Scope "Model" (instanceable = true) {
    def SkelAnimation "Anim" {}
    def Skeleton "Inherit" {}
    def Skeleton "Override" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:animationSource = </Model/Anim>
    }
}
def SkelRoot "R" {
    def Scope "Scope" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:animationSource = </Anim1>
        def Skeleton "Inherit" {}
        def Skeleton "Override" (prepend apiSchemas = ["SkelBindingAPI"]) {
            rel skel:animationSource = </Anim2>
        }
        def Skeleton "Block" (prepend apiSchemas = ["SkelBindingAPI"]) {
            rel skel:animationSource = []
        }
    }
    def Skeleton "Unbound" {}
    def Skeleton "ToInactive" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:animationSource = </Off>
    }
    def Scope "Instance" (prepend references = </Model> prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:animationSource = </Anim1>
    }
}
"#,
    )?;
    let mut cache = Cache::new();
    let mut anim_of = |path: &str| -> Result<Option<String>, SchemaError> {
        let skeleton = Skeleton::get(&stage, path)?.expect("Skeleton");
        let query = cache.skel_query(&skeleton)?.expect("valid topology");
        assert_eq!(query.skeleton().path().as_str(), path);
        Ok(query.anim_query().map(|anim| anim.animation().path().to_string()))
    };
    assert_eq!(anim_of("/R/Scope/Inherit")?.as_deref(), Some("/Anim1"));
    assert_eq!(anim_of("/R/Scope/Override")?.as_deref(), Some("/Anim2"));
    assert_eq!(anim_of("/R/Scope/Block")?, None);
    assert_eq!(anim_of("/R/Unbound")?, None);
    assert_eq!(anim_of("/R/ToInactive")?, None);
    // The binding reaches an instance proxy from above the instance.
    assert_eq!(anim_of("/R/Instance/Inherit")?.as_deref(), Some("/Anim1"));
    // An animation inside the instance is read through its prototype.
    let overridden = anim_of("/R/Instance/Override")?.expect("an animation");
    assert!(stage.prim(overridden.as_str())?.is_in_prototype()?);
    Ok(())
}

/// Each skinnable prim joins the binding of the skeleton in effect at it, with
/// the binding properties it inherits (C++ `testUsdSkelCache.py`'s
/// `test_InheritedSkeletonBinding`).
#[test]
fn cache_skeleton_bindings() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def Skeleton "Skel1" {}
def Skeleton "Skel2" {}
def Skeleton "Off" (active = false) {}
def SkelRoot "R" {
    def Scope "Scope" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Skel1>
        uniform token[] skel:joints = ["scope"]
        uniform token[] skel:blendShapes = ["ignored"]
        def Mesh "Inherit" {}
        def Mesh "Override" (prepend apiSchemas = ["SkelBindingAPI"]) {
            rel skel:skeleton = </Skel2>
            uniform token[] skel:joints = ["override"]
            uniform token[] skel:blendShapes = ["shape"]
        }
        def Mesh "Block" (prepend apiSchemas = ["SkelBindingAPI"]) {
            rel skel:skeleton = []
        }
    }
    def Mesh "Unbound" {}
    def Mesh "ToInactive" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Off>
    }
}
"#,
    )?;
    let root = root(&stage, "/R")?;
    let mut cache = Cache::new();
    cache.populate(&root, PrimPredicate::DEFAULT)?;
    let skeleton = |path: &str| -> Result<Skeleton> { Ok(Skeleton::get(&stage, path)?.expect("Skeleton")) };

    let first = cache.skel_binding(&root, &skeleton("/Skel1")?, PrimPredicate::DEFAULT)?;
    assert_eq!(target_paths(&first), ["/R/Scope/Inherit"]);
    let inherit = &first.skinning_targets()[0];
    assert_eq!(inherit.joint_order(), Some(&["scope".to_string()][..]));
    // The blend-shape bindings are not inherited.
    assert_eq!(inherit.blend_shape_order(), None);

    let second = cache.skel_binding(&root, &skeleton("/Skel2")?, PrimPredicate::DEFAULT)?;
    assert_eq!(target_paths(&second), ["/R/Scope/Override"]);
    let overridden = &second.skinning_targets()[0];
    assert_eq!(overridden.joint_order(), Some(&["override".to_string()][..]));
    assert_eq!(overridden.blend_shape_order(), Some(&["shape".to_string()][..]));

    // Only the active skeletons have bindings, ordered by path.
    let all = cache.skel_bindings(&root, PrimPredicate::DEFAULT)?;
    let skeletons: Vec<_> = all.iter().map(|binding| binding.skeleton().path().as_str()).collect();
    assert_eq!(skeletons, ["/Skel1", "/Skel2"]);
    assert_eq!(target_paths(&all[0]), target_paths(&first));
    // Asked for by name, an inactive skeleton still finds its prims.
    let off = cache.skel_binding(&root, &skeleton("/Off")?, PrimPredicate::DEFAULT)?;
    assert_eq!(target_paths(&off), ["/R/ToInactive"]);
    // Every skinnable prim has a query, bound or not.
    for path in ["/R/Scope/Block", "/R/Unbound", "/R/ToInactive"] {
        assert!(cache.skinning_query(&stage.prim(path)?).is_some(), "{path}");
    }
    Ok(())
}

/// Instance proxies are populated only through a predicate that traverses
/// them, and bind as their prototype's prims do (C++ `testUsdSkelCache.py`'s
/// `test_InstancedSkeletonBinding` and `test_InstancedBlendShape`).
#[test]
fn cache_instanced_bindings() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelAnimation "Anim1" {
    uniform token[] blendShapes = ["override", "shape"]
}
def Skeleton "Skel1" {}
def Scope "Model" (instanceable = true) {
    def Skeleton "Skel" {}
    def BlendShape "Shape" {}
    def Mesh "Inherit" {}
    def Mesh "Override" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Model/Skel>
        uniform token[] skel:joints = ["override"]
        uniform token[] skel:blendShapes = ["override"]
        rel skel:blendShapeTargets = </Model/Shape>
    }
}
def SkelRoot "R" (prepend apiSchemas = ["SkelBindingAPI"]) {
    rel skel:animationSource = </Anim1>
    def Scope "Scope" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Skel1>
        uniform token[] skel:joints = ["scope"]
        def Mesh "Inherit" {}
    }
    def Scope "Instance" (prepend references = </Model> prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Skel1>
        uniform token[] skel:joints = ["instance"]
    }
}
"#,
    )?;
    let root = root(&stage, "/R")?;
    let inherit = stage.prim("/R/Instance/Inherit")?;
    let overridden = stage.prim("/R/Instance/Override")?;
    let mut cache = Cache::new();
    cache.populate(&root, PrimPredicate::DEFAULT)?;
    assert!(cache.skinning_query(&inherit).is_none());
    assert!(cache.skinning_query(&overridden).is_none());

    let proxies = PrimPredicate::DEFAULT_PROXIES;
    cache.populate(&root, proxies)?;
    let skel1 = Skeleton::get(&stage, "/Skel1")?.expect("Skeleton");
    let first = cache.skel_binding(&root, &skel1, proxies)?;
    assert_eq!(target_paths(&first), ["/R/Scope/Inherit", "/R/Instance/Inherit"]);
    let instanced = &first.skinning_targets()[1];
    assert_eq!(instanced.joint_order(), Some(&["instance".to_string()][..]));
    assert_eq!(instanced.blend_shape_order(), None);

    // The skeleton inside the instance binds too, and sorts first by path.
    let all = cache.skel_bindings(&root, proxies)?;
    let skeletons: Vec<_> = all.iter().map(|binding| binding.skeleton().path().as_str()).collect();
    assert_eq!(skeletons, ["/R/Instance/Skel", "/Skel1"]);
    assert_eq!(target_paths(&all[0]), ["/R/Instance/Override"]);

    // The instance's skeleton binds the animation the root names, whose
    // blend-shape order differs from the prim's, so the mapper remaps.
    let query = cache.skinning_query(&overridden).expect("Override query");
    assert_eq!(query.joint_order(), Some(&["override".to_string()][..]));
    assert_eq!(query.blend_shape_order(), Some(&["override".to_string()][..]));
    assert!(query.has_blend_shapes());
    assert!(query.blend_shape_mapper().is_some_and(|mapper| !mapper.is_null()));
    let skel = cache.skel_query(all[0].skeleton())?.expect("valid topology");
    assert_eq!(
        skel.anim_query().map(AnimQuery::blend_shape_order),
        Some(&["override".to_string(), "shape".to_string()][..])
    );
    Ok(())
}

/// One cache populated from two stages that hold the same paths keeps their
/// queries apart.
#[test]
fn cache_two_stages() -> Result<(), SchemaError> {
    let scene = |joint: &str| {
        from_usda(&format!(
            r#"#usda 1.0
def SkelRoot "R" {{
    def Skeleton "Rig" {{
        uniform token[] joints = ["{joint}"]
    }}
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {{
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = ["{joint}"]
    }}
}}
"#
        ))
    };
    let (first, second) = (scene("A")?, scene("B")?);
    let mut cache = Cache::new();
    for stage in [&first, &second] {
        cache.populate(&root(stage, "/R")?, PrimPredicate::DEFAULT)?;
    }
    for (stage, joint) in [(&first, "A"), (&second, "B")] {
        let query = cache.skinning_query(&stage.prim("/R/M")?).expect("M query");
        assert_eq!(query.joint_order(), Some(&[joint.to_string()][..]));
        let rig = Skeleton::get(stage, "/R/Rig")?.expect("Skeleton");
        let skel = cache.skel_query(&rig)?.expect("valid topology");
        assert_eq!(skel.joint_order(), [joint.to_string()]);
    }
    Ok(())
}

/// The cache keeps what it built until it is cleared: a populate after an edit
/// keeps the stale query, and a populate after `clear` picks the edit up.
#[test]
fn cache_clear_repopulates() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "B"]
    }
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Rig>
        uniform token[] skel:joints = ["A"]
    }
}
"#,
    )?;
    let root = root(&stage, "/R")?;
    let mesh = stage.prim("/R/M")?;
    let mut cache = Cache::new();
    cache.populate(&root, PrimPredicate::DEFAULT)?;
    BindingAPI::get(&stage, "/R/M")?
        .expect("BindingAPI")
        .joints_attr()
        .set(Value::TokenVec(vec!["B".into()]))?;
    let order = |cache: &Cache| {
        cache
            .skinning_query(&mesh)
            .and_then(|query| query.joint_order().map(<[_]>::to_vec))
    };
    cache.populate(&root, PrimPredicate::DEFAULT)?;
    assert_eq!(order(&cache), Some(vec!["A".to_string()]));
    cache.clear();
    assert!(cache.skinning_query(&mesh).is_none());
    cache.populate(&root, PrimPredicate::DEFAULT)?;
    assert_eq!(order(&cache), Some(vec!["B".to_string()]));
    Ok(())
}

/// Populate a cache from every Root on `stage` and skin each bound mesh at
/// the default time, checking that each Root computes an extent. Answers
/// the number of prims bound and the number skinned.
fn skin_everything(stage: &Stage) -> Result<(usize, usize), SchemaError> {
    let mut cache = Cache::new();
    let (mut bound, mut skinned) = (0, 0);
    for root in typed(stage, Root::get)? {
        assert!(root.shape_extent(None, None)?.is_some(), "{} extent", root.path());
        cache.populate(&root, PrimPredicate::DEFAULT_PROXIES)?;
        for binding in cache.skel_bindings(&root, PrimPredicate::DEFAULT_PROXIES)? {
            let skel = cache.skel_query(binding.skeleton())?.expect("valid topology");
            let pose = Pose::from(skel.skinning_transforms(None)?.expect("bind pose"));
            for query in binding.skinning_targets() {
                bound += 1;
                let points: Option<Vec<Vec3f>> = query.prim().attribute("points").cast()?;
                if let Some(points) = points
                    && query.skinned_points(&pose, &points, None)?.is_some()
                {
                    skinned += 1;
                }
            }
        }
    }
    Ok((bound, skinned))
}

#[test]
fn cache_skins_assets() -> Result<(), SchemaError> {
    let biplane =
        vendor("core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary/toy_biplane_idle.usdc")?;
    // The biplane binds its 15 skinnable meshes to one skeleton.
    assert_eq!(skin_everything(&biplane)?, (15, 15));
    let elephant = vendor("usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc")?;
    let (bound, skinned) = skin_everything(&elephant)?;
    assert!(bound > 0 && skinned == bound, "{bound} bound, {skinned} skinned");
    Ok(())
}

/// A Root the predicate rejects, here an abstract one, populates nothing, as
/// a C++ `UsdPrimRange` that starts at it is empty.
#[test]
fn cache_root_predicate() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
class SkelRoot "R" {
    def Mesh "M" {}
}
"#,
    )?;
    let root = root(&stage, "/R")?;
    let mesh = stage.prim("/R/M")?;
    let mut cache = Cache::new();
    cache.populate(&root, PrimPredicate::DEFAULT)?;
    assert!(cache.skinning_query(&mesh).is_none());
    cache.populate(&root, PrimPredicate::ALL)?;
    assert!(cache.skinning_query(&mesh).is_some());
    Ok(())
}

/// `extent`'s corners, for comparing against a box written out.
fn corners(extent: Option<Extent>) -> Option<[[f32; 3]; 2]> {
    extent.map(|[min, max]| [min.into(), max.into()])
}

#[test]
fn skeleton_extent_posed() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Skeleton "Rig" (prepend apiSchemas = ["SkelBindingAPI"]) {
        uniform token[] joints = ["A", "A/B"]
        uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)), ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 2, 0, 1))]
        rel skel:animationSource = </R/Anim>
        double3 xformOp:translate.timeSamples = { 1: (0, 0, 0), 2: (0, 0, 3) }
        uniform token[] xformOpOrder = ["xformOp:translate"]
    }
    def SkelAnimation "Anim" {
        uniform token[] joints = ["A/B"]
        float3[] translations.timeSamples = { 1: [(0, 2, 0)], 2: [(4, 0, 0)] }
        quatf[] rotations = [(1, 0, 0, 0)]
        half3[] scales = [(1, 1, 1)]
    }
}
"#,
    )?;
    let rig = Skeleton::get(&stage, "/R/Rig")?.expect("Rig");
    let root = root(&stage, "/R")?;
    let (one, two) = (TimeCode::new(1.0), TimeCode::new(2.0));
    assert_eq!(corners(rig.shape_extent(one, None)?), Some([[0.0; 3], [0.0, 2.0, 0.0]]));
    assert_eq!(corners(rig.shape_extent(two, None)?), Some([[0.0; 3], [4.0, 0.0, 0.0]]));
    let shifted = Mat4d::translation([1.0, 0.0, 0.0]);
    assert_eq!(
        corners(rig.shape_extent(two, shifted)?),
        Some([[1.0, 0.0, 0.0], [5.0, 0.0, 0.0]])
    );
    // The root places the skeleton by its transform at the time asked for.
    assert_eq!(
        corners(root.shape_extent(two, None)?),
        Some([[0.0, 0.0, 3.0], [4.0, 0.0, 3.0]])
    );
    Ok(())
}

#[test]
fn root_extent_bindings() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "Bound" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "A/B"]
        uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)), ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 2, 0, 1))]
    }
    def Mesh "Body" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Bound/Rig>
        float3[] extent = [(-1, 0, 0), (1, 3, 0)]
        int[] primvars:skel:jointIndices = [0] (interpolation = "constant")
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
    }
}
def SkelRoot "Unbound" {
    def Skeleton "Rig" {
        uniform token[] joints = ["A", "A/B"]
        uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)), ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 2, 0, 1))]
    }
    def Mesh "Body" {
        float3[] extent = [(-1, 0, 0), (1, 3, 0)]
    }
}
def SkelRoot "Empty" {
}
"#,
    )?;
    // Body reaches one unit past the joints' box, on X below and above and
    // on Y above, and pads the box by that on every side.
    assert_eq!(
        corners(root(&stage, "/Bound")?.shape_extent(None, None)?),
        Some([[-1.0; 3], [1.0, 3.0, 1.0]])
    );
    assert_eq!(
        corners(root(&stage, "/Unbound")?.shape_extent(None, None)?),
        Some([[0.0; 3], [0.0, 2.0, 0.0]])
    );
    assert_eq!(root(&stage, "/Empty")?.shape_extent(None, None)?, None);
    Ok(())
}

#[test]
fn root_extent_reset() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def Xform "World" {
    double3 xformOp:translate = (0, 5, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]

    def SkelRoot "R" {
        def Skeleton "Kept" {
            uniform token[] joints = ["A"]
            uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (1, 0, 0, 1))]
            double3 xformOp:translate = (0, 0, 1)
            uniform token[] xformOpOrder = ["xformOp:translate"]
        }
        def Skeleton "Reset" {
            uniform token[] joints = ["A"]
            uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (-1, 0, 0, 1))]
            uniform token[] xformOpOrder = ["!resetXformStack!"]
        }
    }
}
"#,
    )?;
    let root = root(&stage, "/World/R")?;
    let shifted = Mat4d::translation([10.0, 0.0, 0.0]);
    assert_eq!(
        corners(root.shape_extent(None, shifted)?),
        Some([[-1.0, 0.0, 0.0], [11.0, 0.0, 1.0]])
    );
    let bound = BBoxCache::new(None, [Purpose::Default])
        .world_bound(root.prim())?
        .aligned_range();
    assert_eq!(
        (bound.min(), bound.max()),
        (gf::vec3d(-1.0, 5.0, 0.0), gf::vec3d(1.0, 5.0, 1.0))
    );
    Ok(())
}

#[test]
fn binding_joint_influences() -> Result<(), SchemaError> {
    let stage = memory()?;
    let binding = BindingAPI::from_prim_unchecked(stage.define_prim("/Model/Gprim")?);

    let indices = binding.create_joint_indices_primvar(false, 3)?;
    assert_eq!(indices.interpolation()?, Interpolation::Vertex);
    assert_eq!(indices.element_size()?, 3);
    let weights = binding.create_joint_weights_primvar(true, None)?;
    assert_eq!(weights.interpolation()?, Interpolation::Constant);
    // The primvars can be authored again with another interpolation or
    // element size.
    let weights = binding.create_joint_weights_primvar(false, 3)?;
    assert_eq!(weights.interpolation()?, Interpolation::Vertex);
    assert_eq!(weights.element_size()?, 3);

    binding.set_rigid_joint_influence(10, 0.5)?;
    let (indices, weights) = (binding.joint_indices_primvar(), binding.joint_weights_primvar());
    assert_eq!(indices.get_at::<Vec<i32>>(None)?, Some(vec![10]));
    assert_eq!(weights.get_at::<Vec<f32>>(None)?, Some(vec![0.5]));
    for primvar in [&indices, &weights] {
        assert_eq!(primvar.interpolation()?, Interpolation::Constant);
        assert_eq!(primvar.element_size()?, 1);
    }
    Ok(())
}

#[test]
fn rigid_influence_overflow() -> Result<(), SchemaError> {
    let stage = memory()?;
    let binding = BindingAPI::from_prim_unchecked(stage.define_prim("/Gprim")?);
    let joint = usize::try_from(i32::MAX).expect("fits") + 1;
    let error = binding.set_rigid_joint_influence(joint, 1.0).expect_err("overflows");
    assert!(matches!(error, SchemaError::JointIndexOverflow { joint: found, .. } if found == joint));
    assert!(!binding.joint_indices_attr().has_authored_value()?);
    assert!(!binding.joint_weights_attr().has_authored_value()?);
    Ok(())
}

#[test]
fn validate_indices_range() {
    assert_eq!(validate_indices(&[0, 2, 1], 3), Ok(()));
    let error = validate_indices(&[0, 3, -1], 3).expect_err("3 is out of range");
    assert_eq!(
        error,
        IndexError {
            index: 3,
            position: 1,
            len: 3
        }
    );
    assert_eq!(error.to_string(), "index 3 at element 1 is not in the range [0, 3)");
    assert_eq!(validate_indices(&[0, -1], 3).map_err(|error| error.index), Err(-1));
}

#[test]
fn animation_transforms_roundtrip() -> Result<(), SchemaError> {
    let stage = memory()?;
    let anim = Animation::define(&stage, "/Anim")?;
    let time = TimeCode::new(1.0);
    let xforms = vec![
        Mat4d::scale([2.0, 2.0, 2.0]) * Mat4d::rotation_z(FRAC_PI_4) * Mat4d::translation([1.0, 2.0, 3.0]),
        Mat4d::translation([0.0, 1.0, 0.0]),
    ];
    let near = |a: &[Mat4d], b: &[Mat4d]| {
        a.len() == b.len()
            && a.iter()
                .zip(b)
                .all(|(a, b)| (0..4).all(|r| (0..4).all(|c| (a[(r, c)] - b[(r, c)]).abs() < 1e-5)))
    };
    assert!(anim.set_transforms(&xforms, time)?);
    let read = anim.transforms(time)?.expect("components at the time");
    assert!(near(&read, &xforms), "{read:?}");

    // A singular matrix late in the array leaves every component as it was.
    let singular = [Mat4d::translation([5.0, 0.0, 0.0]), Mat4d::scale([0.0, 1.0, 1.0])];
    assert!(!anim.set_transforms(&singular, time)?);
    assert!(near(&anim.transforms(time)?.expect("components"), &xforms));
    Ok(())
}

#[test]
fn root_find_nearest() -> Result<()> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "R" {
    def Xform "X" {
        def Mesh "M" {
        }
        def SkelRoot "Inner" {
            def Mesh "M" {
            }
        }
    }
}
def Xform "Outside" {
}
"#,
    )?;
    let found = |path: &str| -> Result<Option<String>> {
        Ok(Root::find(&stage.prim(path)?)?.map(|root| root.path().as_str().to_string()))
    };
    assert_eq!(found("/R/X/M")?.as_deref(), Some("/R"));
    assert_eq!(found("/R")?.as_deref(), Some("/R"));
    assert_eq!(found("/R/X/Inner/M")?.as_deref(), Some("/R/X/Inner"));
    assert_eq!(found("/Outside")?, None);
    Ok(())
}

/// Skeletons the binding tests rebind one mesh's query to: `Skel` binds
/// `Anim`, `Swapped` lists the same joints in the other order, `Short` has
/// one joint, `Reshaped` binds an animation with the blend shapes reversed,
/// and `Twin` repeats `Skel` with an animation of its own in `Skel`'s order.
const REBIND: &str = r#"#usda 1.0
def SkelRoot "R" {
    def SkelAnimation "Anim" {
        uniform token[] blendShapes = ["a", "b"]
    }
    def SkelAnimation "Reversed" {
        uniform token[] blendShapes = ["b", "a"]
    }
    def SkelAnimation "Same" {
        uniform token[] blendShapes = ["a", "b"]
    }
    def Skeleton "Skel" (prepend apiSchemas = ["SkelBindingAPI"]) {
        uniform token[] joints = ["A", "B"]
        rel skel:animationSource = </R/Anim>
    }
    def Skeleton "Swapped" (prepend apiSchemas = ["SkelBindingAPI"]) {
        uniform token[] joints = ["B", "A"]
        rel skel:animationSource = </R/Anim>
    }
    def Skeleton "Short" {
        uniform token[] joints = ["A"]
    }
    def Skeleton "Reshaped" (prepend apiSchemas = ["SkelBindingAPI"]) {
        uniform token[] joints = ["A", "B"]
        rel skel:animationSource = </R/Reversed>
    }
    def Skeleton "Twin" (prepend apiSchemas = ["SkelBindingAPI"]) {
        uniform token[] joints = ["A", "B"]
        rel skel:animationSource = </R/Same>
    }
    def BlendShape "ShapeB" {}
    def Mesh "M" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </R/Skel>
        int[] primvars:skel:jointIndices = [1] (interpolation = "constant")
        float[] primvars:skel:jointWeights = [1] (interpolation = "constant")
        uniform token primvars:skel:skinningMethod = "dualQuaternion"
        matrix4d primvars:skel:geomBindTransform = ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) )
        uniform token[] skel:joints = ["B"]
        uniform token[] skel:blendShapes = ["b"]
        rel skel:blendShapeTargets = </R/ShapeB>
    }
}
"#;

/// The query the cache builds for `/R/M`, bound to `/R/Skel`.
fn mesh_query(stage: &Stage) -> Result<SkinningQuery, SchemaError> {
    Ok(skinning_query(stage, "/R", "/R/M")?.expect("a query"))
}

/// A binding of the skeleton at `skeleton` over `targets`.
fn bind(stage: &Stage, skeleton: &str, targets: Vec<SkinningQuery>) -> Result<Binding, SchemaError> {
    Binding::new(Skeleton::get(stage, skeleton)?.expect("Skeleton"), targets)
}

/// The error a binding of `skeleton` over the mesh's query answers.
fn foreign_error(stage: &Stage, skeleton: &str) -> Result<SchemaError, SchemaError> {
    Ok(bind(stage, skeleton, vec![mesh_query(stage)?]).expect_err("a foreign target"))
}

/// A query built by hand from the binding properties answers as the cache's.
#[test]
fn skinning_query_new() -> Result<(), SchemaError> {
    let stage = from_usda(REBIND)?;
    let prim = stage.prim("/R/M")?;
    let binding = BindingAPI::from_prim_unchecked(prim.clone());
    let properties = BindingProperties {
        joint_indices: Some(binding.joint_indices_attr()),
        joint_weights: Some(binding.joint_weights_attr()),
        skinning_method: Some(binding.skinning_method_attr()),
        geom_bind_transform: Some(binding.geom_bind_transform_attr()),
        joints: Some(binding.joints_attr()),
        blend_shapes: Some(binding.blend_shapes_attr()),
        blend_shape_targets: Some(binding.blend_shape_targets_rel()),
    };
    let skeleton = SkeletonQuery::new(&Skeleton::get(&stage, "/R/Skel")?.expect("Skeleton"))?.expect("valid");
    let shapes = skeleton.anim_query().expect("an animation").blend_shape_order();
    let built = SkinningQuery::new(prim, properties, skeleton.joint_order(), shapes)?;
    let cached = mesh_query(&stage)?;

    let path = |attribute: Option<&Attribute>| attribute.map(|attribute| attribute.path().clone());
    assert_eq!(
        path(built.joint_indices_primvar().map(Primvar::attribute)),
        path(cached.joint_indices_primvar().map(Primvar::attribute))
    );
    assert_eq!(
        path(built.joint_weights_primvar().map(Primvar::attribute)),
        path(cached.joint_weights_primvar().map(Primvar::attribute))
    );
    assert_eq!(
        path(built.geom_bind_transform_attr()),
        path(cached.geom_bind_transform_attr())
    );
    assert_eq!(path(built.skinning_method_attr()), path(cached.skinning_method_attr()));
    assert_eq!(path(built.blend_shapes_attr()), path(cached.blend_shapes_attr()));
    assert_eq!(
        built.blend_shape_targets_rel().map(|rel| rel.path().clone()),
        cached.blend_shape_targets_rel().map(|rel| rel.path().clone())
    );
    assert!(built.blend_shape_targets_rel().is_some());
    assert_eq!(built.skinning_method()?, cached.skinning_method()?);
    assert_eq!(built.has_joint_influences(), cached.has_joint_influences());
    assert_eq!(built.interpolation(), cached.interpolation());
    assert_eq!(built.influences_per_component(), cached.influences_per_component());
    assert_eq!(built.joint_order(), cached.joint_order());
    assert_eq!(built.joint_mapper(), cached.joint_mapper());
    assert_eq!(built.blend_shape_order(), cached.blend_shape_order());
    assert_eq!(built.blend_shape_mapper(), cached.blend_shape_mapper());
    assert!(built.has_blend_shapes() && cached.has_blend_shapes());
    Ok(())
}

/// A query built for one skeleton is refused for another with the same joint
/// count in another order.
#[test]
fn binding_foreign_order() -> Result<(), SchemaError> {
    let stage = from_usda(REBIND)?;
    let error = foreign_error(&stage, "/R/Swapped")?;
    assert!(
        matches!(&error, SchemaError::ForeignSkinningTarget { target, skeleton }
            if target.as_str() == "/R/M" && skeleton.as_str() == "/R/Swapped"),
        "{error:?}"
    );
    Ok(())
}

/// A query built for one skeleton is refused for one with fewer joints.
#[test]
fn binding_foreign_count() -> Result<(), SchemaError> {
    let stage = from_usda(REBIND)?;
    assert!(matches!(
        foreign_error(&stage, "/R/Short")?,
        SchemaError::ForeignSkinningTarget { .. }
    ));
    Ok(())
}

/// Identical joints bound to an animation ordering its blend shapes the
/// other way are another skeleton too.
#[test]
fn binding_foreign_shapes() -> Result<(), SchemaError> {
    let stage = from_usda(REBIND)?;
    assert!(matches!(
        foreign_error(&stage, "/R/Reshaped")?,
        SchemaError::ForeignSkinningTarget { .. }
    ));
    Ok(())
}

/// Equal orders are enough: a separately authored skeleton that matches is
/// accepted, and so is the skeleton the query was built for.
#[test]
fn binding_same_orders() -> Result<(), SchemaError> {
    let stage = from_usda(REBIND)?;
    let twin = bind(&stage, "/R/Twin", vec![mesh_query(&stage)?])?;
    assert_eq!(twin.skeleton().path().as_str(), "/R/Twin");
    assert_eq!(twin.skinning_targets().len(), 1);
    bind(&stage, "/R/Skel", vec![mesh_query(&stage)?])?;
    Ok(())
}
