//! Integration tests for baking skinning and blend shapes into plain
//! geometry (`skel::bake_skinning`, `skel::bake_roots`).

use std::{fs, slice};

use openusd::gf::{self, Vec3f};
use openusd::sdf::{self, Value};
use openusd::usd::{self, PrimPredicate, SchemaBase, Stage, TimeCode};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::{PointBasedSchema, XformCache};
use openusd_schemas::skel::{
    BakeOptions, Binding, BindingAPI, Cache, Pose, Root, SkinningQuery, bake_roots, bake_skinning,
};

mod common;
use common::{from_usda, vendor};

/// A one-joint skeleton under a SkelRoot at `/Root` translated by
/// `(10, 0, 0)`, posed by the animation `anim` describes, over a mesh at
/// `/Root/Group/Body` beneath an Xform translated by `(0, 0, 3)`. The mesh
/// authors two points, `(1, 0, 0)` and `(0, 1, 0)`, each bound wholly to the
/// joint, and whatever `mesh` adds; `group` adds prims beside it. `layer` is
/// the layer's metadata.
fn rig(layer: &str, anim: &str, mesh: &str, group: &str) -> String {
    format!(
        r#"#usda 1.0
({layer})
def SkelRoot "Root" {{
    double3 xformOp:translate = (10, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]
    def Skeleton "Skel" (prepend apiSchemas = ["SkelBindingAPI"]) {{
        uniform token[] joints = ["A"]
        uniform matrix4d[] bindTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
        uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
        rel skel:animationSource = </Root/Anim>
    }}
    def SkelAnimation "Anim" {{
        uniform token[] joints = ["A"]
        {anim}
    }}
    def Xform "Group" {{
        double3 xformOp:translate = (0, 0, 3)
        uniform token[] xformOpOrder = ["xformOp:translate"]
        def Mesh "Body" (prepend apiSchemas = ["SkelBindingAPI"]) {{
            rel skel:skeleton = </Root/Skel>
            int[] faceVertexCounts = [3]
            int[] faceVertexIndices = [0, 1, 1]
            point3f[] points = [(1, 0, 0), (0, 1, 0)]
            int[] primvars:skel:jointIndices = [0, 0] (interpolation = "vertex", elementSize = 1)
            float[] primvars:skel:jointWeights = [1, 1] (interpolation = "vertex", elementSize = 1)
            {mesh}
        }}
        {group}
    }}
}}
"#
    )
}

/// An animation that translates the joint by `(0, 5, 0)` from time 1 to 2.
const LIFT: &str = r#"float3[] translations.timeSamples = { 1: [(0, 0, 0)], 2: [(0, 5, 0)] }
        quatf[] rotations = [(1, 0, 0, 0)]
        half3[] scales = [(1, 1, 1)]"#;

/// An animation that holds the joint at rest.
const STILL: &str = r#"float3[] translations = [(0, 0, 0)]
        quatf[] rotations = [(1, 0, 0, 0)]
        half3[] scales = [(1, 1, 1)]"#;

const BODY: &str = "/Root/Group/Body";

fn root(stage: &Stage) -> Result<Root, SchemaError> {
    Ok(Root::get(stage, "/Root")?.expect("Root"))
}

/// Time samples of a vector array, each with its layer time.
type Samples = Vec<(f64, Vec<Vec3f>)>;

/// The default value and the time samples `layer` authors for the
/// `point3f[]`, `normal3f[]` or `float3[]` attribute at `path`.
fn authored(stage: &Stage, layer: &str, path: &str) -> (Option<Vec<Vec3f>>, Samples) {
    let layer = stage.layer(layer).expect("layer");
    let Some(spec) = layer.attribute(path).expect("attribute path") else {
        return (None, Vec::new());
    };
    let array = |value: Value| value.try_as_vec_3f_vec().expect("vector array");
    let samples = spec.time_samples().unwrap_or_default();
    (
        spec.default().map(array),
        samples.into_iter().map(|(time, value)| (time, array(value))).collect(),
    )
}

/// [`authored`] for the mesh's `attribute` in the root layer.
fn baked(stage: &Stage, attribute: &str) -> (Option<Vec<Vec3f>>, Samples) {
    authored(stage, &root_layer(stage), &format!("{BODY}.{attribute}"))
}

/// The times of `samples`.
fn sample_times(samples: &Samples) -> Vec<f64> {
    samples.iter().map(|(time, _)| *time).collect()
}

/// The root layer's identifier.
fn root_layer(stage: &Stage) -> String {
    stage.root_layer().identifier().to_owned()
}

/// The bindings beneath `root`, found through `predicate`.
fn bindings(root: &Root, predicate: PrimPredicate) -> Result<Vec<Binding>, SchemaError> {
    let mut cache = Cache::new();
    cache.populate(root, predicate)?;
    cache.skel_bindings(root, predicate)
}

/// [`bake_skinning`] with every binding baking into `layer`.
fn bake_into(bindings: &[Binding], layer: &str, options: &BakeOptions) -> Result<(), SchemaError> {
    let paired: Vec<_> = bindings.iter().cloned().map(|binding| (binding, layer)).collect();
    bake_skinning(&paired, options, ..)
}

/// A stage opened from `root`, one of `files` written into a directory kept
/// alive beside it.
fn open_files(files: &[(&str, &str)], root: &str) -> Result<(tempfile::TempDir, Stage), SchemaError> {
    let dir = tempfile::tempdir().map_err(openusd::Error::from)?;
    for (name, usda) in files {
        fs::write(dir.path().join(name), usda).map_err(openusd::Error::from)?;
    }
    let stage = Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(dir.path().join(root).to_str().expect("utf-8"))?;
    Ok((dir, stage))
}

fn near(found: &[Vec3f], expected: &[[f32; 3]]) -> bool {
    found.len() == expected.len()
        && found
            .iter()
            .zip(expected)
            .all(|(found, &expected)| (*found - Vec3f::from(expected)).length() < 1e-5)
}

#[test]
fn bake_points_spaces() -> Result<(), SchemaError> {
    let stage = from_usda(&rig("", LIFT, "", ""))?;
    bake_roots(&[root(&stage)?], ..)?;
    let (default, samples) = baked(&stage, "points");
    // The rest points stay as the default; a skeleton with samples bakes
    // none at the default time.
    assert_eq!(default, Some(vec![gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 1.0, 0.0)]));
    // Skinned in skeleton space, then carried by the skeleton's world
    // transform and back out of the mesh's: a translation of (0, 0, -3).
    let times = sample_times(&samples);
    assert_eq!(times, [1.0, 2.0]);
    assert!(
        near(&samples[0].1, &[[1.0, 0.0, -3.0], [0.0, 1.0, -3.0]]),
        "{samples:?}"
    );
    assert!(
        near(&samples[1].1, &[[1.0, 5.0, -3.0], [0.0, 6.0, -3.0]]),
        "{samples:?}"
    );
    // The bake is what the composed stage reads.
    let points: Option<Vec<Vec3f>> = stage.attribute(format!("{BODY}.points"))?.get_at(TimeCode::new(2.0))?;
    assert!(near(&points.expect("baked"), &[[1.0, 5.0, -3.0], [0.0, 6.0, -3.0]]));
    Ok(())
}

#[test]
fn bake_static_rig() -> Result<(), SchemaError> {
    let lifted = STILL.replace("translations = [(0, 0, 0)]", "translations = [(0, 5, 0)]");
    let stage = from_usda(&rig("", &lifted, "", ""))?;
    bake_roots(&[root(&stage)?], ..)?;
    let (default, samples) = baked(&stage, "points");
    assert!(samples.is_empty(), "{samples:?}");
    assert!(near(
        &default.expect("baked default"),
        &[[1.0, 5.0, -3.0], [0.0, 6.0, -3.0]]
    ));
    Ok(())
}

#[test]
fn bake_playback_frames() -> Result<(), SchemaError> {
    let sparse = r#"float3[] translations.timeSamples = { 1: [(0, 0, 0)], 10: [(0, 9, 0)] }
        quatf[] rotations = [(1, 0, 0, 0)]
        half3[] scales = [(1, 1, 1)]"#;
    let layer = "startTimeCode = 1 endTimeCode = 10 timeCodesPerSecond = 24 framesPerSecond = 24";
    let stage = from_usda(&rig(layer, sparse, "", ""))?;
    bake_roots(&[root(&stage)?], ..)?;
    let (_, samples) = baked(&stage, "points");
    let times = sample_times(&samples);
    assert_eq!(times, (1..=10).map(f64::from).collect::<Vec<_>>());
    // Each frame is skinned, not interpolated between the samples.
    assert!(
        near(&samples[4].1, &[[1.0, 4.0, -3.0], [0.0, 5.0, -3.0]]),
        "{:?}",
        samples[4]
    );
    Ok(())
}

/// A joint turned 90 degrees about Z at time 1.
const TURN: &str = r#"float3[] translations = [(0, 0, 0)]
        quatf[] rotations.timeSamples = { 1: [(0.70710677, 0, 0, 0.70710677)] }
        half3[] scales = [(1, 1, 1)]"#;

#[test]
fn bake_normals() -> Result<(), SchemaError> {
    let vertex = r#"normal3f[] normals = [(1, 0, 0), (0, 0, 1)] (interpolation = "vertex")"#;
    let face_varying = r#"normal3f[] normals = [(1, 0, 0), (0, 0, 1), (1, 0, 0)] (interpolation = "faceVarying")"#;
    for (mesh, expected) in [
        (vertex, vec![[0.0, 1.0, 0.0], [0.0, 0.0, 1.0]]),
        (face_varying, vec![[0.0, 1.0, 0.0], [0.0, 0.0, 1.0], [0.0, 1.0, 0.0]]),
    ] {
        let stage = from_usda(&rig("", TURN, mesh, ""))?;
        bake_roots(&[root(&stage)?], ..)?;
        let (_, samples) = baked(&stage, "normals");
        assert_eq!(samples.len(), 1, "{mesh}");
        assert!(near(&samples[0].1, &expected), "{mesh}: {samples:?}");
        let (_, points) = baked(&stage, "points");
        assert!(near(&points[0].1, &[[0.0, 1.0, -3.0], [-1.0, 0.0, -3.0]]), "{points:?}");
    }
    Ok(())
}

#[test]
fn bake_blend_shapes_then_skinning() -> Result<(), SchemaError> {
    let usda = rig(
        "",
        &format!("{LIFT}\n        uniform token[] blendShapes = [\"Up\"]\n        float[] blendShapeWeights = [0.5]"),
        r#"uniform token[] skel:blendShapes = ["Up"]
            rel skel:blendShapeTargets = </Root/Group/Body/Up>
            def BlendShape "Up" {
                uniform vector3f[] offsets = [(0, 0, 2)]
                uniform int[] pointIndices = [0]
            }"#,
        "",
    );
    let stage = from_usda(&usda)?;
    bake_roots(&[root(&stage)?], ..)?;
    let (_, samples) = baked(&stage, "points");
    // Half the offset on point 0, then the joint's lift, then into the
    // mesh's space.
    assert!(
        near(&samples[1].1, &[[1.0, 5.0, -2.0], [0.0, 6.0, -3.0]]),
        "{samples:?}"
    );
    Ok(())
}

#[test]
fn bake_dual_quaternion() -> Result<(), SchemaError> {
    let mesh = r#"uniform token primvars:skel:skinningMethod = "dualQuaternion""#;
    let stage = from_usda(&rig("", LIFT, mesh, ""))?;
    bake_roots(&[root(&stage)?], ..)?;
    let (_, samples) = baked(&stage, "points");
    assert!(
        near(&samples[1].1, &[[1.0, 5.0, -3.0], [0.0, 6.0, -3.0]]),
        "{samples:?}"
    );
    Ok(())
}

/// An animated ancestor of the mesh adds its sample times, though the
/// skeleton itself is still: C++ reads the mesh's own transform in its
/// place and bakes at the default time alone.
#[test]
fn bake_animated_ancestor() -> Result<(), SchemaError> {
    let usda = rig("", STILL, "", "").replace(
        "double3 xformOp:translate = (0, 0, 3)",
        "double3 xformOp:translate.timeSamples = { 1: (0, 0, 3), 4: (0, 0, 7) }",
    );
    let stage = from_usda(&usda)?;
    bake_roots(&[root(&stage)?], ..)?;
    let (_, samples) = baked(&stage, "points");
    let times = sample_times(&samples);
    assert_eq!(times, [1.0, 4.0]);
    assert!(
        near(&samples[1].1, &[[1.0, 0.0, -7.0], [0.0, 1.0, -7.0]]),
        "{samples:?}"
    );
    Ok(())
}

#[test]
fn bake_root_becomes_xform() -> Result<(), SchemaError> {
    let stage = from_usda(&rig("", LIFT, "", ""))?;
    bake_roots(&[root(&stage)?], ..)?;
    let layer = stage.root_layer();
    let spec = layer.prim("/Root")?.expect("root spec");
    assert_eq!(spec.type_name().as_deref(), Some("Xform"));
    assert_eq!(spec.specifier(), Some(sdf::Specifier::Def));
    drop(layer);
    assert!(Root::get(&stage, "/Root")?.is_none());
    // The binding and the skeleton stay.
    let body = BindingAPI::get(&stage, BODY)?.expect("binding stays applied");
    assert_eq!(
        body.skeleton()?.map(|skel| skel.path().clone()),
        Some(sdf::path("/Root/Skel")?)
    );
    assert!(body.joint_indices_attr().has_authored_value()?);
    assert_eq!(stage.prim("/Root/Skel")?.type_name()?.as_deref(), Some("Skeleton"));
    Ok(())
}

#[test]
fn bake_nested_roots() -> Result<(), SchemaError> {
    let inner = r#"def SkelRoot "Inner" {
            def Mesh "Arm" (prepend apiSchemas = ["SkelBindingAPI"]) {
                rel skel:skeleton = </Root/Skel>
                point3f[] points = [(1, 0, 0)]
                int[] primvars:skel:jointIndices = [0] (interpolation = "vertex", elementSize = 1)
                float[] primvars:skel:jointWeights = [1] (interpolation = "vertex", elementSize = 1)
            }
        }"#;
    let stage = from_usda(&rig("", LIFT, "", inner))?;
    let bindings = bindings(&root(&stage)?, PrimPredicate::DEFAULT)?;
    // Both meshes share the skeleton, so one binding reaches both roots.
    assert_eq!(bindings.len(), 1);
    assert_eq!(bindings[0].skinning_targets().len(), 2);
    bake_into(&bindings, &root_layer(&stage), &BakeOptions::default())?;
    for path in ["/Root", "/Root/Group/Inner"] {
        assert_eq!(stage.prim(path)?.type_name()?.as_deref(), Some("Xform"), "{path}");
    }
    Ok(())
}

#[test]
fn bake_update_extents() -> Result<(), SchemaError> {
    let extent = r#"float3[] extent = [(0, 0, 0), (1, 1, 0)]
            float3[] extent.timeSamples = { 7: [(0, 0, 0), (2, 2, 0)] }"#;
    let off = BakeOptions {
        update_extents: false,
        ..BakeOptions::default()
    };
    for (options, baked) in [(off, false), (BakeOptions::default(), true)] {
        let stage = from_usda(&rig("", LIFT, extent, ""))?;
        let layer = root_layer(&stage);
        bake_into(&bindings(&root(&stage)?, PrimPredicate::DEFAULT)?, &layer, &options)?;
        let (default, samples) = authored(&stage, &layer, &format!("{BODY}.extent"));
        assert_eq!(default, Some(vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 1.0, 0.0)]));
        let times = sample_times(&samples);
        if baked {
            assert_eq!(times, [1.0, 2.0]);
            assert!(
                near(&samples[1].1, &[[0.0, 5.0, -3.0], [1.0, 6.0, -3.0]]),
                "{samples:?}"
            );
        } else {
            assert_eq!(times, [7.0]);
        }
    }
    Ok(())
}

/// Linear curves at `/Root/Group/Hair` beside the mesh, with its points and
/// influences, two units wide, and a stale authored extent.
const HAIR: &str = r#"def BasisCurves "Hair" (prepend apiSchemas = ["SkelBindingAPI"]) {
            rel skel:skeleton = </Root/Skel>
            uniform token type = "linear"
            int[] curveVertexCounts = [2]
            point3f[] points = [(1, 0, 0), (0, 1, 0)]
            float[] widths = [2, 2] (interpolation = "vertex")
            float3[] extent = [(0, 0, 0), (0.5, 0.5, 0)]
            int[] primvars:skel:jointIndices = [0, 0] (interpolation = "vertex", elementSize = 1)
            float[] primvars:skel:jointWeights = [1, 1] (interpolation = "vertex", elementSize = 1)
        }"#;

/// The curves' extent at time 2, the baked points widened by one unit.
const HAIR_EXTENT: [[f32; 3]; 2] = [[-1.0, 4.0, -4.0], [2.0, 7.0, -2.0]];

#[test]
fn bake_curves_extent() -> Result<(), SchemaError> {
    let off = BakeOptions {
        update_extents: false,
        ..BakeOptions::default()
    };
    for (options, baked) in [(off, false), (BakeOptions::default(), true)] {
        let stage = from_usda(&rig("", LIFT, "", HAIR))?;
        let layer = root_layer(&stage);
        bake_into(&bindings(&root(&stage)?, PrimPredicate::DEFAULT)?, &layer, &options)?;
        let (default, samples) = authored(&stage, &layer, "/Root/Group/Hair.extent");
        assert_eq!(default, Some(vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(0.5, 0.5, 0.0)]));
        if baked {
            assert_eq!(sample_times(&samples), [1.0, 2.0]);
            assert!(near(&samples[1].1, &HAIR_EXTENT), "{samples:?}");
        } else {
            assert!(samples.is_empty());
        }
    }
    Ok(())
}

/// `usda` with the SkelRoot of [`rig`] made a model of `kind`, its Group a
/// component, and each holding a stale `extentsHint`.
fn hinted(usda: &str, kind: &str) -> String {
    let hint = "float3[] extentsHint = [(0, 0, 0), (0.1, 0.1, 0.1)]";
    usda.replace(
        "def SkelRoot \"Root\" {",
        &format!("def SkelRoot \"Root\" (kind = \"{kind}\") {{\n    {hint}"),
    )
    .replace(
        "def Xform \"Group\" {",
        &format!("def Xform \"Group\" (kind = \"component\") {{\n        {hint}"),
    )
}

#[test]
fn bake_extent_hints() -> Result<(), SchemaError> {
    let stage = from_usda(&hinted(&rig("", LIFT, "", HAIR), "assembly"))?;
    let layer = root_layer(&stage);
    bake_into(
        &bindings(&root(&stage)?, PrimPredicate::DEFAULT)?,
        &layer,
        &BakeOptions::default(),
    )?;
    // Each model's hint is its own, and bounds the curves' new extent, not
    // the stale one: the Group's in its own space, the root's with the
    // Group's translation.
    let [low, high] = HAIR_EXTENT;
    for (model, lift) in [("/Root/Group", 0.0), ("/Root", 3.0)] {
        let (default, samples) = authored(&stage, &layer, &format!("{model}.extentsHint"));
        assert_eq!(default, None, "{model}");
        assert_eq!(sample_times(&samples), [1.0, 2.0], "{model}");
        let lifted = |[x, y, z]: [f32; 3]| [x, y, z + lift];
        assert!(
            near(&samples[1].1, &[lifted(low), lifted(high)]),
            "{model}: {samples:?}"
        );
    }

    // With the hints off they stay as they were.
    let stage = from_usda(&hinted(&rig("", LIFT, "", HAIR), "assembly"))?;
    let options = BakeOptions {
        update_extent_hints: false,
        ..BakeOptions::default()
    };
    let layer = root_layer(&stage);
    bake_into(&bindings(&root(&stage)?, PrimPredicate::DEFAULT)?, &layer, &options)?;
    let (default, samples) = authored(&stage, &layer, "/Root.extentsHint");
    assert!(default.is_some() && samples.is_empty());
    Ok(())
}

#[test]
fn bake_hint_edit_target() -> Result<(), SchemaError> {
    // A hint goes through the edit target's namespace mapping.
    let variant = hinted(&rig("", LIFT, "", ""), "component").replace(
        "def SkelRoot \"Root\" (kind = \"component\") {",
        r#"def SkelRoot "Root" (kind = "component" variants = { string look = "a" } prepend variantSets = "look") {
    variantSet "look" = { "a" { } }"#,
    );
    let stage = from_usda(&variant)?;
    let layer = root_layer(&stage);
    stage.set_edit_target(usd::EditTarget::for_local_direct_variant(&layer, "/Root{look=a}")?)?;
    bake_into(
        &bindings(&root(&stage)?, PrimPredicate::DEFAULT)?,
        &layer,
        &BakeOptions::default(),
    )?;
    let (_, samples) = authored(&stage, &layer, "/Root{look=a}.extentsHint");
    assert_eq!(sample_times(&samples), [1.0, 2.0]);
    let (default, samples) = authored(&stage, &layer, "/Root.extentsHint");
    assert!(default.is_some() && samples.is_empty());

    // And through its time offset, as the geometry does.
    let rig = hinted(&rig("", LIFT, "", ""), "component");
    let (_dir, stage) = open_files(
        &[
            ("rig.usda", &rig),
            ("shot.usda", "#usda 1.0\n(subLayers = [@./rig.usda@])\n"),
        ],
        "shot.usda",
    )?;
    let bake = sdf::Layer::new_anonymous("bake");
    let bake_id = bake.identifier().to_owned();
    stage.insert_layer(&root_layer(&stage), 0, bake, sdf::LayerOffset::new(10.0, 2.0))?;
    stage.set_edit_target(stage.edit_target_for_local_layer(&bake_id).expect("local"))?;
    bake_roots(&[root(&stage)?], ..)?;
    let (_, samples) = authored(&stage, &bake_id, "/Root.extentsHint");
    assert_eq!(sample_times(&samples), [-4.5, -4.0]);
    Ok(())
}

#[test]
fn bake_hint_failure() -> Result<(), SchemaError> {
    let usda = rig("", LIFT, "", "").replace(
        "def SkelRoot \"Root\" {",
        "def SkelRoot \"Root\" (kind = \"component\") {\n    double extentsHint = 1",
    );
    let stage = from_usda(&usda)?;
    let layer = root_layer(&stage);
    let error = bake_into(
        &bindings(&root(&stage)?, PrimPredicate::DEFAULT)?,
        &layer,
        &BakeOptions::default(),
    )
    .expect_err("a `double` hint takes no extents");
    assert!(matches!(error, SchemaError::BakeExtentHints(_)), "{error:?}");
    // The geometry committed, and the hint is as it was.
    assert_eq!(sample_times(&baked(&stage, "points").1), [1.0, 2.0]);
    assert_eq!(stage.attribute("/Root.extentsHint")?.get::<f64>()?, Some(1.0));
    Ok(())
}

#[test]
fn bake_spec_type_mismatch() -> Result<(), SchemaError> {
    let usda = rig("", LIFT, "", "").replace("point3f[] points", "float3[] points");
    let stage = from_usda(&usda)?;
    let error = bake_roots(&[root(&stage)?], ..).expect_err("mistyped points");
    assert!(
        matches!(&error, SchemaError::BakeSpecType { attribute, .. } if attribute.as_str() == "/Root/Group/Body.points"),
        "{error}"
    );
    assert!(Root::get(&stage, "/Root")?.is_some(), "nothing is written");
    Ok(())
}

#[test]
fn bake_instanced_rejected() -> Result<(), SchemaError> {
    let stage = from_usda(
        r#"#usda 1.0
def SkelRoot "Asset" {
    def Skeleton "Skel" {
        uniform token[] joints = ["A"]
        uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
    }
    def Mesh "Body" (prepend apiSchemas = ["SkelBindingAPI"]) {
        rel skel:skeleton = </Asset/Skel>
        point3f[] points = [(1, 0, 0)]
        int[] primvars:skel:jointIndices = [0] (interpolation = "vertex", elementSize = 1)
        float[] primvars:skel:jointWeights = [1] (interpolation = "vertex", elementSize = 1)
    }
}
def SkelRoot "Instance" (instanceable = true references = </Asset>) {
}
"#,
    )?;
    let instance = Root::get(&stage, "/Instance")?.expect("Root");
    let error = bake_roots(slice::from_ref(&instance), ..).expect_err("instanced root");
    assert!(
        matches!(&error, SchemaError::BakeInstanced { prim } if prim.as_str() == "/Instance"),
        "{error}"
    );

    // A binding found through instance proxies reaches a proxy target.
    let bindings = bindings(&instance, PrimPredicate::DEFAULT_PROXIES)?;
    assert!(!bindings.is_empty());
    let layer = root_layer(&stage);
    let error = bake_into(&bindings, &layer, &BakeOptions::default()).expect_err("proxy target");
    assert!(matches!(error, SchemaError::BakeInstanced { .. }), "{error}");
    let (_, samples) = authored(&stage, &layer, "/Asset/Body.points");
    assert!(samples.is_empty());
    Ok(())
}

#[test]
fn bake_layer_offset() -> Result<(), SchemaError> {
    // The rig sits in a sublayer, so a bake layer inserted ahead of it is
    // the stronger.
    let rig = rig("", LIFT, "", "");
    let (_dir, stage) = open_files(
        &[
            ("rig.usda", &rig),
            (
                "shot.usda",
                "#usda 1.0
(subLayers = [@./rig.usda@])
",
            ),
        ],
        "shot.usda",
    )?;
    let bake = sdf::Layer::new_anonymous("bake");
    let bake_id = bake.identifier().to_owned();
    stage.insert_layer(&root_layer(&stage), 0, bake, sdf::LayerOffset::new(10.0, 2.0))?;
    stage.set_edit_target(stage.edit_target_for_local_layer(&bake_id).expect("local"))?;
    bake_roots(&[root(&stage)?], ..)?;
    // The animation's samples at stage times 1 and 2 are keyed at the layer
    // times that compose to them: (t - 10) / 2.
    let (_, samples) = authored(&stage, &bake_id, &format!("{BODY}.points"));
    let times = sample_times(&samples);
    assert_eq!(times, [-4.5, -4.0]);
    let points: Option<Vec<Vec3f>> = stage.attribute(format!("{BODY}.points"))?.get_at(TimeCode::new(2.0))?;
    assert!(near(&points.expect("baked"), &[[1.0, 5.0, -3.0], [0.0, 6.0, -3.0]]));
    Ok(())
}

#[test]
fn bake_layer_outside_stack() -> Result<(), SchemaError> {
    let asset = rig("", LIFT, "", "");
    let shot = r#"#usda 1.0
def "Shot" (references = @./asset.usda@</Root>) {
}
"#;
    let (_dir, stage) = open_files(&[("asset.usda", &asset), ("shot.usda", shot)], "shot.usda")?;
    let shot = Root::get(&stage, "/Shot")?.expect("the reference brings the SkelRoot");
    let bindings = bindings(&shot, PrimPredicate::DEFAULT)?;
    assert_eq!(bindings.len(), 1);

    // The asset reaches the stage through a reference, outside its root
    // layer stack.
    let referenced = stage
        .layer_identifiers()
        .into_iter()
        .find(|id| id.ends_with("asset.usda"))
        .expect("the reference loads");
    for layer in [referenced.as_str(), "elsewhere.usda"] {
        let error = bake_into(&bindings, layer, &BakeOptions::default()).expect_err("outside the root stack");
        assert!(
            matches!(&error, SchemaError::BakeLayer { layer: found } if found == layer),
            "{error}"
        );
    }
    assert!(Root::get(&stage, "/Shot")?.is_some(), "nothing is written");
    Ok(())
}

#[test]
fn bake_two_stages() -> Result<(), SchemaError> {
    let first = from_usda(&rig("", LIFT, "", ""))?;
    let second = from_usda(&rig("", LIFT, "", ""))?;
    let error = bake_roots(&[root(&first)?, root(&second)?], ..).expect_err("two stages");
    assert!(matches!(error, SchemaError::BakeStages { .. }), "{error}");
    assert!(Root::get(&first, "/Root")?.is_some(), "nothing is written");
    Ok(())
}

#[test]
fn bake_shared_layer() -> Result<(), SchemaError> {
    let usda = rig("", LIFT, "", "");
    let second = usda
        .split_once("def SkelRoot \"Root\"")
        .map(|(_, rest)| format!("def SkelRoot \"Other\"{}", rest.replace("/Root/", "/Other/")))
        .expect("one root");
    let stage = from_usda(&format!("{usda}{second}"))?;
    let other = Root::get(&stage, "/Other")?.expect("Root");
    bake_roots(&[root(&stage)?, other], ..)?;
    for body in [BODY, "/Other/Group/Body"] {
        let (_, samples) = authored(&stage, &root_layer(&stage), &format!("{body}.points"));
        assert_eq!(samples.len(), 2, "{body}");
    }
    Ok(())
}

#[test]
fn bake_biplane() -> Result<(), SchemaError> {
    let stage =
        vendor("core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary/toy_biplane_idle.usdc")?;
    let roots: Vec<Root> = {
        let mut paths = Vec::new();
        stage.traverse(PrimPredicate::DEFAULT, |path| paths.push(path.clone()))?;
        paths
            .into_iter()
            .filter_map(|path| Root::get(&stage, path).transpose())
            .collect::<openusd::Result<_>>()?
    };
    // What the queries skin at one frame, carried into each mesh's space,
    // before the bake turns the roots into Xforms.
    let time = TimeCode::new(10.0);
    let mut expected = Vec::new();
    let mut xforms = XformCache::new(time);
    for root in &roots {
        let mut cache = Cache::new();
        cache.populate(root, PrimPredicate::DEFAULT)?;
        for binding in cache.skel_bindings(root, PrimPredicate::DEFAULT)? {
            let skel = cache.skel_query(binding.skeleton())?.expect("valid skeleton");
            let pose = skel.skinning_transforms(time)?.expect("posed").into();
            let to_prim = xforms.local_to_world_transform(binding.skeleton().prim())?;
            for query in binding.skinning_targets() {
                expected.push((
                    query.prim().path().clone(),
                    skinned(query, &pose, time, to_prim, &mut xforms)?,
                ));
            }
        }
    }
    assert_eq!(expected.len(), 15);
    bake_roots(&roots, ..)?;
    for (path, expected) in expected {
        let mesh = openusd_schemas::geom::Mesh::get(&stage, path.clone())?.expect("Mesh");
        let baked = mesh.points_attr().get_at::<Vec<Vec3f>>(time)?.expect("baked points");
        assert_eq!(baked.len(), expected.len(), "{path}");
        let worst = baked
            .iter()
            .zip(&expected)
            .map(|(baked, expected)| (*baked - *expected).length())
            .fold(0.0, f32::max);
        assert!(worst < 1e-3, "{path}: {worst}");
    }
    Ok(())
}

/// `query`'s prim skinned through `pose` at `time`, in its own space, the
/// skeleton's world transform being `skel_world`.
fn skinned(
    query: &SkinningQuery,
    pose: &Pose,
    time: TimeCode,
    skel_world: gf::Mat4d,
    xforms: &mut XformCache,
) -> Result<Vec<Vec3f>, SchemaError> {
    let rest: Vec<Vec3f> = query.prim().attribute("points").get_at(time)?.expect("rest points");
    let skinned = query.skinned_points(pose, &rest, time)?.expect("skinned");
    let to_prim = skel_world * xforms.local_to_world_transform(query.prim())?.inverse_or_max();
    Ok(skinned
        .into_iter()
        .map(|point| to_prim.transform(point.into()).to_f32())
        .collect())
}

/// A prim bound rigidly to the rig's joint: one constant influence, through
/// `skel:joints` where `joints` authors them.
fn rigid(kind: &str, name: &str, joints: &str, index: u32, body: &str) -> String {
    format!(
        r#"def {kind} "{name}" (prepend apiSchemas = ["SkelBindingAPI"]) {{
            rel skel:skeleton = </Root/Skel>
            {joints}
            int[] primvars:skel:jointIndices = [{index}] (interpolation = "constant", elementSize = 1)
            float[] primvars:skel:jointWeights = [1] (interpolation = "constant", elementSize = 1)
            {body}
        }}"#
    )
}

/// The transform and the op order `prim` bakes in the root layer.
fn baked_xform(stage: &Stage, prim: &str) -> (Vec<(f64, gf::Mat4d)>, Option<Vec<String>>) {
    let layer = stage.root_layer();
    let samples = layer
        .attribute(format!("{prim}.xformOp:transform"))
        .expect("attribute path")
        .and_then(|spec| spec.time_samples())
        .unwrap_or_default();
    let order = layer
        .attribute(format!("{prim}.xformOpOrder"))
        .expect("attribute path")
        .and_then(|spec| spec.default())
        .map(|order| {
            let order = order.try_as_token_vec().expect("token array");
            order.iter().map(|token| token.as_str().to_owned()).collect()
        });
    (
        samples
            .into_iter()
            .map(|(time, xform)| (time, xform.try_as_matrix_4d().expect("matrix")))
            .collect(),
        order,
    )
}

#[test]
fn bake_rigid_transform() -> Result<(), SchemaError> {
    let group = [
        rigid("Sphere", "Ball", "", 0, ""),
        // `skel:joints` maps the one influence onto the skeleton's joint.
        rigid(
            "Cube",
            "Box",
            r#"uniform token[] skel:joints = ["Missing", "A"]"#,
            1,
            "",
        ),
        rigid(
            "Cube",
            "Loose",
            "",
            0,
            r#"uniform token[] xformOpOrder = ["!resetXformStack!"]"#,
        ),
    ]
    .join("\n        ");
    let stage = from_usda(&rig("", LIFT, "", &group))?;
    bake_roots(&[root(&stage)?], ..)?;
    // Skinned in skeleton space, carried by the skeleton's world transform,
    // then into the parent's space: the Group's translation comes back out.
    for prim in ["/Root/Group/Ball", "/Root/Group/Box"] {
        let (samples, order) = baked_xform(&stage, prim);
        assert_eq!(order.as_deref(), Some(&["xformOp:transform".to_owned()][..]), "{prim}");
        assert_eq!(
            samples,
            [
                (1.0, gf::Mat4d::translation([0.0, 0.0, -3.0])),
                (2.0, gf::Mat4d::translation([0.0, 5.0, -3.0]))
            ],
            "{prim}"
        );
    }
    // A prim that resets the stack keeps the reset, and its transform is in
    // world space.
    let (samples, order) = baked_xform(&stage, "/Root/Group/Loose");
    assert_eq!(
        order,
        Some(vec!["!resetXformStack!".to_owned(), "xformOp:transform".to_owned()])
    );
    assert_eq!(samples[1], (2.0, gf::Mat4d::translation([10.0, 5.0, 0.0])));
    let mut xforms = XformCache::new(TimeCode::new(2.0));
    assert_eq!(
        xforms.local_to_world_transform(&stage.prim("/Root/Group/Loose")?)?,
        gf::Mat4d::translation([10.0, 5.0, 0.0])
    );
    Ok(())
}

/// A rigidly bound mesh with blend shapes bakes both its transform and its
/// blend-shaped, unskinned points.
#[test]
fn bake_rigid_blend_shapes() -> Result<(), SchemaError> {
    let prop = rigid(
        "Mesh",
        "Prop",
        "",
        0,
        r#"point3f[] points = [(1, 0, 0), (0, 1, 0)]
            uniform token[] skel:blendShapes = ["Up"]
            rel skel:blendShapeTargets = </Root/Group/Prop/Up>
            def BlendShape "Up" {
                uniform vector3f[] offsets = [(0, 0, 2)]
                uniform int[] pointIndices = [0]
            }"#,
    );
    let anim =
        format!("{LIFT}\n        uniform token[] blendShapes = [\"Up\"]\n        float[] blendShapeWeights = [0.5]");
    let stage = from_usda(&rig("", &anim, "", &prop))?;
    bake_roots(&[root(&stage)?], ..)?;
    let (xforms, _) = baked_xform(&stage, "/Root/Group/Prop");
    assert_eq!(xforms[1], (2.0, gf::Mat4d::translation([0.0, 5.0, -3.0])));
    let (_, points) = authored(&stage, &root_layer(&stage), "/Root/Group/Prop.points");
    assert!(near(&points[1].1, &[[1.0, 0.0, 1.0], [0.0, 1.0, 0.0]]), "{points:?}");
    Ok(())
}

/// An interval between two keys of the animation bakes the poses within it:
/// at the playback frames there, or at its bounds where the stage has none.
#[test]
fn bake_between_keys() -> Result<(), SchemaError> {
    let sparse = r#"float3[] translations.timeSamples = { 1: [(0, 0, 0)], 10: [(0, 9, 0)] }
        quatf[] rotations = [(1, 0, 0, 0)]
        half3[] scales = [(1, 1, 1)]"#;
    let playback = "startTimeCode = 1 endTimeCode = 10 timeCodesPerSecond = 24 framesPerSecond = 24";
    for (layer, expected) in [(playback, vec![4.0, 5.0, 6.0]), ("", vec![4.0, 6.0])] {
        let stage = from_usda(&rig(layer, sparse, "", ""))?;
        bake_roots(&[root(&stage)?], 4.0..=6.0)?;
        let (_, samples) = baked(&stage, "points");
        assert_eq!(sample_times(&samples), expected, "{layer}");
        assert!(
            near(&samples[0].1, &[[1.0, 3.0, -3.0], [0.0, 4.0, -3.0]]),
            "{samples:?}"
        );
    }
    Ok(())
}

/// A frame count a hair under a whole number keeps the last playback frame.
#[test]
fn bake_playback_rounding() -> Result<(), SchemaError> {
    let sparse = r#"float3[] translations.timeSamples = { 0: [(0, 0, 0)], 1: [(0, 1, 0)] }
        quatf[] rotations = [(1, 0, 0, 0)]
        half3[] scales = [(1, 1, 1)]"#;
    // A step of 0.1 from 0 reaches 0.3 in what floating point counts as
    // 2.9999999999999996 steps.
    let layer = "startTimeCode = 0 endTimeCode = 0.3 timeCodesPerSecond = 10 framesPerSecond = 100";
    let stage = from_usda(&rig(layer, sparse, "", ""))?;
    bake_roots(&[root(&stage)?], ..)?;
    let (_, samples) = baked(&stage, "points");
    assert_eq!(sample_times(&samples).len(), 5, "0, 0.1, 0.2, 0.3 and the key at 1");
    Ok(())
}

/// A second skeleton at `/Root/Group/Skel2`, posed by the rig's animation,
/// skinning a mesh at `/Root/Group/Arm`.
const SECOND: &str = r#"def Skeleton "Skel2" (prepend apiSchemas = ["SkelBindingAPI"]) {
            uniform token[] joints = ["A"]
            uniform matrix4d[] bindTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
            uniform matrix4d[] restTransforms = [((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))]
            rel skel:animationSource = </Root/Anim>
        }
        def Mesh "Arm" (prepend apiSchemas = ["SkelBindingAPI"]) {
            rel skel:skeleton = </Root/Group/Skel2>
            point3f[] points = [(1, 0, 0)]
            int[] primvars:skel:jointIndices = [0] (interpolation = "vertex", elementSize = 1)
            float[] primvars:skel:jointWeights = [1] (interpolation = "vertex", elementSize = 1)
        }"#;

/// The stage of `shot.usda`, which sublayers `a.usda` with an offset of 10
/// and a scale of 2, then `b.usda` with an offset of 5, then the rig of
/// `rig`, with the identifiers of the first two.
fn shot(rig: &str) -> Result<(tempfile::TempDir, Stage, String, String), SchemaError> {
    let empty = "#usda 1.0\n";
    let shot = r#"#usda 1.0
(subLayers = [@./a.usda@ (offset = 10; scale = 2), @./b.usda@ (offset = 5), @./rig.usda@])
"#;
    let (dir, stage) = open_files(
        &[
            ("rig.usda", rig),
            ("a.usda", empty),
            ("b.usda", empty),
            ("shot.usda", shot),
        ],
        "shot.usda",
    )?;
    let layers = stage.sub_layers(&root_layer(&stage));
    Ok((dir, stage, layers[1].clone(), layers[2].clone()))
}

/// The stage of `shot.usda` in `dir`, opened afresh from disk.
fn reopen(dir: &tempfile::TempDir) -> Result<Stage, SchemaError> {
    Ok(Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(dir.path().join("shot.usda").to_str().expect("utf-8"))?)
}

#[test]
fn bake_two_layers() -> Result<(), SchemaError> {
    let (dir, stage, a, b) = shot(&rig("", LIFT, "", SECOND))?;
    let bindings = bindings(&root(&stage)?, PrimPredicate::DEFAULT)?;
    assert_eq!(bindings.len(), 2);
    let paired: Vec<_> = bindings
        .into_iter()
        .map(|binding| {
            let layer = match binding.skeleton().path().as_str() {
                "/Root/Skel" => a.as_str(),
                _ => b.as_str(),
            };
            (binding, layer)
        })
        .collect();
    bake_skinning(&paired, &BakeOptions::default(), ..)?;

    // Each layer holds its own binding's outputs, keyed through its own
    // offset: (t - 10) / 2 and t - 5.
    let arm = "/Root/Group/Arm.points";
    assert_eq!(
        sample_times(&authored(&stage, &a, &format!("{BODY}.points")).1),
        [-4.5, -4.0]
    );
    assert!(authored(&stage, &a, arm).1.is_empty());
    assert_eq!(sample_times(&authored(&stage, &b, arm).1), [-4.0, -3.0]);
    assert!(authored(&stage, &b, &format!("{BODY}.points")).1.is_empty());

    // Both layers were saved.
    let stage = reopen(&dir)?;
    let points: Option<Vec<Vec3f>> = stage.attribute(arm)?.get_at(TimeCode::new(2.0))?;
    assert!(near(&points.expect("baked"), &[[1.0, 5.0, 0.0]]));
    let points: Option<Vec<Vec3f>> = stage.attribute(format!("{BODY}.points"))?.get_at(TimeCode::new(2.0))?;
    assert!(near(&points.expect("baked"), &[[1.0, 5.0, -3.0], [0.0, 6.0, -3.0]]));
    Ok(())
}

#[test]
fn bake_roots_unsaved() -> Result<(), SchemaError> {
    let (dir, stage, a, _) = shot(&rig("", LIFT, "", ""))?;
    stage.set_edit_target(stage.edit_target_for_local_layer(&a).expect("local"))?;
    bake_roots(&[root(&stage)?], ..)?;
    assert!(!authored(&stage, &a, &format!("{BODY}.points")).1.is_empty());
    let stage = reopen(&dir)?;
    assert!(
        stage
            .attribute(format!("{BODY}.points"))?
            .time_samples_in(..)?
            .is_empty()
    );
    Ok(())
}

#[test]
fn bake_saves_hint_layer() -> Result<(), SchemaError> {
    let (dir, stage, a, b) = shot(&hinted(&rig("", LIFT, "", ""), "component"))?;
    stage.set_edit_target(stage.edit_target_for_local_layer(&b).expect("local"))?;
    bake_into(
        &bindings(&root(&stage)?, PrimPredicate::DEFAULT)?,
        &a,
        &BakeOptions::default(),
    )?;
    // The hints went to the edit target's layer, which was saved beside the
    // bindings' layer.
    let stage = reopen(&dir)?;
    let hint = stage.attribute("/Root.extentsHint")?;
    assert_eq!(hint.time_samples_in(..)?, [1.0, 2.0]);
    assert!(
        !stage
            .attribute(format!("{BODY}.points"))?
            .time_samples_in(..)?
            .is_empty()
    );
    Ok(())
}

#[test]
fn bake_anonymous_unsaved() -> Result<(), SchemaError> {
    let stage = from_usda(&rig("", LIFT, "", ""))?;
    let bake = sdf::Layer::new_anonymous("bake");
    let bake_id = bake.identifier().to_owned();
    stage.insert_layer(&root_layer(&stage), 0, bake, sdf::LayerOffset::default())?;
    let error = bake_into(
        &bindings(&root(&stage)?, PrimPredicate::DEFAULT)?,
        &bake_id,
        &BakeOptions::default(),
    )
    .expect_err("an anonymous layer has nowhere to save to");
    assert!(
        matches!(&error, SchemaError::Core(openusd::Error::Export(_))),
        "{error:?}"
    );
    // The bake is on the stage all the same.
    assert!(!authored(&stage, &bake_id, &format!("{BODY}.points")).1.is_empty());
    Ok(())
}
