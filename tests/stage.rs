//! Integration tests for `usd::Stage` exercised purely through its public
//! API: opening composed stages, querying composition results, value
//! resolution, prim/attribute/relationship handles, instancing, value
//! clips, and stage-tier authoring.

use anyhow::Result;
use openusd::usd::{
    EditTarget, EditTargetArc, InitialLoadSet, PrimPredicate, PrimStatus, Stage, StageAuthoringError,
    StagePopulationMask,
};
use openusd::{gf, pcp, sdf, tf, usd};

const VENDOR_COMPOSITION: &str = "vendor/usd-wg-assets/test_assets/foundation/stage_composition";

fn manifest_dir() -> String {
    std::env::var("CARGO_MANIFEST_DIR").unwrap()
}

fn composition_path(relative: &str) -> String {
    format!("{}/{VENDOR_COMPOSITION}/{relative}", manifest_dir())
}

fn fixture_path(relative: &str) -> String {
    format!("{}/fixtures/{relative}", manifest_dir())
}

// Composed-scene query shims used throughout these tests: each routes
// through the handle that now owns the query so the assertions stay terse.
fn child_names(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
    Ok(stage.prim(path).child_names()?.into_iter().map(String::from).collect())
}

fn prop_names(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
    Ok(stage
        .prim(path)
        .property_names()?
        .into_iter()
        .map(String::from)
        .collect())
}

fn connections(stage: &Stage, attr: &sdf::Path) -> Result<Vec<sdf::Path>> {
    stage.attribute(attr).connections()
}

fn rel_targets(stage: &Stage, rel: &sdf::Path) -> Result<Vec<sdf::Path>> {
    stage.relationship(rel).targets()
}

fn fwd_targets(stage: &Stage, rel: &sdf::Path) -> Result<Vec<sdf::Path>> {
    stage.relationship(rel).forwarded_targets()
}

// --- Basic stage opening (vendor/usd-wg-assets) ---

#[test]
fn missing_sublayer_retained() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n)\ndef \"Root\" {}\n",
    )?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(stage.composition_errors().iter().any(|error| matches!(
        error,
        pcp::Error::UnresolvedSublayer {
            asset_path,
            introduced_by,
        } if asset_path == "missing.usda" && introduced_by.ends_with("root.usda")
    )));
    assert!(stage.prim("/Root").is_valid()?);
    Ok(())
}

/// A single-layer .usda file should load with correct defaultPrim and
/// root prim list.
#[test]
fn open_single_layer() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    assert_eq!(stage.layer_count(), 1);
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    assert_eq!(
        stage.root_prims()?.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        ["World"]
    );

    Ok(())
}

/// Default traversal should visit active, loaded, defined, non-abstract prims.
#[test]
fn traverse_uses_default_predicate() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;

    assert_eq!(prims, vec!["/World", "/World/CubeActive"]);

    Ok(())
}

/// Exhaustive traversal should preserve raw composed hierarchy traversal.
#[test]
fn traverse_all_visits_every_composed_prim() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

    assert_eq!(prims, vec!["/World", "/World/CubeInactive", "/World/CubeActive"]);

    Ok(())
}

/// A prim defined only in the stronger sublayer should appear in composed
/// children alongside prims from the weaker layer.
#[test]
fn sublayer_children_union() -> Result<()> {
    let path = fixture_path("sublayer_override.usda");
    let stage = Stage::open(&path)?;

    let children = child_names(&stage, "/World")?;
    // Override layer adds Sphere; base layer defines Cube.
    assert!(children.contains(&"Cube".to_string()), "Cube from base layer");
    assert!(children.contains(&"Sphere".to_string()), "Sphere from override layer");

    Ok(())
}

/// The sublayer_same_folder vendor test asset should open correctly with
/// 2 layers and expose the sublayer's prims through composition.
#[test]
fn sublayer_prims_from_weaker_layer() -> Result<()> {
    let path = composition_path("subLayer/sublayer_same_folder.usda");
    let stage = Stage::open(&path)?;

    assert_eq!(stage.layer_count(), 2);
    assert_eq!(stage.default_prim().as_deref(), Some("World"));

    // The weaker sublayer (_stage.usda) defines /World/Cube.
    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;
    assert!(prims.contains(&"/World/Cube".to_string()));

    Ok(())
}

/// Vendor test: reference_same_folder.usda references _stage.usda with
/// defaultPrim. The referenced layer's /World/Cube should appear under the
/// referencing prim.
#[test]
fn reference_default_prim_from_external_layer() -> Result<()> {
    let path = composition_path("references/reference_same_folder.usda");
    let stage = Stage::open(&path)?;

    // /World references _stage.usda's defaultPrim ("World"),
    // so /World/Cube should come from the referenced layer.
    let children = child_names(&stage, "/World")?;
    assert!(
        children.contains(&"Cube".to_string()),
        "Cube from referenced layer should appear under /World"
    );

    Ok(())
}

/// An external reference with an explicit prim path should remap the
/// target prim into the referencing prim's namespace.
/// ref_prim.usda: /World/RefPrim references @ref_target.usda@</Source>.
#[test]
fn reference_explicit_prim_path() -> Result<()> {
    let path = fixture_path("ref_prim.usda");
    let stage = Stage::open(&path)?;

    // /Source/Child in ref_target.usda should appear as /World/RefPrim/Child.
    let children = child_names(&stage, "/World/RefPrim")?;
    assert!(
        children.contains(&"Child".to_string()),
        "referenced children should be namespace-remapped"
    );

    Ok(())
}

// --- Inherit composition ---

/// class_inherit.usda: cubeWithoutSetColor inherits from /_myClass which
/// defines displayColor = green. The prim should pick up the class property.
#[test]
fn inherit_from_class() -> Result<()> {
    let path = composition_path("class_inherit.usda");
    let stage = Stage::open(&path)?;

    // The inherited property should be visible.
    let props = prop_names(&stage, "/World/cubeWithoutSetColor")?;
    assert!(
        props.contains(&"primvars:displayColor".to_string()),
        "inherited property should be visible"
    );

    Ok(())
}

// --- Payload composition ---

/// Vendor test: payload_same_folder.usda has a payload to _stage.usda.
/// The payload's prim hierarchy should be composed into the stage.
#[test]
fn payload_pulls_children() -> Result<()> {
    let path = composition_path("payload/payload_same_folder.usda");
    let stage = Stage::open(&path)?;

    // The payload target layer has /World/Cube. Since /World is the payload
    // target, /World/Cube should appear.
    let children = child_names(&stage, "/World")?;
    assert!(
        children.contains(&"Cube".to_string()),
        "Cube from payload layer should appear under /World"
    );

    Ok(())
}

// --- Session layer ---

/// Opens a stage with session_layer.usda over session_root.usda.
fn open_with_session() -> Result<Stage> {
    let root = fixture_path("session_root.usda");
    let session = fixture_path("session_layer.usda");
    Stage::builder().session_layer(&session).open(&root)
}

/// A stage opened without a session layer should report no session layer.
#[test]
fn no_session_layer_by_default() -> Result<()> {
    let stage = Stage::open(&fixture_path("session_root.usda"))?;

    assert!(!stage.has_session_layer());
    assert!(stage.session_layer().is_none());
    assert_eq!(stage.layer_count(), 1);

    Ok(())
}

/// `defaultPrim` should come from the root layer, not the session layer.
#[test]
fn session_layer_does_not_affect_default_prim() -> Result<()> {
    let stage = open_with_session()?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

/// Children defined only in the root layer should still be visible
/// when a session layer is present.
#[test]
fn session_layer_preserves_children() -> Result<()> {
    let stage = open_with_session()?;

    let children = child_names(&stage, "/World")?;
    assert!(
        children.contains(&"Child".to_string()),
        "root layer's children should be visible: got {children:?}"
    );

    Ok(())
}

#[test]
fn api_schemas_returns_applied_schemas() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let geo = sdf::Path::new("/World/Geo")?;
    let schemas = stage.prim(geo.clone()).api_schemas()?;
    assert!(schemas.contains(&tf::Token::from("MaterialBindingAPI")));
    assert!(schemas.contains(&tf::Token::from("SkelBindingAPI")));
    Ok(())
}

#[test]
fn api_schemas_compose_list_ops() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        append apiSchemas = ["WeakAPI", "RemovedAPI"]
    )
    {
    }
}
"#,
    )?;
    std::fs::write(
        dir.path().join("middle.usda"),
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "World"
{
    over "Geo" (
        prepend apiSchemas = ["StrongAPI"]
    )
    {
    }
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @middle.usda@
    ]
)

over "World"
{
    over "Geo" (
        delete apiSchemas = ["RemovedAPI"]
    )
    {
    }
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let schemas = stage.prim(sdf::Path::new("/World/Geo")?).api_schemas()?;
    assert_eq!(schemas, vec![tf::Token::from("StrongAPI"), tf::Token::from("WeakAPI")]);
    Ok(())
}

#[test]
fn api_schemas_compose_reorder_list_op() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        apiSchemas = ["A", "B", "C"]
    )
    {
    }
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "World"
{
    over "Geo" (
        reorder apiSchemas = ["C", "A"]
    )
    {
    }
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let schemas = stage.prim(sdf::Path::new("/World/Geo")?).api_schemas()?;
    assert_eq!(
        schemas,
        vec![tf::Token::from("C"), tf::Token::from("A"), tf::Token::from("B")]
    );
    Ok(())
}

/// Inherit arc: a class authoring `apiSchemas` contributes to the
/// inheriting prim's composed list, with the local prim's edits applied
/// on top. `has_api_schema` (the surface physics / skel readers depend
/// on) sees both opinions.
#[test]
fn api_schemas_via_inherit() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

class "_Base" (
    prepend apiSchemas = ["BaseAPI"]
)
{
}

def Xform "World"
{
    def Mesh "Geo" (
        inherits = </_Base>
        prepend apiSchemas = ["LocalAPI"]
    )
    {
    }
}
"#,
    )?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let geo = sdf::Path::new("/World/Geo")?;
    assert_eq!(
        stage.prim(geo.clone()).api_schemas()?,
        vec![tf::Token::from("LocalAPI"), tf::Token::from("BaseAPI")],
    );
    assert!(stage.prim(geo.clone()).has_api_schema("BaseAPI")?);
    assert!(stage.prim(geo.clone()).has_api_schema("LocalAPI")?);
    Ok(())
}

/// Reference arc: a referenced asset's `apiSchemas` compose into the
/// referencing prim's list, with the local layer's edits applied on top.
#[test]
fn api_schemas_via_reference() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Source"
)

def Mesh "Source" (
    prepend apiSchemas = ["AssetAPI"]
)
{
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def Xform "World"
{
    def "Geo" (
        references = @asset.usda@
        prepend apiSchemas = ["LocalAPI"]
    )
    {
    }
}
"#,
    )?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let geo = sdf::Path::new("/World/Geo")?;
    assert_eq!(
        stage.prim(geo.clone()).api_schemas()?,
        vec![tf::Token::from("LocalAPI"), tf::Token::from("AssetAPI")],
    );
    Ok(())
}

/// Variant arc: a selected variant authoring `apiSchemas` contributes to
/// the variant-set-owning prim's composed list.
#[test]
fn api_schemas_via_variant() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        variants = {
            string mode = "full"
        }
        prepend variantSets = "mode"
        prepend apiSchemas = ["LocalAPI"]
    )
    {
        variantSet "mode" = {
            "full" (
                prepend apiSchemas = ["VariantAPI"]
            ) {
            }
            "empty" {
            }
        }
    }
}
"#,
    )?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let geo = sdf::Path::new("/World/Geo")?;
    let schemas = stage.prim(geo.clone()).api_schemas()?;
    assert!(
        schemas.contains(&tf::Token::from("VariantAPI")),
        "variant contribution missing: {schemas:?}",
    );
    assert!(
        schemas.contains(&tf::Token::from("LocalAPI")),
        "local contribution missing: {schemas:?}",
    );
    Ok(())
}

/// Property paths resolve to the owning prim's schemas (matches the
/// `specifier` / `kind` convention).
#[test]
fn api_schemas_property_path() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let prim = sdf::Path::new("/World/Geo")?;
    let prop = sdf::Path::new("/World/Geo.points")?;
    assert_eq!(stage.prim(prop).api_schemas()?, stage.prim(prim).api_schemas()?);
    Ok(())
}

#[test]
fn connection_paths_compose_list_ops() -> Result<()> {
    // Stack: weak sublayer authors `append`; root layer authors
    // `prepend`. `connection_paths` must fold edits across both
    // layers, not return only the strongest layer's list op.
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def Shader "Mat"
{
    color3f outputs:out
    append color3f inputs:in.connect = [</Mat.outputs:out>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "Mat"
{
    prepend color3f inputs:in.connect = [</Mat.outputs:strong>]
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let conns = connections(&stage, &sdf::Path::new("/Mat.inputs:in")?)?;
    assert_eq!(
        conns,
        vec![
            sdf::Path::new("/Mat.outputs:strong")?,
            sdf::Path::new("/Mat.outputs:out")?
        ]
    );
    Ok(())
}

#[test]
fn relationship_targets_compose_list_ops() -> Result<()> {
    // Weak sublayer appends a target; root prepends one. Raw targets must
    // fold list-op edits across both layers (spec 12.2.6, 12.4).
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def "Set"
{
    def "A" {}
    def "B" {}
    append rel members = [</Set/B>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "Set"
{
    prepend rel members = [</Set/A>]
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let targets = rel_targets(&stage, &sdf::Path::new("/Set.members")?)?;
    assert_eq!(targets, vec![sdf::Path::new("/Set/A")?, sdf::Path::new("/Set/B")?]);
    Ok(())
}

#[test]
fn relationship_targets_remap_reference() -> Result<()> {
    // Targets authored in a referenced asset's namespace resolve into the
    // referencing prim's namespace (spec 12.4 raw targets across arcs).
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Source"
)

def "Source"
{
    def "Child" {}
    rel members = [</Source/Child>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def "Inst" (
    references = @asset.usda@
)
{
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let targets = rel_targets(&stage, &sdf::Path::new("/Inst.members")?)?;
    assert_eq!(targets, vec![sdf::Path::new("/Inst/Child")?]);
    Ok(())
}

#[test]
fn forwarded_targets_honor_mask() -> Result<()> {
    // Forwarding must not read a relationship on a masked-out prim, so the
    // chain through /Hidden.rel contributes nothing; a direct prim target
    // to the masked prim is still returned (raw target value, not a query).
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def "Vis"
{
    rel chain = [</Hidden.rel>]
    rel direct = [</Hidden>]
}

def "Hidden"
{
    rel rel = [</Hidden/Geom>]
    def "Geom" {}
}
"#,
    )?;

    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/Vis"]))
        .open(root.to_str().expect("utf-8 temp path"))?;

    // /Hidden is masked out: its relationship is not followed.
    assert!(fwd_targets(&stage, &sdf::Path::new("/Vis.chain")?)?.is_empty());
    // A direct prim target is still returned, matching raw targets.
    assert_eq!(
        fwd_targets(&stage, &sdf::Path::new("/Vis.direct")?)?,
        vec![sdf::Path::new("/Hidden")?]
    );
    Ok(())
}

#[test]
fn connection_paths_remap_reference() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Source"
)

def Shader "Source"
{
    color3f outputs:out
    color3f inputs:in.connect = [</Source.outputs:out>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def Shader "Mat" (
    references = @asset.usda@
)
{
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let input = sdf::Path::new("/Mat.inputs:in")?;
    let output = sdf::Path::new("/Mat.outputs:out")?;
    assert_eq!(connections(&stage, &input)?, vec![output.clone()]);

    let graph = usd::ConnectionGraph::from_stage(&stage)?;
    assert_eq!(graph.sources(&input), std::slice::from_ref(&output));
    assert_eq!(graph.sinks(&output), &[input]);
    Ok(())
}

#[test]
fn api_schemas_empty_for_prim_without_schemas() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let props = sdf::Path::new("/World/Props")?;
    assert!(stage.prim(props).api_schemas()?.is_empty());
    Ok(())
}

#[test]
fn has_api_schema_matches_applied() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let geo = sdf::Path::new("/World/Geo")?;
    assert!(stage.prim(geo.clone()).has_api_schema("MaterialBindingAPI")?);
    assert!(!stage.prim(geo.clone()).has_api_schema("SkelRootAPI")?);
    Ok(())
}

#[test]
fn type_name_returns_prim_type() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    assert_eq!(
        stage.prim(sdf::Path::new("/World/Geo")?).type_name()?.as_deref(),
        Some("Mesh")
    );
    assert_eq!(
        stage.prim(sdf::Path::new("/World")?).type_name()?.as_deref(),
        Some("Xform")
    );
    Ok(())
}

fn open_stage_queries_fixture() -> Result<Stage> {
    Stage::open("fixtures/stage_queries.usda")
}

#[test]
fn active_loaded() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert!(stage.prim("/World/ActiveParent/Child").is_active()?);
    assert!(stage.prim("/World/ActiveParent/Child").is_loaded()?);

    assert!(!stage.prim("/World/InactiveParent").is_active()?);
    assert!(!stage.prim("/World/InactiveParent/Child").is_active()?);
    assert!(!stage.prim("/World/InactiveParent/Child").is_loaded()?);

    assert!(!stage.prim("/World/Missing").is_active()?);
    Ok(())
}

#[test]
fn load_none() -> Result<()> {
    let path = composition_path("payload/payload_same_folder.usda");

    let loaded = Stage::open(&path)?;
    assert_eq!(loaded.layer_count(), 2);
    assert!(loaded.prim("/World").is_loaded()?);
    assert_eq!(child_names(&loaded, "/World")?, vec!["Cube"]);

    let unloaded = Stage::builder().load(InitialLoadSet::LoadNone).open(&path)?;
    assert_eq!(unloaded.load(), InitialLoadSet::LoadNone);
    assert_eq!(unloaded.layer_count(), 1);
    assert!(!unloaded.prim("/World").is_loaded()?);
    assert_eq!(child_names(&unloaded, "/World")?, Vec::<String>::new());

    let mut prims = Vec::new();
    unloaded.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;
    assert!(prims.is_empty());
    Ok(())
}

#[test]
fn defined_abstract() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert_eq!(stage.prim("/World/OverOnly").specifier()?, Some(sdf::Specifier::Over));
    assert!(stage.prim("/World/ActiveParent/Child").is_defined()?);
    assert!(!stage.prim("/World/OverOnly").is_defined()?);
    assert!(!stage.prim("/World/OverParent/Child").is_defined()?);

    assert!(stage.prim("/World/ClassParent/Child").is_defined()?);
    assert!(stage.prim("/World/ClassParent").is_abstract()?);
    assert!(stage.prim("/World/ClassParent/Child").is_abstract()?);
    assert!(!stage.prim("/World/ActiveParent/Child").is_abstract()?);
    Ok(())
}

#[test]
fn instance_flag() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert!(stage.prim("/World/Instance").has_composition_arc()?);
    assert!(stage.prim("/World/Instance").is_instance()?);

    assert!(!stage.prim("/World/InstanceableNoArc").has_composition_arc()?);
    assert!(!stage.prim("/World/InstanceableNoArc").is_instance()?);
    Ok(())
}

/// An instance prim's children come only from its composition arcs; a
/// local-only child is discarded (spec 11.3.3).
#[test]
fn instance_children_from_arcs_only() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing.usda"))?;

    let mut children = child_names(&stage, "/Instance")?;
    children.sort();
    assert_eq!(children, vec!["Child".to_string()]);

    // A plain (non-instance) reference still merges local and referenced
    // children.
    let mut non_instance = child_names(&stage, "/NonInstance")?;
    non_instance.sort();
    assert_eq!(non_instance, vec!["Child".to_string(), "LocalOnly".to_string()]);
    Ok(())
}

/// Instances sharing a prototype resolve descendant values identically and
/// expose the prototype's children (spec 11.3.3).
#[test]
fn shared_instances_resolve_identically() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    assert_eq!(
        stage
            .attribute("/A/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    assert_eq!(
        stage
            .attribute("/B/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    assert_eq!(
        stage
            .attribute("/C/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(9.0))
    );

    assert_eq!(child_names(&stage, "/A")?, vec!["Child".to_string()]);
    assert_eq!(child_names(&stage, "/B")?, vec!["Child".to_string()]);
    Ok(())
}

/// `get_prototype` / `get_instances` group instances by shared composition,
/// and the prototype namespace is addressable (spec 11.3.3).
#[test]
fn prototype_queries() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    let proto = stage.prim("/A").prototype()?;
    assert!(proto.is_some());
    assert_eq!(stage.prim("/B").prototype()?, proto); // same composition → shared
    assert_ne!(stage.prim("/C").prototype()?, proto); // different prototype
    assert_eq!(stage.prim("/Proto").prototype()?, None); // not an instance

    let proto = proto.unwrap();
    // Returned sorted by path, so callers need not sort themselves.
    let instances: Vec<String> = stage
        .prim(proto.clone())
        .instances()
        .iter()
        .map(|p| p.to_string())
        .collect();
    assert_eq!(instances, vec!["/A".to_string(), "/B".to_string()]);

    // The prototype namespace is addressable and resolves to the shared
    // (arc-only) subtree.
    assert!(stage.prim(proto.clone()).is_prototype());
    let child = sdf::path(format!("{proto}/Child"))?;
    assert!(stage.prim(child.clone()).is_in_prototype());
    assert_eq!(
        stage
            .attribute(child.append_property("size")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    Ok(())
}

/// Prototype queries respect the population mask: a masked-out instance is
/// not instanced and never appears among a prototype's instances.
#[test]
fn prototype_queries_masked() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/A"]))
        .open(&fixture_path("instancing_shared.usda"))?;

    // /A is in the mask; /B (which shares /A's prototype) is not.
    assert!(stage.prim("/A").is_instance()?);
    assert!(!stage.prim("/B").is_instance()?);

    let proto = stage.prim("/A").prototype()?;
    assert!(proto.is_some());
    assert_eq!(stage.prim("/B").prototype()?, None);

    // The masked-out /B is excluded from the prototype's instance list.
    let proto = proto.unwrap();
    assert_eq!(stage.prim(proto.clone()).instances(), vec![sdf::path("/A")?]);
    assert_eq!(stage.prototypes(), vec![proto]);
    Ok(())
}

/// A nested instance (an instance inside a prototype's subtree) is
/// recognized, resolves values within the queried instance, and shares its
/// own prototype across the outer instances (spec 11.3.3).
#[test]
fn nested_instances() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_nested.usda"))?;

    assert_eq!(
        stage
            .attribute("/A/Sub/L.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );
    assert_eq!(
        stage
            .attribute("/B/Sub/L.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );

    // The nested prims are instances and share one prototype.
    assert!(stage.prim("/A/Sub").is_instance()?);
    assert!(stage.prim("/B/Sub").is_instance()?);
    let nested = stage.prim("/A/Sub").prototype()?;
    assert!(nested.is_some());
    assert_eq!(stage.prim("/B/Sub").prototype()?, nested);

    // The outer instances share a distinct prototype.
    let outer = stage.prim("/A").prototype()?;
    assert_eq!(stage.prim("/B").prototype()?, outer);
    assert_ne!(outer, nested);

    // The nested subtree is also reachable through the outer prototype.
    let outer = outer.unwrap();
    assert_eq!(
        stage
            .attribute(sdf::path(format!("{outer}/Sub/L.v"))?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );
    Ok(())
}

/// A connection inside an instance subtree resolves within the queried
/// instance, not the shared canonical instance (spec 11.3.3 + 11.3.4).
#[test]
fn instance_connection_remaps_to_instance() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

    // Query /I1 first so it becomes canonical.
    assert_eq!(
        connections(&stage, &sdf::path("/I1/Dst.inputs:in")?)?,
        vec![sdf::path("/I1/Src.outputs:out")?]
    );
    // /I2 shares the prototype; its connection must point into /I2.
    assert_eq!(
        connections(&stage, &sdf::path("/I2/Dst.inputs:in")?)?,
        vec![sdf::path("/I2/Src.outputs:out")?]
    );
    Ok(())
}

/// A connection on a prototype *descendant* resolves in the prototype
/// namespace when queried directly on the prototype, and remaps to the
/// queried instance when reached through a proxy (spec 11.3.3 + 12.4).
#[test]
fn prototype_descendant_target_remap() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

    // Query an instance proxy first to register the prototype; the target
    // remaps into that instance's namespace.
    assert_eq!(
        connections(&stage, &sdf::path("/I1/Dst.inputs:in")?)?,
        vec![sdf::path("/I1/Src.outputs:out")?]
    );

    // The same connection queried directly on the prototype descendant stays
    // in the prototype namespace (no instance to remap to).
    let proto = stage.prim("/I1").prototype()?.expect("I1 is an instance");
    let dst_in = proto.append_path("Dst")?.append_property("inputs:in")?;
    assert_eq!(
        connections(&stage, &dst_in)?,
        vec![proto.append_path("Src")?.append_property("outputs:out")?]
    );
    Ok(())
}

/// Forwarding through a relationship that lives inside an instance
/// prototype resolves within the queried instance: the prototype rel is
/// classified correctly (not mistaken for a terminal) and its targets
/// remap into the instance namespace (spec 11.3.3 + 12.4).
#[test]
fn forwarded_targets_through_instance() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Proto"
)

def "Proto"
{
    def "Target" {}
    rel direct = [</Proto/Target>]
    rel chain = [</Proto.direct>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def "I1" (
    instanceable = true
    references = @asset.usda@
)
{
}

def "I2" (
    instanceable = true
    references = @asset.usda@
)
{
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    // chain -> direct (a prototype relationship) -> Target. Each hop stays
    // in the queried instance's namespace.
    assert_eq!(
        fwd_targets(&stage, &sdf::path("/I1.chain")?)?,
        vec![sdf::path("/I1/Target")?]
    );
    assert_eq!(
        fwd_targets(&stage, &sdf::path("/I2.chain")?)?,
        vec![sdf::path("/I2/Target")?]
    );
    Ok(())
}

/// Connection and schema readers descend into instance subtrees, so
/// content inside an instance is not silently skipped. Public traversal
/// stops at instances, but these readers need the full composed namespace.
#[test]
fn readers_index_instanced_content() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

    let graph = usd::ConnectionGraph::from_stage(&stage)?;
    // The connection lives inside the instance /I1; the reader must descend
    // into the instance proxy to index it.
    assert_eq!(
        graph.sources(&sdf::path("/I1/Dst.inputs:in")?),
        &[sdf::path("/I1/Src.outputs:out")?]
    );
    Ok(())
}

/// Default traversal stops at instance prims; `with_instance_proxies`
/// descends into their subtrees (spec 11.3.3).
#[test]
fn traversal_instance_proxies() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    let mut default = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| default.push(p.to_string()))?;
    assert!(default.contains(&"/A".to_string()));
    assert!(!default.contains(&"/A/Child".to_string()));

    let mut proxies = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT.with_instance_proxies(true), |p| {
        proxies.push(p.to_string())
    })?;
    assert!(proxies.contains(&"/A/Child".to_string()));
    Ok(())
}

/// A property authored at an instance root is local to the instance and
/// does not leak onto the shared prototype root (spec 11.3.3): the prototype
/// composes only the referenced opinions.
#[test]
fn prototype_root_drops_instance_overrides() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_root_override.usda"))?;

    // The instance root keeps its local overrides.
    assert_eq!(
        stage
            .attribute("/A.shared")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );
    assert_eq!(
        stage
            .attribute("/A.rootOnly")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(42.0))
    );

    // The shared prototype root drops them: the overridden property falls
    // back to the referenced value and the instance-only property is gone.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(
        stage
            .attribute(proto.append_property("shared")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    assert_eq!(
        stage
            .attribute(proto.append_property("rootOnly")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );
    Ok(())
}

/// A query on the deterministic synthetic prototype path before any instance
/// composes must not leave the prototype root empty: materialization keys off
/// the registry's mint signal, so it overwrites any stale empty index cached
/// at `/__Prototype_N` (spec 11.3.3).
#[test]
fn prototype_root_survives_early_query() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_root_override.usda"))?;

    // Touch the deterministic synthetic path before any instance registers;
    // this caches an empty index at /__Prototype_0.
    assert_eq!(
        stage
            .attribute("/__Prototype_0.shared")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );

    // Composing the instance mints and materializes /__Prototype_0.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(proto.as_str(), "/__Prototype_0");

    // The prototype root now holds the real composition, not the stale empty
    // index that the guard would otherwise have mistaken for it.
    assert_eq!(
        stage
            .attribute(proto.append_property("shared")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    Ok(())
}

/// A query on a synthetic prototype *descendant* before any instance
/// registers caches a stale empty index and an identity redirection; minting
/// the prototype must evict both so the descendant resolves the shared
/// content rather than the stale synthetic composition (spec 11.3.3).
#[test]
fn prototype_descendant_survives_early_query() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    // Touch the synthetic descendant before any instance registers; this
    // caches an empty index at /__Prototype_0/Child and memoizes its path as
    // an identity (non-redirected) mapping.
    assert_eq!(
        stage
            .attribute("/__Prototype_0/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );

    // Composing the instance mints and materializes /__Prototype_0.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(proto.as_str(), "/__Prototype_0");

    // The descendant now resolves the shared content: minting evicted the
    // stale empty index and identity redirection under /__Prototype_0, so the
    // query recomposes it in place from the materialized prototype root.
    assert_eq!(
        stage
            .attribute(proto.append_path("Child")?.append_property("size")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    Ok(())
}

/// A property authored inside a variant selected on an instance is shared
/// content (the selection defines the prototype) and must resolve on the
/// materialized prototype root (spec 11.3.3).
#[test]
fn prototype_root_keeps_variant_opinions() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_variant_root.usda"))?;

    // The instance resolves the variant-authored property.
    assert_eq!(
        stage
            .attribute("/A.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );

    // So must the prototype root: the variant opinion lives at the instance's
    // own namespace (/A{v=x}), and rebasing must not move the spec lookup off
    // it.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(
        stage
            .attribute(proto.append_property("picked")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    Ok(())
}

/// A relationship/connection target authored at a prototype's root resolves
/// into the prototype namespace on the materialized prototype root, and into
/// each instance's namespace on the instances (spec 11.3.3 + 12.4). Exercises
/// the root rebase (`rebase_root`) of the prototype-root map.
#[test]
fn prototype_root_target_remap() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_root_target.usda"))?;

    // On the instances the targets stay in each instance's own namespace.
    assert_eq!(
        rel_targets(&stage, &sdf::path("/A.myrel")?)?,
        vec![sdf::path("/A/Target")?]
    );
    assert_eq!(
        connections(&stage, &sdf::path("/A.inputs:in")?)?,
        vec![sdf::path("/A.outputs:out")?]
    );
    assert_eq!(
        rel_targets(&stage, &sdf::path("/B.myrel")?)?,
        vec![sdf::path("/B/Target")?]
    );

    // On the materialized prototype root they resolve into the prototype
    // namespace, not the canonical instance's.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(
        rel_targets(&stage, &proto.append_property("myrel")?)?,
        vec![proto.append_path("Target")?]
    );
    assert_eq!(
        connections(&stage, &proto.append_property("inputs:in")?)?,
        vec![proto.append_property("outputs:out")?]
    );
    Ok(())
}

/// The resolved variant selection is part of the instancing key: instances
/// of one reference share a prototype iff their selections match (spec
/// 11.3.3). /A and /C select `x` and share; /B selects `y` and is distinct.
#[test]
fn variant_selection_keys_prototype() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_variant_distinct.usda"))?;

    let proto = |p: &str| -> Result<sdf::Path> {
        stage
            .prim(p)
            .prototype()?
            .ok_or_else(|| anyhow::anyhow!("{p} is not an instance"))
    };

    // Same selection (`x`) shares one prototype; the other selection (`y`)
    // gets a distinct one.
    assert_eq!(proto("/A")?, proto("/C")?);
    assert_ne!(proto("/A")?, proto("/B")?);

    // Each prototype resolves its own variant content.
    assert_eq!(
        stage
            .attribute("/A.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    assert_eq!(
        stage
            .attribute("/B.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(2.0))
    );
    assert_eq!(
        stage
            .attribute("/C.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    Ok(())
}

/// A prototype is populated when at least one of its instances is in the
/// population mask (spec 11.3.3): the synthetic `/__Prototype_N` namespace is
/// never named in a user mask, yet its shared content stays readable through
/// the masked instance.
#[test]
fn prototype_visible_under_mask() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/A"]))
        .open(&fixture_path("instancing_shared.usda"))?;

    // /A is in the mask and is an instance; its prototype is reachable.
    assert!(stage.prim("/A").is_instance()?);
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");

    // The prototype's shared content is readable even though /__Prototype_N
    // is never named in the mask, because instance /A is.
    let child = proto.append_path("Child")?;
    assert!(stage.prim(child.clone()).is_valid()?);
    assert_eq!(
        stage
            .attribute(child.append_property("size")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );

    // A prototype with no masked instance stays hidden: /B (and so the
    // prototype it would otherwise expose) is outside the mask.
    assert!(!stage.mask().includes(&sdf::path("/B")?));
    Ok(())
}

/// A prototype's namespace can contain a nested instance: that nested prim
/// is itself an instance and mints its own prototype, and a prim beneath it
/// is an instance proxy of the nested prototype rather than plain prototype
/// content (spec 11.3.3).
#[test]
fn nested_instance_in_prototype() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_nested_in_prototype.usda"))?;

    let proto = stage.prim("/A").prototype()?.expect("A is an instance");

    // The proxy chain through the instance namespace resolves the nested
    // value (/A/Nested is itself an instance).
    assert!(stage.prim("/A/Nested").is_instance()?);
    assert_eq!(
        stage
            .attribute("/A/Nested/Leaf.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(3.0))
    );

    // Inside the prototype namespace, the nested prim is an instance and
    // mints its own, distinct prototype.
    let nested = stage.prim(proto.append_path("Nested")?);
    assert!(nested.is_instance()?);
    let nested_proto = nested.prototype()?.expect("nested prim is an instance");
    assert_ne!(nested_proto, proto);

    // A prim beneath the nested instance (inside the prototype namespace) is
    // an instance proxy of the nested prototype — previously this was
    // reported as plain prototype content.
    let leaf = stage.prim(proto.append_path("Nested")?.append_path("Leaf")?);
    assert!(leaf.is_instance_proxy()?);
    let in_proto = leaf.prim_in_prototype()?.expect("Leaf is an instance proxy");
    assert_eq!(in_proto.path(), &nested_proto.append_path("Leaf")?);
    Ok(())
}

/// An instance's descendant is an instance proxy that maps to a prim in the
/// shared prototype; the instance root and non-instanced prims are not
/// proxies (spec 11.3.3).
#[test]
fn instance_proxy_api() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    assert!(!stage.prim("/A").is_instance_proxy()?);
    assert!(stage.prim("/A/Child").is_instance_proxy()?);

    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    let in_proto = stage
        .prim("/A/Child")
        .prim_in_prototype()?
        .expect("Child is an instance proxy");
    assert_eq!(in_proto.path(), &proto.append_path("Child")?);
    assert!(in_proto.is_in_prototype());

    // A prim in the prototype namespace is in a prototype, not a proxy.
    assert!(!in_proto.is_instance_proxy()?);

    // A nonexistent path under an instance is not a proxy, and has no prim in
    // the prototype.
    assert!(!stage.prim("/A/Missing").is_instance_proxy()?);
    assert!(stage.prim("/A/Missing").prim_in_prototype()?.is_none());
    Ok(())
}

/// Local opinions on an instance's descendants are discarded; values come
/// from the arc (spec 11.3.3).
#[test]
fn instance_descendant_ignores_local_override() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing.usda"))?;

    // Instance: the local `over Child { size = 999 }` is ignored.
    assert_eq!(
        stage
            .attribute("/Instance/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );

    // Non-instance: the local override wins as usual.
    assert_eq!(
        stage
            .attribute("/NonInstance/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(999.0))
    );
    Ok(())
}

#[test]
fn instance_descendant_ignores_local_arc() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_local_arc.usda"))?;

    // The local `over Child (references = </Other/Child>)` carries its own
    // arc; both the local opinion and the node that arc spawns are
    // discarded, so the value comes from the prototype, not /Other/Child.
    assert_eq!(
        stage
            .attribute("/A/Child.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    Ok(())
}

#[test]
fn model_hierarchy() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert_eq!(stage.prim("/World").kind()?.as_deref(), Some("assembly"));
    assert!(stage.prim("/World").is_model()?);
    assert!(stage.prim("/World").is_group()?);

    assert!(stage.prim("/World/Group").is_model()?);
    assert!(stage.prim("/World/Group").is_group()?);
    assert!(stage.prim("/World/Group/Component").is_model()?);
    assert!(stage.prim("/World/Group/Component").is_component()?);

    assert!(!stage.prim("/World/Group/Subcomponent").is_model()?);
    assert!(stage.prim("/World/Group/Subcomponent").is_subcomponent()?);

    assert_eq!(
        stage.prim("/World/InvalidComponentParent/Component").kind()?.as_deref(),
        Some("component")
    );
    assert!(!stage.prim("/World/InvalidComponentParent/Component").is_model()?);
    assert!(!stage.prim("/World/InvalidComponentParent/Component").is_component()?);
    Ok(())
}

#[test]
fn prim_status_bits() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert_eq!(
        stage.prim_status("/World/ClassParent/Child")?,
        PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::ABSTRACT
    );

    assert_eq!(
        stage.prim_status("/World/Instance")?,
        PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::INSTANCE
    );
    Ok(())
}

#[test]
fn traverse_default() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;

    assert!(prims.contains(&"/World".to_string()));
    assert!(prims.contains(&"/World/ActiveParent".to_string()));
    assert!(prims.contains(&"/World/ActiveParent/Child".to_string()));
    assert!(prims.contains(&"/World/Instance".to_string()));

    assert!(!prims.contains(&"/World/InactiveParent".to_string()));
    assert!(!prims.contains(&"/World/InactiveParent/Child".to_string()));
    assert!(!prims.contains(&"/World/OverOnly".to_string()));
    assert!(!prims.contains(&"/World/OverParent".to_string()));
    assert!(!prims.contains(&"/World/OverParent/Child".to_string()));
    assert!(!prims.contains(&"/World/ClassParent".to_string()));
    assert!(!prims.contains(&"/World/ClassParent/Child".to_string()));
    Ok(())
}

#[test]
fn traverse_all_predicate() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

    assert!(prims.contains(&"/World/InactiveParent".to_string()));
    assert!(prims.contains(&"/World/InactiveParent/Child".to_string()));
    assert!(prims.contains(&"/World/OverOnly".to_string()));
    assert!(prims.contains(&"/World/OverParent/Child".to_string()));
    assert!(prims.contains(&"/World/ClassParent".to_string()));
    assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
    Ok(())
}

#[test]
fn custom_predicate() -> Result<()> {
    let stage = open_stage_queries_fixture()?;
    let predicate = PrimPredicate::new(PrimStatus::ACTIVE | PrimStatus::DEFINED, PrimStatus::empty());

    let mut prims = Vec::new();
    stage.traverse(predicate, |p| prims.push(p.as_str().to_string()))?;

    assert!(prims.contains(&"/World/ClassParent".to_string()));
    assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
    assert!(!prims.contains(&"/World/InactiveParent".to_string()));
    assert!(!prims.contains(&"/World/OverOnly".to_string()));
    Ok(())
}

// --- Stage-tier authoring ---

fn in_memory_stage() -> Result<Stage> {
    Stage::builder().in_memory("anon.usda")
}

#[test]
fn author_default_prim() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.set_default_prim("World")?;
    stage.define_prim("/World")?.set_type_name("Xform")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

#[test]
fn default_prim_rejects_path() -> Result<()> {
    let stage = in_memory_stage()?;
    let err = stage.set_default_prim("/World").unwrap_err();
    assert!(matches!(
        err,
        StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. })
    ));
    Ok(())
}

/// Modern OpenUSD allows nested `defaultPrim` values like `"World/Char"`.
/// The write contract must match what the read path will accept.
#[test]
fn default_prim_accepts_nested() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.set_default_prim("World/Mesh")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World/Mesh"));
    Ok(())
}

/// A stage opened from a file is editable — every backend implements the
/// field-level write API — so authoring into its root layer succeeds.
#[test]
fn file_loaded_stage_is_editable() -> Result<()> {
    let stage = Stage::open(&composition_path("subLayer/sublayer_same_folder.usda"))?;
    stage.define_prim("/X")?;
    stage.set_default_prim("World")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

#[test]
fn edit_target_out_of_range() -> Result<()> {
    let stage = in_memory_stage()?;
    let err = stage
        .set_edit_target(EditTarget::for_layer("missing-layer"))
        .unwrap_err();
    assert!(matches!(err, StageAuthoringError::LayerNotFound { .. }));
    Ok(())
}

/// A local edit target maps scene paths to themselves, so authoring is
/// unchanged from the bare-`layer_index` behavior.
#[test]
fn edit_target_local_is_identity() -> Result<()> {
    let target = EditTarget::for_layer("test");
    let path = sdf::path("/A/B")?;
    assert_eq!(target.map_to_spec_path(&path), Some(path));
    Ok(())
}

/// A variant edit target rewrites scene paths into the `{set=sel}`
/// namespace; paths outside the variant prim map to themselves.
#[test]
fn variant_target_maps_selection() -> Result<()> {
    let target = EditTarget::for_local_direct_variant("test", sdf::path("/Prim{set=sel}")?);
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim/child")?),
        Some(sdf::path("/Prim{set=sel}child")?)
    );
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim.attr")?),
        Some(sdf::path("/Prim{set=sel}.attr")?)
    );
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Other")?),
        Some(sdf::path("/Other")?)
    );
    Ok(())
}

/// A bad target is rejected at `edit_context`, leaving the current target
/// unchanged.
#[test]
fn edit_context_rejects_bad_target() -> Result<()> {
    let stage = in_memory_stage()?;
    let before = stage.edit_target().layer_identifier().to_string();
    let result = stage.edit_context(EditTarget::for_layer("missing-layer"));
    assert!(matches!(result, Err(StageAuthoringError::LayerNotFound { .. })));
    assert_eq!(stage.edit_target().layer_identifier(), before);
    Ok(())
}

/// Authoring the variant-owning prim itself through a variant target maps
/// to the bare variant selection, which is not a prim — it must error, not
/// panic.
#[test]
fn define_prim_at_variant_leaf_errors() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.edit_target().layer_identifier().to_string();
    stage.define_prim("/Prim")?;
    stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
    // `/Prim` maps to the variant selection `/Prim{set=sel}`.
    assert!(matches!(
        stage.define_prim("/Prim"),
        Err(StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. }))
    ));
    Ok(())
}

/// In-memory stage with `/Prim` inheriting a local class `/_Class`, so the
/// inherit arc's source layer is the writable root.
fn inherit_stage() -> Result<Stage> {
    let stage = in_memory_stage()?;
    stage.define_prim("/_Class")?;
    stage.define_prim("/Prim")?.set_metadata(
        sdf::FieldKey::InheritPaths.as_str(),
        sdf::Value::PathListOp(sdf::PathListOp::prepended([sdf::path("/_Class")?])),
    )?;
    Ok(stage)
}

/// An arc target on a reference captures the referenced layer and maps composed
/// paths down into its namespace.
#[test]
fn edit_target_for_reference_node() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let target = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    assert!(target.layer_identifier().ends_with("ref_target.usda"));
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/World/MyPrim/Child")?),
        Some(sdf::path("/Source/Child")?)
    );
    Ok(())
}

/// An inherit arc target captures the class-owning layer and maps the composed
/// path to the class path.
#[test]
fn edit_target_for_inherit_node() -> Result<()> {
    let stage = inherit_stage()?;
    let target = stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Inherit)?;
    assert_eq!(target.layer_identifier(), stage.root_layer().identifier());
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim/Child")?),
        Some(sdf::path("/_Class/Child")?)
    );
    Ok(())
}

/// A prim with no arc of the requested kind has no arc target.
#[test]
fn edit_target_no_matching_arc() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Prim")?;
    assert!(matches!(
        stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Reference),
        Err(StageAuthoringError::NoArcNode { .. })
    ));
    Ok(())
}

/// Authoring through an inherit arc target lands the opinion at the class path
/// in the source layer, not at the composed path, and it composes back.
#[test]
fn edit_target_authors_into_class() -> Result<()> {
    let stage = inherit_stage()?;
    let target = stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Inherit)?;
    {
        let _ctx = stage.edit_context(target)?;
        stage.define_prim("/Prim/Child")?;
    }
    assert!(stage.prim("/Prim/Child").is_valid()?);
    assert!(stage.root_layer().data().has_spec(&sdf::path("/_Class/Child")?));
    assert!(!stage.root_layer().data().has_spec(&sdf::path("/Prim/Child")?));
    Ok(())
}

/// `map_to_spec_path` re-maps an embedded relationship target through the same
/// arc mapping (C++ `MapToSpecPath` step 2).
#[test]
fn map_spec_path_remaps_embedded_target() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let target = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/World/MyPrim.rel[/World/MyPrim/Child]")?),
        Some(sdf::path("/Source.rel[/Source/Child]")?)
    );
    Ok(())
}

/// An embedded target outside the arc's co-domain rejects the whole path.
#[test]
fn map_spec_path_rejects_outside_target() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let target = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/World/MyPrim.rel[/Elsewhere]")?),
        None
    );
    Ok(())
}

/// A local target's identity mapping leaves an embedded target untouched.
#[test]
fn map_spec_path_local_keeps_target() -> Result<()> {
    let target = EditTarget::for_layer("test");
    let path = sdf::path("/A.rel[/B].attr")?;
    assert_eq!(target.map_to_spec_path(&path), Some(path));
    Ok(())
}

/// A variant target maps an embedded target without leaving a variant
/// selection on the target path (target paths never carry selections).
#[test]
fn map_spec_path_variant_strips_target() -> Result<()> {
    let target = EditTarget::for_local_direct_variant("test", sdf::path("/Prim{set=sel}")?);
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim.rel[/Prim/T]")?),
        Some(sdf::path("/Prim{set=sel}.rel[/Prim/T]")?)
    );
    Ok(())
}

/// `edit_target_root` names the root layer with an identity mapping and equals
/// the default target installed at open.
#[test]
fn edit_target_root_matches_default() -> Result<()> {
    let stage = in_memory_stage()?;
    let target = stage.edit_target_root();
    assert_eq!(target.layer_identifier(), stage.root_layer().identifier());
    assert_eq!(target.map_to_spec_path(&sdf::path("/A/B")?), Some(sdf::path("/A/B")?));
    assert_eq!(stage.edit_target(), target);
    Ok(())
}

/// `edit_target_session` names the strongest session layer, or is `None` when
/// the stage has no session layer.
#[test]
fn edit_target_session() -> Result<()> {
    let stage = open_with_session()?;
    let target = stage.edit_target_session().expect("session layer");
    assert_eq!(
        target.layer_identifier(),
        stage.session_layer().expect("session layer").identifier()
    );

    assert!(in_memory_stage()?.edit_target_session().is_none());
    Ok(())
}

/// A stage-bound target is rejected by a stage with a different root layer
/// stack identity; a stage-agnostic `for_layer` target is still accepted, and a
/// cloned handle to the same stage accepts its sibling's bound target.
#[test]
fn layer_stack_id_distinguishes_stages() -> Result<()> {
    let stage_a = Stage::builder().in_memory("anon_a.usda")?;
    let stage_b = Stage::builder().in_memory("anon_b.usda")?;
    let bound = stage_a.edit_target_root();
    assert!(matches!(
        stage_b.set_edit_target(bound.clone()),
        Err(StageAuthoringError::EditTargetWrongStage)
    ));
    let root_b = stage_b.root_layer().identifier().to_string();
    assert!(stage_b.set_edit_target(EditTarget::for_layer(root_b)).is_ok());

    // A cloned handle shares the same `StageInner`, so it has the same root
    // layer stack identity and accepts the target built against its sibling.
    let stage_a_clone = stage_a.clone();
    assert!(stage_a_clone.set_edit_target(bound).is_ok());
    Ok(())
}

/// Anonymous root layers are unique per stage even when opened with the same
/// tag, so two such stages have distinct layer stack identities and reject each
/// other's edit targets.
#[test]
fn anonymous_stages_are_distinct() -> Result<()> {
    let stage_a = Stage::builder().in_memory("same.usda")?;
    let stage_b = Stage::builder().in_memory("same.usda")?;
    assert_ne!(stage_a.root_layer().identifier(), stage_b.root_layer().identifier());
    assert!(matches!(
        stage_b.set_edit_target(stage_a.edit_target_root()),
        Err(StageAuthoringError::EditTargetWrongStage)
    ));
    Ok(())
}

/// A target naming a layer is valid; one naming no layer is null and invalid.
#[test]
fn edit_target_null_and_valid() -> Result<()> {
    let valid = EditTarget::for_layer("layer");
    assert!(!valid.is_null());
    assert!(valid.is_valid());

    let null = EditTarget::for_layer("");
    assert!(null.is_null());
    assert!(!null.is_valid());
    Ok(())
}

/// `compose_over` layers a variant refinement onto a reference target, so a
/// stage write resolves through both into the nested spec path; a null target
/// composes to the other.
#[test]
fn edit_target_compose_over() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let weaker = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    let stronger = EditTarget::for_local_direct_variant(weaker.layer_identifier(), sdf::path("/Source{set=sel}")?);

    let composed = stronger.compose_over(&weaker);
    assert_eq!(composed.layer_identifier(), weaker.layer_identifier());
    assert_eq!(
        composed.map_to_spec_path(&sdf::path("/World/MyPrim/Child")?),
        Some(sdf::path("/Source{set=sel}Child")?)
    );

    assert_eq!(EditTarget::for_layer("").compose_over(&weaker), weaker);
    Ok(())
}

/// Composing targets bound to stages with different layer stack identities
/// yields a null target, keeping the cross-stage guard intact.
#[test]
fn compose_over_cross_stack_null() -> Result<()> {
    let stage_a = Stage::builder().in_memory("anon_a.usda")?;
    let stage_b = Stage::builder().in_memory("anon_b.usda")?;
    let composed = stage_a.edit_target_root().compose_over(&stage_b.edit_target_root());
    assert!(composed.is_null());
    Ok(())
}

/// A stage-bound target is accepted by a freshly opened stage with the same
/// root layer, session, and resolver context: layer-stack identity is by
/// composition input, not by stage instance.
#[test]
fn layer_stack_id_same_inputs() -> Result<()> {
    let path = fixture_path("ref_external.usda");
    let stage_a = Stage::open(&path)?;
    let stage_b = Stage::open(&path)?;
    assert!(stage_b.set_edit_target(stage_a.edit_target_root()).is_ok());
    Ok(())
}

/// Authoring a time sample through an arc target with a non-identity layer
/// offset keys the sample at the inverse-mapped source time, so it reads back
/// at the original stage time once composition re-applies the offset.
#[test]
fn arc_target_retimes_time_sample() -> Result<()> {
    let stage = in_memory_stage()?;
    // `/Prim` references `/Source` with a (offset = 10) layer offset, so a
    // source-layer time `t` composes to stage time `t + 10`.
    stage.define_prim("/Source")?.create_attribute("x", "double")?;
    stage.define_prim("/Prim")?.set_metadata(
        sdf::FieldKey::References.as_str(),
        sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
            prim_path: sdf::path("/Source")?,
            layer_offset: sdf::LayerOffset::new(10.0, 1.0),
            ..Default::default()
        }])),
    )?;

    let target = stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Reference)?;
    // Stage time 15 inverse-maps to source time 5.
    assert_eq!(target.map_to_spec_time(15.0), 5.0);
    {
        let _ctx = stage.edit_context(target)?;
        stage
            .attribute("/Prim.x")
            .set_at(sdf::Value::Double(42.0), usd::TimeCode::new(15.0))?;
    }

    // The sample landed at source time 5 in the root layer...
    let samples = stage.attribute("/Source.x").time_samples()?.expect("samples");
    assert_eq!(samples, vec![(5.0, sdf::Value::Double(42.0))]);
    // ...and reads back at stage time 15 through the offset reference.
    assert_eq!(
        stage.attribute("/Prim.x").get_at::<f64>(usd::TimeCode::new(15.0))?,
        Some(42.0)
    );
    Ok(())
}

/// `time_sample_times` retimes samples brought in through a non-identity arc
/// offset identically to the full `time_samples()` map and to `value_at`.
#[test]
fn time_sample_times_retimed() -> Result<()> {
    let stage = in_memory_stage()?;
    // `/Prim` references `/Source` with offset 10, scale 1: a source time `t`
    // composes to stage time `t + 10`.
    stage
        .define_prim("/Source")?
        .create_attribute("x", "double")?
        .set_at(sdf::Value::Double(1.0), usd::TimeCode::new(0.0))?
        .set_at(sdf::Value::Double(3.0), usd::TimeCode::new(10.0))?;
    stage.define_prim("/Prim")?.set_metadata(
        sdf::FieldKey::References.as_str(),
        sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
            prim_path: sdf::path("/Source")?,
            layer_offset: sdf::LayerOffset::new(10.0, 1.0),
            ..Default::default()
        }])),
    )?;

    let attr = stage.attribute("/Prim.x");
    let map = attr.time_samples()?.expect("samples");
    let retimed_keys: Vec<f64> = map.iter().map(|(t, _)| *t).collect();
    assert_eq!(retimed_keys, vec![10.0, 20.0]);
    assert_eq!(attr.time_sample_times()?, retimed_keys);
    assert_eq!(attr.num_time_samples()?, 2);
    // The retimed times read back as live samples through the offset arc.
    assert_eq!(attr.get_at::<f64>(usd::TimeCode::new(10.0))?, Some(1.0));
    assert_eq!(attr.get_at::<f64>(usd::TimeCode::new(20.0))?, Some(3.0));
    Ok(())
}

/// A prim outside the population mask reports no sample times and a zero count,
/// matching the masked behavior of value resolution.
#[test]
fn time_sample_times_masked() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/B"]))
        .in_memory("anon.usda")?;
    stage
        .define_prim("/A")?
        .create_attribute("x", "double")?
        .set_at(sdf::Value::Double(1.0), usd::TimeCode::new(0.0))?
        .set_at(sdf::Value::Double(3.0), usd::TimeCode::new(10.0))?;
    stage.define_prim("/B")?.create_attribute("y", "double")?;

    let masked = stage.attribute("/A.x");
    assert!(masked.time_sample_times()?.is_empty());
    assert_eq!(masked.num_time_samples()?, 0);
    Ok(())
}

/// An arc target on an instance-proxy path redirects to the shared prototype:
/// it finds the arc authored inside the prototype and maps in the prototype's
/// namespace, so a prototype path remaps to the arc source while the proxy
/// path does not reach it.
#[test]
fn edit_target_for_instance_proxy() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_nested_reference.usda"))?;
    let proxy = sdf::path("/World/Inst/OtherChild")?;
    let target = stage.edit_target_for_node(&proxy, EditTargetArc::Reference)?;
    assert!(target.layer_identifier().ends_with("instancing_nested_reference.usda"));

    // The prototype-namespace path remaps to the shared arc source; the proxy
    // path falls outside the mapping's domain, so it does not reach that source.
    let proto = stage
        .prim("/World/Inst")
        .prototype()?
        .expect("instance has a prototype");
    let proto_child = proto.append_path(sdf::path("OtherChild")?)?;
    let source = target.map_to_spec_path(&proto_child).expect("prototype path maps");
    assert_ne!(source, proto_child, "prototype path remaps to the arc source");
    assert_ne!(target.map_to_spec_path(&proxy), Some(source));
    Ok(())
}

// --- Value clips (spec 12.3.4) ---

fn clip_asset(name: &str) -> String {
    format!(
        "{}/vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets/{name}/entry.usd",
        manifest_dir()
    )
}

fn value_f64(stage: &Stage, attr: &str, time: f64) -> Option<f64> {
    match stage
        .attribute(attr)
        .get_at::<sdf::Value>(usd::TimeCode::new(time))
        .expect("value_at")
    {
        Some(sdf::Value::Float(v)) => Some(v as f64),
        Some(sdf::Value::Double(v)) => Some(v),
        Some(sdf::Value::Int64(v)) => Some(v as f64),
        _ => None,
    }
}

fn write_clip_scene(dir: &std::path::Path, root_body: &str, manifest_body: &str, clip_body: &str) -> Result<String> {
    std::fs::write(dir.join("root.usda"), root_body)?;
    std::fs::write(dir.join("manifest.usda"), manifest_body)?;
    std::fs::write(dir.join("clip.usda"), clip_body)?;
    Ok(dir.join("root.usda").to_string_lossy().into_owned())
}

/// A clip overrides a referenced attribute that has no local opinion: the
/// clip's samples win over the reference's (spec 12.3.4.5).
#[test]
fn clip_basic_overrides_reference() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_basic"))?;
    // clip.usd authors size = stage time; the reference authors negatives.
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(10.0));
    assert_eq!(value_f64(&stage, "/Model.size", 7.0), Some(7.0)); // interpolated
    Ok(())
}

/// Local time samples beat clips; a clip beats a referenced attribute that
/// has no local opinion (spec 12.3.4.5).
#[test]
fn clip_strength_local_vs_reference() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_advanced"))?;
    // `local` has a local opinion → local wins (10, not the clip's -10).
    assert_eq!(value_f64(&stage, "/Model.local", 10.0), Some(10.0));
    // `ref` has no local opinion → the clip wins (-10, not the reference's 10).
    assert_eq!(value_f64(&stage, "/Model.ref", 10.0), Some(-10.0));
    Ok(())
}

#[test]
fn clip_local_default_wins() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float localDefault = 3
}
"#,
        r#"#usda 1.0
def "Model"
{
    float localDefault
}
"#,
        r#"#usda 1.0
def "Model"
{
    float localDefault.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(&root)?;
    assert_eq!(value_f64(&stage, "/Model.localDefault", 0.0), Some(3.0));
    Ok(())
}

#[test]
fn clip_anchor_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("sub"))?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    subLayers = [@./sub/weak.usda@]
)

over "Model" (
    clips = {
        dictionary default = {
            double2[] times = [(0, 0)]
        }
    }
)
{
}
"#,
    )?;
    std::fs::write(
        dir.path().join("sub").join("weak.usda"),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("sub").join("manifest.usda"),
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("sub").join("clip.usda"),
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(7.0));
    Ok(())
}

#[test]
fn clip_anchor_reference() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("asset"))?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
def "ShotModel" (
    references = @./asset/model.usda@</Model>
)
{
}
"#,
    )?;
    std::fs::write(
        dir.path().join("asset").join("model.usda"),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("asset").join("manifest.usda"),
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("asset").join("clip.usda"),
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
    assert_eq!(value_f64(&stage, "/ShotModel.size", 0.0), Some(7.0));
    Ok(())
}

#[test]
fn clip_metadata_retimed() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    subLayers = [@./weak.usda@ (offset = 10)]
)
"#,
    )?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
            double2[] times = [(0, 0), (5, 5)]
        }
    }
)
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("manifest.usda"),
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("clip.usda"),
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 0,
        5: 5
    }
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(0.0));
    assert_eq!(value_f64(&stage, "/Model.size", 15.0), Some(5.0));
    Ok(())
}

#[test]
fn clip_initial_jump() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
            double2[] times = [(0, 0), (0, 25), (10, 35)]
        }
    }
)
{
    float size
}
"#,
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 0.0,
        25: 25.0,
        35: 35.0
    }
}
"#,
    )?;

    let stage = Stage::open(&root)?;
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(25.0));
    assert_eq!(value_f64(&stage, "/Model.size", 5.0), Some(30.0));
    Ok(())
}

/// Active-clip selection switches clips by stage time and maps stage time
/// to clip time through the timing curve (spec 12.3.4.3, 12.3.4.4).
#[test]
fn clip_multi_active_switch() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_multi"))?;
    // Stage 10 → clip1 at clip time 10 → -10.
    assert_eq!(value_f64(&stage, "/Model_1.size", 10.0), Some(-10.0));
    // Stage 22 → clip2 active, clip time 6 → -26.
    assert_eq!(value_f64(&stage, "/Model_1.size", 22.0), Some(-26.0));
    Ok(())
}

/// Clip set strength falls back to name order when `clipSets` is unauthored
/// (spec 12.3.4.1): `clip_a` outranks `clip_b` regardless of text order.
#[test]
fn clip_sets_default_order() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_sets"))?;
    // clip_a (primPath /ClipA) wins: attr at stage 0 → 10, not 100.
    assert_eq!(value_f64(&stage, "/DefaultOrderTest.attr", 0.0), Some(10.0));
    assert_eq!(value_f64(&stage, "/DefaultOrderTest.attr", 1.0), Some(20.0));
    Ok(())
}

/// The timing curve maps stage time to clip time, including a jump
/// discontinuity at stage 20 (spec 12.3.4.4, 12.3.4.8).
#[test]
fn clip_timings_curve() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_timings"))?;
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(10.0));
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(15.0));
    assert_eq!(value_f64(&stage, "/Model.size", 20.0), Some(10.0)); // jump → "at and after"
    assert_eq!(value_f64(&stage, "/Model.size", 30.0), Some(15.0));
    Ok(())
}

// --- Sublayer mutation / layer-graph construction ---

/// A weak sublayer carrying one opinion, for the sublayer-mutation tests.
fn opinion_layer(identifier: &str, value: f64) -> Result<sdf::Layer> {
    let mut layer = sdf::Layer::new_anonymous(identifier);
    sdf::AttributeSpec::new(layer.data_mut(), "/A.x", "double", sdf::Variability::Varying, true)?
        .set_default(sdf::Value::Double(value));
    Ok(layer)
}

/// The parent layer's authored `subLayers` asset paths.
fn authored_sublayers(stage: &Stage) -> Vec<String> {
    let root = stage.root_layer();
    root.pseudo_root().and_then(|pr| pr.sublayers()).unwrap_or_default()
}

/// `insert_sub_layer` both composes the new layer's opinion and authors the
/// parent's `subLayers` metadata, so the edit persists on save.
#[test]
fn insert_sub_layer_authors_metadata() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;
    let root_id = stage.root_layer().identifier().to_string();

    let weak = opinion_layer("weak.usda", 5.0)?;
    let weak_id = weak.identifier().to_string();
    stage.insert_sub_layer(&root_id, 0, weak, sdf::LayerOffset::IDENTITY)?;

    assert_eq!(
        stage.attribute("/A.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    assert_eq!(authored_sublayers(&stage), vec![weak_id]);
    Ok(())
}

/// `remove_sub_layer` drops both the composed opinion and the parent's
/// authored `subLayers` entry.
#[test]
fn remove_sub_layer_clears_metadata() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;
    let root_id = stage.root_layer().identifier().to_string();
    let weak = opinion_layer("weak.usda", 5.0)?;
    let weak_id = weak.identifier().to_string();
    stage.insert_sub_layer(&root_id, 0, weak, sdf::LayerOffset::IDENTITY)?;
    assert_eq!(
        stage.attribute("/A.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );

    assert!(stage.remove_sub_layer(&root_id, &weak_id)?, "a sublayer was removed");

    assert_eq!(
        stage.attribute("/A.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None,
        "the removed sublayer's opinion is gone"
    );
    assert!(
        authored_sublayers(&stage).is_empty(),
        "the removed sublayer's subLayers entry is gone"
    );
    Ok(())
}

/// Inserting a sublayer under a file-loaded (and thus editable) parent
/// succeeds and adds exactly one node to the graph.
#[test]
fn insert_sub_layer_into_file_loaded_parent() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(&root, "#usda 1.0\n")?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let root_id = stage.root_layer().identifier().to_string();
    let before = stage.layer_count();

    stage.insert_sub_layer(
        &root_id,
        0,
        opinion_layer("weak.usda", 5.0)?,
        sdf::LayerOffset::IDENTITY,
    )?;

    assert_eq!(
        stage.layer_count(),
        before + 1,
        "the inserted sublayer adds exactly one node"
    );
    Ok(())
}

/// Inserting under a parent that is not in the stage fails with
/// `LayerNotFound` and adds no node.
#[test]
fn insert_sub_layer_missing_parent() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;

    let err = stage
        .insert_sub_layer(
            "nope.usda",
            0,
            opinion_layer("weak.usda", 5.0)?,
            sdf::LayerOffset::IDENTITY,
        )
        .unwrap_err();

    assert!(matches!(err, StageAuthoringError::LayerNotFound { .. }));
    assert_eq!(stage.layer_count(), 1, "no node added for a missing parent");
    Ok(())
}

/// A layer reached through both the session and the root collections is
/// collapsed to one node, keeping the layer count, id set, and root/session
/// split consistent. The session sublayers `shared.usda` and the root
/// sublayers it too, so the four collected layers fold to three nodes.
#[test]
fn from_layers_dedups_order() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(dir.path().join("shared.usda"), "#usda 1.0\n")?;
    std::fs::write(
        dir.path().join("session.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n",
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n")?;

    let stage = Stage::builder()
        .session_layer(dir.path().join("session.usda").to_string_lossy().into_owned())
        .open(root.to_str().expect("utf-8 temp path"))?;

    assert_eq!(
        stage.layer_count(),
        3,
        "the duplicate shared layer collapses to one node"
    );
    let ids = stage.layer_identifiers();
    let unique: std::collections::HashSet<_> = ids.iter().collect();
    assert_eq!(ids.len(), unique.len(), "no duplicate id survives");
    assert!(
        stage.root_layer().identifier().ends_with("root.usda"),
        "the root stays the first non-session layer after dedup"
    );
    Ok(())
}

/// When the stage root is itself reached as a session sublayer, the root slot
/// collapses onto that shared node — but the root must still resolve to the
/// shared layer, not slip to its own dependency or vanish.
#[test]
fn from_layers_root_shared_with_session() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(dir.path().join("dep.usda"), "#usda 1.0\n")?;
    std::fs::write(
        dir.path().join("shared.usda"),
        "#usda 1.0\n(\n    subLayers = [@dep.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("session.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n",
    )?;
    // Open the shared layer itself as the stage root: it is also reached as a
    // session sublayer, so the root slot collapses onto that node.
    let shared = dir.path().join("shared.usda");
    let stage = Stage::builder()
        .session_layer(dir.path().join("session.usda").to_string_lossy().into_owned())
        .open(shared.to_str().expect("utf-8 temp path"))?;

    assert_eq!(stage.layer_count(), 3, "the shared root/session layer is one node");
    assert!(
        stage.root_layer().identifier().ends_with("shared.usda"),
        "the root resolves to the shared layer, not the next dependency"
    );
    Ok(())
}

// --- Stage-tier authoring verified through composed handles ---

#[test]
fn define_prim() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/World")?.set_type_name("Xform")?;
    stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
    assert!(stage.prim("/World").is_defined()?);
    assert!(stage.prim("/World/Mesh").is_defined()?);
    assert_eq!(stage.prim("/World").type_name()?.as_deref(), Some("Xform"));
    assert_eq!(stage.prim("/World/Mesh").type_name()?.as_deref(), Some("Mesh"));
    Ok(())
}

/// A query that misses (the prim is not yet authored) caches the miss; authoring
/// the prim must invalidate that cache so the next query sees it.
#[test]
fn authoring_invalidates_cached_miss() -> Result<()> {
    let stage = in_memory_stage()?;
    assert!(!stage.prim("/World").is_valid()?);

    stage.define_prim("/World")?.set_type_name("Xform")?;

    assert!(stage.prim("/World").is_valid()?);
    assert_eq!(stage.prim("/World").type_name()?.as_deref(), Some("Xform"));
    Ok(())
}

#[test]
fn override_prim() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.override_prim("/A/B")?;
    assert_eq!(stage.prim("/A").specifier()?, Some(sdf::Specifier::Over));
    assert_eq!(stage.prim("/A/B").specifier()?, Some(sdf::Specifier::Over));
    Ok(())
}

// --- Adapted from in-module tests: value resolution, existence, authoring ---

/// A direct arc to a `permission = private` site is retained as a
/// composition error while the prim still composes (spec 10.3.3).
#[test]
fn arc_permission_denied_surfaced() -> Result<()> {
    let path = format!(
        "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             ErrorPermissionDenied_root/usda/root.usd",
        manifest_dir()
    );
    let stage = Stage::builder().open(&path)?;

    // Querying /Model composes the private inherit and retains the error.
    assert!(
        stage
            .prim("/Model")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "attr"),
        "private inherit must stay visible"
    );
    assert!(
        stage
            .composition_errors()
            .iter()
            .any(|error| matches!(error, pcp::Error::ArcPermissionDenied { .. })),
        "composition_errors should contain the permission error"
    );

    Ok(())
}

/// Reading a field from a single-layer stage should return the authored value.
#[test]
fn field_single_layer() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    // CubeInactive composes as inactive; CubeActive as active.
    assert!(!stage.prim("/World/CubeInactive").is_active()?);
    assert!(stage.prim("/World/CubeActive").is_active()?);

    Ok(())
}

// --- Sublayer composition ---

/// sublayer_override.usda sublayers sublayer_base.usda. Both layers define
/// /World/Cube but with different displayColor values. The stronger (override)
/// layer's opinion should win (first-opinion-wins rule).
#[test]
fn sublayer_stronger_opinion_wins() -> Result<()> {
    let path = fixture_path("sublayer_override.usda");
    let stage = Stage::open(&path)?;

    assert_eq!(stage.layer_count(), 2);

    // /World/Cube.primvars:displayColor is overridden to blue [(0,0,1)] in
    // the stronger layer, base has red [(1,0,0)].
    let prop_path = sdf::Path::new("/World/Cube")?.append_property("primvars:displayColor")?;
    let value = stage.attribute(&prop_path).get::<sdf::Value>()?;
    assert!(value.is_some(), "displayColor should have a composed value");

    // The composed value must come from the stronger layer (blue),
    // not the weaker layer (red). Verify by checking it's not the base red.
    let value = value.unwrap();
    let base_red = sdf::Value::Vec3fVec(vec![gf::vec3f(1.0, 0.0, 0.0)]);
    assert_ne!(value, base_red, "stronger layer opinion should win over weaker");

    Ok(())
}

/// The active.usda vendor test has prims with active=true/false metadata.
/// Verify field resolution returns the correct authored values.
#[test]
fn field_active_metadata() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    assert!(!stage.prim("/World/CubeInactive").is_active()?);
    assert!(stage.prim("/World/CubeActive").is_active()?);

    Ok(())
}

// --- Reference composition ---

/// An external reference with defaultPrim should pull the referenced prim's
/// children into the referencing prim's namespace.
/// ref_external.usda: /World/MyPrim references ref_target.usda (defaultPrim="Source").
/// ref_target.usda defines /Source/Child with displayColor.
#[test]
fn reference_external_default_prim() -> Result<()> {
    let path = fixture_path("ref_external.usda");
    let stage = Stage::open(&path)?;

    // /World/MyPrim should exist via the reference.
    assert!(stage.prim("/World/MyPrim").is_valid()?);

    // /World/MyPrim/Child should be reachable via namespace remapping.
    let children = child_names(&stage, "/World/MyPrim")?;
    assert!(
        children.contains(&"Child".to_string()),
        "referenced children should be visible"
    );

    Ok(())
}

/// class_inherit.usda: cubeWithSetColor inherits from /_myClass but
/// overrides displayColor locally. Local opinion (red) should win
/// over the inherited opinion (green).
#[test]
fn inherit_local_opinion_wins() -> Result<()> {
    let path = composition_path("class_inherit.usda");
    let stage = Stage::open(&path)?;

    // The local displayColor (red) should win over inherited (green).
    let prop = sdf::Path::new("/World/cubeWithSetColor")?.append_property("primvars:displayColor")?;
    let value = stage.attribute(&prop).get::<sdf::Value>()?;
    assert!(value.is_some());

    // Verify it's the local red, not the inherited green.
    let green = sdf::Value::Vec3fVec(vec![gf::vec3f(0.0, 0.8, 0.0)]);
    assert_ne!(value.unwrap(), green, "local opinion should win over inherited");

    Ok(())
}

// --- Variant selection ---

/// The local opinion on radius (1) should be stronger than the variant's (2).
#[test]
fn variant_local_opinion_wins() -> Result<()> {
    let path = format!(
        "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
        manifest_dir()
    );
    let stage = Stage::open(&path)?;

    // The local radius=1 should win over variant radius=2.
    let prop = sdf::Path::new("/World/Sphere")?.append_property("radius")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(1.0), "local opinion (1) should win over variant (2)");

    Ok(())
}

// --- Specialize composition ---

/// The local opinion on displayColor (yellow) should win over the
/// specialized source's displayColor (red).
#[test]
fn specialize_local_opinion_wins() -> Result<()> {
    let path = composition_path("inherit_and_specialize.usda");
    let stage = Stage::open(&path)?;

    let prop = sdf::Path::new("/World/cubeScene/specializes")?.append_property("primvars:displayColor")?;
    let value = stage.attribute(&prop).get::<sdf::Value>()?;
    assert!(value.is_some());

    // Local is yellow (0.8, 0.8, 0), source is red (0.8, 0, 0).
    let red = sdf::Value::Vec3fVec(vec![gf::vec3f(0.8, 0.0, 0.0)]);
    assert_ne!(value.unwrap(), red, "local opinion should win over specialized");

    Ok(())
}

/// A prim with `instanceable = true` composes as instanceable.
#[test]
fn instanceable_true_parses_and_is_readable() -> Result<()> {
    let path = fixture_path("instanceable_metadata.usda");
    let stage = Stage::open(&path)?;

    assert!(stage.prim("/Root/InstancePrototype").is_instanceable()?);

    Ok(())
}

/// A prim with `instanceable = false` composes as not instanceable.
#[test]
fn instanceable_false_parses_and_is_readable() -> Result<()> {
    let path = fixture_path("instanceable_metadata.usda");
    let stage = Stage::open(&path)?;

    assert!(!stage.prim("/Root/NotInstanceable").is_instanceable()?);

    Ok(())
}

/// A prim without `instanceable` metadata defaults to not instanceable.
#[test]
fn instanceable_absent_defaults_false() -> Result<()> {
    let path = fixture_path("instanceable_metadata.usda");
    let stage = Stage::open(&path)?;

    assert!(!stage.prim("/Root").is_instanceable()?);

    Ok(())
}

// --- Variant fallback selection ---

/// A variant fallback should select the specified variant when no authored
/// selection exists. The prim should expose opinions from the fallback variant.
#[test]
fn variant_fallback_selects_preferred() -> Result<()> {
    let path = fixture_path("variant_fallback.usda");
    let fallbacks = pcp::VariantFallbackMap::new().add("shadingComplexity", ["simple"]);
    let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

    // /NoSelection has no authored selection. With fallback "simple",
    // the complexity field should be 0.5 (not 1.0 from "full").
    let prop = sdf::Path::new("/NoSelection")?.append_property("complexity")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(0.5), "fallback 'simple' should give complexity=0.5");

    Ok(())
}

/// An authored selection should take priority over a variant fallback at the
/// stage level.
#[test]
fn variant_fallback_does_not_override_authored() -> Result<()> {
    let path = fixture_path("variant_fallback.usda");
    let fallbacks = pcp::VariantFallbackMap::new().add("shadingComplexity", ["none"]);
    let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

    // /Root has authored selection "full". Even with fallback "none",
    // the authored selection should win.
    let prop = sdf::Path::new("/Root")?.append_property("complexity")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(1.0), "authored 'full' should win over fallback 'none'");

    Ok(())
}

// --- Inherit child propagation ---

/// A prim that inherits a class should expose the class's children even
/// when the inheriting prim has no local override for them.
#[test]
fn inherit_child_exists_without_local_override() -> Result<()> {
    let path = fixture_path("inherit_child_propagation.usda");
    let stage = Stage::open(&path)?;

    // /Instance inherits /BaseClass which has child /BaseClass/Child.
    // /Instance/Child should exist even though Instance has no local "Child".
    let children = child_names(&stage, "/Instance")?;
    assert!(
        children.contains(&"Child".to_string()),
        "inherited child should appear: got {children:?}"
    );

    // The inherited property should be accessible.
    assert!(
        stage
            .prim("/Instance/Child")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "name"),
        "property from inherited child should be visible"
    );

    Ok(())
}

/// Nested children from an inherited class should propagate through
/// multiple levels even without local overrides at any level.
#[test]
fn inherit_nested_child_propagation() -> Result<()> {
    let path = fixture_path("inherit_nested_child.usda");
    let stage = Stage::open(&path)?;

    // /Prim inherits /Base. /Base/A/B exists with val=1.0.
    // /Prim/A should exist, /Prim/A/B should exist.
    let a_children = child_names(&stage, "/Prim")?;
    assert!(
        a_children.contains(&"A".to_string()),
        "first-level child: got {a_children:?}"
    );

    let b_children = child_names(&stage, "/Prim/A")?;
    assert!(
        b_children.contains(&"B".to_string()),
        "second-level child: got {b_children:?}"
    );

    assert!(
        stage
            .prim("/Prim/A/B")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "val"),
        "deeply nested inherited property should be visible"
    );

    Ok(())
}

/// Children should propagate through an inherit chain (Leaf → Middle → GrandBase).
#[test]
fn inherit_chain_child_propagation() -> Result<()> {
    let path = fixture_path("inherit_chain_child.usda");
    let stage = Stage::open(&path)?;

    // /Leaf inherits /Middle which inherits /GrandBase.
    // /GrandBase/Deep exists with x=42. /Leaf/Deep should exist.
    let children = child_names(&stage, "/Leaf")?;
    assert!(
        children.contains(&"Deep".to_string()),
        "chain-inherited child: got {children:?}"
    );

    assert!(
        stage
            .prim("/Leaf/Deep")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "x"),
        "property from chain-inherited child should be visible"
    );

    Ok(())
}

/// A session layer's opinions should be stronger than the root layer's.
#[test]
fn session_layer_opinion_wins() -> Result<()> {
    let stage = open_with_session()?;

    assert!(stage.has_session_layer());
    assert_eq!(stage.layer_count(), 2);
    assert!(stage
        .session_layer()
        .expect("configured session layer")
        .identifier()
        .ends_with("session_layer.usda"));

    let prop = sdf::Path::new("/World")?.append_property("radius")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(99.0), "session layer opinion should win");

    Ok(())
}

/// The session layer can add properties not present in the root layer.
#[test]
fn session_layer_adds_properties() -> Result<()> {
    let stage = open_with_session()?;

    let prop = sdf::Path::new("/World")?.append_property("visibility")?;
    let value = stage.attribute(&prop).get::<String>()?;
    assert_eq!(value, Some("hidden".to_string()));

    Ok(())
}

/// The root layer's properties not overridden by the session layer
/// should still be accessible.
#[test]
fn session_layer_preserves_root_opinions() -> Result<()> {
    let stage = open_with_session()?;

    let prop = sdf::Path::new("/World")?.append_property("name")?;
    let value = stage.attribute(&prop).get::<String>()?;
    assert_eq!(value, Some("root".to_string()));

    Ok(())
}

#[test]
fn mask_traverse() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/World/ActiveParent/Child"]))
        .open("fixtures/stage_queries.usda")?;

    assert_eq!(
        stage.root_prims()?.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        ["World"]
    );
    assert_eq!(child_names(&stage, "/World")?, vec!["ActiveParent"]);
    assert_eq!(child_names(&stage, "/World/ActiveParent")?, vec!["Child"]);

    assert!(stage.prim("/World").is_valid()?);
    assert!(stage.prim("/World/ActiveParent/Child").is_valid()?);
    assert!(!stage.prim("/World/Group").is_valid()?);
    assert_eq!(stage.prim("/World/Group").kind()?, None);

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;
    assert_eq!(
        prims,
        vec!["/World", "/World/ActiveParent", "/World/ActiveParent/Child"]
    );
    Ok(())
}

#[test]
fn mask_skips_dependency() -> Result<()> {
    let path = composition_path("references/reference_invalid.usda");
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/World/cube"]))
        .open(&path)?;

    assert_eq!(
        stage.root_prims()?.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        ["World"]
    );
    assert_eq!(child_names(&stage, "/World")?, vec!["cube"]);
    assert!(!stage.prim("/World/invalid_reference").is_valid()?);
    Ok(())
}

/// `Stage::custom_layer_data` reads the root layer's `customLayerData`
/// dictionary (C++ `UsdStage::GetRootLayer()->GetCustomLayerData`).
#[test]
fn custom_layer_data() -> Result<()> {
    let stage = in_memory_stage()?;
    assert!(stage.custom_layer_data()?.is_none());

    let dict = sdf::Value::Dictionary([("tool".to_string(), sdf::Value::String("rs".into()))].into());
    stage.set_custom_layer_data(dict)?;

    let Some(sdf::Value::Dictionary(read)) = stage.custom_layer_data()? else {
        panic!("customLayerData should resolve to a dictionary");
    };
    assert_eq!(read.get("tool"), Some(&sdf::Value::String("rs".into())));
    Ok(())
}

#[test]
fn create_attribute() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Sphere")?.set_type_name("Sphere")?;
    stage.create_attribute("/Sphere.radius", "double")?;

    let attr = stage.attribute("/Sphere.radius");
    assert_eq!(attr.type_name()?.as_deref(), Some("double"));
    assert!(attr.is_custom()?, "generic attributes are authored custom");
    // The property composes as an attribute (not a relationship).
    let radius = sdf::Path::new("/Sphere.radius")?;
    let attrs = stage.prim("/Sphere").attributes()?;
    assert!(attrs.iter().any(|a| a.path() == &radius));
    Ok(())
}

#[test]
fn create_relationship() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
    let rel = stage
        .create_relationship("/Mesh.material:binding")?
        .set_variability(sdf::Variability::Uniform)?;

    assert!(rel.is_custom()?, "generic relationships are authored custom");
    // The property composes as a relationship (not an attribute).
    let binding = sdf::Path::new("/Mesh.material:binding")?;
    let rels = stage.prim("/Mesh").relationships()?;
    assert!(rels.iter().any(|r| r.path() == &binding));
    Ok(())
}

/// `defaultPrim` writes target the root layer regardless of `EditTarget`
/// (mirrors C++ `UsdStage::SetDefaultPrim` going through `GetRootLayer`).
/// In-memory root with a file-loaded session layer; setting the edit
/// target to the read-only session layer must not block the write.
#[test]
fn default_prim_targets_root() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    let session_id = stage.session_layer().expect("session layer").identifier().to_string();
    stage.set_edit_target(EditTarget::for_layer(session_id))?;
    stage.set_default_prim("World")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

/// Exercises `StageBuilder::in_memory`'s session-layer branch: the
/// anonymous root must end up at `session_layer_count`, the edit target
/// must point there, and authoring on the in-memory root must work
/// (with the session layer remaining read-only).
#[test]
fn in_memory_session_layer() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    assert!(stage.has_session_layer());
    assert_eq!(stage.layer_count(), 2);
    assert_eq!(stage.edit_target().layer_identifier(), stage.root_layer().identifier());
    stage.define_prim("/World")?.set_type_name("Xform")?;
    assert!(stage.prim("/World").is_defined()?);
    Ok(())
}

/// `edit_context` restores the previous edit target when the guard drops.
#[test]
fn edit_context_restores_on_drop() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    let root_id = stage.root_layer().identifier().to_string();
    let session_id = stage.session_layer().expect("session layer").identifier().to_string();
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    {
        let _ctx = stage.edit_context(EditTarget::for_layer(session_id.clone()))?;
        assert_eq!(stage.edit_target().layer_identifier(), session_id);
    }
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    Ok(())
}

/// The guard restores the target even when the scope exits early via `?`.
#[test]
fn edit_context_restores_on_error() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    let root_id = stage.root_layer().identifier().to_string();
    let session_id = stage.session_layer().expect("session layer").identifier().to_string();
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    let authored: std::result::Result<(), StageAuthoringError> = (|| {
        let _ctx = stage.edit_context(EditTarget::for_layer(session_id))?;
        // Authoring a prim at a property path is invalid; the write fails and
        // `?` returns from this closure with the guard still in scope.
        stage.define_prim("/A.x")?;
        Ok(())
    })();
    assert!(authored.is_err());
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    Ok(())
}

/// A significant edit inside a variant must invalidate the composed
/// (variant-stripped) prim, whose cache key is not on the variant path's
/// ancestor chain.
#[test]
fn variant_edit_invalidates_stripped_path() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.edit_target().layer_identifier().to_string();
    stage.define_prim("/Prim")?;

    // Cache a composed miss at the scene path.
    assert!(!stage.prim("/Prim/child").is_valid()?);
    assert!(stage.is_indexed(&sdf::path("/Prim/child")?));

    // Author the child inside the variant: `/Prim/child` -> `/Prim{set=sel}child`.
    stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
    stage.define_prim("/Prim/child")?;

    // The stripped composed key must be dropped so the next query rebuilds.
    assert!(!stage.is_indexed(&sdf::path("/Prim/child")?));
    Ok(())
}

#[test]
fn clip_skips_missing_attr() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
}
"#,
        r#"#usda 1.0
def "Model"
{
    float ghost
}
"#,
        r#"#usda 1.0
def "Model"
{
    float ghost.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(&root)?;
    assert!(
        !stage
            .prim("/Model")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "ghost"),
        "the clip must not fabricate an attribute"
    );
    assert_eq!(
        stage
            .attribute("/Model.ghost")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );
    Ok(())
}
