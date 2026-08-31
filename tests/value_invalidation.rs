//! Cached-answer invalidation: an `AttributeQuery` that resolved once must never
//! replay a source the stage has moved on from.
//!
//! Each test warms a query, mutates the stage, and requires the query to agree
//! with a freshly resolved read — the differential shape, since what matters is
//! not which value is right but that the two never diverge.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::path::Path as FsPath;
use std::rc::Rc;

use openusd::Result;
use openusd::usd::{InitialLoadSet, LoadPolicy, Stage};
use openusd::{sdf, usd};

/// Reads `path` both through a warmed query and through a fresh attribute
/// handle, requiring the two to agree, and returns the value.
fn agreed(stage: &Stage, query: &usd::AttributeQuery, path: &str, time: f64) -> Result<Option<f64>> {
    let replayed = query.get_at::<f64>(usd::TimeCode::new(time))?;
    let resolved = stage.attribute(path)?.get_at::<f64>(usd::TimeCode::new(time))?;
    assert_eq!(replayed, resolved, "the replayed source diverged from a fresh read");
    Ok(replayed)
}

/// The body of the clip layer these tests read: one attribute the clip set
/// schedules at time 0. Written verbatim by each test that needs a clip on disk.
const CLIP_BODY: &str = "#usda 1.0\n\ndef \"Clip\"\n{\n    double size.timeSamples = {\n        0: 42.0,\n    }\n}\n";

/// The identifier the stage holds the layer whose file name is `leaf` under, for
/// an edit that must reach composition through the graph rather than through a
/// second `sdf::Layer` opened alongside it.
fn layer_by_leaf(stage: &Stage, leaf: &str) -> String {
    stage
        .layer_stack()
        .into_iter()
        .find(|id| FsPath::new(id).ends_with(leaf))
        .expect("layer is loaded")
}

/// The file name at the end of a layer identifier, for reporting which layer a
/// composed site came from without depending on how the stage canonicalized its
/// path.
fn leaf_of(identifier: &str) -> String {
    FsPath::new(identifier)
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default()
}

/// A clip layer that joins the graph with no edit of its own must still reach
/// the queries sourcing from it.
///
/// The clip's asset does not resolve when the stage opens, so the attribute
/// resolves to nothing and the query memoizes that empty source.
/// Loading an unrelated payload interns the very layer the clip set names: no
/// change round runs over it, and the load's own invalidation drops only the
/// payload's subtree, so the clip cache noticing the join is the only thing that
/// can restale `/Model`.
#[test]
fn clip_join_flips_source() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0

def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            string primPath = "/Clip"
            double2[] active = [(0, 0)]
        }
    }
)
{
    double size
}

def "Holder" (
    payload = @./clip.usda@</Clip>
)
{
}
"#,
    )?;

    let stage = Stage::builder()
        .load(InitialLoadSet::LoadNone)
        .open(dir.path().join("root.usda").to_str().unwrap())?;
    let query = stage.attribute_query("/Model.size")?;
    assert_eq!(
        agreed(&stage, &query, "/Model.size", 0.0)?,
        None,
        "the clip cannot be opened, so nothing sources the attribute"
    );

    // The clip layer appears, and something unrelated pulls it into the graph.
    fs::write(dir.path().join("clip.usda"), CLIP_BODY)?;
    stage.load("/Holder", LoadPolicy::WithDescendants)?;
    // Composition is demand-driven, so the payload's layer joins when something
    // composes the prim that pulls it in — not when the rule changes.
    stage.prim("/Holder")?.type_name()?;

    assert_eq!(
        agreed(&stage, &query, "/Model.size", 0.0)?,
        Some(42.0),
        "the joined layer is the clip the set named, so the clip now sources the value"
    );
    Ok(())
}

/// A clip layer that is also a graph layer is read live: editing it through the
/// stage moves the clip-sourced value, where a cached copy of the file would
/// have kept answering with what was on disk.
#[test]
fn clip_layer_edit_reaches() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    subLayers = [
        @./clip.usda@
    ]
)

def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            string primPath = "/Clip"
            double2[] active = [(0, 0)]
        }
    }
)
{
    double size
}
"#,
    )?;
    fs::write(dir.path().join("clip.usda"), CLIP_BODY)?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let query = stage.attribute_query("/Model.size")?;
    assert_eq!(agreed(&stage, &query, "/Model.size", 0.0)?, Some(42.0));

    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let resynced = resynced.clone();
        stage.add_sink(move |_stage: &Stage, change: &usd::CommittedChange<'_>| {
            resynced.borrow_mut().extend(change.resynced.iter().cloned());
        })
    };

    // Author into the clip layer through the stage. The clip cache and the graph
    // must be looking at one layer for this to be visible at all.
    let clip_identifier = layer_by_leaf(&stage, "clip.usda");
    stage
        .layer_mut(&clip_identifier)
        .expect("just found in the layer stack")
        .edit(|edit| {
            edit.attribute_mut(&sdf::path("/Clip.size")?)
                .expect("the clip layer parsed")
                .expect("the clip authors the attribute")
                .set_time_sample(0.0, sdf::Value::Double(7.0));
            Ok(())
        })?;

    assert_eq!(
        agreed(&stage, &query, "/Model.size", 0.0)?,
        Some(7.0),
        "the edited clip layer is the one the clip set reads"
    );
    // A clip sources values anywhere below its anchor, so an observer is told to
    // re-resolve the anchor's subtree rather than one property.
    assert!(
        resynced.borrow().contains(&sdf::path("/Model")?),
        "the clip set's anchor must be reported, got {:?}",
        resynced.borrow()
    );
    Ok(())
}

/// A manifest synthesized from a clip set's clips is derived from what those
/// clips declare, so editing one regenerates it: an attribute the clips did not
/// carry becomes clip-sourced once one of them does.
#[test]
fn clip_manifest_regenerates() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    subLayers = [
        @./clip.usda@
    ]
)

def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            string primPath = "/Clip"
            double2[] active = [(0, 0)]
        }
    }
)
{
    double size
    double other
}
"#,
    )?;
    fs::write(dir.path().join("clip.usda"), CLIP_BODY)?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let query = stage.attribute_query("/Model.other")?;
    assert_eq!(
        agreed(&stage, &query, "/Model.other", 0.0)?,
        None,
        "the synthesized manifest declares only what the clip carries"
    );

    let clip_identifier = layer_by_leaf(&stage, "clip.usda");
    stage
        .layer_mut(&clip_identifier)
        .expect("just found in the layer stack")
        .edit(|edit| {
            sdf::AttributeSpec::new(
                edit.data_mut(),
                "/Clip.other",
                "double",
                sdf::Variability::Varying,
                false,
            )?
            .set_time_sample(0.0, sdf::Value::Double(7.0));
            Ok(())
        })?;

    assert_eq!(
        agreed(&stage, &query, "/Model.other", 0.0)?,
        Some(7.0),
        "the manifest regenerates, so the clip now declares — and sources — the attribute"
    );
    Ok(())
}

/// A value authored at a referenced site reaches the prims that read it through
/// the reference, not just the prim it was authored on.
#[test]
fn value_edit_reaches_referrer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0

def "Source"
{
    def "Inner"
    {
        double x = 1
    }
}

def "Ref" (
    references = </Source>
)
{
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let query = stage.attribute_query("/Ref/Inner.x")?;
    assert_eq!(agreed(&stage, &query, "/Ref/Inner.x", 0.0)?, Some(1.0));

    stage.attribute("/Source/Inner.x")?.set(sdf::Value::Double(5.0))?;

    assert_eq!(
        agreed(&stage, &query, "/Ref/Inner.x", 0.0)?,
        Some(5.0),
        "the referrer composes the edited site"
    );
    Ok(())
}

/// A relocate renames a referenced prim in the referrer's namespace, so the
/// composed path an edit lands at is not the authored path with the arc's root
/// swapped in. The value tier follows the rename through the dependent's own
/// composition graph, so the query at the relocated path sees the edit.
///
/// This is the public-query half: that the translated victim is *reached*. How
/// narrowly it is reached — that nothing above it is swept in — is
/// `value_edit_restale_radius`'s job.
#[test]
fn relocated_value_edit_reaches() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    relocates = {
        </Ref/Inner>: </Ref/Moved>
    }
)

def "Source"
{
    def "Inner"
    {
        double x = 1
    }
}

def "Ref" (
    references = </Source>
)
{
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let query = stage.attribute_query("/Ref/Moved.x")?;
    assert_eq!(
        agreed(&stage, &query, "/Ref/Moved.x", 0.0)?,
        Some(1.0),
        "the relocate moved the referenced prim, and its value came with it"
    );

    stage.attribute("/Source/Inner.x")?.set(sdf::Value::Double(5.0))?;

    assert_eq!(
        agreed(&stage, &query, "/Ref/Moved.x", 0.0)?,
        Some(5.0),
        "the edited site composes at the relocated path"
    );
    Ok(())
}

/// An opinion authored inside a variant lands at `/P{v=x}Child.size`, which
/// composes into `/P/Child` — a path the authored one does not prefix. A query
/// warmed on the composed path before the value existed must still pick it up.
#[test]
fn variant_authoring_reaches_stripped() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0

def "P" (
    variants = {
        string v = "x"
    }
    prepend variantSets = "v"
)
{
    variantSet "v" = {
        "x" {
            def "Child"
            {
                double size
            }
        }
    }
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let query = stage.attribute_query("/P/Child.size")?;
    assert_eq!(agreed(&stage, &query, "/P/Child.size", 0.0)?, None);

    let root = stage.root_layer().identifier().to_owned();
    stage.layer_mut(&root).expect("loaded").edit(|edit| {
        edit.attribute_mut(&sdf::path("/P{v=x}Child.size")?)
            .expect("the root layer parsed")
            .expect("the variant declares the attribute")
            .set_default(sdf::Value::Double(3.0));
        Ok(())
    })?;

    assert_eq!(
        agreed(&stage, &query, "/P/Child.size", 0.0)?,
        Some(3.0),
        "the variant-authored opinion composes at the stripped path"
    );
    Ok(())
}

/// Layer-stack mutations move which opinions compose without editing any of
/// them. A warmed query must track every one of them, so the sequence below
/// checks agreement after each step rather than only at the end.
#[test]
fn stack_mutations_keep_current() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\n(\n    subLayers = [\n        @./weak.usda@\n    ]\n)\n\ndef \"B\"\n{\n    double y = 2\n}\n",
    )?;
    fs::write(
        dir.path().join("weak.usda"),
        "#usda 1.0\n\ndef \"A\"\n{\n    double x = 1\n}\n",
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let a = stage.attribute_query("/A.x")?;
    let b = stage.attribute_query("/B.y")?;
    assert_eq!(agreed(&stage, &a, "/A.x", 0.0)?, Some(1.0));
    assert_eq!(agreed(&stage, &b, "/B.y", 0.0)?, Some(2.0));

    let weak = layer_by_leaf(&stage, "weak.usda");

    stage.mute_layer(weak.clone());
    assert_eq!(
        agreed(&stage, &a, "/A.x", 0.0)?,
        None,
        "the muted layer's opinion is gone"
    );
    assert_eq!(agreed(&stage, &b, "/B.y", 0.0)?, Some(2.0));

    stage.unmute_layer(&weak);
    assert_eq!(agreed(&stage, &a, "/A.x", 0.0)?, Some(1.0));

    // A stronger opinion in the root layer wins over the sublayer's; the
    // attribute is declared there for the first time, which is a spec add as
    // well as a value.
    stage.create_attribute("/A.x", "double")?.set(sdf::Value::Double(3.0))?;
    assert_eq!(agreed(&stage, &a, "/A.x", 0.0)?, Some(3.0));

    // Root metadata that retimes the stack, and one that retargets expressions:
    // neither moves these values, and both must leave the queries agreeing.
    stage.set_time_codes_per_second(48.0)?;
    assert_eq!(agreed(&stage, &a, "/A.x", 0.0)?, Some(3.0));
    stage.set_expression_variables(HashMap::from([(
        "WHICH".to_string(),
        sdf::Value::String("b".to_string()),
    )]))?;
    assert_eq!(agreed(&stage, &a, "/A.x", 0.0)?, Some(3.0));
    assert_eq!(agreed(&stage, &b, "/B.y", 0.0)?, Some(2.0));
    Ok(())
}

/// A cached source holds handles into the graph — the layer stack its winning
/// opinion composed in. Unloading a payload retires the stack it was the last
/// owner of, so replaying a query whose source named it must recheck its stamp
/// before touching the site, and an unrelated query must keep working.
#[test]
fn reclaimed_stack_replays_safely() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("payload.usda"),
        "#usda 1.0\n\ndef \"Inner\"\n{\n    double x = 1\n}\n",
    )?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0

def "Holder" (
    payload = @./payload.usda@</Inner>
)
{
}

def "Other"
{
    double y = 2
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let held = stage.attribute_query("/Holder.x")?;
    let other = stage.attribute_query("/Other.y")?;
    assert_eq!(agreed(&stage, &held, "/Holder.x", 0.0)?, Some(1.0));
    assert_eq!(agreed(&stage, &other, "/Other.y", 0.0)?, Some(2.0));

    stage.unload("/Holder")?;

    assert_eq!(
        agreed(&stage, &held, "/Holder.x", 0.0)?,
        None,
        "the payload's opinion is unloaded, and replaying must not read the retired stack"
    );
    assert_eq!(
        agreed(&stage, &other, "/Other.y", 0.0)?,
        Some(2.0),
        "an unrelated query keeps replaying across the reclamation"
    );
    Ok(())
}

/// An inert `over` can fill a site a reference culled as empty, which makes the
/// referrer's composed child exist where it did not. That is a change of
/// existence, so the dependent is reported as a resync rather than as an info
/// change on the authored path alone.
#[test]
fn unculled_dependent_resyncs() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(dir.path().join("source.usda"), "#usda 1.0\n\ndef \"Source\"\n{\n}\n")?;
    fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\n\ndef \"Ref\" (\n    references = @./source.usda@</Source>\n)\n{\n}\n",
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    assert!(!stage.prim("/Ref/Child")?.is_valid()?, "nothing composes there yet");

    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let resynced = resynced.clone();
        stage.add_sink(move |_stage: &Stage, change: &usd::CommittedChange<'_>| {
            resynced.borrow_mut().extend(change.resynced.iter().cloned());
        })
    };

    // An `over` in the referenced layer: inert, so the spec tier handles it. The
    // target is not in the root layer stack, so its identifier comes from the
    // composed prim's own spec stack.
    let source = stage
        .prim("/Ref")?
        .prim_stack()?
        .into_iter()
        .map(|site| site.layer)
        .find(|id| FsPath::new(id).ends_with("source.usda"))
        .expect("the reference target contributes a spec");
    stage.layer_mut(&source).expect("loaded").edit(|edit| {
        sdf::PrimSpec::new(edit.data_mut(), "/Source/Child", sdf::Specifier::Over, "")?;
        Ok(())
    })?;

    assert!(
        stage.prim("/Ref/Child")?.is_valid()?,
        "the referrer's child composes once the site carries a spec"
    );
    assert!(
        resynced.borrow().contains(&sdf::path("/Ref/Child")?),
        "the dependent whose existence moved must be resynced, got {:?}",
        resynced.borrow()
    );
    Ok(())
}

/// A spec-tier edit splices the affected prims' memoized spec stacks instead of
/// rebuilding them, and the memo has to end up where a fresh composition would.
/// Checked on the edited prim and on a *dependent* reached through a reference,
/// which is the case the splice exists for: it keeps that prim's referenced-node
/// entries rather than re-deriving the whole stack.
#[test]
fn spec_edit_matches_reopen() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("source.usda"),
        "#usda 1.0\n\ndef \"Src\"\n{\n    double x = 1\n}\n",
    )?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    subLayers = [
        @./weak.usda@
    ]
)

def "Ref" (
    references = @./source.usda@</Src>
)
{
}
"#,
    )?;
    fs::write(dir.path().join("weak.usda"), "#usda 1.0\n")?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    // Warm both memos before the edit.
    let _ = stage.prim("/Ref")?.prim_stack()?;

    // An inert `over` in the sublayer: the spec tier refreshes rather than drops.
    let weak = layer_by_leaf(&stage, "weak.usda");
    stage.layer_mut(&weak).expect("loaded").edit(|edit| {
        sdf::PrimSpec::new(edit.data_mut(), "/Ref", sdf::Specifier::Over, "")?;
        Ok(())
    })?;
    let sites = |stage: &Stage| -> Result<Vec<(String, sdf::Path)>> {
        Ok(stage
            .prim("/Ref")?
            .prim_stack()?
            .into_iter()
            .map(|site| (leaf_of(&site.layer), site.path))
            .collect())
    };
    let spliced = sites(&stage)?;

    // The same content composed from scratch. The edit lives in memory until the
    // layer is saved, so the reopened stage would otherwise read the old file.
    stage.layer_mut(&weak).expect("loaded").save()?;
    let reopened = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let fresh = sites(&reopened)?;

    assert_eq!(spliced, fresh, "the spliced stack must be what a fresh build composes");
    assert!(
        spliced.iter().any(|(layer, _)| layer == "weak.usda"),
        "the authored `over` joined the stack, got {spliced:?}",
    );
    assert!(
        spliced.iter().any(|(layer, _)| layer == "source.usda"),
        "the referenced node kept its entry, got {spliced:?}",
    );
    Ok(())
}

/// The end-to-end case where instance-proxy redirection and a relocate meet: a
/// query on an instance proxy replays a source resolved in the *prototype*
/// namespace, so a translation that lands in the instance namespace instead
/// would leave the revision that query holds unstamped, and it would replay a
/// stale source forever.
#[test]
fn relocated_proxy_restales() -> Result<()> {
    let dir = tempfile::tempdir()?;
    fs::write(
        dir.path().join("source.usda"),
        "#usda 1.0\n\ndef \"Source\"\n{\n    def \"Inner\"\n    {\n        double x = 1\n    }\n}\n",
    )?;
    // The relocate lives in the *referenced* stack so it is part of the shared
    // content a prototype composes, and it renames a prim that stack references
    // in turn — an opinion at a relocation source is invalid in the stack that
    // relocates it.
    fs::write(
        dir.path().join("model.usda"),
        r#"#usda 1.0
(
    relocates = {
        </Model/Inner>: </Model/Moved>
    }
)

def "Model" (
    references = @./source.usda@</Source>
)
{
}
"#,
    )?;
    fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0

def "Inst" (
    references = @./model.usda@</Model>
    instanceable = true
)
{
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    let moved = stage.prim("/Inst/Moved")?;
    assert!(
        moved.is_instance_proxy()?,
        "the query must resolve through a prototype for this to test the redirect"
    );
    let query = stage.attribute_query("/Inst/Moved.x")?;
    assert_eq!(agreed(&stage, &query, "/Inst/Moved.x", 0.0)?, Some(1.0));

    // The answer is resolved in the prototype's namespace: the proxy path has
    // no cached index of its own, so a restale landing there would never reach
    // the revision this query holds.
    let attribute = stage.attribute("/Inst/Moved.x")?;
    assert!(
        attribute.resolve_info()?.node().is_some(),
        "an authored opinion resolves through a composition node"
    );

    // A reference target is not in the root layer stack, so its identifier comes
    // from the composed prim's own stack.
    let source = moved
        .prim_stack()?
        .into_iter()
        .map(|site| site.layer)
        .find(|id| leaf_of(id) == "source.usda")
        .expect("the reference target contributes a spec");
    stage.layer_mut(&source).expect("loaded").edit(|edit| {
        edit.attribute_mut(&sdf::path("/Source/Inner.x")?)
            .expect("the source layer parsed")
            .expect("the attribute is authored there")
            .set_default(sdf::Value::Double(7.0));
        Ok(())
    })?;

    assert_eq!(
        agreed(&stage, &query, "/Inst/Moved.x", 0.0)?,
        Some(7.0),
        "the warmed proxy query must see the edit, not replay the prototype's old source"
    );
    Ok(())
}
