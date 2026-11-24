//! Splines on a composed stage: value resolution at a time, where a spline
//! stands among an attribute's other value sources, retiming through layer
//! offsets, authoring, and flattening.

use std::cell::Cell;
use std::fs;
use std::rc::Rc;

use openusd::Result;
use openusd::sdf;
use openusd::ts;
use openusd::usd::{self, ResolveInfoSource, Stage, StageAuthoringError, TimeCode};
use openusd::usdc;
use openusd::vt::Value;

/// Writes each `(name, text)` layer into `dir` and opens the first as a stage.
fn open(dir: &tempfile::TempDir, layers: &[(&str, &str)]) -> Result<Stage> {
    for (name, text) in layers {
        fs::write(dir.path().join(name), text)?;
    }
    Stage::open(dir.path().join(layers[0].0).to_str().expect("a UTF-8 path"))
}

fn value_at(stage: &Stage, attr: &str, time: f64) -> Result<Option<Value>> {
    stage.attribute(attr)?.get_at::<Value>(TimeCode::new(time))
}

/// A line through `(0, 0)` and `(10, 20)`, held outside its knots.
const RAMP: &str = "{ 0: 0; post linear, 10: 20; post linear }";

/// A spline answers at every numeric time, at the attribute's precision,
/// and not at the default time.
#[test]
fn value_at_time() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let text = format!("#usda 1.0\ndef \"P\"\n{{\n    float x.spline = {RAMP}\n    half h.spline = {RAMP}\n}}\n");
    let stage = open(&dir, &[("root.usda", &text)])?;

    assert_eq!(value_at(&stage, "/P.x", 5.0)?, Some(Value::Float(10.0)));
    assert_eq!(value_at(&stage, "/P.x", -3.0)?, Some(Value::Float(0.0)));
    assert_eq!(value_at(&stage, "/P.x", 99.0)?, Some(Value::Float(20.0)));
    assert_eq!(stage.attribute("/P.x")?.get_at::<f32>(TimeCode::new(2.5))?, Some(5.0));
    assert!(matches!(value_at(&stage, "/P.h", 5.0)?, Some(Value::Half(half)) if half.to_f64() == 10.0));
    assert_eq!(stage.attribute("/P.x")?.get::<Value>()?, None);

    let attr = stage.attribute("/P.x")?;
    assert!(attr.has_spline()?);
    assert_eq!(attr.resolve_info()?.source(), ResolveInfoSource::Spline);
    assert_eq!(
        attr.resolve_info_at(TimeCode::new(5.0))?.source(),
        ResolveInfoSource::Spline
    );
    assert_eq!(attr.resolve_info_at(None)?.source(), ResolveInfoSource::None);
    assert!(attr.resolve_info_at(None)?.has_authored_value_opinion());
    assert!(attr.resolve_info()?.value_source_might_be_time_varying());

    // A spline holds no samples, and may vary all the same.
    assert_eq!(attr.num_time_samples()?, 0);
    assert!(attr.time_samples()?.is_none_or(|samples| samples.is_empty()));
    assert!(attr.might_be_time_varying()?);

    // A query replays the same values.
    let query = attr.query();
    assert_eq!(query.get_at::<Value>(TimeCode::new(5.0))?, Some(Value::Float(10.0)));
    assert_eq!(query.get_at::<Value>(TimeCode::new(7.5))?, Some(Value::Float(15.0)));
    Ok(())
}

/// At one site, samples answer before a spline and a spline before a default;
/// the default still answers the default time.
#[test]
fn site_order() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let text = format!(
        "#usda 1.0\ndef \"P\"\n{{\n    \
         double sampled = 7\n    double sampled.timeSamples = {{ 0: 100, 10: 200 }}\n    double sampled.spline = {RAMP}\n    \
         double curved = 7\n    double curved.spline = {RAMP}\n}}\n"
    );
    let stage = open(&dir, &[("root.usda", &text)])?;

    assert_eq!(value_at(&stage, "/P.sampled", 5.0)?, Some(Value::Double(150.0)));
    assert!(!stage.attribute("/P.sampled")?.has_spline()?);
    assert_eq!(stage.attribute("/P.sampled")?.num_time_samples()?, 2);

    assert_eq!(value_at(&stage, "/P.curved", 5.0)?, Some(Value::Double(10.0)));
    assert_eq!(stage.attribute("/P.curved")?.get::<f64>()?, Some(7.0));
    assert!(stage.attribute("/P.curved")?.has_spline()?);
    Ok(())
}

/// Across sites the strongest opinion answers: a default hides a weaker
/// spline at every time, and a spline hides weaker samples.
#[test]
fn strength_order() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = format!(
        "#usda 1.0\n(\n    subLayers = [@./weak.usda@]\n)\nover \"P\"\n{{\n    \
         double pinned = 3\n    double curved.spline = {RAMP}\n}}\n"
    );
    let weak = format!(
        "#usda 1.0\ndef \"P\"\n{{\n    double pinned.spline = {RAMP}\n    \
         double curved.timeSamples = {{ 0: 100, 10: 200 }}\n}}\n"
    );
    let stage = open(&dir, &[("root.usda", &root), ("weak.usda", &weak)])?;

    assert_eq!(value_at(&stage, "/P.pinned", 5.0)?, Some(Value::Double(3.0)));
    assert!(!stage.attribute("/P.pinned")?.has_spline()?);
    assert_eq!(stage.attribute("/P.pinned")?.spline()?, None);

    assert_eq!(value_at(&stage, "/P.curved", 5.0)?, Some(Value::Double(10.0)));
    assert!(stage.attribute("/P.curved")?.has_spline()?);
    // The weaker samples are not listed: the walk ends at the spline.
    assert_eq!(stage.attribute("/P.curved")?.num_time_samples()?, 0);
    Ok(())
}

/// Where a spline is a value block the attribute has no value, and nothing
/// weaker answers in its place.
#[test]
fn value_block() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0\n(\n    subLayers = [@./weak.usda@]\n)\nover \"P\"\n{\n    \
                double x.spline = { post: none, 0: 0; post none, 10: 20; post linear }\n    \
                double empty.spline = {}\n}\n";
    let weak =
        "#usda 1.0\ndef \"P\"\n{\n    double x = 5\n    double x.timeSamples = { 0: 1 }\n    double empty = 5\n}\n";
    let stage = open(&dir, &[("root.usda", root), ("weak.usda", weak)])?;

    assert_eq!(value_at(&stage, "/P.x", -1.0)?, Some(Value::Double(0.0)));
    assert_eq!(value_at(&stage, "/P.x", 5.0)?, None);
    assert_eq!(value_at(&stage, "/P.x", 10.0)?, None);
    assert_eq!(value_at(&stage, "/P.x", 20.0)?, None);
    let info = stage.attribute("/P.x")?.resolve_info_at(TimeCode::new(5.0))?;
    assert!(info.value_is_blocked());
    assert_eq!(info.blocked_by(), Some(ResolveInfoSource::Spline));

    // A spline with no knots has no value anywhere.
    assert_eq!(value_at(&stage, "/P.empty", 1.0)?, None);
    assert_eq!(stage.attribute("/P.empty")?.get::<f64>()?, Some(5.0));
    Ok(())
}

/// A blocked `timeSamples` field withholds a weaker spline, as it withholds
/// weaker samples, and leaves a weaker default to answer.
#[test]
fn samples_block_hides_spline() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0
(
    subLayers = [@./weak.usda@]
)
over \"P\"
{
    double x
}
";
    let weak = format!(
        "#usda 1.0
def \"P\"
{{
    double x = 3
    double x.spline = {RAMP}
}}
"
    );
    let stage = open(&dir, &[("root.usda", root), ("weak.usda", &weak)])?;
    assert_eq!(value_at(&stage, "/P.x", 5.0)?, Some(Value::Double(10.0)));

    // Text has no spelling for the block, which is a field of its own.
    stage.root_layer().edit(|edit| {
        edit.data_mut().set_field(
            &sdf::path("/P.x")?,
            sdf::FieldKey::TimeSamples.as_str(),
            Value::ValueBlock,
        );
        Ok(())
    })?;
    assert_eq!(value_at(&stage, "/P.x", 5.0)?, Some(Value::Double(3.0)));
    assert!(!stage.attribute("/P.x")?.has_spline()?);
    Ok(())
}

/// A layer offset retimes a spline as it retimes samples, and the values of
/// a `timecode` attribute's spline with its times.
#[test]
fn layer_offset() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0\n(\n    subLayers = [@./anim.usda@ (offset = 10; scale = 2)]\n)\n";
    let anim = format!(
        "#usda 1.0\ndef \"P\"\n{{\n    double x.spline = {RAMP}\n    \
         timecode t.spline = {{ 0: 0; post linear, 10: 10; post linear }}\n}}\n"
    );
    let stage = open(&dir, &[("root.usda", root), ("anim.usda", &anim)])?;

    // Stage time 20 is layer time 5.
    assert_eq!(value_at(&stage, "/P.x", 20.0)?, Some(Value::Double(10.0)));
    assert_eq!(value_at(&stage, "/P.x", 10.0)?, Some(Value::Double(0.0)));
    // The layer's time 5 is the stage's time 20.
    assert_eq!(
        value_at(&stage, "/P.t", 20.0)?,
        Some(Value::TimeCode(sdf::TimeCode(20.0)))
    );

    let spline = stage.attribute("/P.x")?.spline()?.expect("a spline");
    let knots: Vec<_> = spline.knots().iter().map(|knot| (knot.time, knot.value)).collect();
    assert_eq!(knots, [(10.0, 0.0), (30.0, 20.0)]);
    let timed = stage.attribute("/P.t")?.spline()?.expect("a spline");
    let knots: Vec<_> = timed.knots().iter().map(|knot| (knot.time, knot.value)).collect();
    assert_eq!(knots, [(10.0, 10.0), (30.0, 30.0)]);
    Ok(())
}

fn ramp() -> ts::Spline {
    let linear = |time: f64, value: f64| ts::Knot {
        next_interp: ts::InterpMode::Linear,
        ..ts::Knot::new(time, value)
    };
    let mut spline = ts::Spline::new(ts::ValueType::Double);
    spline
        .set_knots([linear(0.0, 0.0), linear(10.0, 20.0)])
        .expect("valid knots");
    spline
}

#[test]
fn removed_knot_roundtrip() -> Result<()> {
    let dir = tempfile::tempdir()?;
    for body in [
        "hermite, 0: 0; post curve (2), 3: 3; post curve (1), 6: 9; pre (-1)",
        "bezier, 0: 0; post curve (1, 0), 3: 1; pre (1, 0, autoEase); post curve (1, 0, autoEase), \
         6: 2; post curve (1, 0), 9: 9; pre (1, 0, autoEase); post curve (1, 0, autoEase), 12: 12; pre (1, 0)",
    ] {
        let text = format!("#usda 1.1\ndef \"P\" {{ double x.spline = {{ {body} }} }}\n");
        let stage = open(&dir, &[("source.usda", &text)])?;
        let attr = stage.attribute("/P.x")?;
        let mut spline = attr.spline()?.expect("authored spline");
        let interior = spline.knots()[spline.knots().len() / 2].time;
        spline.remove_knot(interior).expect("interior knot");
        let attr = attr.set_spline(spline)?;

        let text = stage.root_layer().export_to_string()?;
        let reloaded = open(&dir, &[("edited.usda", &text)])?;
        let reloaded = reloaded.attribute("/P.x")?;
        for time in [1.5, 4.5, 7.5, 10.5] {
            assert_eq!(
                attr.get_at::<f64>(TimeCode::new(time))?,
                reloaded.get_at::<f64>(TimeCode::new(time))?,
                "{body} at {time}"
            );
        }
    }
    Ok(())
}

/// A generic read of the `spline` field answers the strongest spline in
/// stage time, whether or not it is what the attribute reads from.
#[test]
fn field_read() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0\n(\n    subLayers = [@./anim.usda@ (offset = 10; scale = 2)]\n)\nover \"P\"\n{\n    double x = 3\n}\n";
    let anim = format!("#usda 1.0\ndef \"P\"\n{{\n    double x.spline = {RAMP}\n}}\n");
    let stage = open(&dir, &[("root.usda", root), ("anim.usda", &anim)])?;

    // The stronger default hides the spline from the attribute.
    assert_eq!(stage.attribute("/P.x")?.spline()?, None);
    let field = stage.field::<ts::Spline>("/P.x", "spline")?.expect("a spline opinion");
    let times: Vec<_> = field.knots().iter().map(|knot| knot.time).collect();
    assert_eq!(times, [10.0, 30.0]);
    Ok(())
}

/// A spline is set through the attribute, checked against its type, and
/// removed by a clear or a block.
#[test]
fn authoring() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;
    stage.define_prim("/P")?;
    let attr = stage.create_attribute("/P.x", "double")?;
    assert!(!attr.has_spline()?);

    let attr = attr.set_spline(ramp())?;
    assert!(attr.has_spline()?);
    assert_eq!(attr.spline()?, Some(ramp()));
    assert_eq!(attr.get_at::<f64>(TimeCode::new(2.5))?, Some(5.0));

    // A time sample at the same site answers first.
    let attr = attr.set_at(1.0, TimeCode::new(0.0))?;
    assert_eq!(attr.get_at::<f64>(TimeCode::new(2.5))?, Some(1.0));
    assert!(!attr.has_spline()?);

    let attr = attr.clear()?;
    assert!(!attr.has_spline()?);
    assert_eq!(attr.get_at::<f64>(TimeCode::new(2.5))?, None);

    let attr = attr.set_spline(ramp())?.block()?;
    assert!(!attr.has_spline()?);
    assert_eq!(attr.get_at::<f64>(TimeCode::new(2.5))?, None);

    // The spline's type must be the attribute's, and a spline is not
    // metadata.
    let float = stage.create_attribute("/P.f", "float")?;
    let error = float.clone().set_spline(ramp()).expect_err("a spline of doubles");
    assert!(
        error.to_string().contains("cannot hold a spline of double values"),
        "{error}"
    );
    let time = stage.create_attribute("/P.t", "timecode")?;
    let error = time.clone().set_spline(ramp()).expect_err("not time-valued");
    assert!(matches!(error, StageAuthoringError::ValueType(_)), "{error:?}");
    let mut timed = ramp();
    timed.set_time_valued(true);
    time.set_spline(timed)?;

    let token = stage.create_attribute("/P.s", "token")?;
    token.clone().set_spline(ramp()).expect_err("no spline of tokens");
    let error = float
        .set_metadata("spline", Value::Spline(ramp()))
        .expect_err("a reserved field");
    assert!(matches!(error, StageAuthoringError::ReservedField { .. }), "{error:?}");
    Ok(())
}

/// A query built before a spline is set, cleared or blocked reads what the
/// attribute reads after each edit, and a stage sink hears of each.
#[test]
fn edits_reach_queries() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;
    stage.define_prim("/P")?;
    let attr = stage.create_attribute("/P.x", "double")?.set(1.0)?;
    let query = attr.query();
    let at = |time: f64| query.get_at::<f64>(TimeCode::new(time));
    assert_eq!(at(2.5)?, Some(1.0));

    let notices = Rc::new(Cell::new(0));
    let heard = notices.clone();
    let _sink = stage.add_sink(move |_: &Stage, _: &usd::CommittedChange<'_>| heard.set(heard.get() + 1))?;

    let attr = attr.set_spline(ramp())?;
    assert_eq!(at(2.5)?, Some(5.0));
    assert_eq!(notices.get(), 1);
    assert!(query.might_be_time_varying()?);

    // A second spline replaces the first.
    let mut steeper = ramp();
    steeper.retime(0.0, 0.5)?;
    let attr = attr.set_spline(steeper)?;
    assert_eq!(at(2.5)?, Some(10.0));

    let attr = attr.clear()?;
    assert_eq!(at(2.5)?, None);
    assert!(!query.might_be_time_varying()?);

    attr.set_spline(ramp())?.block()?;
    assert_eq!(at(2.5)?, None);
    assert_eq!(notices.get(), 5);
    Ok(())
}

/// A spline set through an edit target that retimes is stored in the
/// target's time and reads back in the stage's.
#[test]
fn authoring_through_offset() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0\ndef \"A\" (\n    references = @./anim.usda@</A> (offset = 10; scale = 2)\n)\n{\n}\n";
    let anim = "#usda 1.0\ndef \"A\"\n{\n    double x = 0\n}\n";
    let stage = open(&dir, &[("root.usda", root), ("anim.usda", anim)])?;

    let target = stage.edit_target_for_node(&sdf::path("/A")?, usd::EditTargetArc::Reference)?;
    stage.set_edit_target(target)?;
    let attr = stage.attribute("/A.x")?.set_spline(ramp())?;

    assert_eq!(attr.spline()?, Some(ramp()));
    assert_eq!(attr.get_at::<f64>(TimeCode::new(5.0))?, Some(10.0));
    Ok(())
}

/// A flattened stage keeps the spline that answers, in stage time, beside
/// the default that answers the default time.
#[test]
fn flatten() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0\n(\n    subLayers = [@./anim.usda@ (offset = 10; scale = 2), @./weak.usda@]\n)\n";
    let anim = format!("#usda 1.0\ndef \"P\"\n{{\n    double x = 4\n    double x.spline = {RAMP}\n}}\n");
    let weak = "#usda 1.0\ndef \"P\"\n{\n    double x.timeSamples = { 0: 100 }\n}\n";
    let stage = open(&dir, &[("root.usda", root), ("anim.usda", &anim), ("weak.usda", weak)])?;

    let text = stage.flatten()?.export_to_string()?;
    assert!(
        text.contains("double x = 4\n")
            && text.contains(
                "double x.spline = {\n        10: 0; pre (0, 0); post linear,\n        30: 20; post linear,\n"
            )
            && !text.contains("timeSamples"),
        "{text}"
    );

    let flat = open(&dir, &[("flat.usda", &text)])?;
    for time in [5.0, 10.0, 20.0, 30.0, 45.0] {
        assert_eq!(
            value_at(&flat, "/P.x", time)?,
            value_at(&stage, "/P.x", time)?,
            "at {time}"
        );
    }
    assert_eq!(value_at(&flat, "/P.x", 20.0)?, Some(Value::Double(10.0)));
    assert_eq!(flat.attribute("/P.x")?.get::<f64>()?, Some(4.0));
    Ok(())
}

/// A flattened stage reads what the stage read where the walk and the fields
/// present disagree: a spline beside an empty sample map, and a curved
/// `timecode` spline under an offset that scales.
#[test]
fn flatten_matches_stage() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0\n(\n    subLayers = [@./anim.usda@ (offset = 10; scale = 2)]\n)\n";
    let anim = format!(
        "#usda 1.0\ndef \"P\"\n{{\n    double x.timeSamples = {{}}\n    double x.spline = {RAMP}\n    \
         timecode t.spline = {{\n        bezier,\n        post: sloped(1),\n        \
         0: 0; post curve (2, 1),\n        10: 10; pre (2, 0),\n    }}\n}}\n"
    );
    let stage = open(&dir, &[("root.usda", root), ("anim.usda", &anim)])?;
    assert_eq!(value_at(&stage, "/P.x", 20.0)?, Some(Value::Double(10.0)));

    let text = stage.flatten()?.export_to_string()?;
    let flat = open(&dir, &[("flat.usda", &text)])?;
    for attr in ["/P.x", "/P.t"] {
        for time in [0.0, 10.0, 13.0, 20.0, 27.5, 30.0, 50.0] {
            let expected = value_at(&stage, attr, time)?;
            assert!(expected.is_some(), "{attr} at {time}");
            assert_eq!(value_at(&flat, attr, time)?, expected, "{attr} at {time}\n{text}");
        }
    }
    Ok(())
}

/// A spline the stage reads under a declaration that does not take it is
/// one no layer can hold, and flattening says so.
#[test]
fn flatten_refuses_misdeclared() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = "#usda 1.0
(
    subLayers = [@./weak.usda@]
)
over \"P\"
{
    int x
}
";
    let weak = format!(
        "#usda 1.0
def \"P\"
{{
    double x.spline = {RAMP}
}}
"
    );
    let stage = open(&dir, &[("root.usda", root), ("weak.usda", &weak)])?;
    assert_eq!(value_at(&stage, "/P.x", 5.0)?, Some(Value::Double(10.0)));

    let error = stage.flatten().expect_err("a spline an int attribute cannot declare");
    assert!(error.to_string().contains("cannot hold a spline"), "{error}");
    Ok(())
}

/// An attribute that holds a spline is redeclared only as a type that takes
/// the spline.
#[test]
fn retype_checks_spline() -> Result<()> {
    let mut data = sdf::Data::rooted();
    let path = sdf::path("/P.x")?;
    sdf::PrimSpec::new(&mut data, &sdf::path("/P")?, sdf::Specifier::Def, "")?;
    let mut attr = sdf::AttributeSpec::new(&mut data, &path, "double", sdf::Variability::Varying, false)?;
    attr.set_spline(ramp())?;
    assert!(attr.has_spline());

    assert!(attr.set_type_name("int").is_err());
    assert!(attr.set_type_name("float").is_err());
    assert!(attr.set_type_name("timecode").is_err());
    assert_eq!(attr.type_name().map(|name| name.to_string()), Some("double".to_owned()));
    attr.clear_spline();
    attr.set_type_name("float")?;
    Ok(())
}

/// A stage reads the same spline values from a crate layer as from text.
#[test]
fn crate_layer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let text = "#usda 1.0\ndef \"P\"\n{\n    float x.spline = {\n        bezier,\n        post: loop repeat,\n        \
                1: 8; pre (0, 0); post curve (1.3, 0.125),\n        6: 20; pre (1.3, -0.2); post curve (2, 0.3),\n    }\n}\n";
    let stage = open(&dir, &[("root.usda", text)])?;

    let binary = dir.path().join("root.usdc");
    let layer = stage.root_layer();
    let layer = layer.try_borrow()?;
    usdc::CrateWriter::write(layer.data(), &mut fs::File::create(&binary)?)?;
    let from_crate = Stage::open(binary.to_str().expect("a UTF-8 path"))?;

    for time in [0.0, 1.0, 2.5, 4.0, 6.0, 8.5, 20.0] {
        let expected = value_at(&stage, "/P.x", time)?;
        assert!(expected.is_some(), "a value at {time}");
        assert_eq!(value_at(&from_crate, "/P.x", time)?, expected, "at {time}");
    }
    Ok(())
}
