//! Cost of editing a composed stage as its history, its loaded layers and
//! its clip changes grow, on synthetic scenes written to a temporary
//! directory.
//!
//! Each scenario runs at growing sizes and prints, per size, the time an
//! operation takes and what composing it cost ([`pcp::Tally`]), so a cost
//! that grows with the size shows as a per-operation time that grows with
//! it:
//!
//! - `cascade` loads a payload whose layer references a chain of layers
//!   (depth) or a fan of them (width), each opened on demand.
//! - `undo` builds an undo history of `h` value edits, then times further
//!   value edits and payload unload/load pairs, whose reclaims collect the
//!   layers the history names.
//! - `clips` re-points a clip set again and again, rotating through a pool
//!   of clip files, reading the clipped value after each change; the layer
//!   count it ends with shows whether retracted clips are released.
//! - `reclaim` unloads and loads one payload among `n` loaded ones, each
//!   with a layer of its own.
//!
//! # Usage
//! ```bash
//! cargo run --release -p openusd --example edit_bench -- [cascade|undo|clips|reclaim]...
//! ```
//!
//! With no scenario named, every one runs.

use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::time::{Duration, Instant};

use openusd::usd::{InitialLoadSet, LoadPolicy, Stage, UndoStage};
use openusd::{gf, pcp, sdf, usd, vt};

fn main() -> openusd::Result<()> {
    let named: Vec<String> = std::env::args().skip(1).collect();
    let runs = |name: &str| named.is_empty() || named.iter().any(|n| n == name);
    if runs("cascade") {
        cascade()?;
    }
    if runs("undo") {
        undo()?;
    }
    if runs("clips") {
        clips()?;
    }
    if runs("reclaim") {
        reclaim()?;
    }
    Ok(())
}

/// Loads a payload whose layer reaches others on demand: a chain of
/// references `depth` long, then a fan of `width` references.
fn cascade() -> openusd::Result<()> {
    println!("cascade: load /P, whose payload reaches the layers below on demand");
    for depth in [8, 32, 80] {
        let dir = tempfile::tempdir()?;
        for i in 0..depth {
            let next = if i + 1 < depth {
                format!(" (references = @c{}.usda@</X>)", i + 1)
            } else {
                String::new()
            };
            write(
                dir.path(),
                &format!("c{i}.usda"),
                &format!("def \"X\"{next} {{\n    def \"C{i}\" {{}}\n}}\n"),
            )?;
        }
        let stage = open_none(dir.path(), "def \"P\" (payload = @c0.usda@</X>) {}\n")?;
        let (time, tally) = timed(&stage, || {
            stage.load("/P", LoadPolicy::WithDescendants)?;
            stage.prim("/P")?.child_names()?;
            Ok(())
        })?;
        row(&format!("chain depth {depth}"), time, 1, tally, &stage);
    }
    for width in [100, 1_000, 5_000] {
        let dir = tempfile::tempdir()?;
        let mut hub = String::from("def \"X\" {\n");
        for i in 0..width {
            write(
                dir.path(),
                &format!("l{i}.usda"),
                &format!("def \"L\" {{\n    double v = {i}\n}}\n"),
            )?;
            writeln!(hub, "    def \"E{i}\" (references = @l{i}.usda@</L>) {{}}").expect("a string takes text");
        }
        hub.push_str("}\n");
        write(dir.path(), "hub.usda", &hub)?;
        let stage = open_none(dir.path(), "def \"P\" (payload = @hub.usda@</X>) {}\n")?;
        let (time, tally) = timed(&stage, || {
            stage.load("/P", LoadPolicy::WithDescendants)?;
            for i in 0..width {
                stage.prim(format!("/P/E{i}").as_str())?.child_names()?;
            }
            Ok(())
        })?;
        row(&format!("fan width {width}"), time, 1, tally, &stage);
    }
    Ok(())
}

/// Times value edits, and payload unload/load pairs, on an undo stage whose
/// history holds `h` recorded edits.
fn undo() -> openusd::Result<()> {
    println!("undo: per-operation cost with h edits recorded");
    for h in [0, 1_000, 10_000, 50_000] {
        let dir = tempfile::tempdir()?;
        write(dir.path(), "q.usda", "def \"Y\" {\n    def \"C\" {}\n}\n")?;
        let stage = open(
            dir.path(),
            "def \"P\" {\n    double x = 0\n}\ndef \"Q\" (payload = @q.usda@</Y>) {}\n",
        )?;
        let stage = UndoStage::from(stage);
        stage.prim("/Q/C")?.is_valid()?;
        let x = stage.attribute("/P.x")?;
        for i in 0..h {
            x.clone().set(f64::from(i))?;
        }
        const EDITS: u32 = 200;
        let (time, tally) = timed(&stage, || {
            for i in 0..EDITS {
                x.clone().set(f64::from(i))?;
            }
            Ok(())
        })?;
        row(&format!("h {h:>6}: value edit"), time, EDITS, tally, &stage);
        const PAIRS: u32 = 20;
        let (time, tally) = timed(&stage, || {
            for _ in 0..PAIRS {
                stage.unload("/Q")?;
                stage.load("/Q", LoadPolicy::WithDescendants)?;
                stage.prim("/Q/C")?.is_valid()?;
            }
            Ok(())
        })?;
        row(&format!("h {h:>6}: unload+load"), time, PAIRS, tally, &stage);
    }
    Ok(())
}

/// Re-points a clip set `changes` times, rotating through `pool` clip files,
/// reading the clipped value after each change.
fn clips() -> openusd::Result<()> {
    println!("clips: re-point a clip set, read the clipped value");
    for (pool, changes) in [(2, 2_000), (50, 2_000), (500, 2_000)] {
        let dir = tempfile::tempdir()?;
        for i in 0..pool {
            write(
                dir.path(),
                &format!("clip{i}.usda"),
                &format!("def \"M\" {{\n    double x.timeSamples = {{\n        0: {i},\n    }}\n}}\n"),
            )?;
        }
        let stage = open(dir.path(), "def \"A\" {\n    double x\n}\n")?;
        let x = stage.attribute("/A.x")?;
        let point = |i: usize| -> openusd::Result<()> {
            stage.prim("/A")?.set_metadata(
                sdf::FieldKey::Clips.as_str(),
                clip_set(&format!("./clip{}.usda", i % pool)),
            )?;
            let read = x.get_at::<f64>(usd::TimeCode::new(0.0))?;
            assert_eq!(read, Some((i % pool) as f64), "the clip the set names answers");
            Ok(())
        };
        point(0)?;
        let first = 100;
        let (time, tally) = timed(&stage, || (1..=first).try_for_each(point))?;
        row(
            &format!("pool {pool:>3}: first {first}"),
            time,
            first as u32,
            tally,
            &stage,
        );
        (first + 1..changes - first).try_for_each(point)?;
        let (time, tally) = timed(&stage, || (changes - first..changes).try_for_each(point))?;
        row(
            &format!("pool {pool:>3}: last {first}"),
            time,
            first as u32,
            tally,
            &stage,
        );
        // The same edit and read with the set left alone: what a change
        // costs beyond authoring metadata and reading a value.
        let (time, tally) = timed(&stage, || {
            (0..first).try_for_each(|i| -> openusd::Result<()> {
                stage.prim("/A")?.set_metadata("documentation", format!("{i}"))?;
                x.get_at::<f64>(usd::TimeCode::new(0.0))?;
                Ok(())
            })
        })?;
        row(&format!("pool {pool:>3}: control"), time, first as u32, tally, &stage);
    }
    Ok(())
}

/// Unloads and loads one payload among `n` loaded ones, each with a layer of
/// its own.
fn reclaim() -> openusd::Result<()> {
    println!("reclaim: unload+load one payload among n loaded");
    for n in [100, 1_000, 5_000] {
        let dir = tempfile::tempdir()?;
        let mut root = String::new();
        for i in 0..n {
            write(dir.path(), &format!("p{i}.usda"), "def \"Y\" {\n    def \"C\" {}\n}\n")?;
            writeln!(root, "def \"P{i}\" (payload = @p{i}.usda@</Y>) {{}}").expect("a string takes text");
        }
        let stage = open(dir.path(), &root)?;
        for i in 0..n {
            stage.prim(format!("/P{i}/C").as_str())?.is_valid()?;
        }
        const PAIRS: u32 = 20;
        let (time, tally) = timed(&stage, || {
            for _ in 0..PAIRS {
                stage.unload("/P0")?;
                stage.load("/P0", LoadPolicy::WithDescendants)?;
                stage.prim("/P0/C")?.is_valid()?;
            }
            Ok(())
        })?;
        row(&format!("n {n:>5}: unload+load"), time, PAIRS, tally, &stage);
    }
    Ok(())
}

/// A one-clip set sourcing `/M` from `asset` over all time.
fn clip_set(asset: &str) -> vt::Value {
    let set = vt::Dictionary::from([
        ("assetPaths".to_string(), vt::Value::AssetPathVec(vec![asset.into()])),
        ("primPath".to_string(), vt::Value::String("/M".to_string())),
        ("active".to_string(), vt::Value::Vec2dVec(vec![gf::vec2d(0.0, 0.0)])),
    ]);
    vt::Value::Dictionary(vt::Dictionary::from([(
        "default".to_string(),
        vt::Value::Dictionary(set),
    )]))
}

/// Writes `body` under a `#usda 1.0` header as `dir/name`.
fn write(dir: &Path, name: &str, body: &str) -> std::io::Result<()> {
    fs::write(dir.join(name), format!("#usda 1.0\n{body}"))
}

/// Opens a stage on a root layer holding `body`, loading every payload.
fn open(dir: &Path, body: &str) -> openusd::Result<Stage> {
    write(dir, "root.usda", body)?;
    Stage::open(&dir.join("root.usda").to_string_lossy())
}

/// Opens a stage on a root layer holding `body`, loading no payload.
fn open_none(dir: &Path, body: &str) -> openusd::Result<Stage> {
    write(dir, "root.usda", body)?;
    Stage::builder()
        .load(InitialLoadSet::LoadNone)
        .open(&dir.join("root.usda").to_string_lossy())
}

/// Runs `work`, returning how long it took and what composing it cost.
fn timed(stage: &Stage, work: impl FnOnce() -> openusd::Result<()>) -> openusd::Result<(Duration, pcp::Tally)> {
    let before = stage.tally();
    let start = Instant::now();
    work()?;
    let time = start.elapsed();
    let after = stage.tally();
    Ok((
        time,
        pcp::Tally {
            visits: after.visits - before.visits,
            population_checks: after.population_checks - before.population_checks,
            builds: after.builds - before.builds,
            demands: after.demands - before.demands,
        },
    ))
}

/// Prints one measured row: the total and per-operation time over `ops`
/// operations, what composing cost, and the layers the stage holds after.
fn row(label: &str, time: Duration, ops: u32, tally: pcp::Tally, stage: &Stage) {
    println!(
        "  {label:<28} {:>10.3} ms  {:>9.1} us/op  builds {:>6}  demands {:>5}  visits {:>6}  layers {:>5}",
        time.as_secs_f64() * 1e3,
        time.as_secs_f64() * 1e6 / f64::from(ops),
        tally.builds,
        tally.demands,
        tally.visits,
        stage.layer_count(),
    );
}
