//! Spline evaluation against curves C++ sampled.
//!
//! `fixtures/ts/testTsSplineSampling.txt` is the baseline of C++
//! `testTsSplineSampling`: for each spline of the `TsTest_Museum` collection,
//! a dump of the spline and the polylines `TsSpline::Sample` drew for it.
//! Every vertex of a polyline is a point on the curve, so the spline built
//! from the dump must evaluate to the vertex's value at the vertex's time.
//!
//! The collection covers Bezier and Hermite curves, held and linear
//! segments, inner loops, looping extrapolation, dual-valued knots, and
//! regressive tangents. Only the double-precision cases are checked: the
//! baseline dumps each spline once, as a spline of doubles.

use std::fs;

use openusd::ts;

/// One sampling of a spline: the test case's heading, the span of time it
/// sampled, and the vertices of every polyline it drew.
struct Case {
    heading: String,
    span: (f64, f64),
    vertices: Vec<(f64, f64)>,
}

/// A spline of the collection with its double-precision samplings.
struct Entry {
    name: String,
    /// The dump the spline was built from, as C++ wrote it.
    dump: String,
    spline: ts::Spline,
    cases: Vec<Case>,
}

fn number(text: &str) -> f64 {
    text.trim()
        .parse()
        .unwrap_or_else(|e| panic!("bad number {text:?}: {e}"))
}

fn extrapolation(text: &str) -> ts::Extrapolation {
    match text.split_once(' ') {
        Some(("Sloped", slope)) => ts::Extrapolation::Sloped(number(slope)),
        _ => match text {
            "ValueBlock" => ts::Extrapolation::ValueBlock,
            "Held" => ts::Extrapolation::Held,
            "Linear" => ts::Extrapolation::Linear,
            "LoopRepeat" => ts::Extrapolation::LoopRepeat,
            "LoopReset" => ts::Extrapolation::LoopReset,
            "LoopOscillate" => ts::Extrapolation::LoopOscillate,
            other => panic!("unknown extrapolation {other:?}"),
        },
    }
}

/// Reads the baseline into the splines it dumps and their samplings.
fn parse(text: &str) -> Vec<Entry> {
    let mut entries: Vec<Entry> = Vec::new();
    let mut knots: Vec<ts::Knot> = Vec::new();
    // Whether the vertices being read belong to a double-precision case.
    let mut sampling = false;
    // Whether the lines being read are a spline's dump.
    let mut dumping = false;

    // A spline's knots are complete once its first test case starts.
    fn finish(entries: &mut [Entry], knots: &mut Vec<ts::Knot>) {
        if let (Some(entry), false) = (entries.last_mut(), knots.is_empty()) {
            entry
                .spline
                .set_knots_with(knots.drain(..), ts::AntiRegression::None)
                .expect("the dumped knots are valid");
        }
    }

    for line in text.lines() {
        // A spline's dump runs from its name to the rule above its cases.
        dumping &= !line.starts_with("---");
        if dumping
            && !line.is_empty()
            && !line.starts_with("Spline: ")
            && let Some(entry) = entries.last_mut()
        {
            entry.dump.push_str(line);
            entry.dump.push('\n');
        }
        let field = line.trim();
        if let Some(name) = line.strip_prefix("Spline: ") {
            finish(&mut entries, &mut knots);
            entries.push(Entry {
                name: name.to_owned(),
                dump: String::new(),
                spline: ts::Spline::new(ts::ValueType::Double),
                cases: Vec::new(),
            });
            sampling = false;
            dumping = true;
        } else if line.starts_with("Test Case ") {
            finish(&mut entries, &mut knots);
            sampling = line.contains("<double, GfVec2d>");
            if sampling {
                let entry = entries.last_mut().expect("a case follows a spline");
                // `Sample<double, GfVec2d>([1, 5], 125, 500, 1)`
                let span = line.split_once("([").and_then(|(_, rest)| rest.split_once(']'));
                let (min, max) = span
                    .and_then(|(span, _)| span.split_once(", "))
                    .expect("a sampled span");
                entry.cases.push(Case {
                    heading: line.to_owned(),
                    span: (number(min), number(max)),
                    vertices: Vec::new(),
                });
            }
        } else if let Some(vertex) = field.strip_prefix('(').and_then(|rest| rest.strip_suffix(')')) {
            // A polyline's heading is parenthesized too, after its index.
            if sampling && line.starts_with("    ") {
                let (time, value) = vertex.split_once(", ").expect("a time and a value");
                let case = entries.last_mut().and_then(|entry| entry.cases.last_mut());
                case.expect("a vertex follows a case")
                    .vertices
                    .push((number(time), number(value)));
            }
        } else if line == "Knot:" {
            knots.push(ts::Knot::default());
        } else if let Some(entry) = entries.last_mut().filter(|entry| entry.cases.is_empty()) {
            let spline = &mut entry.spline;
            if let Some(kind) = field.strip_prefix("curve type ") {
                spline.set_curve_type(kind.to_lowercase().parse::<ts::CurveType>().expect("a curve type"));
            } else if let Some(mode) = field.strip_prefix("pre extrap ") {
                spline.set_pre_extrapolation(extrapolation(mode));
            } else if let Some(mode) = field.strip_prefix("post extrap ") {
                spline.set_post_extrapolation(extrapolation(mode));
            } else if let Some(params) = field.strip_prefix("start ") {
                let values: Vec<f64> = params
                    .split(", ")
                    .map(|part| number(part.rsplit(' ').next().expect("a value")))
                    .collect();
                let [proto_start, proto_end, pre, post, value_offset] = values[..] else {
                    panic!("five loop parameters in {params:?}");
                };
                spline.set_loop_params(ts::LoopParams {
                    proto_start,
                    proto_end,
                    num_pre_loops: pre as i32,
                    num_post_loops: post as i32,
                    value_offset,
                });
            } else if let Some(knot) = knots.last_mut() {
                if let Some(time) = field.strip_prefix("time ") {
                    knot.time = number(time);
                } else if let Some(value) = field
                    .strip_prefix("value ")
                    .filter(|_| !field.starts_with("value type"))
                {
                    knot.value = number(value);
                } else if let Some(value) = field.strip_prefix("preValue ") {
                    knot.pre_value = Some(number(value));
                } else if let Some(mode) = field.strip_prefix("next interp ") {
                    knot.next_interp = match mode {
                        "ValueBlock" => ts::InterpMode::ValueBlock,
                        "Held" => ts::InterpMode::Held,
                        "Linear" => ts::InterpMode::Linear,
                        "Curve" => ts::InterpMode::Curve,
                        other => panic!("unknown interpolation {other:?}"),
                    };
                } else if let Some(width) = field.strip_prefix("pre-tan width ") {
                    knot.pre_tangent.width = number(width);
                } else if let Some(slope) = field.strip_prefix("pre-tan slope ") {
                    knot.pre_tangent.slope = number(slope);
                } else if let Some(width) = field.strip_prefix("post-tan width ") {
                    knot.post_tangent.width = number(width);
                } else if let Some(slope) = field.strip_prefix("post-tan slope ") {
                    knot.post_tangent.slope = number(slope);
                }
            }
        }
    }
    entries
}

/// Whether two values agree to five digits. A sampled vertex comes from
/// subdividing the curve and an evaluation from solving its time cubic in
/// closed form, which loses digits to cancellation: C++ `TsSpline::Eval`
/// reads `RegressivePreFringe` two parts in a million off its own samples.
fn close(a: f64, b: f64) -> bool {
    (a - b).abs() <= 1e-5 * a.abs().max(b.abs()).max(1.0)
}

/// A spline writes itself as C++ streams a `TsSpline`: the dump each
/// spline of the baseline was built from.
#[test]
fn museum_dumps() {
    let text = fs::read_to_string("fixtures/ts/testTsSplineSampling.txt").expect("the C++ baseline");
    for entry in parse(&text.replace("\r\n", "\n")) {
        assert_eq!(entry.spline.to_string(), entry.dump, "{}", entry.name);
    }
}

#[test]
fn museum_samples() {
    let text = fs::read_to_string("fixtures/ts/testTsSplineSampling.txt").expect("the C++ baseline");
    let entries = parse(&text);
    assert_eq!(entries.len(), 80, "40 splines, each sampled with and without sources");

    let mut checked = 0;
    let mut failures = Vec::new();
    for entry in &entries {
        assert!(!entry.cases.is_empty(), "{} has double-precision cases", entry.name);
        for case in &entry.cases {
            for &(time, expected) in &case.vertices {
                // A polyline is cut at the ends of the sampled span, at a
                // point on its last edge and not on the curve.
                if (time - case.span.0).abs() < 1e-9 || (time - case.span.1).abs() < 1e-9 {
                    continue;
                }
                checked += 1;
                // A polyline ends on the near side of a jump, which is the
                // spline's pre-value there.
                let sides = [entry.spline.eval(time), entry.spline.eval_pre_value(time)];
                if !sides.iter().flatten().any(|&value| close(value, expected)) {
                    failures.push(format!(
                        "{} at {time}: C++ sampled {expected}, evaluated {sides:?}\n    {}",
                        entry.name, case.heading
                    ));
                }
            }
        }
    }
    assert!(checked > 1900, "only {checked} vertices checked");
    assert!(
        failures.is_empty(),
        "{} of {checked} vertices differ:\n{}",
        failures.len(),
        failures.iter().take(40).cloned().collect::<Vec<_>>().join("\n")
    );
}
