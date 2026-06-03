//! Composition compliance tests.
//!
//! Each asset is opened via `Stage::open` through both the `.usda` text parser
//! and the `.usdc` binary parser, and the composed result is validated against
//! the vendor `pcp.txt` baseline by regenerating that dump byte-for-byte (see
//! [`run_pcp`] / [`pcp_dump`]). Assets the dump generator cannot reproduce yet
//! ([`SKIP_PCP_COMPLIANCE`]) fall back to the looser `pcp.json` existence checks
//! ([`run_existence`]); that fallback retires as suppressions clear.

use std::path::Path;

use openusd::{pcp, sdf, usd};

const ASSETS: &str = "vendor/core-spec-supplemental-release_dec2025/composition/tests/assets";

/// JSON schema for loading pcp.json baselines.
mod schema {
    use std::collections::HashMap;

    #[derive(serde::Deserialize)]
    #[serde(rename_all = "PascalCase")]
    pub struct Baseline {
        pub entry: String,
        #[serde(default)]
        pub composing: HashMap<String, PrimData>,
        #[serde(default)]
        pub errors: Vec<String>,
    }

    #[derive(serde::Deserialize, Debug)]
    pub struct PrimData {
        #[serde(default, rename = "Child names")]
        pub child_names: Vec<String>,
        #[serde(default, rename = "Property names")]
        pub property_names: Vec<String>,
    }
}

#[derive(Clone, Copy)]
enum Format {
    Text,
    Binary,
}

impl std::fmt::Display for Format {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Format::Text => "text",
            Format::Binary => "binary",
        })
    }
}

/// Variant fallbacks a test relies on. The C++ Pcp test framework registers
/// variant fallbacks through its plugin registry; our harness has none, so the
/// few cases that depend on a non-default selection configure it here. `case1`'s
/// `standin` set must select `render` (its `anim`/`layout`/`sim` variants
/// reference intentionally-absent files); without the fallback the first
/// variant, `anim`, is selected and its reference is unresolved.
fn variant_fallbacks_for(name: &str) -> pcp::VariantFallbackMap {
    match name {
        "case1_root" => pcp::VariantFallbackMap::new().add("standin", ["render"]),
        _ => pcp::VariantFallbackMap::new(),
    }
}

fn open_stage(name: &str, entry: &Path) -> usd::Stage {
    usd::Stage::builder()
        .on_error(|_| Ok(()))
        .variant_fallbacks(variant_fallbacks_for(name))
        .open(entry.to_str().unwrap())
        .unwrap()
}

/// Validates an asset through the parser selected by `format`.
///
/// Active assets are checked against the byte-exact `pcp.txt` golden (see
/// [`run_golden`]); suppressed assets fall back to the looser `pcp.json`
/// existence checks (see [`run_existence`]). Running this for both
/// [`Format::Text`] and [`Format::Binary`] exercises both the `.usda` and
/// `.usdc` parsers against the same baseline. The `pcp.json` path is a
/// transitional fallback — it retires as suppressions clear.
fn run(name: &str, format: Format) {
    let test_dir = Path::new(ASSETS).join(name);
    let baseline_path = test_dir.join("pcp.json");
    let json =
        std::fs::read_to_string(&baseline_path).unwrap_or_else(|e| panic!("read {}: {e}", baseline_path.display()));
    let baseline: schema::Baseline = serde_json::from_str(&json).expect("parse pcp.json");

    let entry = match format {
        Format::Text => test_dir.join("usda").join(&baseline.entry),
        Format::Binary => test_dir.join(&baseline.entry),
    };
    if !entry.exists() {
        return;
    }

    if SKIP_PCP_COMPLIANCE.contains(&name) {
        run_existence(name, format, &baseline, &entry);
    } else {
        run_pcp(name, format, &test_dir, &baseline, &entry);
    }
}

/// Validates a suppressed asset by checking that every baselined prim, child,
/// and property merely *exists* in the composed stage — the original, looser
/// `pcp.json` check. Skips error cases and assets with no composing data.
fn run_existence(name: &str, format: Format, baseline: &schema::Baseline, entry: &Path) {
    if !baseline.errors.is_empty() || baseline.composing.is_empty() {
        return;
    }

    let stage = open_stage(name, entry);

    // Collect every prim, including inactive/class/over prims, so the PCP
    // baselines can validate composition independent of stage traversal policy.
    let mut prims = Vec::new();
    stage
        .traverse(usd::PrimPredicate::ALL, |path| prims.push(path.to_string()))
        .unwrap();

    let mut failures = Vec::new();

    for (prim_path, expected) in &baseline.composing {
        // Check prim exists.
        if !prims.iter().any(|p| p == prim_path) {
            failures.push(format!("missing prim: {prim_path}"));
            continue;
        }

        // Check child names.
        for child in &expected.child_names {
            let child_path = format!("{prim_path}/{child}");
            if !prims.iter().any(|p| p == &child_path) {
                failures.push(format!("missing child: {child_path}"));
            }
        }

        // Check property names.
        for prop in &expected.property_names {
            let prop_path = format!("{prim_path}.{prop}");
            if !stage.has_spec(sdf::path(&prop_path).unwrap()).unwrap_or(false) {
                failures.push(format!("missing property: {prop_path}"));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "composition test {name} ({format}) failed:\n  {}",
        failures.join("\n  "),
    );
}

/// Assets whose `pcp.txt` baseline the [`run_pcp`] harness cannot reproduce
/// yet, so they fall back to the looser `pcp.json` existence checks. Three
/// reasons:
///
/// - The golden carries a Python traceback or a trailing `Errors`/`Warning`
///   section (the C++ test framework prints these for error cases); our
///   generated body has no such trailer.
/// - The golden contains a `Time Offsets`, `Prohibited child names`, or
///   `Deleted target paths` section. The generator does not emit these yet
///   (relocate prohibited-children composition and per-prim time-offset dumps
///   are future work).
/// - A known composition gap: the golden is a genuine mismatch we have not
///   fixed yet. These are grouped at the end of the list, each cluster tagged
///   with a `TODO` naming the missing mechanism; remove an asset once its
///   cluster lands.
///
/// Assets outside this list are compared byte-for-byte; a real composition
/// mismatch there is a bug to fix, not a reason to suppress.
const SKIP_PCP_COMPLIANCE: &[&str] = &[
    "BasicInherits_root",
    "BasicPayload_root",
    "BasicRelocateToAnimInterfaceAsNewRootPrim_root",
    "BasicRelocateToAnimInterface_root",
    "BasicTimeOffset_root",
    "ElidedAncestralRelocates_root",
    "ErrorArcCycle_root",
    "ErrorInconsistentProperties_root",
    "ErrorInvalidAuthoredRelocates_root",
    "ErrorInvalidConflictingRelocates_root",
    "ErrorInvalidInstanceTargetPath_root",
    "ErrorInvalidPayload_root",
    "ErrorInvalidPreRelocateTargetPath_root",
    "ErrorInvalidReferenceToRelocationSource_root",
    "ErrorInvalidTargetPath_root",
    "ErrorOpinionAtRelocationSource_root",
    "ErrorRelocateWithVariantSelection_root",
    "ErrorSublayerCycle_root",
    "PayloadsAndAncestralArcs2_root",
    "PayloadsAndAncestralArcs3_root",
    "ReferenceListOpsWithOffsets_root",
    "RelocatePrimsWithSameName_root",
    "RelocateToNone_root",
    "SubrootReferenceAndVariants_root",
    "SubrootReferenceNonCycle_root",
    "TimeCodesPerSecond_root",
    "TimeCodesPerSecond_root_12fps",
    "TimeCodesPerSecond_root_24tcps_12fps",
    "TimeCodesPerSecond_root_48tcps",
    "TimeCodesPerSecond_session",
    "TimeCodesPerSecond_session_24fps",
    "TimeCodesPerSecond_session_48tcps",
    "TrickyConnectionToRelocatedAttribute_root",
    "TrickyInheritsAndRelocates2_root",
    "TrickyInheritsAndRelocates3_root",
    "TrickyInheritsAndRelocates4_root",
    "TrickyInheritsAndRelocates5_root",
    "TrickyInheritsAndRelocatesToNewRootPrim_root",
    "TrickyInheritsAndRelocates_root",
    "TrickyListEditedTargetPaths_root",
    "TrickyLocalClassHierarchyWithRelocates_root",
    "TrickyMultipleRelocations2_root",
    "TrickyMultipleRelocations3_root",
    "TrickyMultipleRelocations4_root",
    "TrickyMultipleRelocations5_root",
    "TrickyMultipleRelocationsAndClasses2_root",
    "TrickyMultipleRelocationsAndClasses_root",
    "TrickyMultipleRelocations_root",
    "TrickyRelocatedTargetInVariant_root",
    "TrickyRelocationOfPrimFromPayload_root",
    "TrickyRelocationOfPrimFromVariant_root",
    "TrickyRelocationSquatter_root",
    "TrickySpecializesAndRelocates_root",
    "TrickySpookyInheritsInSymmetricArmRig_root",
    "TrickySpookyInheritsInSymmetricBrowRig_root",
    "TrickySpookyInherits_root",
    "TrickySpookyVariantSelectionInClass_root",
    "TrickySpookyVariantSelection_root",
    "TrickyVariantOverrideOfRelocatedPrim_root",
    "TypicalReferenceToChargroupWithRename_root",
    "bug69932_root",
    "bug92827_root",
    // --- Known composition gaps below: each `TODO` names the missing mechanism.
    //
    // TODO(specializes): implement `_EvalImpliedSpecializes` — copy specializes
    // nodes to the root layer stack. C++ `PcpCompareSiblingNodeStrength` orders
    // the globally-weak specializes band by distinguishing the implied copy
    // (site != origin) from the propagated original, which the in-place band
    // sort cannot reproduce without the copy-to-root.
    "BasicSpecializes_root",
    "BasicSpecializesAndInherits_root",
    "BasicSpecializesAndReferences_root",
    "BasicSpecializesAndVariants_root",
    "SpecializesAndAncestralArcs_root",
    "SpecializesAndAncestralArcs2_root",
    "SpecializesAndAncestralArcs3_root",
    "SpecializesAndAncestralArcs4_root",
    "SpecializesAndAncestralArcs5_root",
    "SpecializesAndVariants4_root",
    "TrickyNestedSpecializes_root",
    "TrickyNestedSpecializes2_root",
    "TrickySpecializesAndInherits_root",
    "TrickySpecializesAndInherits2_root",
    "TrickySpecializesAndInherits3_root",
    "VariantSpecializesAndReferenceSurprisingBehavior_root",
    // TODO(variant-strength): the remaining variant cases need the ancestral
    // variant re-evaluation a sub-root arc target requires (a variant set
    // carried into a sub-build, which the top-level build does not yet re-expand
    // — the indexer defers these to the recursive builder), an inherit authored
    // inside a variant, or a weaker-selection precedence edge the builder gets
    // wrong too.
    "TrickyVariantSelectionInVariant_root",
    "TrickyVariantWeakerSelection2_root",
    "TrickyVariantWeakerSelection4_root",
    "SubrootInheritsAndVariants_root",
    "SubrootReferenceAndVariants2_root",
    "TrickyInheritsInVariants_root",
    "TrickyInheritsInVariants2_root",
    // TODO(variant-arcs): forward attribute connections / relationship targets
    // and references introduced inside a selected variant — the variant's
    // `Attribute connections` block is missing from the composed result.
    "BasicVariantWithConnections_root",
    "BasicVariantWithReference_root",
    // TODO(instancing): route instance prims through shared prototypes so the
    // prim stack and child names match the prototype-composed result.
    "BasicInstancing_root",
    "BasicInstancingAndNestedInstances_root",
    // TODO(implied-classes): the remaining implied/nested-class cases still
    // differ. Each defers a descendant prim to the recursive builder — its
    // ancestor graph carries a variant/specialize/relocate node the
    // ancestral-inherit seed cannot deepen yet (`SubrootReferenceAndClasses`
    // needs specializes), so the builder composes that prim with the older
    // ordering. `PayloadsAndAncestralArcs` also exercises a sub-root payload,
    // but its inherit prims are what still fail.
    "PayloadsAndAncestralArcs_root",
    "ImpliedAndAncestralInherits_ComplexEvaluation_root",
    "TrickyNestedClasses_root",
    "TrickyNestedClasses2_root",
    "TrickyNestedClasses4_root",
    "SubrootReferenceAndClasses_root",
    // TODO(subroot-relocates): a sub-root reference whose target carries
    // relocates — the relocated child set / prim stack differs.
    "SubrootReferenceAndRelocates_root",
    // TODO(expr-arcs): evaluate variable expressions in reference/payload asset
    // paths so the composed arc target resolves.
    "ExpressionsInPayloads_root",
    "ExpressionsInReferences_root",
];

/// The composition-dump separator: 72 dashes, matching the C++
/// `testPcpCompositionResults` framework.
fn separator() -> String {
    "-".repeat(72)
}

/// Display name for a layer identifier: its path relative to the asset's
/// `usda/` directory, with `/` separators. For the common case where every
/// layer lives directly in `usda/` this is the basename (`root.usd`); layers
/// in subdirectories keep their relative prefix (`sub1/sub1.usd`), matching the
/// C++ dump. Falls back to the basename when the identifier is not under
/// `canonical_base` (the already-canonicalized entry directory).
fn display_name(canonical_base: Option<&Path>, identifier: &str) -> String {
    if let (Some(base), Ok(id)) = (canonical_base, std::fs::canonicalize(identifier)) {
        if let Ok(rel) = id.strip_prefix(base) {
            return rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/");
        }
    }
    Path::new(identifier)
        .file_name()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| identifier.to_string())
}

/// A `Prim Stack` / `Property stacks` site line: four spaces, the layer
/// display name in a 20-wide field, one space, then the spec path.
fn site_line(out: &mut String, canonical_base: Option<&Path>, identifier: &str, path: &sdf::Path) {
    use std::fmt::Write as _;
    let _ = writeln!(out, "    {:<20} {}", display_name(canonical_base, identifier), path);
}

/// Python list-literal of names, e.g. `['a', 'b']` (matching the C++ dump,
/// which prints the result of `repr(list)`).
fn name_list(names: &[String]) -> String {
    let quoted: Vec<String> = names.iter().map(|n| format!("'{n}'")).collect();
    format!("[{}]", quoted.join(", "))
}

/// Emits a per-property `<header>:` section whose entries are keyed and ordered
/// by the composed property path (`Property stacks`, `Relationship targets`,
/// `Attribute connections` all share this shape). Each group prints its path
/// header then its items via `emit_item`. Nothing is written for an empty
/// `groups`.
fn write_grouped<T>(
    out: &mut String,
    header: &str,
    mut groups: Vec<(sdf::Path, Vec<T>)>,
    mut emit_item: impl FnMut(&mut String, &T),
) {
    use std::fmt::Write as _;
    if groups.is_empty() {
        return;
    }
    groups.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));
    let _ = writeln!(out, "{header}:");
    for (prop_path, items) in &groups {
        let _ = writeln!(out, "{prop_path}:");
        for item in items {
            emit_item(out, item);
        }
    }
    out.push('\n');
}

/// Regenerates the `pcp.txt` composition dump for a stage in the exact format
/// of the vendor baselines, so it can be diffed against the baseline
/// byte-for-byte instead of parsing the baseline into a structure.
fn pcp_dump(name: &str, entry: &str, base: &Path, stage: &usd::Stage) -> String {
    use std::fmt::Write as _;
    let sep = separator();
    let mut out = String::new();

    // The entry directory is canonicalized once; layer identifiers are then
    // displayed relative to it (see `display_name`).
    let canonical_base = std::fs::canonicalize(base).ok();
    let base = canonical_base.as_deref();

    let _ = writeln!(out, "Loading @composition/tests/assets/{name}/usda/{entry}@");
    out.push('\n');

    let _ = writeln!(out, "{sep}");
    let _ = writeln!(out, "Layer Stack:");
    for identifier in stage.layer_stack() {
        let _ = writeln!(out, "     {}", display_name(base, &identifier));
    }
    out.push('\n');

    let mut prims = Vec::new();
    stage
        .traverse(usd::PrimPredicate::ALL, |path| prims.push(path.clone()))
        .unwrap();

    for path in &prims {
        let prim = stage.prim_at_path(path.clone());

        let _ = writeln!(out, "{sep}");
        let _ = writeln!(out, "Results for composing <{path}>");
        out.push('\n');

        let _ = writeln!(out, "Prim Stack:");
        for (identifier, spec_path) in prim.prim_stack().unwrap() {
            site_line(&mut out, base, &identifier, &spec_path);
        }
        out.push('\n');

        let selections = prim.variant_sets().get_all_variant_selections().unwrap();
        if !selections.is_empty() {
            let _ = writeln!(out, "Variant Selections:");
            for (set, sel) in &selections {
                let _ = writeln!(out, "    {{{set} = {sel}}}");
            }
            out.push('\n');
        }

        let children = stage.prim_children(path.clone()).unwrap();
        if !children.is_empty() {
            let _ = writeln!(out, "Child names:");
            let _ = writeln!(out, "     {}", name_list(&children));
            out.push('\n');
        }

        let properties = stage.prim_properties(path.clone()).unwrap();
        if !properties.is_empty() {
            let _ = writeln!(out, "Property names:");
            let _ = writeln!(out, "     {}", name_list(&properties));
            out.push('\n');
        }

        // Property stacks list every property with an authored spec.
        let mut stacks: Vec<(sdf::Path, Vec<(String, sdf::Path)>)> = Vec::new();
        for name in &properties {
            let prop = prim.attribute(name);
            let stack = prop.property_stack().unwrap();
            if !stack.is_empty() {
                stacks.push((prop.path().clone(), stack));
            }
        }
        write_grouped(&mut out, "Property stacks", stacks, |out, (identifier, spec_path)| {
            site_line(out, base, identifier, spec_path);
        });

        // Relationship targets and attribute connections, split by spec type.
        let mut rel_targets: Vec<(sdf::Path, Vec<sdf::Path>)> = Vec::new();
        let mut attr_conns: Vec<(sdf::Path, Vec<sdf::Path>)> = Vec::new();
        for name in &properties {
            let Some(prop_path) = path.append_property(name).ok() else {
                continue;
            };
            match stage.spec_type(prop_path.clone()).unwrap() {
                Some(sdf::SpecType::Relationship) => {
                    let targets = prim.relationship(name).get_targets().unwrap();
                    if !targets.is_empty() {
                        rel_targets.push((prop_path, targets));
                    }
                }
                Some(sdf::SpecType::Attribute) => {
                    let conns = prim.attribute(name).get_connections().unwrap();
                    if !conns.is_empty() {
                        attr_conns.push((prop_path, conns));
                    }
                }
                _ => {}
            }
        }

        let emit_target = |out: &mut String, target: &sdf::Path| {
            let _ = writeln!(out, "    {target}");
        };
        write_grouped(&mut out, "Relationship targets", rel_targets, emit_target);
        write_grouped(&mut out, "Attribute connections", attr_conns, emit_target);
    }

    out
}

/// Builds a compact report of the first `limit` differing lines between the
/// generated dump and the baseline, aligned by line number. A full structural
/// diff is unnecessary — the dumps share line structure, so the first
/// divergences point straight at the offending prim/section.
fn first_diff_lines(actual: &str, expected: &str, limit: usize) -> String {
    use std::fmt::Write as _;
    let actual: Vec<&str> = actual.lines().collect();
    let expected: Vec<&str> = expected.lines().collect();
    let mut report = String::new();
    let mut shown = 0;
    for i in 0..actual.len().max(expected.len()) {
        let a = actual.get(i).copied().unwrap_or("<eof>");
        let g = expected.get(i).copied().unwrap_or("<eof>");
        if a != g {
            let _ = writeln!(report, "  line {}:\n    actual: {a}\n    golden: {g}", i + 1);
            shown += 1;
            if shown >= limit {
                let _ = writeln!(report, "  …");
                break;
            }
        }
    }
    report
}

/// Regenerates the composition dump from the stage parsed by `format` and
/// asserts it matches the vendor `pcp.txt` baseline byte-for-byte.
///
/// The generated dump is format-independent: the `Loading` header is pinned to
/// the `usda/` source path the baseline records, and layer display names are
/// taken relative to the entry layer's directory (`usda/` for text, the asset
/// root for the `.usdc` copies), so the same baseline validates both parsers.
fn run_pcp(name: &str, format: Format, test_dir: &Path, baseline: &schema::Baseline, entry: &Path) {
    let expected = std::fs::read_to_string(test_dir.join("pcp.txt"))
        .expect("read pcp.txt")
        .replace("\r\n", "\n");

    let stage = open_stage(name, entry);
    let base = entry.parent().expect("entry has a parent directory");
    let actual = pcp_dump(name, &baseline.entry, base, &stage);
    if actual != expected {
        // Persist the full generated dump so a failing case can be diffed
        // against its baseline without re-running; the panic message only shows
        // the first few differing lines to keep test output readable.
        let dir = Path::new("target").join("pcp_out");
        let _ = std::fs::create_dir_all(&dir);
        let actual_path = dir.join(format!("{name}.{format}.actual.txt"));
        let _ = std::fs::write(&actual_path, &actual);
        panic!(
            "composition pcp mismatch for {name} ({format})\n  wrote {}\n{}",
            actual_path.display(),
            first_diff_lines(&actual, &expected, 6),
        );
    }
}

macro_rules! composition_tests {
    ($($name:ident),* $(,)?) => {
        composition_tests!(@expand $($name),*);
    };
    (@expand $($name:ident),*) => {
        $(
            composition_tests!(@one $name);
        )*
    };
    (@one $name:ident) => {
        #[cfg(test)]
        #[allow(non_snake_case)]
        mod $name {
            use super::*;
            #[test]
            fn text() { run(stringify!($name), Format::Text); }
            #[test]
            fn binary() { run(stringify!($name), Format::Binary); }
        }
    };
}

composition_tests! {
    BasicAncestralReference_root,
    BasicDuplicateSublayer_root,
    BasicInherits_root,
    BasicInstancing_root,
    BasicInstancingAndNestedInstances_root,
    BasicInstancingAndVariants_root,
    BasicListEditing_root,
    BasicListEditingWithInherits_root,
    BasicLocalAndGlobalClassCombination_root,
    BasicNestedPayload_root,
    BasicNestedVariants_root,
    BasicNestedVariantsWithSameName_root,
    BasicOwner_root,
    BasicPayload_root,
    BasicPayloadDiamond_root,
    BasicReference_session,
    BasicReferenceAndClass_root,
    BasicReferenceAndClassDiamond_root,
    BasicReferenceDiamond_root,
    BasicRelocateToAnimInterface_root,
    BasicRelocateToAnimInterfaceAsNewRootPrim_root,
    BasicSpecializes_root,
    BasicSpecializesAndInherits_root,
    BasicSpecializesAndReferences_root,
    BasicSpecializesAndVariants_root,
    BasicTimeOffset_root,
    BasicVariantWithConnections_root,
    BasicVariantWithReference_root,
    bug69932_root,
    bug74847_root,
    bug92827_root,
    case1_root,
    ElidedAncestralRelocates_root,
    ErrorArcCycle_root,
    ErrorConnectionPermissionDenied_root,
    ErrorInconsistentProperties_root,
    ErrorInvalidAuthoredRelocates_root,
    ErrorInvalidConflictingRelocates_root,
    ErrorInvalidInstanceTargetPath_root,
    ErrorInvalidPayload_root,
    ErrorInvalidPreRelocateTargetPath_root,
    ErrorInvalidReferenceToRelocationSource_root,
    ErrorInvalidTargetPath_root,
    ErrorOpinionAtRelocationSource_root,
    ErrorOwner_root,
    ErrorPermissionDenied_root,
    ErrorRelocateWithVariantSelection_root,
    ErrorSublayerCycle_root,
    ExpressionsInPayloads_root,
    ExpressionsInReferences_root,
    ImpliedAndAncestralInherits_ComplexEvaluation_root,
    ImpliedAndAncestralInherits_root,
    PayloadsAndAncestralArcs_root,
    PayloadsAndAncestralArcs2_root,
    PayloadsAndAncestralArcs3_root,
    ReferenceListOpsWithOffsets_root,
    RelativePathPayloads_root,
    RelativePathReferences_root,
    RelocatePrimsWithSameName_root,
    RelocateToNone_root,
    SpecializesAndAncestralArcs_root,
    SpecializesAndAncestralArcs2_root,
    SpecializesAndAncestralArcs3_root,
    SpecializesAndAncestralArcs4_root,
    SpecializesAndAncestralArcs5_root,
    SpecializesAndVariants_root,
    SpecializesAndVariants2_root,
    SpecializesAndVariants3_root,
    SpecializesAndVariants4_root,
    SubrootInheritsAndVariants_root,
    SubrootReferenceAndClasses_root,
    SubrootReferenceAndRelocates_root,
    SubrootReferenceAndVariants_root,
    SubrootReferenceAndVariants2_root,
    SubrootReferenceNonCycle_root,
    TimeCodesPerSecond_root,
    TimeCodesPerSecond_root_12fps,
    TimeCodesPerSecond_root_24tcps_12fps,
    TimeCodesPerSecond_root_48tcps,
    TimeCodesPerSecond_session,
    TimeCodesPerSecond_session_24fps,
    TimeCodesPerSecond_session_48tcps,
    TrickyClassHierarchy_root,
    TrickyConnectionToRelocatedAttribute_root,
    TrickyInheritsAndRelocates_root,
    TrickyInheritsAndRelocates2_root,
    TrickyInheritsAndRelocates3_root,
    TrickyInheritsAndRelocates4_root,
    TrickyInheritsAndRelocates5_root,
    TrickyInheritsAndRelocatesToNewRootPrim_root,
    TrickyInheritsInVariants_root,
    TrickyInheritsInVariants2_root,
    TrickyListEditedTargetPaths_root,
    TrickyLocalClassHierarchyWithRelocates_root,
    TrickyMultipleRelocations_root,
    TrickyMultipleRelocations2_root,
    TrickyMultipleRelocations3_root,
    TrickyMultipleRelocations4_root,
    TrickyMultipleRelocations5_root,
    TrickyMultipleRelocationsAndClasses_root,
    TrickyMultipleRelocationsAndClasses2_root,
    TrickyNestedClasses_root,
    TrickyNestedClasses2_root,
    TrickyNestedClasses3_root,
    TrickyNestedClasses4_root,
    TrickyNestedSpecializes_root,
    TrickyNestedSpecializes2_root,
    TrickyNestedVariants_root,
    TrickyNonLocalVariantSelection_root,
    TrickyRelocatedTargetInVariant_root,
    TrickyRelocationOfPrimFromPayload_root,
    TrickyRelocationOfPrimFromVariant_root,
    TrickyRelocationSquatter_root,
    TrickySpecializesAndInherits_root,
    TrickySpecializesAndInherits2_root,
    TrickySpecializesAndInherits3_root,
    TrickySpecializesAndRelocates_root,
    TrickySpookyInherits_root,
    TrickySpookyInheritsInSymmetricArmRig_root,
    TrickySpookyInheritsInSymmetricBrowRig_root,
    TrickySpookyVariantSelection_root,
    TrickySpookyVariantSelectionInClass_root,
    TrickyVariantAncestralSelection_root,
    TrickyVariantIndependentSelection_root,
    TrickyVariantInPayload_root,
    TrickyVariantOverrideOfLocalClass_root,
    TrickyVariantOverrideOfRelocatedPrim_root,
    TrickyVariantSelectionInVariant_root,
    TrickyVariantSelectionInVariant2_root,
    TrickyVariantWeakerSelection_root,
    TrickyVariantWeakerSelection2_root,
    TrickyVariantWeakerSelection3_root,
    TrickyVariantWeakerSelection4_root,
    TypicalReferenceToChargroup_root,
    TypicalReferenceToChargroupWithRename_root,
    TypicalReferenceToRiggedModel_root,
    VariantSpecializesAndReference_root,
    VariantSpecializesAndReferenceSurprisingBehavior_root,
}

#[cfg(test)]
mod reorder {
    use super::*;

    fn open_fixture() -> usd::Stage {
        usd::Stage::open("fixtures/reorder.usda").expect("open reorder fixture")
    }

    #[test]
    fn prim_order_reorders_named_children() {
        let stage = open_fixture();
        let children = stage.prim_children(sdf::path("/Root").unwrap()).unwrap();
        assert_eq!(children, vec!["C", "D", "A", "B"]);
    }

    #[test]
    fn property_order_ignored_in_usd_mode() {
        // USD value resolution ignores `reorder properties`, so the composed
        // order follows authoring order despite the `reorder properties = [y, x]`
        // opinion in the fixture.
        let stage = open_fixture();
        let props = stage.prim_properties(sdf::path("/Props").unwrap()).unwrap();
        assert_eq!(props, vec!["x", "y", "z"]);
    }
}

#[cfg(test)]
mod value_resolution {
    use std::collections::HashMap;

    use super::*;
    use openusd::sdf::{FieldKey, Specifier, Value, Variability};

    fn open_fixture() -> usd::Stage {
        usd::Stage::open("fixtures/value_resolution.usda").expect("open value_resolution fixture")
    }

    fn dictionary<'a>(dict: &'a HashMap<String, Value>, key: &str) -> &'a HashMap<String, Value> {
        match dict.get(key) {
            Some(Value::Dictionary(value)) => value,
            other => panic!("expected dictionary at {key:?}, got {other:?}"),
        }
    }

    fn string<'a>(dict: &'a HashMap<String, Value>, key: &str) -> &'a str {
        match dict.get(key) {
            Some(Value::String(value) | Value::Token(value)) => value,
            other => panic!("expected string/token at {key:?}, got {other:?}"),
        }
    }

    #[test]
    fn specifier_inherit_only_resolves_to_class() {
        // Local `over` opinion plus an inherit from a `class`. With strongest-
        // wins this would be `over`; per spec 12.2.1 it must be `class`.
        let stage = open_fixture();
        let value: Option<Value> = stage
            .field(sdf::path("/InheritOnly").unwrap(), FieldKey::Specifier)
            .unwrap();
        assert_eq!(value, Some(Value::Specifier(Specifier::Class)));
    }

    #[test]
    fn specifier_all_over_resolves_to_over() {
        let stage = open_fixture();
        let value: Option<Value> = stage
            .field(sdf::path("/AllOver").unwrap(), FieldKey::Specifier)
            .unwrap();
        assert_eq!(value, Some(Value::Specifier(Specifier::Over)));
    }

    #[test]
    fn specifier_def_resolves_to_def() {
        let stage = open_fixture();
        let value: Option<Value> = stage
            .field(sdf::path("/DefPrim").unwrap(), FieldKey::Specifier)
            .unwrap();
        assert_eq!(value, Some(Value::Specifier(Specifier::Def)));
    }

    #[test]
    fn variability_weakest_opinion_wins() {
        // The weak sublayer authors `uniform` while the strong layer omits the
        // field. Per spec 12.2.3 the resolved variability is the weakest
        // authored opinion (`uniform`).
        let stage = open_fixture();
        let value: Option<Value> = stage
            .field(sdf::path("/VarTest.attr").unwrap(), FieldKey::Variability)
            .unwrap();
        assert_eq!(value, Some(Value::Variability(Variability::Uniform)));
    }

    #[test]
    fn custom_any_true() {
        // Only the weak sublayer authors `custom`. Per spec 12.2.4 the
        // resolved value is `true` because *any* opinion in the stack is true.
        let stage = open_fixture();
        let value: Option<Value> = stage
            .field(sdf::path("/CustomTest.attr").unwrap(), FieldKey::Custom)
            .unwrap();
        assert_eq!(value, Some(Value::Bool(true)));
    }

    #[test]
    fn dictionary_values_compose_recursively() {
        let stage = open_fixture();
        let value: Option<Value> = stage
            .field(sdf::path("/DictTest").unwrap(), FieldKey::CustomData)
            .unwrap();
        let Some(Value::Dictionary(dict)) = value else {
            panic!("customData should resolve to a dictionary");
        };

        assert_eq!(string(&dict, "strongOnly"), "strong");
        assert_eq!(string(&dict, "weakOnly"), "weak");
        assert_eq!(string(&dict, "strongOver"), "strong");

        let nested = dictionary(&dict, "nested");
        assert_eq!(string(nested, "strongNested"), "strong");
        assert_eq!(string(nested, "weakNested"), "weak");

        let deep = dictionary(nested, "deep");
        assert_eq!(string(deep, "conflict"), "strong");
        assert_eq!(string(deep, "strongDeep"), "strong");
        assert_eq!(string(deep, "weakDeep"), "weak");

        assert_eq!(string(&dict, "strongScalarWins"), "strong-scalar");
        let strong_dict = dictionary(&dict, "strongDictWins");
        assert_eq!(string(strong_dict, "strongNested"), "strong");
    }

    #[test]
    fn layer_metadata_dictionary_uses_root_layer_only() {
        let stage = open_fixture();
        let value: Option<Value> = stage.field(sdf::Path::abs_root(), FieldKey::CustomLayerData).unwrap();
        let Some(Value::Dictionary(dict)) = value else {
            panic!("customLayerData should resolve to a dictionary");
        };

        assert_eq!(string(&dict, "rootOnly"), "root");
        assert!(!dict.contains_key("weakOnly"));

        let nested = dictionary(&dict, "nested");
        assert_eq!(string(nested, "rootNested"), "root");
        assert!(!nested.contains_key("weakNested"));
    }
}
