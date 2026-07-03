//! Composition compliance tests.
//!
//! Each asset is opened via `Stage::open` through both the `.usda` text parser
//! and the `.usdc` binary parser, and the composed result is validated against
//! the vendor `pcp.txt` baseline by regenerating that dump byte-for-byte (see
//! [`assert_dump_matches`] / [`pcp_txt::pcp_dump`]). The handful of goldens that
//! can never be reproduced byte-for-byte ([`UNREPRODUCIBLE_GOLDEN`]) fall back to
//! the looser `pcp.json` existence checks ([`assert_prims_exist`]).

use std::path::Path;

use openusd::{pcp, sdf, usd};

const ASSETS: &str = "vendor/core-spec-supplemental-release_dec2025/composition/tests/assets";

/// JSON schema for loading pcp.json baselines.
mod pcp_json {
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

/// Global variant fallbacks for the museum assets.
///
/// The C++ Pcp test framework registers these through its plugin registry; we
/// have no plugin system, so this function compensates for that gap. The
/// registration is global, not per-asset: a `standin` variant set with no
/// authored selection resolves to `render` (e.g. `case1`,
/// `TypicalReferenceToRiggedModel`), while an asset that authors a `standin`
/// selection overrides it (e.g. `BasicNestedVariants` selects `anim`).
fn variant_fallbacks() -> pcp::VariantFallbackMap {
    pcp::VariantFallbackMap::new().add("standin", ["render"])
}

fn open_stage(entry: &Path) -> usd::Stage {
    usd::Stage::builder()
        .variant_fallbacks(variant_fallbacks())
        .open(entry.to_str().unwrap())
        .unwrap()
}

/// Validates an asset through the parser selected by `format`.
///
/// Active assets are checked against the byte-exact `pcp.txt` golden (see
/// [`assert_dump_matches`]); suppressed assets fall back to the looser `pcp.json`
/// existence checks (see [`assert_prims_exist`]). Running this for both
/// [`Format::Text`] and [`Format::Binary`] exercises both the `.usda` and
/// `.usdc` parsers against the same baseline. The `pcp.json` path is a
/// transitional fallback — it retires as suppressions clear.
fn run(name: &str, format: Format) {
    let test_dir = Path::new(ASSETS).join(name);
    let baseline_path = test_dir.join("pcp.json");
    let json =
        std::fs::read_to_string(&baseline_path).unwrap_or_else(|e| panic!("read {}: {e}", baseline_path.display()));
    let baseline: pcp_json::Baseline = serde_json::from_str(&json).expect("parse pcp.json");

    let entry = match format {
        Format::Text => test_dir.join("usda").join(&baseline.entry),
        Format::Binary => test_dir.join(&baseline.entry),
    };
    if !entry.exists() {
        return;
    }

    if UNREPRODUCIBLE_GOLDEN.contains(&name) {
        assert_prims_exist(name, format, &baseline, &entry);
    } else {
        assert_dump_matches(name, format, &test_dir, &baseline, &entry);
    }
}

/// Validates an [`UNREPRODUCIBLE_GOLDEN`] asset by checking that every baselined
/// prim, child, and property merely *exists* in the composed stage — the looser
/// `pcp.json` check. Skips error cases and assets with no composing data.
fn assert_prims_exist(name: &str, format: Format, baseline: &pcp_json::Baseline, entry: &Path) {
    if !baseline.errors.is_empty() || baseline.composing.is_empty() {
        return;
    }

    let stage = open_stage(entry);

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
        let props = stage.prim(prim_path.as_str()).property_names().unwrap_or_default();
        for prop in &expected.property_names {
            if !props.iter().any(|p| p.as_str() == prop.as_str()) {
                failures.push(format!("missing property: {prim_path}.{prop}"));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "composition test {name} ({format}) failed:\n  {}",
        failures.join("\n  "),
    );
}

/// Assets whose `pcp.txt` golden can never be reproduced byte-for-byte, so they
/// stay on the looser `pcp.json` existence check permanently. Every other
/// compliance asset is compared byte-for-byte; a real composition mismatch is a
/// bug to fix, not a reason to suppress.
///
/// In each case the golden is a Python traceback or a pxr-internal C++
/// `file.cpp:line` warning emitted while the reference test framework loads the
/// asset — text tied to the C++ implementation's source layout, not to
/// composition behavior. The per-entry comments below say which.
const UNREPRODUCIBLE_GOLDEN: &[&str] = &[
    // Variant selection authored inside an inherit / reference / relocate path.
    // The C++ text parser rejects these at load with a traceback; our parser
    // rejects them too (`usda::parser`'s `reject_variant_selection_in_path` and
    // its tests), but we do not emit the traceback body.
    "BasicInherits_root",
    "ErrorRelocateWithVariantSelection_root",
    "SubrootReferenceAndVariants_root",
    // Empty internal path — a payload, and a `relocates` target `<>`
    // respectively — which C++ logs as an "Ill-formed SdfPath <>" warning
    // carrying a `pxr/usd/sdf/path.cpp` location.
    "BasicPayload_root",
    "RelocateToNone_root",
];

/// Helper functions that generate a string matching the `pcp.txt` composition
/// dump from a set of spec files: we run our PCP engine, take the dump, and
/// compare it against the vendor golden to confirm compositions are correct.
/// The code here is mostly junky, unattractive string-formatting, but it only
/// runs during tests, so it does not matter much.
mod pcp_txt {
    use std::path::Path;

    use openusd::{pcp, sdf, usd};

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

    /// A `Time Offsets` row. A node row (`path` is `Some`) prints the layer in a
    /// 20-wide field, the path in a 15-wide field, then the arc and offset; a
    /// sublayer row prints the layer in a 32-wide field (keeping the arc column
    /// aligned with node rows), then `sublayer` and the offset.
    fn time_offset_line(
        out: &mut String,
        canonical_base: Option<&Path>,
        layer_id: &str,
        path: Option<&sdf::Path>,
        arc: &str,
        offset: sdf::LayerOffset,
    ) {
        use std::fmt::Write as _;
        let layer = display_name(canonical_base, layer_id);
        let (off, scale) = (offset.offset, offset.scale);
        match path {
            Some(path) => {
                let _ = writeln!(
                    out,
                    "    {layer:<20} {:<15} {arc:<10} (offset={off:.2}, scale={scale:.2})",
                    path.to_string(),
                );
            }
            None => {
                let _ = writeln!(out, "        {layer:<32} {arc:<10} (offset={off:.2}, scale={scale:.2})");
            }
        }
    }

    /// Tree pre-order walk of a prim index's nodes (C++ `WalkNodes` over the root
    /// node), excluding the synthetic inert tree root. Children are visited in their
    /// stored strength order.
    fn walk_nodes(index: &pcp::PrimIndex) -> Vec<pcp::NodeId> {
        let Some(root) = index.root() else {
            return Vec::new();
        };
        let mut out = Vec::new();
        let mut stack: Vec<pcp::NodeId> = index.children(root).iter().rev().copied().collect();
        while let Some(id) = stack.pop() {
            out.push(id);
            stack.extend(index.children(id).iter().rev().copied());
        }
        out
    }

    /// Python list-literal of names, e.g. `['a', 'b']` (matching the C++ dump,
    /// which prints the result of `repr(list)`).
    fn name_list<S: AsRef<str>>(names: &[S]) -> String {
        let quoted: Vec<String> = names.iter().map(|n| format!("'{}'", n.as_ref())).collect();
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
    pub fn pcp_dump(name: &str, entry: &str, base: &Path, stage: &usd::Stage) -> String {
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
            let prim = stage.prim(path.clone());

            let _ = writeln!(out, "{sep}");
            let _ = writeln!(out, "Results for composing <{path}>");
            out.push('\n');

            let _ = writeln!(out, "Prim Stack:");
            for (identifier, spec_path) in prim.prim_stack().unwrap() {
                site_line(&mut out, base, &identifier, &spec_path);
            }
            out.push('\n');

            // Time Offsets: walk the prim index's nodes in tree pre-order, printing
            // each node's cumulative `map_to_root` offset and every non-identity
            // sublayer member offset (C++ `testPcpCompositionResults`'s node walk).
            let index = prim.prim_index().graph().unwrap();
            let walk = walk_nodes(&index);
            let has_offsets = walk.iter().any(|&id| {
                let node = index.node(id);
                !node.map_to_parent().time_offset().is_identity()
                    || stage.node_layer_stack(node).iter().any(|(_, off)| !off.is_identity())
            });
            if has_offsets {
                let _ = writeln!(out, "Time Offsets:");
                for id in walk {
                    let node = index.node(id);
                    let layer_id = stage.layer_identifier(node.layer_id()).unwrap_or_default();
                    // Lowercase arc name matching C++ `PcpArcType`'s `displayName`.
                    let arc = match node.arc() {
                        pcp::ArcType::Root => "root",
                        pcp::ArcType::Inherit => "inherit",
                        pcp::ArcType::Variant => "variant",
                        pcp::ArcType::Relocate => "relocate",
                        pcp::ArcType::Reference => "reference",
                        pcp::ArcType::Payload => "payload",
                        pcp::ArcType::Specialize => "specialize",
                    };
                    time_offset_line(
                        &mut out,
                        base,
                        &layer_id,
                        Some(node.path()),
                        arc,
                        node.map_to_root().time_offset(),
                    );
                    for &(layer, off) in stage.node_layer_stack(node).iter() {
                        if !off.is_identity() {
                            let layer_id = stage.layer_identifier(layer).unwrap_or_default();
                            time_offset_line(&mut out, base, &layer_id, None, "sublayer", off);
                        }
                    }
                }
                out.push('\n');
            }

            let selections = prim.variant_sets().get_all_variant_selections().unwrap();
            if !selections.is_empty() {
                let _ = writeln!(out, "Variant Selections:");
                for (set, sel) in &selections {
                    let _ = writeln!(out, "    {{{set} = {sel}}}");
                }
                out.push('\n');
            }

            let (children, prohibited) = prim.prim_index().child_names().unwrap();
            if !children.is_empty() {
                let _ = writeln!(out, "Child names:");
                let _ = writeln!(out, "     {}", name_list(&children));
                out.push('\n');
            }

            if !prohibited.is_empty() {
                let _ = writeln!(out, "Prohibited child names:");
                let _ = writeln!(out, "     {}", name_list(&prohibited));
                out.push('\n');
            }

            let properties = prim.property_names().unwrap();
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
            // Deleted target paths from both kinds merge into one map, printed last.
            let rel_paths: std::collections::HashSet<sdf::Path> = prim
                .relationships()
                .unwrap()
                .iter()
                .map(|rel| rel.path().clone())
                .collect();
            let mut rel_targets: Vec<(sdf::Path, Vec<sdf::Path>)> = Vec::new();
            let mut attr_conns: Vec<(sdf::Path, Vec<sdf::Path>)> = Vec::new();
            let mut deleted: Vec<(sdf::Path, Vec<sdf::Path>)> = Vec::new();
            for name in &properties {
                let Some(prop_path) = path.append_property(name).ok() else {
                    continue;
                };
                if rel_paths.contains(&prop_path) {
                    let (targets, del) = prim.relationship(name).compute_targets().unwrap();
                    if !targets.is_empty() {
                        rel_targets.push((prop_path.clone(), targets));
                    }
                    if !del.is_empty() {
                        deleted.push((prop_path, del));
                    }
                } else {
                    let (conns, del) = prim.attribute(name).compute_connections().unwrap();
                    if !conns.is_empty() {
                        attr_conns.push((prop_path.clone(), conns));
                    }
                    if !del.is_empty() {
                        deleted.push((prop_path, del));
                    }
                }
            }

            let emit_target = |out: &mut String, target: &sdf::Path| {
                let _ = writeln!(out, "    {target}");
            };
            write_grouped(&mut out, "Relationship targets", rel_targets, emit_target);
            write_grouped(&mut out, "Attribute connections", attr_conns, emit_target);
            write_grouped(&mut out, "Deleted target paths", deleted, emit_target);
        }

        out
    }

    /// Builds a compact report of the first `limit` differing lines between the
    /// generated dump and the baseline, aligned by line number. A full structural
    /// diff is unnecessary — the dumps share line structure, so the first
    /// divergences point straight at the offending prim/section.
    pub fn first_diff_lines(actual: &str, expected: &str, limit: usize) -> String {
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

    /// The "CANNOT {verb}" phrasing for an arc, shared by the prohibited-relocation
    /// and arc-cycle diagnostics (the closing hop of a cycle uses "CANNOT {verb}").
    fn arc_cannot_verb(arc: pcp::ArcType) -> &'static str {
        match arc {
            pcp::ArcType::Inherit | pcp::ArcType::Specialize => "inherit from",
            pcp::ArcType::Relocate => "be relocated from",
            _ => "reference",
        }
    }

    /// The present-tense arc phrasing used in an arc-cycle chain ("references" / …).
    fn arc_present_verb(arc: pcp::ArcType) -> &'static str {
        match arc {
            pcp::ArcType::Inherit | pcp::ArcType::Specialize => "inherits from",
            pcp::ArcType::Relocate => "is relocated from",
            _ => "references",
        }
    }

    /// Renders the trailing `Errors`/footer section of the composition dump from the
    /// recoverable errors collected during composition, matching the C++ test
    /// framework's output.
    ///
    /// The framework prints only a subset of error kinds. Per-prim errors (e.g.
    /// invalid payloads) are grouped under an `Errors while composing </Prim>`
    /// section per prim, in first-seen (composition) order; layer-stack errors
    /// (sublayer cycles, invalid authored relocates) follow under a single
    /// `Errors while computing Layer Stack` section. Other kinds (e.g.
    /// `MissingDefaultPrim`) fall through the wildcard and are omitted, matching
    /// the baselines. A new error kind opts in by adding an arm below. When any
    /// error is rendered, the dump ends with the framework's `ERROR:` footer.
    pub fn error_trailer(name: &str, errors: &[pcp::Error], base: Option<&Path>, order: &[sdf::Path]) -> String {
        use std::fmt::Write as _;

        // Layer identifiers inside trailer messages use the asset-repo-relative form
        // `composition/tests/assets/<name>/usda/<rel>`, matching the `Loading` header
        // rather than the bare-basename form the site lines use.
        let layer_id = |id: &str| format!("composition/tests/assets/{name}/usda/{}", display_name(base, id));

        // `Some(site)` is a per-prim error grouped under that prim; `None` is a
        // layer-stack error. Collected in composition order.
        let entries: Vec<(Option<&sdf::Path>, String)> = errors
        .iter()
        .filter_map(|e| match e {
            pcp::Error::UnresolvedLayer {
                asset_path,
                arc: pcp::ArcType::Payload,
                introduced_by,
                site_path,
            } => Some((
                Some(site_path),
                format!(
                    "Could not open asset @{}@ for payload introduced by @{}@<{site_path}>.",
                    layer_id(asset_path),
                    layer_id(introduced_by),
                ),
            )),
            pcp::Error::UnresolvedPrimPath {
                arc,
                target_layer,
                prim_path,
                introduced_by,
                site_path,
            } if matches!(arc, pcp::ArcType::Payload | pcp::ArcType::Reference) => {
                let kind = if matches!(arc, pcp::ArcType::Payload) {
                    "payload"
                } else {
                    "reference"
                };
                Some((
                    Some(site_path),
                    format!(
                        "Unresolved {kind} prim path @{}@<{prim_path}> introduced by @{}@<{site_path}>",
                        layer_id(target_layer),
                        layer_id(introduced_by),
                    ),
                ))
            }
            pcp::Error::ProhibitedRelocationSource {
                arc,
                site,
                site_layer,
                target,
                target_layer,
                reloc_source,
                reloc_layer,
                composing,
            } => {
                let verb = arc_cannot_verb(*arc);
                Some((
                    Some(composing),
                    format!(
                        "@{}@<{site}>\nCANNOT {verb}:\n@{}@<{target}>\n\
                         which is a prohibited child of its parent because it would require allowing opinions \
                         from the source of a relocation at @{}@<{reloc_source}>.",
                        layer_id(site_layer),
                        layer_id(target_layer),
                        layer_id(reloc_layer),
                    ),
                ))
            }
            pcp::Error::OpinionAtRelocationSource {
                source_path,
                layer,
                composing,
            } => Some((
                Some(composing),
                format!(
                    "The layer @{}@ has an invalid opinion at the relocation source path <{source_path}>, \
                     which will be ignored.",
                    layer_id(layer),
                ),
            )),
            pcp::Error::InvalidExternalTargetPath {
                is_connection,
                target,
                property,
                layer,
                arc,
                arc_root,
                composing,
            } => {
                let kind = if *is_connection {
                    "attribute connection"
                } else {
                    "relationship target"
                };
                let arc = match arc {
                    pcp::ArcType::Inherit => "inherit",
                    pcp::ArcType::Specialize => "specializes",
                    pcp::ArcType::Payload => "payload",
                    pcp::ArcType::Variant => "variant",
                    _ => "reference",
                };
                Some((
                    Some(composing),
                    format!(
                        "The {kind} <{}> from <{}> in layer @{}@ refers to a path outside the scope of the {arc} \
                         from <{}>.  Ignoring.",
                        target,
                        property,
                        layer_id(layer),
                        arc_root,
                    ),
                ))
            }
            pcp::Error::InvalidInstanceTargetPath {
                is_connection,
                target,
                property,
                layer,
                composing,
            } => {
                let kind = if *is_connection {
                    "attribute connection"
                } else {
                    "relationship target"
                };
                Some((
                    Some(composing),
                    format!(
                        "The {kind} <{}> from <{}> in layer @{}@ is authored in a class but refers to an instance \
                         of that class.  Ignoring.",
                        target,
                        property,
                        layer_id(layer),
                    ),
                ))
            }
            pcp::Error::InconsistentPropertyType {
                property,
                defining_layer,
                defining_path,
                defining_is_attribute,
                conflicting_layer,
                conflicting_path,
                conflicting_is_attribute,
                composing,
            } => {
                let kind = |is_attr: bool| if is_attr { "an attribute spec" } else { "a relationship spec" };
                Some((
                    Some(composing),
                    format!(
                        "The property <{}> has inconsistent spec types.  \
                         The defining spec is @{}@<{}> and is {}.  \
                         The conflicting spec is @{}@<{}> and is {}.  The conflicting spec will be ignored.",
                        property,
                        layer_id(defining_layer),
                        defining_path,
                        kind(*defining_is_attribute),
                        layer_id(conflicting_layer),
                        conflicting_path,
                        kind(*conflicting_is_attribute),
                    ),
                ))
            }
            pcp::Error::SublayerCycle { root_layer, seen_layer } => Some((
                None,
                format!(
                    "Sublayer hierarchy with root layer @{}@ has cycles. \
                     Detected when layer @{}@ was seen in the layer stack for the second time.",
                    layer_id(root_layer),
                    layer_id(seen_layer),
                ),
            )),
            pcp::Error::InvalidRelocate {
                source_path,
                target_path,
                layer,
                reason,
            } => Some((
                None,
                format!(
                    "Relocation from <{source_path}> to <{target_path}> authored at @{}@</> is invalid and will be ignored: \
                     {reason}",
                    layer_id(layer),
                ),
            )),
            pcp::Error::ArcCycle(info) => {
                let mut msg = format!("Cycle detected:\n@{}@<{}>", layer_id(&info.root_layer), info.composing);
                let last = info.hops.len() - 1;
                for (i, hop) in info.hops.iter().enumerate() {
                    let prefix = if i == 0 { "" } else { "which " };
                    let verb = if i == last {
                        format!("CANNOT {}", arc_cannot_verb(hop.arc))
                    } else {
                        arc_present_verb(hop.arc).to_string()
                    };
                    msg.push_str(&format!("\n{prefix}{verb}:\n@{}@<{}>", layer_id(&hop.layer), hop.path));
                }
                // The C++ cycle diagnostic ends with a blank line, so each cycle
                // section shows two blank lines before its separator.
                msg.push('\n');
                Some((Some(&info.composing), msg))
            }
            pcp::Error::SameTargetRelocations { target, sources } => {
                let list = sources
                    .iter()
                    .map(|(s, l)| format!("relocation from <{s}> authored at @{}@</>", layer_id(l)))
                    .collect::<Vec<_>>()
                    .join("; ");
                Some((
                    None,
                    format!(
                        "The path <{}> is the target of multiple relocations from different sources. \
                         The following relocates to this target are invalid and will be ignored: {list}.",
                        target,
                    ),
                ))
            }
            pcp::Error::ConflictingRelocation {
                source_path,
                target_path,
                layer,
                other_source_path,
                other_target_path,
                other_layer,
                reason,
            } => Some((
                None,
                format!(
                    "Relocation from <{}> to <{}> authored at @{}@</> conflicts with another relocation \
                     from <{}> to <{}> authored at @{}@</> and will be ignored: {}",
                    source_path,
                    target_path,
                    layer_id(layer),
                    other_source_path,
                    other_target_path,
                    layer_id(other_layer),
                    reason,
                ),
            )),
            _ => None,
        })
        .collect();

        if entries.is_empty() {
            return String::new();
        }

        // Group per prim, then order the prim sections by traversal order (matching
        // the dump body) — not by when each error was collected, since a relocate
        // target can compose before the prim that authors the relocation. Layer-stack
        // errors follow under one section.
        let mut per_prim: Vec<(sdf::Path, Vec<String>)> = Vec::new();
        let mut layer_stack: Vec<String> = Vec::new();
        for (site, msg) in entries {
            match site {
                Some(path) => match per_prim.iter_mut().find(|(p, _)| p == path) {
                    Some((_, msgs)) => msgs.push(msg),
                    None => per_prim.push((path.clone(), vec![msg])),
                },
                None => layer_stack.push(msg),
            }
        }
        let order_index = |p: &sdf::Path| order.iter().position(|q| q == p).unwrap_or(usize::MAX);
        per_prim.sort_by_key(|(p, _)| order_index(p));

        let mut sections: Vec<(String, Vec<String>)> = per_prim
            .into_iter()
            .map(|(path, msgs)| (format!("Errors while composing <{path}>"), msgs))
            .collect();
        if !layer_stack.is_empty() {
            sections.push(("Errors while computing Layer Stack".to_string(), layer_stack));
        }

        let mut out = String::new();
        out.push('\n');
        for (header, msgs) in &sections {
            let _ = writeln!(out, "{}", separator());
            let _ = writeln!(out, "{header}");
            out.push('\n');
            for msg in msgs {
                let _ = writeln!(out, "{msg}");
            }
            out.push('\n');
        }
        let _ = writeln!(out, "ERROR: Unexpected error(s) encountered during test!");
        out
    }
}

/// Regenerates the composition dump from the stage parsed by `format` and
/// asserts it matches the vendor `pcp.txt` baseline byte-for-byte.
///
/// The generated dump is format-independent: the `Loading` header is pinned to
/// the `usda/` source path the baseline records, and layer display names are
/// taken relative to the entry layer's directory (`usda/` for text, the asset
/// root for the `.usdc` copies), so the same baseline validates both parsers.
fn assert_dump_matches(name: &str, format: Format, test_dir: &Path, baseline: &pcp_json::Baseline, entry: &Path) {
    let expected = std::fs::read_to_string(test_dir.join("pcp.txt"))
        .expect("read pcp.txt")
        .replace("\r\n", "\n");

    let stage = usd::Stage::builder()
        .variant_fallbacks(variant_fallbacks())
        .open(entry.to_str().unwrap())
        .unwrap();
    let base = entry.parent().expect("entry has a parent directory");
    // `pcp_dump` runs the queries that surface the errors into `errors`, so the
    // trailer is appended afterward.
    let mut actual = pcp_txt::pcp_dump(name, &baseline.entry, base, &stage);
    let canonical_base = std::fs::canonicalize(base).ok();
    // Order the per-prim error sections by traversal order (matching the dump
    // body), since errors may be collected in a different order.
    let mut order = Vec::new();
    stage
        .traverse(usd::PrimPredicate::ALL, |p| order.push(p.clone()))
        .unwrap();
    actual.push_str(&pcp_txt::error_trailer(
        name,
        &stage.composition_errors(),
        canonical_base.as_deref(),
        &order,
    ));
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
            pcp_txt::first_diff_lines(&actual, &expected, 6),
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

/// Composition over assets with arc cycles and invalid relocates must terminate
/// (these once overflowed the stack or hung). The compliance harness suppresses
/// these assets for their `Errors` trailer, and `assert_prims_exist` skips error
/// cases without traversing — so the termination + composed-result guarantees
/// are exercised here directly.
#[cfg(test)]
mod cycle_termination {
    use super::*;

    fn open(asset: &str) -> usd::Stage {
        let entry = Path::new(ASSETS).join(asset).join("usda").join("root.usd");
        open_stage(&entry)
    }

    /// `ErrorArcCycle` mixes reference, inherit, self-inherit, co-recursive, and
    /// ancestral-reference cycles. Traversing every prim must finish, and the
    /// dropped cycle arcs must leave the documented composed shape: the reference
    /// diamond keeps three nodes, while the self- and co-recursive inherits gain
    /// no runaway namespace child.
    #[test]
    fn error_arc_cycle_terminates() {
        let stage = open("ErrorArcCycle_root");
        let mut count = 0;
        stage.traverse(usd::PrimPredicate::ALL, |_| count += 1).unwrap();
        assert!(count > 0, "traversal composed at least one prim");

        // The reference diamond GroupRoot -> A -> B -> A keeps GroupA's child.
        let group_root = stage.prim(sdf::path("/GroupRoot").unwrap());
        assert_eq!(
            group_root
                .child_names()
                .unwrap()
                .iter()
                .map(|t| t.as_str())
                .collect::<Vec<_>>(),
            ["ChildA"]
        );

        // A prim inheriting its own ancestor gains no further self-named child.
        let yap_child = stage.prim(sdf::path("/YetAnotherParent/Child").unwrap());
        assert!(yap_child.child_names().unwrap().is_empty());

        // The co-recursive inherit resolves one level then drops the cycle.
        let corec = stage.prim(sdf::path("/CoRecursiveParent1/Child1/Child2").unwrap());
        assert!(corec.child_names().unwrap().is_empty());
    }

    /// `bug92827` authors a relocate whose target is an ancestor of its source.
    /// The relocate is invalid and dropped (it once hung), while the layer's
    /// valid relocate still makes `B` a prohibited child of `/Rig/Other/A`.
    #[test]
    fn bug92827_invalid_relocate_dropped() {
        let stage = open("bug92827_root");
        let a = stage.prim(sdf::path("/Rig/Other/A").unwrap());
        let (children, prohibited) = a.prim_index().child_names().unwrap();
        assert_eq!(children.iter().map(|t| t.as_str()).collect::<Vec<_>>(), ["Instance"]);
        assert_eq!(prohibited.iter().map(|t| t.as_str()).collect::<Vec<_>>(), ["B"]);
    }
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
        let children = stage.prim(sdf::path("/Root").unwrap()).child_names().unwrap();
        assert_eq!(
            children.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
            ["C", "D", "A", "B"]
        );
    }

    #[test]
    fn property_order_ignored_in_usd_mode() {
        // USD value resolution ignores `reorder properties`, so the composed
        // order follows authoring order despite the `reorder properties = [y, x]`
        // opinion in the fixture.
        let stage = open_fixture();
        let props = stage.prim(sdf::path("/Props").unwrap()).property_names().unwrap();
        assert_eq!(props.iter().map(|t| t.as_str()).collect::<Vec<_>>(), ["x", "y", "z"]);
    }
}

#[cfg(test)]
mod value_resolution {
    use std::collections::HashMap;

    use super::*;
    use openusd::sdf::{Specifier, Value, Variability};

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
            Some(Value::String(value)) => value,
            Some(Value::Token(value)) => value.as_str(),
            other => panic!("expected string/token at {key:?}, got {other:?}"),
        }
    }

    #[test]
    fn specifier_inherit_only_resolves_to_class() {
        // Local `over` opinion plus an inherit from a `class`. With strongest-
        // wins this would be `over`; per spec 12.2.1 it must be `class`.
        let stage = open_fixture();
        let value = stage.prim(sdf::path("/InheritOnly").unwrap()).specifier().unwrap();
        assert_eq!(value, Some(Specifier::Class));
    }

    #[test]
    fn specifier_all_over_resolves_to_over() {
        let stage = open_fixture();
        let value = stage.prim(sdf::path("/AllOver").unwrap()).specifier().unwrap();
        assert_eq!(value, Some(Specifier::Over));
    }

    #[test]
    fn specifier_def_resolves_to_def() {
        let stage = open_fixture();
        let value = stage.prim(sdf::path("/DefPrim").unwrap()).specifier().unwrap();
        assert_eq!(value, Some(Specifier::Def));
    }

    #[test]
    fn variability_weakest_opinion_wins() {
        // The weak sublayer authors `uniform` while the strong layer omits the
        // field. Per spec 12.2.3 the resolved variability is the weakest
        // authored opinion (`uniform`).
        let stage = open_fixture();
        let value = stage
            .prim(sdf::path("/VarTest").unwrap())
            .attribute("attr")
            .variability()
            .unwrap();
        assert_eq!(value, Some(Variability::Uniform));
    }

    #[test]
    fn custom_any_true() {
        // Only the weak sublayer authors `custom`. Per spec 12.2.4 the
        // resolved value is `true` because *any* opinion in the stack is true.
        let stage = open_fixture();
        let value = stage
            .prim(sdf::path("/CustomTest").unwrap())
            .attribute("attr")
            .is_custom()
            .unwrap();
        assert!(value);
    }

    #[test]
    fn dictionary_values_compose_recursively() {
        let stage = open_fixture();
        let value = stage.prim(sdf::path("/DictTest").unwrap()).custom_data().unwrap();
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
        let value = stage.custom_layer_data().unwrap();
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
