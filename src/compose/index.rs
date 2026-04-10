//! Prim composition index.
//!
//! A [`PrimIndex`] records, for a single composed prim, the ordered list of
//! layer specs that contribute opinions — from strongest to weakest. Value
//! resolution walks this list and returns the first opinion found.
//!
//! # LIVRPS strength ordering
//!
//! USD composes opinions using six arc types, ordered by strength:
//!
//! 1. **L**ocal — direct opinions in the root layer stack (sublayers)
//! 2. **I**nherits — opinions from class prims (`inherits = </Class>`)
//! 3. **V**ariants — opinions from the selected variant (`variants = { string v = "sel" }`)
//! 4. **R**eferences — opinions from referenced layers (`references = @model.usd@</Prim>`)
//! 5. **P**ayloads — like references but deferred (`payload = @heavy.usd@</Prim>`)
//! 6. **S**pecializes — like inherits but weakest (`specializes = </Base>`)
//!
//! Within each arc type, opinions are ordered by layer strength (root layer
//! strongest, deepest sublayer weakest).
//!
//! # How composition works
//!
//! ## Direct arcs
//!
//! Given a simple scene:
//!
//! ```text
//! # root.usda
//! def "Model" (
//!     references = @model.usd@</Model>
//! ) {
//!     string name = "local_opinion"    # L — strongest
//! }
//! ```
//!
//! ```text
//! # model.usd
//! def "Model" {
//!     string name = "from_reference"   # R — weaker
//! }
//! ```
//!
//! The prim index for `/Model` contains two nodes: `root.usda:/Model` (Root)
//! and `model.usd:/Model` (Reference). Querying `name` returns `"local_opinion"`
//! because local opinions are stronger than references.
//!
//! ## Recursive arc processing
//!
//! Arcs are followed transitively. If a referenced layer introduces an
//! inherit, that inherit is resolved within the referenced layer's context:
//!
//! ```text
//! # root.usda
//! def "Model" (references = @model.usd@</Model>) { }
//! class "Class" { }
//! ```
//!
//! ```text
//! # model.usd
//! def "Model" (inherits = </Class>) { }
//! class "Class" { double x = 1.0 }
//! ```
//!
//! The index for `/Model` includes: `root.usda:/Model` (Root),
//! `model.usd:/Model` (Reference), and `model.usd:/Class` (Inherit — discovered
//! by recursively processing arcs on the reference node).
//!
//! ## Sublayer stacks for external arcs
//!
//! When a reference or payload points to an external layer, that layer may
//! have its own sublayers. The target's full sublayer stack is included:
//!
//! ```text
//! # root.usda
//! def "Model" (references = @A.usd@</Model>) { }
//! ```
//!
//! ```text
//! # A.usd
//! (subLayers = [@B.usd@])
//! def "Model" { }
//! ```
//!
//! ```text
//! # B.usd
//! def "Model" { string x = "from_sublayer" }
//! ```
//!
//! The reference to `A.usd` brings in both `A.usd` and `B.usd` as the
//! target's layer stack, so `/Model.x` resolves to `"from_sublayer"`.
//!
//! ## Ancestral arc propagation (seeds)
//!
//! When a parent prim has composition arcs, descendants automatically pick
//! up opinions from the corresponding descendant path in the arc's target.
//! This is handled by "seed" collection — before building the index for a
//! prim, we walk its ancestors to find arcs that introduce remapped paths:
//!
//! ```text
//! # root.usda
//! def "Set" (payload = @set.usd@</Set>) { }
//! ```
//!
//! ```text
//! # set.usd
//! def "Set" {
//!     def "Prop" { string x = "from_payload" }
//! }
//! ```
//!
//! Building the index for `/Set/Prop`: the ancestor `/Set` has a payload arc.
//! The seed collector remaps `/Set/Prop` through the payload to produce
//! `set.usd:/Set/Prop`, so the property `x` is found.
//!
//! Seeds are expanded iteratively — if a seed introduces further arcs (e.g.
//! a reference inside a variant in a referenced layer), those are expanded
//! too, to arbitrary depth.
//!
//! ## Variant resolution
//!
//! Variant selections are gathered from all accumulated nodes (L + I),
//! following first-opinion-wins. The selection is applied by appending
//! `{setName=selection}` to each existing node's path, since the variant
//! set may be defined on the prim itself or on an inherited class:
//!
//! ```text
//! class "_class" (
//!     variantSets = "color"
//!     variants = { string color = "red" }
//! ) {
//!     variantSet "color" = {
//!         "red"  { string paint = "crimson" }
//!         "blue" { string paint = "navy" }
//!     }
//! }
//! def "Model" (inherits = </_class>) { }
//! ```
//!
//! The variant set lives on `/_class`, so variant resolution appends
//! `{color=red}` to the class path: `/_class{color=red}`.
//!
//! Variant sets can be nested (a variant spec defines another variant set),
//! so resolution loops until no new variant nodes are produced. When no
//! explicit selection is authored, the first variant in the set is used as
//! the default.
//!
//! ## Cross-seed variant resolution
//!
//! A variant selection authored in one composition context (e.g. an
//! ancestral variant override) may apply to a variant set introduced by a
//! different context (e.g. a reference). After all seeds are processed, a
//! final pass gathers all variant selections from the full node set and
//! resolves any remaining unprocessed variant sets:
//!
//! ```text
//! # root.usda
//! def "Group" (
//!     references = @group.usd@</Group>
//!     variants = { string standin = "sim" }
//! ) { }
//! ```
//!
//! ```text
//! # group.usd
//! def "Group" (variantSets = "standin") {
//!     variantSet "standin" = {
//!         "sim" { over "Model" (variants = { string v = "sim" }) { } }
//!     }
//!     def "Model" (references = @model.usd@</Model>) { }
//! }
//! ```
//!
//! The variant selection `standin=sim` comes from root.usda (one seed), but
//! the variant set is defined in group.usd (loaded via reference — another
//! seed). The cross-seed pass connects them.
//!
//! # Implementation structure
//!
//! - [`PrimIndex::build`] — entry point. Collects seeds, runs LIVRPS per
//!   seed, applies cross-seed variant resolution, then deduplicates nodes.
//! - [`build_recursive`] — runs the LIVRPS algorithm for a single path
//!   within a given layer stack. Called once per seed and recursively for
//!   each arc target.
//! - [`collect_seeds`] — walks ancestor prims to find composition arcs that
//!   introduce remapped paths for the target prim. Expands iteratively.
//! - [`resolve_cross_seed_variants`] — post-pass that resolves variant
//!   selections spanning multiple seed contexts.
//! - [`resolve_variant_selections_in`] — gathers explicit variant selections
//!   from nodes, with fallback to the first variant as default.
//!
//! See <https://openusd.org/release/glossary.html#livrps-strength-ordering>

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{LayerData, ListOp, Path, Payload, PayloadListOp, Reference, Value};

/// The type of composition arc that introduced a [`Node`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArcType {
    /// Direct opinions from the root layer stack (sublayers).
    Root,
    /// Inherited from a class prim.
    Inherit,
    /// Contributed by a selected variant.
    Variant,
    /// Brought in via a reference arc.
    Reference,
    /// Brought in via a payload arc.
    Payload,
    /// Contributed by a specializes arc (weakest).
    Specialize,
}

/// A single contributing spec in the composition index.
///
/// Each node points to a specific layer (by index) and the path within that
/// layer where the prim's opinions live. The path may differ from the
/// composed prim path when namespace remapping is involved (e.g. references).
#[derive(Debug, Clone)]
pub struct Node {
    /// Index into the stage's layer list.
    pub layer_index: usize,
    /// The path within that layer (may differ from composed path due to remapping).
    pub path: Path,
    /// The composition arc that introduced this node.
    #[allow(dead_code)] // Part of the public data model; read by tests and downstream users.
    pub arc: ArcType,
}

/// Composition index for a single prim.
///
/// Contains an ordered list of [`Node`]s from strongest to weakest.
/// Value resolution walks this list and takes the first opinion found.
#[derive(Debug, Clone)]
pub struct PrimIndex {
    /// Nodes ordered from strongest to weakest.
    pub nodes: Vec<Node>,
}

impl PrimIndex {
    /// Returns `true` if no layers contribute opinions for this prim.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Builds a prim index for the given path across the layer stack.
    ///
    /// Follows LIVERPS ordering:
    /// Local (sublayers) > Inherits > Variants > References > Payloads > Specializes.
    ///
    /// Composition arcs are processed recursively: when a reference or payload
    /// introduces nodes from another layer stack, the arcs on those nodes
    /// (inherits, variants, nested references, etc.) are followed as well.
    ///
    /// Ancestral arcs are also propagated: if a parent prim has a reference or
    /// payload, the descendant prim picks up the corresponding descendant spec
    /// from the referenced layer.
    pub(crate) fn build(path: &Path, layers: &[LayerData], identifiers: &[String]) -> Self {
        let mut nodes = Vec::new();

        // Collect all (layer_index, source_path, arc_type) seeds by walking
        // both the root layer stack and ancestral composition arcs.
        let seeds = collect_seeds(path, layers, identifiers);

        // Run LIVRPS on each seed context.
        for (layer_indices, source_path, arc) in &seeds {
            build_recursive(source_path, layer_indices, *arc, layers, identifiers, &mut nodes, 0);
        }

        // Post-process: resolve variant selections that span across seeds.
        resolve_cross_seed_variants(&mut nodes, layers, identifiers);

        // Propagate implied inherits/specializes through prefix equivalences.
        // Seeds encode equivalent prefixes (e.g. /Rig ↔ /_class ↔ /CharRig).
        // Inherit targets under one prefix should also resolve under the others.
        propagate_implied_arcs(&seeds, &mut nodes, layers);

        // Overlapping ancestor walks can produce the same node from multiple seeds.
        let mut seen = HashSet::new();
        nodes.retain(|n| seen.insert((n.layer_index, n.path.clone())));

        PrimIndex { nodes }
    }

    /// Resolves a field by walking nodes from strongest to weakest, returning the first opinion.
    ///
    /// When `prop_suffix` is `None`, queries use the node's path directly (zero-copy).
    /// When `Some`, appends the suffix to form a property path for each node.
    /// A [`Value::ValueBlock`] explicitly blocks opinions from weaker layers.
    pub(crate) fn resolve_field(
        &self,
        field: &str,
        layers: &[LayerData],
        prop_suffix: Option<&str>,
    ) -> Result<Option<Value>> {
        for node in &self.nodes {
            let query_path = match prop_suffix {
                Some(suffix) => Cow::Owned(Path::new(&format!("{}{suffix}", node.path))?),
                None => Cow::Borrowed(&node.path),
            };

            let data = &layers[node.layer_index];
            if !data.has_field(&query_path, field) {
                continue;
            }

            let value = data.get(&query_path, field)?;
            if matches!(value.as_ref(), Value::ValueBlock) {
                return Ok(None);
            }
            return Ok(Some(value.into_owned()));
        }

        Ok(None)
    }
}

/// Maximum recursion depth for nested composition arcs.
const MAX_COMPOSITION_DEPTH: usize = 100;

/// Recursively builds the LIVRPS index for a prim within a given layer stack.
///
/// `layer_stack` contains the indices into `layers` that form the current
/// composition context (e.g. the root layer + sublayers, or a referenced
/// layer + its sublayers). `arc` is the arc type that introduced this context.
fn build_recursive(
    path: &Path,
    layer_stack: &[usize],
    arc: ArcType,
    layers: &[LayerData],
    identifiers: &[String],
    nodes: &mut Vec<Node>,
    depth: usize,
) {
    assert!(
        depth <= MAX_COMPOSITION_DEPTH,
        "composition depth exceeded {MAX_COMPOSITION_DEPTH} for {path} — possible cycle"
    );

    // L — Local opinions within this layer stack.
    let local_start = nodes.len();
    for &i in layer_stack {
        if layers[i].has_spec(path) {
            nodes.push(Node {
                layer_index: i,
                path: path.clone(),
                arc,
            });
        }
    }
    let local_nodes_range = local_start..nodes.len();

    // I — Inherits: compose PathListOp across local nodes, then build
    // full index (with ancestral seed expansion) for each inherited prim.
    let inherits = compose_arc_list_in::<Path>(&nodes[local_nodes_range.clone()], FieldKey::InheritPaths, layers);
    for inherit_path in &inherits {
        let resolved = path.make_absolute(inherit_path);
        let seeds = collect_seeds(&resolved, layers, identifiers);
        for (stack, spath, _) in &seeds {
            build_recursive(spath, stack, ArcType::Inherit, layers, identifiers, nodes, depth + 1);
        }
    }

    // V — Variants: resolve variant selections iteratively. For each
    // selection, try appending it to every existing node's path (the
    // variant set may be defined on the prim itself or an inherited class).
    // Variant specs can themselves define nested variant sets, so we loop
    // until no new variant nodes are added.
    let mut processed_variants = HashSet::new();
    loop {
        let all_nodes_so_far = local_start..nodes.len();
        let selections = resolve_variant_selections_in(&nodes[all_nodes_so_far], layers);
        if selections.is_empty() {
            break;
        }

        let before = nodes.len();
        for (set_name, selection) in &selections {
            // Snapshot paths before mutating `nodes` in the inner loop.
            let bases: Vec<Path> = nodes[local_start..before].iter().map(|n| n.path.clone()).collect();
            for base in &bases {
                let variant_path = base.append_variant_selection(set_name, selection);
                if !processed_variants.insert(variant_path.clone()) {
                    continue;
                }
                for &i in layer_stack {
                    if layers[i].has_spec(&variant_path) {
                        nodes.push(Node {
                            layer_index: i,
                            path: variant_path.clone(),
                            arc: ArcType::Variant,
                        });
                    }
                }
            }
        }

        // No new variant nodes — all selections fully resolved.
        if nodes.len() == before {
            break;
        }
    }

    // Collect the range of all nodes added so far (L + I + V) for arc lookups.
    // In LIVRPS, arcs introduced by variants must also be followed.
    let all_opinion_nodes = local_start..nodes.len();

    // R — References: compose ReferenceListOp across L+I+V nodes, then
    // recursively build for each referenced layer stack.
    let references = compose_arc_list_in::<Reference>(&nodes[all_opinion_nodes.clone()], FieldKey::References, layers);
    for reference in &references {
        add_arc_nodes_recursive(
            &reference.asset_path,
            &reference.prim_path,
            ArcType::Reference,
            nodes,
            layers,
            identifiers,
            depth,
        );
    }

    // P — Payloads: same as references but weaker.
    let payloads = collect_payloads_in(&nodes[all_opinion_nodes.clone()], layers);
    for payload in &payloads {
        add_arc_nodes_recursive(
            &payload.asset_path,
            &payload.prim_path,
            ArcType::Payload,
            nodes,
            layers,
            identifiers,
            depth,
        );
    }

    // S — Specializes: composed across L+I+V nodes, build full index
    // (with ancestral seed expansion) for each specialized prim.
    let specializes = compose_arc_list_in::<Path>(&nodes[all_opinion_nodes], FieldKey::Specializes, layers);
    for specialize_path in &specializes {
        let resolved = path.make_absolute(specialize_path);
        let seeds = collect_seeds(&resolved, layers, identifiers);
        for (stack, spath, _) in &seeds {
            build_recursive(spath, stack, ArcType::Specialize, layers, identifiers, nodes, depth + 1);
        }
    }
}

/// Collects seed contexts for building a prim's composition index.
///
/// Returns `(layer_stack, source_path, arc_type)` tuples. The first entry is
/// always the root layer stack at the original path. Additional entries come
/// from ancestors that have composition arcs — the descendant suffix is
/// appended to the ancestor's remapped path.
fn collect_seeds(path: &Path, layers: &[LayerData], identifiers: &[String]) -> Vec<(Vec<usize>, Path, ArcType)> {
    let root_stack: Vec<usize> = (0..layers.len()).collect();
    let mut seeds = vec![(root_stack, path.clone(), ArcType::Root)];
    let mut seen = HashSet::new();

    // Iteratively expand seeds: for each seed, walk its remapped path's
    // ancestors within its layer stack to discover further arc mappings.
    let mut i = 0;
    while i < seeds.len() {
        let (ref layer_stack, ref seed_path, _) = seeds[i];
        let layer_stack = layer_stack.clone();
        let seed_path = seed_path.clone();
        i += 1;

        let mut ancestor_opt = seed_path.parent();
        while let Some(ancestor) = ancestor_opt {
            if ancestor == Path::abs_root() {
                break;
            }

            if layer_stack.iter().any(|&li| layers[li].has_spec(&ancestor)) {
                let mut ancestor_nodes = Vec::new();
                build_recursive(
                    &ancestor,
                    &layer_stack,
                    ArcType::Root,
                    layers,
                    identifiers,
                    &mut ancestor_nodes,
                    0,
                );
                // Variant sets from referenced layers need cross-seed resolution
                // to match with local variant selections.
                resolve_cross_seed_variants(&mut ancestor_nodes, layers, identifiers);
                for anode in &ancestor_nodes {
                    if anode.arc == ArcType::Root {
                        continue;
                    }
                    let Some(remapped_path) = seed_path.replace_prefix(&ancestor, &anode.path) else {
                        continue;
                    };
                    let key = (vec![anode.layer_index], remapped_path.clone());
                    if seen.insert(key) {
                        seeds.push((vec![anode.layer_index], remapped_path, anode.arc));
                    }
                }
            }

            ancestor_opt = ancestor.parent();
        }
    }

    seeds
}

/// Propagates implied inherit and specialize arcs through prefix equivalences.
///
/// Seeds for a composed prim encode a chain of path mappings:
///
/// ```text
/// /Rig/SymToesRig → /_class_CharRig/SymToesRig → /CharRig/SymToesRig
///       (root)             (inherit)                 (reference)
/// ```
///
/// All share suffix `/SymToesRig` with different prefixes. When an
/// inherit target `/CharRig/_Class_ToesRig` is found on a node from one
/// prefix, implied arcs at the equivalent prefixes (`/_class_CharRig/_Class_ToesRig`,
/// `/Rig/_Class_ToesRig`) must also be added.
fn propagate_implied_arcs(seeds: &[(Vec<usize>, Path, ArcType)], nodes: &mut Vec<Node>, layers: &[LayerData]) {
    if seeds.len() <= 1 {
        return;
    }

    // Seeds encode prefix equivalences — each seed's path is the composed
    // path with its ancestor portion remapped through a composition arc.
    // Extract prefixes by stripping the composed path's prim name suffix.
    let composed = seeds[0].1.as_str();
    let Some(last_slash) = composed.rfind('/') else {
        return;
    };
    let suffix = &composed[last_slash..];

    let mut prefix_map: Vec<(&str, &[usize])> = Vec::new();
    for (stack, spath, _) in seeds {
        let s = spath.as_str();
        if let Some(stripped) = s.strip_suffix(suffix) {
            prefix_map.push((stripped, stack));
        }
    }

    if prefix_map.len() <= 1 {
        return;
    }

    // Collect new implied nodes into a separate vec, then extend.
    let mut seen: HashSet<(usize, Path)> = nodes.iter().map(|n| (n.layer_index, n.path.clone())).collect();
    let mut new_nodes = Vec::new();

    for node in nodes.iter() {
        if node.arc != ArcType::Inherit && node.arc != ArcType::Specialize {
            continue;
        }
        let node_path = node.path.as_str();

        for &(prefix, _) in &prefix_map {
            // Skip empty prefix to avoid false positives on root paths.
            if prefix.is_empty() || !node_path.starts_with(prefix) {
                continue;
            }
            let tail = &node_path[prefix.len()..];

            for &(other_prefix, other_stack) in &prefix_map {
                if other_prefix == prefix {
                    continue;
                }
                let remapped = Path::from(format!("{other_prefix}{tail}"));
                for &li in other_stack {
                    if layers[li].has_spec(&remapped) && seen.insert((li, remapped.clone())) {
                        new_nodes.push(Node {
                            layer_index: li,
                            path: remapped.clone(),
                            arc: node.arc,
                        });
                    }
                }
            }
        }
    }

    nodes.append(&mut new_nodes);
}

/// Resolves variant selections that span across seeds.
///
/// After all seeds have been processed, there may be variant selections
/// authored in one seed's context (e.g. an ancestral variant override)
/// that should apply to variant sets introduced by another seed (e.g.
/// a reference). This pass gathers all variant selections from existing
/// nodes and resolves any unprocessed variant sets.
fn resolve_cross_seed_variants(nodes: &mut Vec<Node>, layers: &[LayerData], identifiers: &[String]) {
    let mut processed = HashSet::new();
    for node in nodes.iter() {
        if node.arc == ArcType::Variant {
            processed.insert(node.path.clone());
        }
    }

    let selections = resolve_variant_selections_in(nodes, layers);
    if selections.is_empty() {
        return;
    }

    let orig_len = nodes.len();
    for (set_name, selection) in &selections {
        for idx in 0..orig_len {
            let variant_path = nodes[idx].path.append_variant_selection(set_name, selection);
            if !processed.insert(variant_path.clone()) {
                continue;
            }

            let start = nodes.len();
            for (i, layer) in layers.iter().enumerate() {
                if layer.has_spec(&variant_path) {
                    nodes.push(Node {
                        layer_index: i,
                        path: variant_path.clone(),
                        arc: ArcType::Variant,
                    });
                }
            }
            let end = nodes.len();

            if start < end {
                // Collect arcs from new variant nodes before mutating `nodes`.
                let new_variant_nodes: Vec<Node> = nodes[start..end].to_vec();
                let refs = compose_arc_list_in::<Reference>(&new_variant_nodes, FieldKey::References, layers);
                let payloads = collect_payloads_in(&new_variant_nodes, layers);
                for reference in &refs {
                    add_arc_nodes_recursive(
                        &reference.asset_path,
                        &reference.prim_path,
                        ArcType::Reference,
                        nodes,
                        layers,
                        identifiers,
                        0,
                    );
                }
                for payload in &payloads {
                    add_arc_nodes_recursive(
                        &payload.asset_path,
                        &payload.prim_path,
                        ArcType::Payload,
                        nodes,
                        layers,
                        identifiers,
                        0,
                    );
                }
            }
        }
    }
}

/// Resolves variant selections by walking nodes strongest-to-weakest.
///
/// For each variant set, the first opinion wins.
fn resolve_variant_selections_in(nodes: &[Node], layers: &[LayerData]) -> HashMap<String, String> {
    let mut selections: HashMap<String, String> = HashMap::new();

    // Gather explicit selections (first opinion wins).
    for node in nodes {
        let data = &layers[node.layer_index];
        if let Ok(value) = data.get(&node.path, FieldKey::VariantSelection.as_str()) {
            if let Value::VariantSelectionMap(map) = value.into_owned() {
                for (set_name, selection) in map {
                    selections.entry(set_name).or_insert(selection);
                }
            }
        }
    }

    // For variant sets without an explicit selection, use the first variant
    // name as the default (matches USD's behavior).
    for node in nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, ChildrenKey::VariantSetChildren.as_str()) else {
            continue;
        };
        let Value::TokenVec(set_names) = value.into_owned() else {
            continue;
        };
        for set_name in set_names {
            let Entry::Vacant(entry) = selections.entry(set_name) else {
                continue;
            };
            let set_path = node.path.append_variant_selection(entry.key(), "");
            let Ok(val) = data.get(&set_path, ChildrenKey::VariantChildren.as_str()) else {
                continue;
            };
            let Value::TokenVec(variants) = val.into_owned() else {
                continue;
            };
            if let Some(first) = variants.into_iter().next() {
                entry.insert(first);
            }
        }
    }

    selections
}

/// Composes a list-op field across nodes, returning the flattened list.
fn compose_arc_list_in<T: Default + Clone + PartialEq>(nodes: &[Node], field: FieldKey, layers: &[LayerData]) -> Vec<T>
where
    Value: TryInto<ListOp<T>>,
{
    let field = field.as_str();
    let mut combined: Option<ListOp<T>> = None;

    // Walk from strongest to weakest, combining ListOps into a single reduced op.
    for node in nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, field) else {
            continue;
        };
        let Ok(list_op) = value.into_owned().try_into() else {
            continue;
        };
        combined = Some(match combined {
            Some(stronger) => stronger.combined_with(&list_op),
            None => list_op,
        });
    }

    combined.map(|op| op.reduced().flatten()).unwrap_or_default()
}

/// Collects payloads from nodes, handling both single `Payload` and `PayloadListOp`.
fn collect_payloads_in(nodes: &[Node], layers: &[LayerData]) -> Vec<Payload> {
    let mut combined: Option<PayloadListOp> = None;

    // Walk from strongest to weakest, combining payload ListOps.
    for node in nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, FieldKey::Payload.as_str()) else {
            continue;
        };

        let list_op = match value.into_owned() {
            Value::Payload(p) => PayloadListOp {
                explicit: true,
                explicit_items: vec![p],
                ..Default::default()
            },
            Value::PayloadListOp(op) => op,
            _ => continue,
        };

        combined = Some(match combined {
            Some(stronger) => stronger.combined_with(&list_op),
            None => list_op,
        });
    }

    combined.map(|op| op.reduced().flatten()).unwrap_or_default()
}

/// Adds nodes from a referenced or payloaded layer, then recursively
/// processes composition arcs on the target's layer stack.
///
/// If `asset_path` is empty, the target is internal (same layer stack).
/// `prim_path` is used for namespace remapping; if empty, the target
/// layer's `defaultPrim` is used.
fn add_arc_nodes_recursive(
    asset_path: &str,
    prim_path: &Path,
    arc: ArcType,
    nodes: &mut Vec<Node>,
    layers: &[LayerData],
    identifiers: &[String],
    depth: usize,
) {
    if asset_path.is_empty() {
        // Internal reference — target is within the same layer stack.
        // Use seed expansion so ancestor arcs (e.g. variants) are propagated.
        if prim_path.is_empty() {
            return;
        }
        let seeds = collect_seeds(prim_path, layers, identifiers);
        for (stack, spath, _) in &seeds {
            build_recursive(spath, stack, arc, layers, identifiers, nodes, depth + 1);
        }
    } else {
        // External reference — find the target layer and its sublayer stack.
        let Some(layer_index) = find_layer(asset_path, identifiers) else {
            return;
        };

        let source = if prim_path.is_empty() {
            // Use the target layer's defaultPrim.
            let root = Path::abs_root();
            let Ok(value) = layers[layer_index].get(&root, FieldKey::DefaultPrim.as_str()) else {
                return;
            };
            match value.into_owned() {
                Value::Token(name) | Value::String(name) => Path::new(&format!("/{name}")).unwrap_or_default(),
                _ => return,
            }
        } else {
            prim_path.clone()
        };

        // Use seed expansion so ancestor arcs in the target layer are propagated.
        let target_stack = find_sublayer_stack(layer_index, layers, identifiers);
        let seeds = collect_seeds(&source, layers, identifiers);
        // First seed is always the root stack; replace it with the target's sublayer stack.
        for (i, (stack, spath, _)) in seeds.iter().enumerate() {
            let effective_stack = if i == 0 { &target_stack } else { stack };
            build_recursive(spath, effective_stack, arc, layers, identifiers, nodes, depth + 1);
        }
    }
}

/// Returns the layer indices forming a sublayer stack rooted at `root_layer`.
///
/// Walks the `subLayers` field recursively to find all sublayers.
fn find_sublayer_stack(root_layer: usize, layers: &[LayerData], identifiers: &[String]) -> Vec<usize> {
    let mut stack = vec![root_layer];
    let mut queue = vec![root_layer];

    while let Some(idx) = queue.pop() {
        let root = Path::abs_root();
        let Ok(value) = layers[idx].get(&root, FieldKey::SubLayers.as_str()) else {
            continue;
        };
        if let Value::StringVec(sub_paths) = value.into_owned() {
            for sub_path in sub_paths {
                if let Some(sub_idx) = find_layer(&sub_path, identifiers) {
                    if !stack.contains(&sub_idx) {
                        stack.push(sub_idx);
                        queue.push(sub_idx);
                    }
                }
            }
        }
    }

    stack
}

/// Finds a layer index whose identifier matches `asset_path`.
///
/// Tries an exact match first, then falls back to suffix matching at a
/// path separator boundary (so `_stage.usda` matches `/abs/path/_stage.usda`
/// but not `/abs/path/not_stage.usda`). Strips leading `./` before matching.
fn find_layer(asset_path: &str, identifiers: &[String]) -> Option<usize> {
    let sep = std::path::MAIN_SEPARATOR as u8;
    let needle = asset_path.strip_prefix("./").unwrap_or(asset_path);

    for (i, id) in identifiers.iter().enumerate() {
        if *id == needle {
            return Some(i);
        }

        if id.ends_with(needle) {
            let prefix_len = id.len() - needle.len();
            if prefix_len > 0 && id.as_bytes()[prefix_len - 1] == sep {
                return Some(i);
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;
    use crate::compose::collect_layers;
    use crate::sdf::LayerData;

    use anyhow::Result;

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

    /// Loads layers and splits into parallel vecs for PrimIndex::build.
    fn load_layers(path: &str) -> Result<(Vec<LayerData>, Vec<String>)> {
        let resolver = DefaultResolver::new();
        let collected = collect_layers(&resolver, path)?;
        let mut layers = Vec::new();
        let mut identifiers = Vec::new();
        for layer in collected {
            identifiers.push(layer.identifier);
            layers.push(layer.data);
        }
        Ok((layers, identifiers))
    }

    /// Builds a prim index for a given path string.
    fn build(layers: &[LayerData], identifiers: &[String], prim: &str) -> PrimIndex {
        PrimIndex::build(&Path::from(prim), layers, identifiers)
    }

    #[test]
    fn single_layer_root_node() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("active.usda"))?;
        let index = build(&layers, &ids, "/World");

        assert_eq!(index.nodes.len(), 1);
        assert_eq!(index.nodes[0].layer_index, 0);
        assert_eq!(index.nodes[0].arc, ArcType::Root);
        Ok(())
    }

    #[test]
    fn sublayer_two_root_nodes() -> Result<()> {
        let (layers, ids) = load_layers(&fixture_path("sublayer_override.usda"))?;
        let index = build(&layers, &ids, "/World");

        assert_eq!(index.nodes.len(), 2, "both layers should have /World");
        assert_eq!(index.nodes[0].layer_index, 0, "stronger layer first");
        assert_eq!(index.nodes[1].layer_index, 1, "weaker layer second");
        Ok(())
    }

    #[test]
    fn prim_only_in_stronger_layer() -> Result<()> {
        let (layers, ids) = load_layers(&fixture_path("sublayer_override.usda"))?;
        let index = build(&layers, &ids, "/World/Sphere");

        assert_eq!(index.nodes.len(), 1);
        assert_eq!(index.nodes[0].layer_index, 0);
        Ok(())
    }

    #[test]
    fn nonexistent_prim_empty_index() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("active.usda"))?;
        let index = build(&layers, &ids, "/DoesNotExist");

        assert!(index.is_empty());
        Ok(())
    }

    #[test]
    fn reference_arc_present() -> Result<()> {
        let (layers, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        let index = build(&layers, &ids, "/World/MyPrim");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Reference));
        Ok(())
    }

    #[test]
    fn inherit_arc_present() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("class_inherit.usda"))?;
        let index = build(&layers, &ids, "/World/cubeWithoutSetColor");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn inherit_root_is_strongest() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("class_inherit.usda"))?;
        let index = build(&layers, &ids, "/World/cubeWithSetColor");
        let arcs: Vec<_> = index.nodes.iter().map(|n| n.arc).collect();

        assert_eq!(arcs[0], ArcType::Root);
        assert!(arcs.contains(&ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn variant_arc_with_selection() -> Result<()> {
        let path = format!(
            "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
            manifest_dir()
        );
        let (layers, ids) = load_layers(&path)?;
        let index = build(&layers, &ids, "/World/Sphere");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Variant));

        let variant_node = index.nodes.iter().find(|n| n.arc == ArcType::Variant).unwrap();
        assert_eq!(variant_node.path.as_str(), "/World/Sphere{size=small}");
        Ok(())
    }

    #[test]
    fn specialize_arc_present() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("inherit_and_specialize.usda"))?;
        let index = build(&layers, &ids, "/World/cubeScene/specializes");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Specialize));
        Ok(())
    }

    #[test]
    fn find_layer_exact_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer(&ids[0], &ids).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_suffix_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("ref_target.usda", &ids).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_no_partial_name_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("target.usda", &ids).is_none());
        Ok(())
    }

    #[test]
    fn find_layer_not_found() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("nonexistent.usda", &ids).is_none());
        Ok(())
    }

    /// External references with `./` relative paths and nested references
    /// should be followed recursively (diamond pattern: Root -> A,B -> C).
    #[test]
    fn reference_diamond_recursive() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/BasicReferenceDiamond_root/usda/root.usd",
            manifest_dir()
        );
        let (layers, ids) = load_layers(&path)?;
        let index = build(&layers, &ids, "/Root");

        // Root references A.usd</A> and B.usd</B>, both of which reference C.usd</C>.
        assert!(
            index
                .nodes
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/A"),
            "should have node from A.usd"
        );
        assert!(
            index
                .nodes
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/B"),
            "should have node from B.usd"
        );
        assert!(
            index
                .nodes
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/C"),
            "should have node from C.usd via nested reference"
        );

        // A.usd defines A_attr on /A — verify the property spec is accessible.
        let a_idx = find_layer("A.usd", &ids).unwrap();
        let a_attr_path = Path::new("/A.A_attr").unwrap();
        assert!(
            layers[a_idx].has_spec(&a_attr_path),
            "A.usd should have spec at /A.A_attr"
        );
        Ok(())
    }

    /// Variant that introduces a specializes arc should propagate the
    /// specialized prim's variant opinions to the composing prim.
    #[test]
    fn specializes_from_variant() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/SpecializesAndVariants_root/usda/root.usd",
            manifest_dir()
        );
        let (layers, ids) = load_layers(&path)?;
        let index = build(&layers, &ids, "/B");

        // /B has variant introducingVariantSet=introducingVariant which specializes /A.
        // /A has variant nestedVariantSet=nestedVariant with property "test".
        assert!(
            index.nodes.iter().any(|n| n.arc == ArcType::Specialize),
            "should have specialize node from variant"
        );
        // The /A variant should also be present.
        assert!(
            index
                .nodes
                .iter()
                .any(|n| n.path.as_str().contains("{nestedVariantSet=nestedVariant}")),
            "should have /A's variant node"
        );
        Ok(())
    }

    /// References inside variant specs should be collected as dependencies
    /// so the target layers are loaded. Descendant prims should then pick up
    /// inherit arcs from the referenced layer through ancestral propagation.
    #[test]
    fn variant_reference_and_inherit_propagation() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/BasicVariantWithConnections_root/usda/root.usd",
            manifest_dir()
        );
        let (layers, ids) = load_layers(&path)?;

        // camera_perspective.usd should be loaded (referenced from inside a variant).
        assert!(
            find_layer("camera_perspective.usd", &ids).is_some(),
            "camera_perspective.usd should be collected from variant reference"
        );

        // /main_cam/Lens should inherit /camera/_localclass_Lens from camera_perspective.usd.
        let index = build(&layers, &ids, "/main_cam/Lens");
        assert!(
            index
                .nodes
                .iter()
                .any(|n| n.path.as_str() == "/camera/_localclass_Lens"),
            "should have inherit node for _localclass_Lens"
        );
        Ok(())
    }

    /// Variant selections from inherited classes should propagate to
    /// the inheriting prim, including selections nested inside the
    /// class's own variant specs.
    #[test]
    fn inherited_variant_selection_propagation() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/TrickyVariantWeakerSelection2_root/usda/root.usd",
            manifest_dir()
        );
        let (layers, ids) = load_layers(&path)?;
        let index = build(&layers, &ids, "/bob");

        // /bob inherits _class_geotype which has geotype_selector=select_cube.
        // That variant sets geotype=cube. /bob's geotype=cube variant payloads geo.usd.
        // /bob/bob_body should exist from the payload.
        assert!(
            index.nodes.iter().any(|n| n.path.as_str().contains("{geotype=cube}")),
            "should have geotype=cube variant node from inherited selection"
        );
        Ok(())
    }
}
