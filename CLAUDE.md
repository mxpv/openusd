# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a pure Rust implementation of OpenUSD (Universal Scene Description), Pixar's open-source framework for 3D computer graphics data interchange. The project aims to provide native Rust support without C++ dependencies for reading and writing USD files.

## Architecture

The codebase follows the same module structure as the C++ OpenUSD SDK:

- **`sdf/`** - Scene Description Foundations: Core data types, traits, and abstractions. Contains the `AbstractData` trait, `Value` enum (60+ variants), `Path`, `Spec`, `ListOp`, and schema field keys. `Layer` (C++ `SdfLayer`) bundles a resolved identifier with a backing `AbstractData` and exposes a Layer-tier authoring surface (`create_prim` / `override_prim` / `create_attribute` / `create_relationship` / `set_default_prim` / `clear_default_prim`) plus typed spec views (`PrimSpec[Mut]`, `AttributeSpec[Mut]`, `RelationshipSpec[Mut]`, `PseudoRootSpec[Mut]`). Authoring errors flow through `AuthoringError`.

- **`usda/`** - Text format (`.usda`): Lexer (logos) + recursive descent parser. `TextReader` implements `AbstractData`; `TextWriter` emits `.usda`.

- **`usdc/`** - Binary format (`.usdc`): USD's crate format with compressed data handling. `CrateData` implements `AbstractData`; `CrateWriter` emits `.usdc`.

- **`usdz/`** - Archive format (`.usdz`): ZIP-based package. `Archive` reads and `ArchiveWriter` emits `.usdz`.

- **`ar/`** - Asset Resolution: `Resolver` trait maps asset paths (`@...@`) to physical locations. `DefaultResolver` searches the filesystem.

- **`layer`** - Layer collection: `Collector::collect` recursively resolves and loads all layers from a root file, following sublayers, references, and payloads. Corresponds to C++ `PcpLayerStack`. `Collector` and `DependencyKind` are re-exported from the crate root. Defines `layer::Error` for recoverable collection failures (e.g. unresolved assets).

- **`pcp/`** - Prim Cache Population (composition engine): Implements LIVRPS strength ordering to compose opinions across layers. Corresponds to C++ `Pcp` module.
  - `pcp/mod.rs` — `pcp::Error`: composition errors (arc cycles, unresolved layers, missing/invalid `defaultPrim`, and `ArcPermissionDenied` for a direct arc to a `permission = private` site). `LayerStack`: bundles layers, identifiers, and precomputed sublayer stacks (C++ `PcpLayerStack`). `VariantFallbackMap`: maps variant set names to ordered fallback selections (C++ `PcpVariantFallbackMap`).
  - `pcp/cache.rs` — `Cache`: lazily-built per-prim composition cache (C++ `PcpCache`). Owns a `LayerStack` and passes it by shared reference to each build. `Cache::process_changes` is the single entry point for surgical invalidation — Stage feeds `(layer_index, sdf::ChangeList)` pairs and the cache classifies + applies. Returns `Result` from all public methods. `ensure_index` also enforces arc permissions: `detect_arc_permissions` finds each direct composition arc whose target site is `permission = private` (spec 10.3.3), then `PrimIndex::mark_permission_denied_under` marks every node reached through a denied target path `PERMISSION_DENIED` (the C++ `_AddArc` + `_InertSubtree` behavior) so it stops contributing to value resolution while staying visible structurally, and queues a `pcp::Error::ArcPermissionDenied` in `pending_errors` (the C++ `allErrors` out-param analog). Denied target paths flow down `CompositionContext::denied_prefixes` so descendant prims composed separately (where the arc is extended, not authored) are inerted too. `Stage::try_or_handle` drains `take_pending_errors` after each query — once the cache borrow is released, so the handler may re-enter — and routes them to `on_error`.
  - `pcp/change.rs` — `Changes` (`pub(crate)`), `CacheChanges`, `LayerStackChanges`: C++ `PcpChanges` analog. Three-tier classifier (significant / prim / spec) feeds `Changes::did_change` (pure analysis) and `Changes::apply` (commit). External callers go through `Cache::process_changes`, which ties both phases to the same cache instance.
  - `pcp/deps.rs` — `Dependencies`: reverse `(layer_index, site_path) → prim_index_paths` map populated at the end of `Cache::ensure_index`. Drives `lookup_with_ancestors` and `subtree_lookup` for change fanout. Synthetic self-registrations on every layer make cached misses (empty `PrimIndex`) reachable.
  - `pcp/index.rs`, `pcp/graph.rs`, `pcp/resolve.rs` — per-prim composition tree (C++ `PcpPrimIndex` / `PcpNodeRef`), split across three files: `graph.rs` owns the graph types (`Node`, `NodeId`, `NodeFlags`, `ArcType`, `PrimIndexGraph`) and the strength-order projection; `resolve.rs` owns value resolution over a composed `PrimIndex` (`PrimIndex::opinions()` and the `resolve_*` field walks); `index.rs` hosts the recursive `IndexBuilder` driver, the `PrimIndex` struct with its build/relocate entry points, and `CompositionContext`. `pcp/indexer.rs` holds `Indexer`, the in-progress task-queue replacement for `IndexBuilder` (C++ `Pcp_PrimIndexer`): it grows the graph node-by-node by draining a priority `BinaryHeap<Task>` (`EvalNodeReferences` before `EvalNodePayloads`, C++ `Task::Type`), without the builder's global `(layer, path, arc)` dedup set, so reference/payload diamonds (a shared target reached by two arc paths contributes a node on each) are kept rather than collapsed. Ancestral opinions enter through the graph-clone seed (C++ `_BuildInitialPrimIndexFromAncestor`): a child prim clones its parent's already-composed graph and deepens every site path by the child name (`PrimIndexGraph::append_child_name_to_all_sites`), so the references and payloads an ancestor introduced re-evaluate at the deepened path through the same queue. Inherits compose as class-based arcs (C++ `_EvalNodeInherits` → `_AddClassBasedArc`), and a class brought in through a reference is mirrored into the referencing namespace by implied-class propagation (C++ `_EvalImpliedClasses` → `_EvalImpliedClassTree`): an `EvalImpliedClasses` task carries a node's class-based children one level up toward the root, repeating up the arc chain; `Node` carries `sibling_num_at_origin` / `depth_below_introduction` / `path_at_introduction` (C++ `PcpNode`) for the class-hierarchy strength and start-node logic, and a non-contributing implied placeholder is marked `INERT`. `build_with_cache_in` composes with the `Indexer` where it reports support (currently local sites, external reference/payload arcs with explicit root-level targets, ancestral reference/payload propagation, and inherits of a root-level class with their implied classes) and otherwise falls back to `IndexBuilder` (specializes, variants, relocates, internal references, `defaultPrim` targets, sub-root arc targets needing a `PreviousFrame` sub-index, and instances); the byte-exact `pcp.txt` composition goldens validate the result as the ported feature set grows. `ArcType` variants are ordered by LIVERPS strength via `#[repr(u8)]` + derived `Ord`. `PrimIndexGraph` stores nodes in an append-only arena (`NodeId` handles index it and stay stable for the life of the index — no `Rc`/`RefCell`, so the whole index is `Send + Sync`) plus a separate `strength_order` projection; value resolution walks `PrimIndex::nodes()` (the projection, strongest first), while the builder reads `arena()` in structural order. Each node represents a `(layerStack, path)` site (C++ `PcpNode`): it holds a `layer_stack` of `(layer index, sublayer offset)` members, strongest first, plus a `has_specs` flag (C++ `PcpNode::HasSpecs`) recording whether any member authors a spec at its path. The task-queue `Indexer` stores the node's full site layer stack — so a cloned ancestral site deepened to a child with no opinion there is kept with `has_specs == false` — while `IndexBuilder` stores only the authoring members (always `has_specs == true`); value resolution iterates `node.layers()` and skips non-authoring layers naturally (each member's effective offset is `map_to_root`'s arc offset with the sublayer offset composed on top). `node.layer_index()` is the representative (strongest) member, and `is_empty` / `has_composition_arc` / the prim-stack dump exclude `has_specs == false` nodes. Reading a reference/payload from a member folds that member's sublayer offset into the arc offset (`compose_references_in` / `collect_payloads_in`, C++ `PcpComposeSiteReferences`). A reference/payload whose target authors no spec is kept as a `CULLED` node carrying the target layer stack: `PrimIndex::all_nodes()` surfaces it (and dependency registration covers its layers) so an editor and change tracking see the arc, while value resolution (`nodes()`), `is_empty`, and `has_composition_arc` skip it. A direct arc to a `permission = private` site (and any node reached through it, in this prim or a descendant) is marked `PERMISSION_DENIED` (C++ `_InertSubtree`): `nodes()` / `has_spec` / child names keep it for structural visibility, but `PrimIndex::opinions()` (the single value-resolution chokepoint) skips it, so its opinions never win. Each node also carries `parent`/`children`/`origin` tree links, a `NodeFlags` bitset (reserving the C++ `PcpNodeRef` state surface; `INERT`, `CULLED`, `PERMISSION_DENIED`, `HAS_SPECIALIZES`, `IMPLIED_CLASS`, and `RELOCATE_SOURCE` are set today), `namespace_depth` / `specialize_chain_depth` for strength comparison, and `map_to_parent` / `map_to_root` (`MapFunction`) for namespace translation and the arc-level retiming (`MapFunction` carries an `sdf::LayerOffset`) across arcs. The graph is a single rooted tree under a synthetic, inert root (`NodeFlags::INERT`) that owns every otherwise-parentless node (root `L` site, ancestor arcs, implied classes, relocate inserts); value resolution skips it, and re-parenting under its identity mapping is offset-neutral. `finalize_strength_order` builds the projection as a pre-order DFS of strength-ordered children, then appends the globally-weak specialize band (spec 10.4.1) ordered by the node strength comparator (`compare_sibling_node_strength` / `compare_node_strength`: arc type, specializes-chain depth, namespace depth, origin strength, sibling number) — mirroring C++ `_EvalImpliedSpecializes` copy-to-root without mutating the tree. Relocate nodes, grafted after the build, splice into the finalized projection. `IndexBuilder` takes a `&LayerStack` and evaluates LIVRPS with a `CompositionContext` flowing from parent to child; each build takes only `&` references (Rayon-friendly — see the `TODO(rayon)` at the cross-prim driver). The root `L` site scans only the build's ambient layer stack (the stage root layer stack, or a referenced asset's sublayer stack for an arc target) — opinions from other layer stacks arrive solely by following their arcs. Class arcs (inherit/specialize) and internal references compose their target as a full sub-index within that ambient stack (`merge_full_index` → `build_with_cache_in`), carrying the target's own ancestral context. A class a referenced prim brings in is mirrored into the referencing namespace by `propagate_implied_through_transfer` (C++ `_EvalImpliedClassTree`), conjugating the class arc through the reference's `MapFunction` (`implied_class` / `with_root_identity`); running it at each nesting level carries the implied class up the full reference chain to the root.
  - `pcp/mapping.rs` — `MapFunction`: namespace mapping between composition arcs (C++ `PcpMapFunction`). Stores (source, target) path pairs with longest-prefix matching alongside an `sdf::LayerOffset` time retiming. `MapFunction::new` canonicalizes the pairs (C++ `PcpMapFunction::Create`), dropping any a shorter-prefix entry already implies (e.g. an identity pair `(/A, /A)` made redundant by `(/, /)`) so the reverse lookup `map_target_to_source` stays unambiguous — implied-class conjugations (`implied_class` = `T ∘ C ∘ T⁻¹`) otherwise produce such redundant pairs. `compose` concatenates both path and time offsets. `node.map_to_root.time_offset()` is the node's arc-level offset; a contributing layer's effective offset folds its sublayer offset on top (`node.layers()`).
  - `pcp/rel.rs` — `Relocates`: isolated relocate object owning per-layer `layerRelocates`. Resolves pre-relocation source paths, builds relocated prim indices, and adjusts child name lists. Each relocate node carries the source site's full layer stack (`Node::new_site` / `graft_relocate_node` take a `Vec<(usize, LayerOffset)>`), so a relocate source spanning several sublayers keeps every member. Receives external data (`&LayerStack`, cached indices/contexts) through method parameters; does not reference `Cache` directly.
  - `pcp/clip.rs` — `ClipSet`: value clips (spec 12.3.4). Parses the explicit `clips` / `clipSets` metadata model and maps stage time to clip time during attribute value resolution. Template clips are resolved to explicit metadata elsewhere.

- **`usd/`** - Composed stage API: `usd::Stage` provides the high-level API for opening USD files and querying the composed scene graph. Delegates composition to `pcp::Cache`. `StageBuilder` configures the stage with a custom resolver, error handler (`on_error`), variant fallback selections (`variant_fallbacks`), an optional session layer (`session_layer`), payload loading behavior (`initial_load_set` / `InitialLoadSet`), and a working-set filter (`population_mask` / `StagePopulationMask`). `StageBuilder::open` loads a root layer from disk; `StageBuilder::in_memory` creates an empty writable anonymous root (C++ `UsdStage::CreateInMemory`). Stage-tier authoring (`define_prim` / `override_prim` / `create_attribute` / `create_relationship` / `set_default_prim`) routes through the current `EditTarget` (a subset of C++ `UsdEditTarget`): it pairs a `layer_index` with a `pcp::MapFunction` that maps scene paths to spec paths, so authoring through the chokepoint `Stage::with_target_layer_at` writes at `EditTarget::map_to_spec_path`. `EditTarget::for_layer_index` is the identity-mapping local target; `EditTarget::for_local_direct_variant` routes writes into a variant's `{set=sel}` namespace, which `sdf::Layer` materializes end-to-end (`create_prim` / `create_attribute` accept variant-segment paths and build the variant set / variant spec scaffolding via `namespace_chain`; arc-based reference/specialize targets are still TODO). `EditContext` is the RAII guard (C++ `UsdEditContext`) returned by `Stage::edit_context` that restores the previous target on `Drop`. Each authoring closure returns an `sdf::ChangeList` (in layer namespace) that `Cache::process_changes` classifies and applies for surgical invalidation. Errors surface via `StageAuthoringError` (including `OutsideEditTarget` when a path can't be mapped). `usd/prim.rs` defines `Prim` / `Attribute` / `Relationship` / `VariantSets` composed handles (C++ `UsdPrim` / `UsdAttribute` / `UsdRelationship` / `UsdVariantSets` analogs) — value-type wrappers around `(stage, path)` returned from the authoring methods. Setters consume `self` and return `Self` so chains bind directly (`let p = stage.define_prim(...)?.set_type_name(...)?.set_kind(...)?`); lookup-style methods (`create_attribute`, `path`, `get`, `time_samples`) take `&self`. Composition introspection mirrors the C++ handle surface: `Prim::prim_stack` (`UsdPrim::GetPrimStack`), `Attribute`/`Relationship::property_stack` (`UsdProperty::GetPropertyStack`), `Prim::variant_sets().get_all_variant_selections()` (`UsdVariantSets::GetAllVariantSelections`), plus the stage-scoped `Stage::layer_stack` (`UsdStage::GetLayerStack`) and `Stage::prim_at_path` (`UsdStage::GetPrimAtPath`); these return `(layer identifier, spec path)` sites where C++ returns spec handles. The older path-keyed `Stage` scene queries (`prim_children`, `relationship_targets`, …) are slated to move onto these handles (see the `TODO` in `usd/stage.rs`). Stage-level interpolation lives in `usd/interp.rs` and is exposed as `usd::InterpolationType`. Public users should import modules, e.g. `use openusd::{sdf, usd};`, rather than root-level `Stage` re-exports.

- **`expr`** - Variable expression tokenizer and parser for USD's expression syntax.

- **`schemas/`** - Domain-schema readers/authoring layered on top of the core `sdf` / `usd` machinery (the AOUSD core spec covers composition, value resolution, and file formats — not these schemas). Each sub-module is feature-gated: `geom` (UsdGeom), `physics` (UsdPhysics), `skel` (UsdSkel + skinning), `lux` (UsdLux), `shade` (UsdShade), `render` (UsdRender). `schemas/registry.rs` is the eventual schema-registry surface (currently a stub).

- **`math`** - Shared 4×4 row-major matrix helpers used by the schema layer.

The `AbstractData` trait in `sdf/mod.rs` serves as the central abstraction, providing a unified interface for text, binary, and archive format readers.

## Development Commands

```bash
# Build the project (use --all-features to include the gated schema modules)
cargo build --all-features

# Run tests (including comprehensive format validation tests)
cargo test --all-targets --all-features

# Lint with Clippy (strict warnings as errors)
cargo clippy --all-targets --all-features -- -D warnings

# Format code
cargo fmt

# Check formatting
cargo fmt --all -- --check --files-with-diff

# Generate documentation
cargo doc --no-deps

# Run security/dependency audits
cargo deny check

# Run examples
cargo run --example dump_usdc -- path/to/file.usd
```

## Planning New Features

When implementing a new feature from the spec:

1. Read `docs/aousd_core_spec_1.0.1.pdf` to understand how the feature works and what it does
2. Research how the C++ OpenUSD implementation handles it: https://github.com/PixarAnimationStudios/OpenUSD
3. Review the Python reference implementation if applicable: `vendor/core-spec-supplemental-release_dec2025/`

## Code Standards

- Project targets Rust version specified in `rust-toolchain.toml` with MSRV defined in `clippy.toml`
- Maximum line width: 120 characters (rustfmt.toml)
- All warnings treated as errors in CI
- Comprehensive test coverage (50% minimum) with grcov
- Security auditing with cargo-deny
- Pre-1.0: backward compatibility is not a constraint. Prefer the cleanest design and change or remove public APIs freely; don't keep deprecated shims, compatibility shims, or worse-but-compatible behavior. Update all call sites in the same change.

## Code Quality

- Write clean and idiomatic Rust code
- Less is better - prefer functionality offered by stdlib
- Code requires documentation
- Proof read and reword docs and/or comments as needed
- Do not use `**bold** — description` pattern in doc comments or bullet lists; use plain text or link directly to the item instead
- Never remove comments during refactoring if they are still applicable
- Comments must describe the code as it stands, not its edit history or the alternatives it didn't take. Don't justify the absence or removal of code, and don't contrast the chosen approach with a rejected one (e.g. "no separate X pre-check is needed here", "X was removed because…", "assign directly rather than through Y", "instead of calling Z", "we use A so we don't B"). Such notes only make sense to someone who saw the prior version or the alternative and are noise to a fresh reader. State what the present code does and a rationale that stands on its own, not what it no longer does or could have done.
- Don't reference planning phases or steps (e.g. "Phase 1", "Step 2") in code, comments, names, fixtures, or commit messages; describe what the code does or, for deferred work, name the missing feature in a `TODO`
- Wrap prose at 80 characters — Markdown, plans, design write-ups, and doc-comment text; Rust code still follows rustfmt (120)
- Mark performance/parallelism opportunities with a `TODO(rayon)` (or `TODO(perf)`) comment in new code and when refactoring existing code, instead of optimizing prematurely; say what is independent or parallelizable so the seam is actionable later
- Re-export key types from module roots so users can access them without deep paths (e.g. `sdf::FieldKey` not `sdf::schema::FieldKey`)
- Avoid raw path string manipulations; use `Path` methods instead of building or parsing path strings manually
- Don't add "Generated with Claude Code" or "Co-Authored-By: Claude" to commits, PRs, or release notes

## Testing

The test suite includes extensive binary format tests using fixture files in `fixtures/` directory. Tests validate:
- Data type parsing (integers, floats, strings, arrays, etc.)
- USD-specific types (paths, references, payloads, layer offsets)
- Compression handling
- Time-sampled data
- Scene hierarchy traversal

Prefer using USD assets from `vendor/usd-wg-assets/` for test fixtures when a suitable file exists. Only add new files to `fixtures/` when vendor assets don't cover the specific case needed.

Test function names MUST be terse — 2–4 underscore-separated words, no more. Match the existing naming convention of the file. Prefer `add_api_schema_dup_delete` over `add_api_schema_clears_duplicate_delete_opinions`, `light_api_skips_non_light` over `read_light_api_returns_none_on_non_light_prim`. Drop redundant prefixes like `read_`/`reads_` when the test file already targets a reader; favour the subject + outcome (`light_api_via_applied_schema`) over verbose sentences.

To pull a typed payload out of a `Value` in tests, use the `EnumTryAs`-generated `try_as_*()` accessor followed by `unwrap()`/`expect("…")` rather than a `let Value::Variant(x) = … else { panic!() }` block. Keep the descriptive message by preferring `expect`.

## Dependencies

Key external dependencies:
- `anyhow` - Error handling
- `bitflags` - Bitflag sets (e.g. `PrimPredicate`)
- `bytemuck` - Safe transmutation for binary data
- `half` - 16-bit floating point support (re-exported as `f16`)
- `logos` - Lexer generator for USDA tokenization
- `lz4_flex` - Compression for binary format
- `num-traits` - Numeric traits
- `strum` - Enum derive macros (Display, EnumIs, EnumTryAs, IntoStaticStr, etc.)
- `thiserror` - Error type derive macros for `layer::Error`, `pcp::Error`, and `CompositionError`
- `zip` - USDZ archive reading
- `serde` (optional, `serde` feature) - Serialization support

Domain schemas are gated behind per-module features (`geom`, `lux`, `physics`, `render`, `shade`, `skel`); use `--all-features` when building, testing, or linting.

The project maintains a minimal dependency footprint and uses cargo-deny to prevent license conflicts and vulnerability introduction. Allowed licenses: MIT, Apache-2.0, Zlib, Unicode-3.0.
