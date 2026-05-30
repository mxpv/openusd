# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a pure Rust implementation of OpenUSD (Universal Scene Description), Pixar's open-source framework for 3D computer graphics data interchange. The project aims to provide native Rust support without C++ dependencies for reading and writing USD files.

## Architecture

The codebase follows the same module structure as the C++ OpenUSD SDK:

- **`sdf/`** - Scene Description Foundations: Core data types, traits, and abstractions. Contains the `AbstractData` trait, `Value` enum (60+ variants), `Path`, `Spec`, `ListOp`, and schema field keys. `Layer` (C++ `SdfLayer`) bundles a resolved identifier with a backing `AbstractData` and exposes a Layer-tier authoring surface (`create_prim` / `override_prim` / `create_attribute` / `create_relationship` / `set_default_prim` / `clear_default_prim`) plus typed spec views (`PrimSpec[Mut]`, `AttributeSpec[Mut]`, `RelationshipSpec[Mut]`, `PseudoRootSpec[Mut]`). Authoring errors flow through `AuthoringError`.

- **`usda/`** - Text format (`.usda`) reader: Lexer (logos) + recursive descent parser. `TextReader` implements `AbstractData`.

- **`usdc/`** - Binary format (`.usdc`) reader: USD's crate format with compressed data handling. `CrateData` implements `AbstractData`.

- **`usdz/`** - Archive format (`.usdz`) reader: ZIP-based package reader.

- **`ar/`** - Asset Resolution: `Resolver` trait maps asset paths (`@...@`) to physical locations. `DefaultResolver` searches the filesystem.

- **`layer`** - Layer collection: `collect_layers` recursively resolves and loads all layers from a root file, following sublayers, references, and payloads. Corresponds to C++ `PcpLayerStack`. Defines `layer::Error` for recoverable collection failures (e.g. unresolved assets).

- **`pcp/`** - Prim Cache Population (composition engine): Implements LIVRPS strength ordering to compose opinions across layers. Corresponds to C++ `Pcp` module.
  - `pcp/mod.rs` — `pcp::Error`: composition errors (arc cycles, unresolved layers, missing/invalid `defaultPrim`). `LayerStack`: bundles layers, identifiers, and precomputed sublayer stacks (C++ `PcpLayerStack`). `VariantFallbackMap`: maps variant set names to ordered fallback selections (C++ `PcpVariantFallbackMap`).
  - `pcp/cache.rs` — `Cache`: lazily-built per-prim composition cache (C++ `PcpCache`). Owns a `LayerStack` and passes it by shared reference to each build. `Cache::process_changes` is the single entry point for surgical invalidation — Stage feeds `(layer_index, sdf::ChangeList)` pairs and the cache classifies + applies. Returns `Result` from all public methods.
  - `pcp/change.rs` — `Changes` (`pub(crate)`), `CacheChanges`, `LayerStackChanges`: C++ `PcpChanges` analog. Three-tier classifier (significant / prim / spec) feeds `Changes::did_change` (pure analysis) and `Changes::apply` (commit). External callers go through `Cache::process_changes`, which ties both phases to the same cache instance.
  - `pcp/deps.rs` — `Dependencies`: reverse `(layer_index, site_path) → prim_index_paths` map populated at the end of `Cache::ensure_index`. Drives `lookup_with_ancestors` and `subtree_lookup` for change fanout. Synthetic self-registrations on every layer make cached misses (empty `PrimIndex`) reachable.
  - `pcp/index.rs` — `PrimIndex`, `Node`, `NodeIndex`, `ArcType`: per-prim composition graph (C++ `PcpPrimIndex`). `ArcType` variants are ordered by LIVERPS strength via `#[repr(u8)]` + derived `Ord`. Nodes are stored in a flat arena (`PrimIndexGraph`) ordered strongest-to-weakest. Each node carries `map_to_parent` and `map_to_root` (`MapFunction`) for namespace translation and retiming (`MapFunction` carries an `sdf::LayerOffset`) across arcs. `IndexBuilder` takes a `&LayerStack` and evaluates LIVRPS with a `CompositionContext` flowing from parent to child; each build takes only `&` references (Rayon-friendly).
  - `pcp/mapping.rs` — `MapFunction`: namespace mapping between composition arcs (C++ `PcpMapFunction`). Stores (source, target) path pairs with longest-prefix matching alongside an `sdf::LayerOffset` time retiming. `compose` concatenates both path and time offsets. Effective offset for a node is `node.map_to_root.time_offset()`.
  - `pcp/rel.rs` — `Relocates`: isolated relocate object owning per-layer `layerRelocates`. Resolves pre-relocation source paths, builds relocated prim indices, and adjusts child name lists. Receives external data (`&LayerStack`, cached indices/contexts) through method parameters; does not reference `Cache` directly.

- **`usd/`** - Composed stage API: `usd::Stage` provides the high-level API for opening USD files and querying the composed scene graph. Delegates composition to `pcp::Cache`. `StageBuilder` configures the stage with a custom resolver, error handler (`on_error`), variant fallback selections (`variant_fallbacks`), an optional session layer (`session_layer`), payload loading behavior (`initial_load_set` / `InitialLoadSet`), and a working-set filter (`population_mask` / `StagePopulationMask`). `StageBuilder::open` loads a root layer from disk; `StageBuilder::in_memory` creates an empty writable anonymous root (C++ `UsdStage::CreateInMemory`). Stage-tier authoring (`define_prim` / `override_prim` / `create_attribute` / `create_relationship` / `set_default_prim`) routes through the current `EditTarget` (a minimal subset of C++ `UsdEditTarget` — currently just a `layer_index`, no per-arc path mapping yet); each authoring closure returns an `sdf::ChangeList` that `Cache::process_changes` classifies and applies for surgical invalidation. Errors surface via `StageAuthoringError`. `usd/prim.rs` defines `Prim` / `Attribute` / `Relationship` composed handles (C++ `UsdPrim` / `UsdAttribute` / `UsdRelationship` analogs) — value-type wrappers around `(stage, path)` returned from the authoring methods. Setters consume `self` and return `Self` so chains bind directly (`let p = stage.define_prim(...)?.set_type_name(...)?.set_kind(...)?`); lookup-style methods (`create_attribute`, `path`, `get`, `time_samples`) take `&self`. Stage-level interpolation lives in `usd/interp.rs` and is exposed as `usd::InterpolationType`. Public users should import modules, e.g. `use openusd::{sdf, usd};`, rather than root-level `Stage` re-exports.

- **`expr`** - Variable expression tokenizer and parser for USD's expression syntax.

The `AbstractData` trait in `sdf/mod.rs` serves as the central abstraction, providing a unified interface for text, binary, and archive format readers.

## Development Commands

```bash
# Build the project
cargo build

# Run tests (including comprehensive format validation tests)
cargo test

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

## Code Quality

- Write clean and idiomatic Rust code
- Less is better - prefer functionality offered by stdlib
- Code requires documentation
- Proof read and reword docs and/or comments as needed
- Do not use `**bold** — description` pattern in doc comments or bullet lists; use plain text or link directly to the item instead
- Never remove comments during refactoring if they are still applicable
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
- `bytemuck` - Safe transmutation for binary data
- `half` - 16-bit floating point support (re-exported as `f16`)
- `logos` - Lexer generator for USDA tokenization
- `lz4_flex` - Compression for binary format
- `num-traits` - Numeric traits
- `strum` - Enum derive macros (Display, EnumIs, EnumTryAs, IntoStaticStr, etc.)
- `thiserror` - Error type derive macros for `layer::Error`, `pcp::Error`, and `CompositionError`
- `zip` - USDZ archive reading

The project maintains a minimal dependency footprint and uses cargo-deny to prevent license conflicts and vulnerability introduction. Allowed licenses: MIT, Apache-2.0, Zlib, Unicode-3.0.
