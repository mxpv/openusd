# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a pure Rust implementation of OpenUSD (Universal Scene Description), Pixar's open-source framework for 3D computer graphics data interchange. The project aims to provide native Rust support without C++ dependencies for reading and writing USD files.

## Architecture

The codebase mirrors the C++ OpenUSD SDK's module layout. Each module's own `//!` doc comment is the source of truth for its internals; the summaries below are a navigational map — read the module docs (e.g. `pcp/mod.rs`, `usd/stage.rs`) for the detail.

- **`tf/`** - Tools Foundation (C++ `Tf`): `tf::Token`, an interned-identifier string (C++ `TfToken`) holding either a `&'static str` (zero-alloc, `const fn new`) or a runtime `Arc<str>`. Backs `sdf::Value::Token` / `TokenVec` and every API that mirrors a C++ `TfToken` (prim/property names, `typeName`, `kind`, token-valued attributes). Equality/hash/ordering are by text, so static and shared tokens compare equal; it derefs to `str` and compares against `str`/`&str`.

- **`sdf/`** - Scene Description Foundations (C++ `Sdf`): core data types and the central `AbstractData` trait — the unified interface the text, binary, and archive readers all implement. Key types: `Value` (60+ variants), `AssetPath` (C++ `SdfAssetPath`), `Path`, `PathTable` (namespace-keyed map, C++ `SdfPathTable`), `Spec`, `ListOp`, schema `FieldKey`s, and `Layer` (C++ `SdfLayer`: identifier + backing `AbstractData` + the layer-tier authoring surface and typed spec views). `sdf/expr.rs` is the `` `...` `` variable-expression engine (C++ `SdfVariableExpression`), re-exported as `sdf::expr` / `sdf::Expr`.

- **`usda/`** - Text format `.usda`: logos lexer + recursive-descent parser. `TextReader` / `TextWriter`.

- **`usdc/`** - Binary crate format `.usdc` (compressed). `CrateData` / `CrateWriter`.

- **`usdz/`** - ZIP-based `.usdz` package. `Archive` / `ArchiveWriter`.

- **`ar/`** - Asset Resolution (C++ `Ar`): the `Resolver` trait maps `@...@` asset paths to physical locations; `DefaultResolver` searches the filesystem.

- **`layer`** - Layer collection (C++ `PcpLayerStack`, loading half): `Collector::collect` recursively resolves and loads all layers from a root file, following sublayers, references, and payloads. `Collector` / `DependencyKind` are re-exported from the crate root; `layer::Error` covers recoverable collection failures.

- **`pcp/`** - Prim Cache Population, the composition engine (C++ `Pcp`): LIVERPS strength ordering across layers. `pcp/mod.rs` has the LIVERPS overview and a per-file structure table — start there. Principal types: `LayerGraph` (layer + sublayer DAG), `IndexCache` (lazy per-prim cache, C++ `PcpCache`; `process_changes` is the single surgical-invalidation entry point), `Indexer` (the sole task-queue composition path, C++ `Pcp_PrimIndexer`), `PrimIndex` / `PrimIndexGraph` (arena-backed `Send + Sync` tree of per-`(layerStack, path)` `Node`s), `MapFunction` (namespace mapping, C++ `PcpMapFunction`), plus relocates, instancing (`PrototypeRegistry`), value clips, `Dependencies`, and `Changes`. Composition is kept a pure function of `(graph, context, cached indices)` to stay parallelizable (`TODO(rayon)` seams).

- **`usd/`** - Composed stage API (C++ `Usd`): `usd::Stage` is a cheap `Rc<StageInner>` handle (C++ `UsdStageRefPtr`) that delegates composition to `pcp::IndexCache`. `StageBuilder` configures resolver, variant fallbacks, session layer, load set, and population mask (`open` from disk, `in_memory` for an anonymous root). Stage-tier authoring (`define_prim` / `create_attribute` / …) routes through the current `EditTarget`, with `EditContext` as the RAII guard; each authoring closure returns an `sdf::ChangeList` fed to `process_changes`. Composed handles — `Prim`, `Attribute`, `Relationship`, and the `schemas/` views — are `Clone` value types owning a `Stage` clone, and most methods mirror a C++ `UsdPrim` / `UsdAttribute` / … member by name. `usd::SchemaBase` (`usd/schema.rs`) is the root of the schema-view hierarchy. Public users import modules (`use openusd::{sdf, usd};`) rather than root-level re-exports.

- **`schemas/`** - Domain schemas layered on `sdf` / `usd` (not part of the AOUSD core spec, which covers only composition, value resolution, and file formats). Feature-gated per family — see the table in `schemas/mod.rs`. Families: `geom`, `lux`, `media`, `physics`, `proc`, `render`, `shade`, `skel`, `ui`, `vol`; `lux` / `media` / `proc` / `skel` / `vol` enable `geom` transitively. `schemas/registry.rs` is a stub for the eventual schema registry.

- **`gf/`** - Graphics Foundations (C++ `Gf`): `bytemuck::Pod` vector / quaternion / matrix types (`Vec2/3/4` in f32/f64/f16/i32, `Quatf/d/h`, `Mat2d` / `Mat3d` / `Matrix4d`) for bulk binary serialization, row-major / row-vector convention. See `gf/mod.rs` for the linear-algebra conventions. `From` / `TryFrom` bridge every gf type to `sdf::Value`.

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
- Order a file top-down by importance so the first thing a reader sees is the main type, not a helper: the primary type definition (and the structs it depends on) first, then its `impl` blocks, then free-standing helper functions, then the `#[cfg(test)] mod tests`. Don't open a file with a small private helper.
- Code requires documentation
- Proof read and reword docs and/or comments as needed
- Do not use `**bold** — description` pattern in doc comments or bullet lists; use plain text or link directly to the item instead
- A doc comment documents only its own item. Don't describe another type, module, or method inside it (e.g. don't enumerate a `Layer`'s methods in a `Relocate` type alias's doc); document each item on the item itself and use an intra-doc link (`` [`Foo`] ``) when a cross-reference is genuinely needed
- Do not use decorative box-drawing section-divider comments (e.g. `// ── Section ──────`); group code with a plain `//` comment or rely on the item's own doc comment
- Never remove comments during refactoring if they are still applicable
- Comments must describe the code as it stands, not its edit history or the alternatives it didn't take. Don't justify the absence or removal of code, and don't contrast the chosen approach with a rejected one (e.g. "no separate X pre-check is needed here", "X was removed because…", "assign directly rather than through Y", "instead of calling Z", "we use A so we don't B"). This includes contrasts with a prior implementation's performance or shape — "a subtree walk rather than a full scan", "O(1) instead of the previous O(n)", "now keyed by path" — which only make sense to someone who saw the old code; state the present behavior positively ("walks the `prefix` subtree") instead. Such notes only make sense to someone who saw the prior version or the alternative and are noise to a fresh reader. State what the present code does and a rationale that stands on its own, not what it no longer does or could have done.
- Don't reference planning phases or steps (e.g. "Phase 1", "Step 2") in code, comments, names, fixtures, or commit messages; describe what the code does or, for deferred work, name the missing feature in a `TODO`
- Wrap prose at 80 characters — Markdown, plans, design write-ups, and doc-comment text; Rust code still follows rustfmt (120)
- Mark performance/parallelism opportunities with a `TODO(rayon)` (or `TODO(perf)`) comment in new code and when refactoring existing code, instead of optimizing prematurely; say what is independent or parallelizable so the seam is actionable later
- Re-export key types from module roots so users can access them without deep paths (e.g. `sdf::FieldKey` not `sdf::schema::FieldKey`)
- Reference types through their module, not a fully-qualified or bare path: `use crate::{sdf, gf, tf};` then write `sdf::TimeCode`, `gf::Vec3f`, `tf::Token`. Don't write inline `crate::tf::Token::from(...)` (or `openusd::tf::Token` in tests), and don't `use crate::tf::Token;` to get a bare `Token` when `tf::Token` reads clearly (it also avoids clashes, e.g. the `usda` lexer's own `Token`)
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
- `thiserror` - Error type derive macros for typed errors such as `layer::Error` and `pcp::Error`
- `zip` - USDZ archive reading
- `serde` (optional, `serde` feature) - Serialization support

Domain schemas are gated behind per-module features (`geom`, `lux`, `media`, `physics`, `proc`, `render`, `shade`, `skel`, `ui`, `vol`); use `--all-features` when building, testing, or linting.

The project maintains a minimal dependency footprint and uses cargo-deny to prevent license conflicts and vulnerability introduction. Allowed licenses: MIT, Apache-2.0, Zlib, Unicode-3.0.
