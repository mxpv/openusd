# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a pure Rust implementation of OpenUSD (Universal Scene Description), Pixar's open-source framework for 3D computer graphics data interchange. The project aims to provide native Rust support without C++ dependencies for reading and writing USD files.

## Architecture

The codebase follows the same module structure as the C++ OpenUSD SDK:

- **`sdf/`** - Scene Description Foundations: Core data types, traits, and abstractions. Contains the `AbstractData` trait, `Value` enum (60+ variants), `Path`, `Spec`, `ListOp`, and schema field keys.

- **`usda/`** - Text format (`.usda`) reader: Lexer (logos) + recursive descent parser. `TextReader` implements `AbstractData`.

- **`usdc/`** - Binary format (`.usdc`) reader: USD's crate format with compressed data handling. `CrateData` implements `AbstractData`.

- **`usdz/`** - Archive format (`.usdz`) reader: ZIP-based package reader.

- **`ar/`** - Asset Resolution: `Resolver` trait maps asset paths (`@...@`) to physical locations. `DefaultResolver` searches the filesystem.

- **`layer`** - Layer collection: `collect_layers` recursively resolves and loads all layers from a root file, following sublayers, references, and payloads. Corresponds to C++ `PcpLayerStack`. Defines `layer::Error` for recoverable collection failures (e.g. unresolved assets).

- **`pcp/`** - Prim Cache Population (composition engine): Implements LIVRPS strength ordering to compose opinions across layers. Corresponds to C++ `Pcp` module.
  - `pcp/mod.rs` — `pcp::Error`: composition errors (arc cycles, unresolved layers, missing/invalid `defaultPrim`). `LayerStack`: bundles layers, identifiers, and precomputed sublayer stacks (C++ `PcpLayerStack`). `VariantFallbackMap`: maps variant set names to ordered fallback selections (C++ `PcpVariantFallbackMap`).
  - `pcp/cache.rs` — `Cache`: lazily-built per-prim composition cache (C++ `PcpCache`). Owns a `LayerStack` and passes it by shared reference to each build. Returns `Result` from all public methods.
  - `pcp/index.rs` — `PrimIndex`, `Node`, `NodeIndex`, `ArcType`: per-prim composition graph (C++ `PcpPrimIndex`). `ArcType` variants are ordered by LIVERPS strength via `#[repr(u8)]` + derived `Ord`. Nodes are stored in a flat arena (`PrimIndexGraph`) ordered strongest-to-weakest. Each node carries `map_to_parent` and `map_to_root` (`MapFunction`) for namespace translation across arcs. `IndexBuilder` takes a `&LayerStack` and evaluates LIVRPS with a `CompositionContext` flowing from parent to child; each build takes only `&` references (Rayon-friendly).
  - `pcp/mapping.rs` — `MapFunction`: namespace mapping between composition arcs (C++ `PcpMapFunction`). Stores (source, target) path pairs with longest-prefix matching. Supports compose, inverse, and identity operations.
  - `pcp/rel.rs` — `Relocates`: isolated relocate object owning per-layer `layerRelocates`. Resolves pre-relocation source paths, builds relocated prim indices, and adjusts child name lists. Receives external data (`&LayerStack`, cached indices/contexts) through method parameters; does not reference `Cache` directly.

- **`stage`** - Composed stage: `Stage` provides the high-level API for opening USD files and querying the composed scene graph. Delegates composition to `pcp::Cache`. `StageBuilder` configures the stage with a custom resolver, error handler (`on_error`), variant fallback selections (`variant_fallbacks`), and an optional session layer (`session_layer`).

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