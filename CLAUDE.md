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

- **`layer`** - Layer collection: `collect_layers` recursively resolves and loads all layers from a root file, following sublayers, references, and payloads. Corresponds to C++ `PcpLayerStack`.

- **`pcp/`** - Prim Cache Population (composition engine): Implements LIVRPS strength ordering to compose opinions across layers. Corresponds to C++ `Pcp` module.
  - `pcp/cache.rs` — `Cache`: lazily-built per-prim composition cache (C++ `PcpCache`).
  - `pcp/index.rs` — `PrimIndex`, `Node`, `ArcType`: per-prim strength-ordered node list (C++ `PcpPrimIndex`). `IndexBuilder` evaluates LIVRPS inline with a `CompositionContext` flowing from parent to child.

- **`stage`** - Composed stage: `Stage` provides the high-level API for opening USD files and querying the composed scene graph. Delegates composition to `pcp::Cache`.

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
- Never remove comments during refactoring if they are still applicable
- Re-export key types from module roots so users can access them without deep paths (e.g. `sdf::FieldKey` not `sdf::schema::FieldKey`)

## Git

- Keep commit messages brief and to the point
- Use a short, descriptive commit title (50 characters or less)
- Include a brief commit body that summarizes changes in 1-3 sentences when needed (wrap at 120 characters)
- Keep commits focused and atomic - one logical change per commit
- Don't add "Generated with Claude Code" to commit messages or pull request descriptions
- Don't add "Co-Authored-By: Claude noreply@anthropic.com" to commit messages or pull request descriptions
- Before opening a PR or making a commit, run `cargo fmt`, `cargo clippy`, and `cargo test` to ensure code passes formatting, lint, and unit tests

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
- `zip` - USDZ archive reading

The project maintains a minimal dependency footprint and uses cargo-deny to prevent license conflicts and vulnerability introduction. Allowed licenses: MIT, Apache-2.0, Zlib, Unicode-3.0.