# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a pure Rust implementation of OpenUSD (Universal Scene Description), Pixar's open-source framework for 3D computer graphics data interchange. The project aims to provide native Rust support without C++ dependencies for reading and writing USD files.

## Architecture

The codebase is organized into three main modules:

- **`sdf/`** - Scene Description Foundations: Core data types, traits, and abstractions corresponding to USD's SDF module. Contains the `AbstractData` trait that defines the interface for accessing scene description data.

- **`usda/`** - Text format (.usda) reader: Parser implementation for USD's ASCII text format using logos for tokenization and a recursive descent parser.

- **`usdc/`** - Binary format (.usdc) reader: Implementation for USD's binary crate format, including compressed data handling and efficient memory layout parsing.

The `AbstractData` trait in `sdf/mod.rs` serves as the central abstraction, providing a unified interface for both text and binary format readers.

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

## Git

- Keep commit messages brief and to the point
- Use a short, descriptive commit title (50 characters or less)
- Include a brief commit body that summarizes changes in 1-3 sentences when needed (wrap at 120 characters)
- Keep commits focused and atomic - one logical change per commit
- Don't add "Generated with Claude Code" to commit messages or pull request descriptions
- Don't add "Co-Authored-By: Claude noreply@anthropic.com" to commit messages or pull request descriptions
- Before opening a PR or making a commit, make sure the code passes lint, formatting, and unit tests

## Testing

The test suite includes extensive binary format tests using fixture files in `fixtures/` directory. Tests validate:
- Data type parsing (integers, floats, strings, arrays, etc.)
- USD-specific types (paths, references, payloads, layer offsets)
- Compression handling
- Time-sampled data
- Scene hierarchy traversal

Test fixtures are small USD files covering specific format features and edge cases.

## Dependencies

Key external dependencies:
- `anyhow` - Error handling
- `bytemuck` - Safe transmutation for binary data
- `half` - 16-bit floating point support
- `logos` - Lexer generator for USDA tokenization
- `lz4_flex` - Compression for binary format
- `num-traits` - Numeric traits
- `strum` - Enum utilities

The project maintains a minimal dependency footprint and uses cargo-deny to prevent license conflicts and vulnerability introduction.