# openusd

[![Crates.io Version](https://img.shields.io/crates/v/openusd)](https://crates.io/crates/openusd)
[![docs.rs](https://img.shields.io/docsrs/openusd)](https://docs.rs/crate/openusd/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/mxpv/openusd/graph/badge.svg?token=LAPV2T3AI8)](https://codecov.io/gh/mxpv/openusd)
[![dependency status](https://deps.rs/repo/github/mxpv/openusd/status.svg)](https://deps.rs/repo/github/mxpv/openusd)

[USD](https://openusd.org/release/index.html) is an open-source framework developed by `Pixar` for the efficient interchange of 3D computer graphics data across different software applications.

This project aims to implement [OpenUSD](https://github.com/PixarAnimationStudios/OpenUSD) library in plain Rust (with no native C++ dependencies).

## Documentation

The following list of docs was used during crate development:

- [User documentation](https://openusd.org/release/index.html)
- [Book of USD](https://remedy-entertainment.github.io/USDBook/)
- [API Documentation](https://openusd.org/release/api/index.html)
- [USD Cookbook](https://github.com/ColinKennedy/USD-Cookbook)

## Supported features

The USD library is a fairly large project to replicate. For the most up-to-date information on what features are currently supported by the crate, follow issue https://github.com/mxpv/openusd/issues/1 in our repository.

## Getting started

To begin, simply clone the repository including its submodules.
Make sure you have [`Rust`](https://www.rust-lang.org/tools/install) installed on your system, `rustup` will do the rest.

```bash
# Clone the project
git clone --recurse-submodules https://github.com/mxpv/openusd.git
cd openusd

# Use cargo to build, test, lint, etc.
cargo build
cargo clippy

# Run examples
cargo run --example dump_usdc -- ~/caldera/layers/cameras.usd
```

## Minimum supported Rust version (MSRV)

The project typically targets the latest stable Rust version. Please refer to [rust-toolchain.toml](./rust-toolchain.toml) for exact version currently used by our CIs.
