# openusd

![Crates.io Version](https://img.shields.io/crates/v/openusd)
![docs.rs](https://img.shields.io/docsrs/openusd)

[USD](https://openusd.org/release/index.html) is an efficient, scalable system for authoring, reading, and streaming time-sampled scene description for interchange between graphics applications.

This project aims to reimplement [USD library](https://github.com/PixarAnimationStudios/OpenUSD) in plain Rust (with no native C++ dependencies).

## Getting started.

To begin, simply clone the repository including its submodules.
Make sure you have `Rust` already installed on your system.

```bash
git clone --recurse-submodules https://github.com/mxpv/openusd.git
cd openusd

cargo build
cargo clippy
```

## Minimum supported Rust version (MSRV)

The project typically targets the latest stable Rust version. Please refer to [rust-toolchain.toml](./rust-toolchain.toml) for exact version currently used by our CIs.
