//! Example that dumps structural data of a usdc file.
//!
//! # Usage:
//! ```bash
//! cargo run --example dump_usdc ./extern/usd-wg-assets/full_assets/ElephantWithMonochord/SoC-ElephantWithMonochord.usdc
//! ```

use std::{env, fs};

use anyhow::{Context as _, Result};
use openusd::usdc::{CrateFile, Version};

fn main() -> Result<()> {
    let args = env::args().collect::<Vec<_>>();

    let path = args
        .get(1)
        .context("Missing path to usdc file, use: cargo run --example dump_usdc {PATH_TO_FILE}.usdc")?;

    let reader = fs::File::open(path).context("Failed to read crate file")?;
    let file = CrateFile::open(reader).context("Failed to read crate file")?;

    println!("-- Bootrap header");
    println!("Magic: {:?}", file.bootstrap.ident);
    println!("Version: {}", Version::from(file.bootstrap));
    println!("TOC offset: {}", file.bootstrap.toc_offset);
    println!();

    println!("-- Sections:");
    for (index, section) in file.sections.iter().enumerate() {
        println!(
            "#{}:\t{} (start: {}, size: {})",
            index,
            section.name(),
            section.start,
            section.size
        );
    }
    println!();

    println!("-- Tokens:");
    for (index, token) in file.tokens.iter().enumerate() {
        println!("#{}:\t{}", index, token);
    }
    println!();

    println!("-- Strings:");
    for (index, string) in file.strings.iter().enumerate() {
        println!("#{}:\t{}", index, string);
    }
    println!();

    println!("-- Fields: ");
    file.fields.iter().enumerate().for_each(|(index, field)| {
        let ty = field.value_rep.ty().unwrap_or_default();
        println!("#{}:\t{} ({})", index, field.token_index, ty);
    });
    println!();

    println!("-- Field sets: ");
    file.fieldsets.iter().enumerate().for_each(|(index, fieldset)| {
        println!("#{}:\t{:?}", index, fieldset);
    });

    println!("-- Paths: ");
    file.paths.iter().enumerate().for_each(|(index, path)| {
        println!("#{}:\t{}", index, path);
    });
    println!();

    println!("-- Specs: ");
    file.specs.iter().enumerate().for_each(|(index, spec)| {
        let path = &file.paths[spec.path_index];

        println!("#{}:\t{} -> {} ({})", index, spec.fieldset_index, path, spec.spec_type);
    });
    println!();

    Ok(())
}
