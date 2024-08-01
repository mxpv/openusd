//! This examples dumps binary USDC file.
//!
//! Mainly this will print binary's structural data, specs, and fields that belong to each spec.
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
    let mut file = CrateFile::open(reader).context("Failed to read crate file")?;

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
    println!();

    println!("-- Paths: ");
    file.paths.iter().enumerate().for_each(|(index, path)| {
        println!("#{}:\t{}", index, path);
    });
    println!();

    println!("-- Specs: ");
    for i in 0..file.specs.len() {
        let spec = file.specs[i];
        let path = &file.paths[spec.path_index];
        println!("#{}:\t{} ({})", spec.fieldset_index, path, spec.spec_type);

        let mut index = spec.fieldset_index;

        while index < file.fieldsets.len() {
            let current = match file.fieldsets[index] {
                Some(value) => value,
                None => break,
            };

            index += 1;

            let field = file.fields[current];

            let value = file
                .value(field.value_rep)
                .expect("Unable to retrieve value rep, please file an issue");

            let name = &file.tokens[field.token_index];

            println!("\t\t{} -> {:?}", name, value);
        }
    }
    println!();

    Ok(())
}
