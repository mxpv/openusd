//! Convert a layer from one file format to another, the way `usdcat -o` does.
//!
//! The input is opened the way the library opens any layer, so its format is
//! whatever claims the file: the extension, or the content for the ambiguous
//! `.usd`. The output format comes from its own extension. `--from` and `--to`
//! override either with a format id, for a path whose extension names no
//! format.
//!
//! Only the layer's own scene description is converted. Sublayers, references
//! and payloads are left as the authored asset paths they are, so this is
//! `usdcat` without `--flatten`.
//!
//! # Usage
//! ```bash
//! cargo run -p openusd --example convert -- scene.usda scene.usdc
//! cargo run -p openusd --example convert -- --from usda schema.txt schema.usdc
//! ```

use std::env;
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::Path;
use std::process;

use openusd::{Error, Result, sdf};

/// How to call this.
const USAGE: &str = "usage: cargo run -p openusd --example convert -- [--from <id>] [--to <id>] <input> <output>";

fn main() -> Result<()> {
    let mut arguments = env::args().skip(1);
    let mut paths = Vec::new();
    let mut from = None;
    let mut to = None;
    // A flag with no value is reported rather than ignored: converting through
    // a format the caller did not name would be the wrong kind of helpful.
    let mut malformed = false;
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--from" => {
                from = arguments.next();
                malformed |= from.is_none();
            }
            "--to" => {
                to = arguments.next();
                malformed |= to.is_none();
            }
            _ => paths.push(argument),
        }
    }

    if malformed {
        eprintln!("{USAGE}");
        process::exit(2);
    }
    let [input, output] = paths.as_slice() else {
        eprintln!("{USAGE}");
        process::exit(2);
    };

    // Two ways in: the library's own load path, which resolves the asset and
    // chooses the format as every other layer read does, or the format the
    // caller named, which decodes the bytes as that whatever the file is.
    let opened;
    let forced;
    let data: &dyn sdf::AbstractData = match &from {
        None => {
            opened = sdf::Layer::open(input)?;
            opened.data()
        }
        Some(id) => {
            forced = format_named(id)?.read_bytes(fs::read(input)?.into(), input)?;
            &*forced
        }
    };

    let target = match &to {
        Some(id) => format_named(id)?,
        None => format_claiming(output)?,
    };
    if !target.caps().can_write() {
        return Err(Error::UnsupportedFormat(target.format_id().to_string()));
    }

    // Buffered: both writers emit in small pieces, so an unbuffered file sink
    // costs a syscall each. Flushed by hand, since dropping a `BufWriter`
    // swallows whatever its last write hit.
    let mut sink = BufWriter::new(File::create(output)?);
    target.write(data, &mut sink)?;
    sink.flush()?;

    println!("{input} -> {output} ({})", target.format_id());
    Ok(())
}

/// The format registered under `id`.
fn format_named(id: &str) -> Result<&'static dyn sdf::FileFormat> {
    sdf::LayerRegistry::find_by_id(id).ok_or_else(|| Error::UnsupportedFormat(id.to_owned()))
}

/// The format claiming `path`'s extension.
fn format_claiming(path: &str) -> Result<&'static dyn sdf::FileFormat> {
    Path::new(path)
        .extension()
        .and_then(|extension| extension.to_str())
        .and_then(sdf::LayerRegistry::find_by_extension)
        .ok_or_else(|| Error::UnsupportedFormat(path.to_owned()))
}
