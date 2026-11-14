//! Prints the USD layer a `.mtlx` reads as, in `usda` text.
//!
//! ```sh
//! cargo run -p openusd-mtlx --example cat -- path/to/material.mtlx
//! ```

use std::env;
use std::process::ExitCode;

use openusd::sdf;

fn main() -> ExitCode {
    let Some(path) = env::args().nth(1) else {
        eprintln!("usage: cat <file.mtlx>");
        return ExitCode::FAILURE;
    };
    let registry = sdf::LayerRegistry::default().with_format(&openusd_mtlx::MTLX);
    let text = registry
        .find_or_open(&path)
        .map_err(|error| error.to_string())
        .and_then(|layer| layer.ok_or_else(|| format!("{path} does not resolve")))
        .and_then(|layer| layer.borrow().export_to_string().map_err(|error| error.to_string()));
    match text {
        Ok(text) => {
            print!("{text}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
