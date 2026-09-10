//! Generates the views for every schema family this build enables.
//!
//! A family's definitions are the vendored `schemas/<library>/schema.usda`,
//! and what comes out is what `src/<family>/mod.rs` includes: the views, and
//! the schema data its `register` hands a registry. A family that is not
//! enabled generates nothing, so a build with no features writes no files at
//! all.

use std::env;
use std::path::Path;

include!("families.rs");

fn main() {
    let schemas = Path::new("schemas");
    let mut builder = configured(schemas);

    for (family, library) in FAMILIES {
        if env::var_os(format!("CARGO_FEATURE_{}", family.to_uppercase())).is_some() {
            builder = builder.schema(schemas.join(library).join("schema.usda"));
        }
    }

    if let Err(error) = builder.generate() {
        panic!("generating schema views: {error}");
    }
}
