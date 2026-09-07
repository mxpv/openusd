//! Generates Rust schema views from OpenUSD `schema.usda` files.
//!
//! This is the Rust answer to `usdGenSchema`, shaped as a build dependency: a
//! consumer describes its schema libraries in `build.rs`, and the generated
//! views join the crate through
//! [`openusd::include_schema!`](openusd::include_schema).
//!
//! ```no_run
//! // build.rs
//! openusd_build::configure()
//!     .search_path("schemas")
//!     .schema("schemas/usdGeom/schema.usda")
//!     .generate()?;
//! # Ok::<(), openusd_build::Error>(())
//! ```
//!
//! ```ignore
//! // src/lib.rs
//! pub mod geom {
//!     openusd::include_schema!("usdGeom");
//! }
//! ```
//!
//! A library's name comes from the `libraryName` its `schema.usda` declares,
//! not from the path, so the two spellings above name one library.
//!
//! Reading a `schema.usda` and emitting from it is not implemented yet:
//! [`Builder::generate`] accepts what to build and writes nothing.

mod error;

use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::PathBuf;

pub use error::Error;

/// Starts describing what to generate. See [`Builder`].
pub fn configure() -> Builder {
    Builder {
        out_dir: None,
        search_paths: Vec::new(),
        extern_libraries: BTreeMap::new(),
        schemas: Vec::new(),
    }
}

/// What to generate, and where.
///
/// Every method takes and returns the builder, so a `build.rs` reads as one
/// expression.
#[derive(Debug)]
pub struct Builder {
    out_dir: Option<PathBuf>,
    search_paths: Vec<PathBuf>,
    extern_libraries: BTreeMap<String, String>,
    schemas: Vec<PathBuf>,
}

impl Builder {
    /// Writes generated files to `dir` instead of `OUT_DIR`.
    ///
    /// A build script needs this only when it writes somewhere it also reads
    /// from, such as a checked-in copy; `OUT_DIR` is the ordinary destination,
    /// and where [`openusd::include_schema!`](openusd::include_schema) looks.
    #[must_use]
    pub fn out_dir(mut self, dir: impl Into<PathBuf>) -> Self {
        self.out_dir = Some(dir.into());
        self
    }

    /// Adds a directory that a `schema.usda`'s sublayers resolve through, the
    /// way [`ar::DefaultResolver::with_search_paths`](openusd::ar::DefaultResolver::with_search_paths)
    /// takes them.
    ///
    /// Upstream schemas sublayer each other by bare path
    /// (`subLayers = [@usd/schema.usda@]`), which is what a search path
    /// resolves. Repeatable, and searched in the order given.
    #[must_use]
    pub fn search_path(mut self, dir: impl Into<PathBuf>) -> Self {
        self.search_paths.push(dir.into());
        self
    }

    /// Declares where a library this run does not generate already lives, so
    /// the generated code can name types from it.
    ///
    /// `library` is the `libraryName` that library's `schema.usda` declares and
    /// `rust_path` the module path its views are reachable at, as in
    /// `("usdGeom", "openusd_schemas::geom")`. A class inheriting from a
    /// library this run does not generate needs it declared here. Keyed by
    /// library name, so declaring one twice keeps the last.
    #[must_use]
    pub fn extern_library(mut self, library: impl Into<String>, rust_path: impl Into<String>) -> Self {
        self.extern_libraries.insert(library.into(), rust_path.into());
        self
    }

    /// Adds a `schema.usda` to generate a library from. Repeatable.
    #[must_use]
    pub fn schema(mut self, path: impl Into<PathBuf>) -> Self {
        self.schemas.push(path.into());
        self
    }

    /// Generates every configured library.
    ///
    /// Configuring no schemas is not an error and writes nothing: a consumer
    /// whose families are feature-gated generates none of them when its
    /// features are off, and its `build.rs` should not have to know that.
    ///
    /// Otherwise the output directory must be known, from
    /// [`out_dir`](Self::out_dir) or from the `OUT_DIR` a build script runs
    /// with, and is created if it does not exist.
    // TODO: read each schema's layer stack, validate it the way usdGenSchema
    // does, and emit the views, schematics and manifest. Telling cargo what to
    // watch belongs with that, and so does the option that turns it off: what
    // generation depends on is the layers a schema resolves to, sublayers
    // included, which only the loader knows. The configured paths are not that
    // set, and printing any `cargo:rerun-if-changed` line at all switches off
    // cargo's own "rerun if the package changed" default, so printing a
    // narrower set would track less than printing none.
    pub fn generate(self) -> Result<(), Error> {
        if self.schemas.is_empty() {
            return Ok(());
        }

        let out_dir = match self.out_dir {
            Some(dir) => dir,
            None => env::var_os("OUT_DIR").map(PathBuf::from).ok_or(Error::NoOutDir)?,
        };
        fs::create_dir_all(&out_dir).map_err(|source| Error::Io { path: out_dir, source })?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A run with nothing configured writes nothing and needs no destination,
    /// which is the state a consumer's build script is in when every schema
    /// family it can generate is behind a feature that is off.
    #[test]
    fn no_schemas_writes_nothing() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path().join("generated");

        configure().out_dir(&out).generate().expect("nothing to do");

        assert!(!out.exists(), "a run with no schemas creates no output directory");
    }

    /// The destination is created on demand, since `OUT_DIR` exists but a
    /// caller's own path need not.
    #[test]
    fn out_dir_created() {
        let dir = tempfile::tempdir().expect("tempdir");
        let out = dir.path().join("nested/generated");

        configure()
            .out_dir(&out)
            .schema("schemas/usdGeom/schema.usda")
            .generate()
            .expect("generates");

        assert!(out.is_dir(), "the output directory is created if it is missing");
    }

    /// With schemas to build and nowhere to put them, generation stops rather
    /// than guessing.
    #[test]
    fn missing_out_dir_reported() {
        let error = configure()
            .schema("schemas/usdGeom/schema.usda")
            .generate()
            .expect_err("this crate has no build script, so its tests run without OUT_DIR set");

        assert!(matches!(error, Error::NoOutDir), "{error}");
    }

    /// A repeated option accumulates, except an extern library, which is keyed
    /// by library name and keeps the last declaration.
    ///
    /// Nothing reads either yet; they are what the generator will be given.
    #[test]
    fn repeated_options() {
        let builder = configure()
            .schema("schemas/usdGeom/schema.usda")
            .schema("schemas/usdLux/schema.usda")
            .extern_library("usdGeom", "crate::geom")
            .extern_library("usdGeom", "openusd_schemas::geom");

        assert_eq!(builder.schemas.len(), 2);
        assert_eq!(
            builder.extern_libraries.get("usdGeom").map(String::as_str),
            Some("openusd_schemas::geom")
        );
    }
}
