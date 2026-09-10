//! What generation can fail with.

use std::io;
use std::path::PathBuf;

use crate::validate::Violation;

/// A failure while generating a schema library.
///
/// A build script runs this, so a variant that has a file to name names it:
/// the message is all a contributor sees when `cargo build` stops.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// Generation had schemas to build but nowhere to write them.
    #[error("no output directory: call Builder::out_dir, or run this from a build script, which sets OUT_DIR")]
    NoOutDir,

    /// Reading a schema through `openusd` failed.
    #[error(transparent)]
    Core(#[from] openusd::Error),

    /// A schema's layers did not compose, so what it declares cannot be read.
    #[error("{schema} does not compose: {diagnostic}")]
    Composition {
        /// The schema that was being read.
        schema: PathBuf,
        /// What composition reported. An unresolved sublayer usually wants a
        /// `search_path`.
        diagnostic: String,
    },

    /// A schema library did not name itself, so nothing can refer to it.
    #[error("{schema}: no /GLOBAL prim declares customData.libraryName")]
    NoLibraryName {
        /// The schema that was being read.
        schema: PathBuf,
    },

    /// A schema declares something the generator cannot honour.
    #[error("{origin}: {violation}")]
    Definition {
        /// Where the offending declaration lives, layer and path.
        origin: String,
        /// Which rule it broke.
        violation: Violation,
    },

    /// A field holds a value the generated declaration has no Rust literal for.
    ///
    /// Only a fallback or a piece of metadata reaches the table, so this is a
    /// value type nothing generated has needed yet rather than an unusual
    /// schema. It stops the build: a fallback that went missing would leave the
    /// generated schemas answering differently from the ones they came from.
    #[error("{schema}.{field} holds a {kind} value, which the generated declaration cannot express")]
    UnwritableValue {
        /// The schema declaring it.
        schema: String,
        /// The field on it.
        field: String,
        /// The value type that has no literal.
        kind: &'static str,
    },

    /// The generator wrote Rust that does not parse.
    ///
    /// A defect in this crate rather than anything a schema can ask for, but it
    /// surfaces in a consumer's build, so it says which schema was being
    /// generated and what the parser made of it.
    #[error("generated Rust for {schema} does not parse: {cause}")]
    Malformed {
        /// The schema being generated.
        schema: String,
        /// What parsing the emitted tokens reported.
        cause: String,
    },

    /// A file or directory could not be read, written or created.
    #[error("cannot access {path}")]
    Io {
        /// What was being read or written.
        path: PathBuf,
        /// What the filesystem reported.
        #[source]
        source: io::Error,
    },
}

impl Error {
    /// The first diagnostic `stage` raised, named against the schema it came
    /// from.
    ///
    /// Composition reports many; the first is the one a contributor fixes,
    /// and the rest usually follow from it.
    pub(crate) fn composition(schema: &std::path::Path, stage: &openusd::usd::Stage) -> Option<Self> {
        let diagnostic = stage.composition_errors().first()?.to_string();
        Some(Error::Composition {
            schema: schema.to_path_buf(),
            diagnostic,
        })
    }
}

/// A malformed path names nothing to read.
///
/// Written out rather than derived: `#[from]` builds a conversion into the
/// variant holding that type, and this belongs in [`Error::Core`] with every
/// other core failure. Its own variant would let one failure arrive two ways —
/// as itself, or nested in a `Core` — and leave a caller matching in two
/// places for it. `openusd::Error` already tells them apart.
impl From<openusd::sdf::PathParseError> for Error {
    fn from(source: openusd::sdf::PathParseError) -> Self {
        Error::Core(source.into())
    }
}

/// Authoring the layers this crate writes goes through the same door every
/// other edit does. Written out for the reason above.
impl From<openusd::sdf::EditError> for Error {
    fn from(source: openusd::sdf::EditError) -> Self {
        Error::Core(source.into())
    }
}

/// Writing a generated layer out as text, which is how both reach the files a
/// consumer's build script leaves behind. Written out for the reason above.
impl From<openusd::sdf::ExportError> for Error {
    fn from(source: openusd::sdf::ExportError) -> Self {
        Error::Core(source.into())
    }
}

/// A field that will not decode is schema data this crate cannot use. Written
/// out for the reason above.
impl From<openusd::sdf::DataError> for Error {
    fn from(source: openusd::sdf::DataError) -> Self {
        Error::Core(source.into())
    }
}
