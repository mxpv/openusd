//! What generation can fail with.

use std::io;
use std::path::PathBuf;

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
