//! The crate-root error type.
//!
//! Every module reports failures with its own error type (e.g.
//! [`usda::ParseError`], [`pcp::QueryError`], [`sdf::AuthoringError`]); this
//! module folds them into the one [`enum@Error`] end users consume, so `?`
//! converges in application code and composed-stage queries have a single
//! error type spanning the module boundaries a query crosses.

use std::convert::Infallible;
use std::{error, io, mem, result};

use crate::{pcp, sdf, usd, usda, usdc, usdz};

/// Largest module error nested directly in [`enum@Error`]; anything bigger is
/// boxed so the enum stays within the size the assertion below pins. The
/// boxes are justified against 64-bit layouts, so the budget-exceeded checks
/// on the boxing `From` impls hold only there.
/// `Result<T, Error>` rides every composed-stage read query, so the error arm
/// must not bloat the return ABI of calls that overwhelmingly succeed.
const INLINE_ERROR_BUDGET: usize = 64;

/// Any failure the crate can report, one variant per module error family.
///
/// Every variant is transparent — Display and `source` are the wrapped
/// error's own. A module error up to `INLINE_ERROR_BUDGET` bytes nests
/// directly; a larger one is boxed by its manual `From` impl below.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// Byte I/O failed.
    #[error(transparent)]
    Io(#[from] io::Error),

    /// A path string failed to parse.
    #[error(transparent)]
    Path(#[from] sdf::PathParseError),

    /// A layer backend failed to decode an authored field value.
    #[error(transparent)]
    Data(#[from] sdf::DataError),

    /// A value does not cast to the requested type.
    #[error(transparent)]
    Cast(#[from] sdf::CastError),

    /// A value conversion outside the crate's own types failed. The home a
    /// downstream `TryFrom<sdf::Value>` error converts into (via
    /// [`Error::convert`]) so extension value types satisfy the generic
    /// accessors' `T::Error: Into<Error>` bound.
    #[error(transparent)]
    Convert(Box<dyn error::Error + Send + Sync>),

    /// A variable expression failed to parse.
    #[error(transparent)]
    Expr(#[from] sdf::ExprError),

    /// A path expression could not be compiled into an evaluator.
    #[error(transparent)]
    PathExpr(#[from] sdf::EvalError),

    /// A file format failed to read or write a layer.
    #[error(transparent)]
    Format(#[from] sdf::FormatError),

    /// A layer could not be exported or saved.
    #[error(transparent)]
    Export(#[from] sdf::ExportError),

    /// `usda` text failed to parse.
    #[error(transparent)]
    Parse(Box<usda::ParseError>),

    /// `usdc` crate data failed to read.
    #[error(transparent)]
    Read(#[from] usdc::ReadError),

    /// A `usdz` package failed to read or write.
    #[error(transparent)]
    Archive(Box<usdz::ArchiveError>),

    /// A stage population mask was built from an invalid path.
    #[error(transparent)]
    PopulationMask(#[from] pcp::PopulationMaskError),

    /// Answering a composed query or building a prim index failed.
    #[error(transparent)]
    Query(#[from] pcp::QueryError),

    /// A stage authoring call failed.
    #[error(transparent)]
    Authoring(#[from] usd::StageAuthoringError),

    /// A namespace edit failed.
    #[error(transparent)]
    NamespaceEdit(#[from] usd::NamespaceEditError),

    /// An API schema could not be applied.
    #[error(transparent)]
    ApplyApi(#[from] usd::ApplyApiError),

    /// Registering schema families or building their definitions failed.
    #[error(transparent)]
    SchemaRegistry(Box<usd::SchemaRegistryError>),

    /// The stage root or session layer's asset path resolved to nothing.
    #[error("failed to resolve asset path: {0}")]
    UnresolvedAsset(String),

    /// No registered file format claims the resolved location.
    #[error("no file format registered for {0}")]
    UnsupportedFormat(String),
}

impl Error {
    /// Wraps a caller-supplied conversion failure, the one-liner behind a
    /// downstream `impl From<MyError> for openusd::Error`.
    pub fn convert(error: impl error::Error + Send + Sync + 'static) -> Self {
        Self::Convert(Box::new(error))
    }
}

/// The crate-wide result type, defaulting to the root [`enum@Error`].
pub type Result<T, E = Error> = result::Result<T, E>;

// The largest inline payload plus the discriminant word.
const _: () = assert!(mem::size_of::<Error>() <= INLINE_ERROR_BUDGET + mem::size_of::<usize>());

/// An infallible conversion can never produce an error; the impl exists so
/// generic `TryFrom<sdf::Value>` bounds accept the reflexive conversion.
impl From<Infallible> for Error {
    fn from(error: Infallible) -> Self {
        match error {}
    }
}

#[cfg(target_pointer_width = "64")]
const _: () = assert!(mem::size_of::<usda::ParseError>() > INLINE_ERROR_BUDGET);

impl From<usda::ParseError> for Error {
    fn from(error: usda::ParseError) -> Self {
        Self::Parse(Box::new(error))
    }
}

#[cfg(target_pointer_width = "64")]
const _: () = assert!(mem::size_of::<usdz::ArchiveError>() > INLINE_ERROR_BUDGET);

impl From<usdz::ArchiveError> for Error {
    fn from(error: usdz::ArchiveError) -> Self {
        Self::Archive(Box::new(error))
    }
}

#[cfg(target_pointer_width = "64")]
const _: () = assert!(mem::size_of::<usd::SchemaRegistryError>() > INLINE_ERROR_BUDGET);

impl From<usd::SchemaRegistryError> for Error {
    fn from(error: usd::SchemaRegistryError) -> Self {
        Self::SchemaRegistry(Box::new(error))
    }
}

/// Layer-level authoring failures route through the stage-tier variant, so
/// code mixing layer- and stage-level calls converges with one `?`.
impl From<sdf::AuthoringError> for Error {
    fn from(error: sdf::AuthoringError) -> Self {
        Self::Authoring(error.into())
    }
}

/// Layer edit failures route through the stage-tier variant, like
/// [`sdf::AuthoringError`].
impl From<sdf::EditError> for Error {
    fn from(error: sdf::EditError) -> Self {
        Self::Authoring(error.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transparent_display() {
        let error = Error::from(sdf::Path::new("not a path").unwrap_err());
        assert_eq!(
            error.to_string(),
            sdf::Path::new("not a path").unwrap_err().to_string(),
            "the root error renders as the module error it wraps"
        );
    }

    #[test]
    fn nested_cause_stays_typed() {
        let error = Error::from(pcp::QueryError::from(sdf::PathParseError {
            input: "x".into(),
            offset: 0,
            reason: "test",
        }));
        // The typed cause stays matchable through the enum nesting.
        let Error::Query(pcp::QueryError::Path(path_error)) = error else {
            panic!("expected Query(Path), got: {error}");
        };
        assert_eq!(path_error.reason, "test");
    }
}
