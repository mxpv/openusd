//! The located error type for `usda` text parsing.

use std::borrow::Cow;
use std::error::Error as StdError;
use std::fmt;
use std::ops::Range;

/// Longest source line rendered in full. Longer lines are windowed around the
/// caret, so a failure on one of the very long single-line arrays that
/// crate-to-text conversion emits reports a readable excerpt.
const SNIPPET_WIDTH: usize = 160;

/// The marker placed at each end of a windowed snippet.
const ELLIPSIS: &str = "...";

/// A `usda` parse failure together with the source location it points at.
///
/// The line and column are resolved once, when the error is built. Formatting
/// generates the caret line from the stored snippet and marker.
#[derive(Debug)]
pub struct ParseError {
    cause: RawError,
    line: usize,
    column: usize,
    snippet: Box<str>,
    /// Byte range of the offending token within `snippet`.
    marker: Range<usize>,
    source_name: Option<Box<str>>,
}

impl ParseError {
    /// Locates `span` within `source`, keeping only the offending line.
    pub(super) fn new(cause: RawError, source: &str, span: Range<usize>) -> Self {
        // An end-of-input span starts one past the last byte, which belongs to
        // no line; step back onto the final character so the location lands on
        // real text. The walk stops at 0, which is always a char boundary.
        let mut offset = span.start.min(source.len());
        if offset == source.len() && offset > 0 {
            offset -= 1;
            while !source.is_char_boundary(offset) {
                offset -= 1;
            }
        }

        let line_start = source[..offset].rfind('\n').map_or(0, |index| index + 1);
        let line_end = source[offset..].find('\n').map_or(source.len(), |index| offset + index);
        let line = source[..line_start].matches('\n').count() + 1;

        // Clamp the marker against the trimmed line, so a span reaching that
        // line's `\r` cannot index past the snippet while formatting.
        let full_line = &source[line_start..line_end];
        let full_line = full_line.strip_suffix('\r').unwrap_or(full_line);
        let visible_end = line_start + full_line.len();
        let marker_start = offset.min(visible_end) - line_start;
        let marker_end = span.end.min(visible_end) - line_start;

        // Counted from the clamped start so the column and the caret agree.
        let column = full_line[..marker_start].chars().count() + 1;
        let (snippet, marker) = window(full_line, marker_start..marker_end.max(marker_start));

        Self {
            cause,
            line,
            column,
            snippet,
            marker,
            source_name: None,
        }
    }

    /// The 1-based line the error points at.
    pub fn line(&self) -> usize {
        self.line
    }

    /// The 1-based column the error points at, counted in characters.
    pub fn column(&self) -> usize {
        self.column
    }

    /// The offending source line, without its line terminator. A line longer
    /// than can be usefully printed is excerpted around the caret.
    pub fn snippet(&self) -> &str {
        &self.snippet
    }

    /// Names the source the text was read from, so the rendered location reads
    /// `name:line:column`.
    pub fn with_source_name(mut self, name: impl Into<Box<str>>) -> Self {
        self.source_name = Some(name.into());
        self
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "error: {}", self.cause)?;
        write!(f, " --> ")?;
        if let Some(name) = &self.source_name {
            write!(f, "{name}:")?;
        }
        writeln!(f, "{}:{}", self.line, self.column)?;

        let gutter = self.line.to_string();
        let pad = gutter.len();
        writeln!(f, "{:pad$} |", "")?;
        writeln!(f, "{gutter} | {}", self.snippet)?;
        write!(f, "{:pad$} | ", "")?;
        // Tabs stay tabs so the caret lands under the token.
        for ch in self.snippet[..self.marker.start].chars() {
            write!(f, "{}", if ch == '\t' { '\t' } else { ' ' })?;
        }
        let width = self.snippet[self.marker.clone()].chars().count().max(1);
        write!(f, "{:^<width$}", "")
    }
}

impl StdError for ParseError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.cause.0.source.as_deref().map(|source| source as _)
    }
}

/// The parser-internal failure behind a [`ParseError`]: the innermost message,
/// the breadcrumb trail of grammar productions above it, and the typed failure
/// that started it when one exists (a path or number that failed to parse).
///
/// One pointer wide, so the cursor and parser hot paths return a cheap
/// `Result`; the located, user-facing [`ParseError`] is built from this once,
/// at the parser's public entry point.
pub(crate) struct RawError(Box<Inner>);

/// Heap payload of [`RawError`].
struct Inner {
    /// The innermost failure message.
    message: Cow<'static, str>,
    /// Breadcrumbs naming the grammar productions the failure surfaced
    /// through, pushed innermost-first.
    trail: Vec<Cow<'static, str>>,
    /// The typed failure that started it, when one exists.
    source: Option<Box<dyn StdError + Send + Sync>>,
}

impl RawError {
    /// Wraps a failure message.
    pub(crate) fn new(message: impl Into<Cow<'static, str>>) -> Self {
        Self(Box::new(Inner {
            message: message.into(),
            trail: Vec::new(),
            source: None,
        }))
    }

    /// Pushes a breadcrumb naming the grammar production the failure is
    /// surfacing through.
    fn push(mut self, crumb: impl Into<Cow<'static, str>>) -> Self {
        self.0.trail.push(crumb.into());
        self
    }
}

impl fmt::Display for RawError {
    /// Renders the trail outermost-first, ending with the innermost message.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for crumb in self.0.trail.iter().rev() {
            write!(f, "{crumb}: ")?;
        }
        write!(f, "{}", self.0.message)
    }
}

impl fmt::Debug for RawError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawError")
            .field("message", &self.0.message)
            .field("trail", &self.0.trail)
            .field("source", &self.0.source)
            .finish()
    }
}

/// Every typed error converts by keeping its rendered message and itself as
/// the source, so `?` works throughout the parser and the original error stays
/// reachable through [`StdError::source`] on [`ParseError`].
impl<E: StdError + Send + Sync + 'static> From<E> for RawError {
    fn from(error: E) -> Self {
        Self(Box::new(Inner {
            message: error.to_string().into(),
            trail: Vec::new(),
            source: Some(Box::new(error)),
        }))
    }
}

/// Returns `Err(RawError)` built from a format string.
macro_rules! bail {
    ($($arg:tt)*) => {
        return Err($crate::usda::error::RawError::new(format!($($arg)*)))
    };
}

/// Returns a failure built from a format string unless `cond` holds.
macro_rules! ensure {
    ($cond:expr, $($arg:tt)*) => {
        if !$cond {
            bail!($($arg)*);
        }
    };
}

pub(crate) use {bail, ensure};

/// Breadcrumb wrapping for parser `Result`s and `Option`s.
pub(crate) trait Ctx<T> {
    /// Wraps the failure with a breadcrumb naming the enclosing production.
    fn context(self, crumb: impl Into<Cow<'static, str>>) -> Result<T, RawError>;

    /// Like [`context`](Self::context), but builds the breadcrumb lazily.
    fn with_context<C: Into<Cow<'static, str>>>(self, f: impl FnOnce() -> C) -> Result<T, RawError>;
}

impl<T, E: Into<RawError>> Ctx<T> for Result<T, E> {
    fn context(self, crumb: impl Into<Cow<'static, str>>) -> Result<T, RawError> {
        self.map_err(|error| error.into().push(crumb))
    }

    fn with_context<C: Into<Cow<'static, str>>>(self, f: impl FnOnce() -> C) -> Result<T, RawError> {
        self.map_err(|error| error.into().push(f()))
    }
}

impl<T> Ctx<T> for Option<T> {
    /// A missing value reports the breadcrumb itself as the failure.
    fn context(self, crumb: impl Into<Cow<'static, str>>) -> Result<T, RawError> {
        self.ok_or_else(|| RawError::new(crumb))
    }

    fn with_context<C: Into<Cow<'static, str>>>(self, f: impl FnOnce() -> C) -> Result<T, RawError> {
        self.ok_or_else(|| RawError::new(f()))
    }
}

/// Trims `line` to a window around `marker` when it is too long to print,
/// returning the excerpt and the marker rebased onto it.
fn window(line: &str, marker: Range<usize>) -> (Box<str>, Range<usize>) {
    if line.len() <= SNIPPET_WIDTH {
        return (line.into(), marker);
    }

    let mut start = marker.start.saturating_sub(SNIPPET_WIDTH / 2);
    while start > 0 && !line.is_char_boundary(start) {
        start -= 1;
    }
    // Bound the excerpt itself, so an offending token wider than the window
    // cannot pull the rest of the line in behind it.
    let mut end = start.saturating_add(SNIPPET_WIDTH).min(line.len());
    while end < line.len() && !line.is_char_boundary(end) {
        end += 1;
    }

    let prefix = if start > 0 { ELLIPSIS } else { "" };
    let suffix = if end < line.len() { ELLIPSIS } else { "" };
    let excerpt = format!("{prefix}{}{suffix}", &line[start..end]);
    let shift = prefix.len();
    let rebased = (marker.start - start + shift)..(marker.end.min(end) - start + shift);

    (excerpt.into(), rebased)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn locate(source: &str, span: Range<usize>) -> ParseError {
        ParseError::new(RawError::new("boom"), source, span)
    }

    #[test]
    fn eof_lands_on_text() {
        // The span sits one past the final byte; the location must stay inside
        // the file rather than naming a line that does not exist.
        let source = "abc\ndef\n";
        let error = locate(source, source.len()..source.len());
        assert_eq!(error.line(), 2);
        assert_eq!(error.snippet(), "def");
    }

    #[test]
    fn empty_source() {
        let error = locate("", 0..0);
        assert_eq!(error.line(), 1);
        assert_eq!(error.column(), 1);
        assert_eq!(error.snippet(), "");
    }

    #[test]
    fn crlf_marker_clamped() {
        // A span covering the `\r` must not index past the trimmed snippet.
        let source = "ab\r\ncd\r\n";
        let error = locate(source, 2..4);
        assert_eq!(error.snippet(), "ab");
        assert_eq!(error.column(), 3);
        assert!(error.to_string().contains("1 | ab"), "got: {error}");
    }

    #[test]
    fn column_matches_caret() {
        let source = "  float x = =\n";
        let error = locate(source, 12..13);
        let rendered = error.to_string();
        let caret = rendered.lines().last().expect("caret line");
        let caret_column = caret.find('^').expect("caret") - "  | ".len() + 1;
        assert_eq!(caret_column, error.column());
    }

    #[test]
    fn multibyte_column() {
        // Three 2-byte chars, so the second `=` is byte 9 but character 7.
        let source = "\u{e9}\u{e9}\u{e9} = =\n";
        let error = locate(source, 9..10);
        assert_eq!(error.column(), 7, "columns count characters, not bytes");
    }

    #[test]
    fn long_line_windowed() {
        let line = format!("float[] p = [{}]", "1.0, ".repeat(400));
        let marker = line.len() - 2;
        let error = locate(&line, marker..line.len() - 1);

        assert!(
            error.snippet().len() < SNIPPET_WIDTH + 2 * ELLIPSIS.len() + 8,
            "snippet should be windowed, got {} bytes",
            error.snippet().len()
        );
        assert!(error.snippet().starts_with(ELLIPSIS), "got: {}", error.snippet());
        // The true column is unaffected by windowing.
        assert_eq!(error.column(), marker + 1);
    }

    #[test]
    fn long_marker_capped() {
        // The offending token alone is wider than the window.
        let line = format!("x = \"{}\"", "y".repeat(4000));
        let error = locate(&line, 4..line.len());

        assert!(
            error.snippet().len() <= SNIPPET_WIDTH + 2 * ELLIPSIS.len(),
            "snippet should stay bounded, got {} bytes",
            error.snippet().len()
        );
        assert!(
            error.to_string().lines().count() == 5,
            "render stays five lines, got: {error}"
        );
    }

    #[test]
    fn short_line_kept_whole() {
        let error = locate("float x = 1\n", 10..11);
        assert_eq!(error.snippet(), "float x = 1");
        assert!(!error.snippet().contains(ELLIPSIS));
    }
}
