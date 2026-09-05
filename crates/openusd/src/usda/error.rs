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

/// Stands in for the source lines between the two ends of a span, of which a
/// diagnostic prints only the ends.
const ELIDED_LINES: &str = "...";

/// A `usda` parse failure together with the source location it points at.
///
/// The location is resolved once, when the error is built; formatting renders
/// the stored lines and their carets.
#[derive(Debug)]
pub struct ParseError {
    cause: RawError,
    head: MarkedLine,
    /// The line the span closes on, when it closes on a later one than it opens.
    ///
    /// Boxed because the span of an ordinary token stays within one line, and
    /// [`SchemaRegistryError`](crate::usd::SchemaRegistryError) and
    /// [`ArchiveError`](crate::usdz::ArchiveError) carry a `ParseError` by
    /// value: the common failure should not grow by the rare one's cost.
    tail: Option<Box<MarkedLine>>,
    source_name: Option<Box<str>>,
}

/// One source line with the region of it a diagnostic marks.
///
/// A span reaching past the line is clamped to it, so the two ends of a span
/// crossing a line boundary mark the same thing under one rule: whatever of the
/// span falls on that line.
#[derive(Debug)]
struct MarkedLine {
    /// 1-based line number.
    line: usize,
    /// 1-based column the mark starts at, counted in characters.
    column: usize,
    /// The line without its terminator, windowed when too long to print whole.
    snippet: Box<str>,
    /// Byte range within `snippet` the caret underlines.
    marker: Range<usize>,
}

/// Which end of a span a [`MarkedLine`] carries.
enum Edge {
    /// The line the span opens on, marked from where the span starts.
    Opens,
    /// The line the span closes on, marked from that line's own start.
    Closes,
}

impl MarkedLine {
    /// Marks the part of `span` falling on `line`, which carries the span's
    /// `edge`. Both are byte offsets into the source `line` came from.
    fn mark(line: &Line<'_>, span: &Range<usize>, edge: Edge) -> Self {
        // Clamping against the trimmed line keeps a span reaching that line's
        // `\r`, or lying off it entirely, from indexing past the snippet while
        // formatting.
        let visible_end = line.end();
        let from = match edge {
            Edge::Opens => span.start.clamp(line.start, visible_end),
            Edge::Closes => line.start,
        } - line.start;
        let to = span.end.clamp(line.start, visible_end) - line.start;

        // A windowed excerpt has to keep the span's own boundary on this line,
        // rather than the line edge its other end is clamped to.
        let focus = match edge {
            Edge::Opens => from,
            Edge::Closes => to,
        };

        // Counted before windowing, whose ellipsis prefix would shift it.
        let column = line.text[..from].chars().count() + 1;
        let (snippet, marker) = window(line.text, from..to, focus);
        Self {
            line: line.number,
            column,
            snippet,
            marker,
        }
    }

    /// Writes the numbered source line and the caret line under it, without a
    /// trailing newline.
    fn write(&self, f: &mut fmt::Formatter<'_>, pad: usize) -> fmt::Result {
        let (line, snippet) = (self.line, &self.snippet);
        writeln!(f, "{line:pad$} | {snippet}")?;
        write!(f, "{:pad$} | ", "")?;
        // Tabs stay tabs so the caret lands under the token.
        for ch in snippet[..self.marker.start].chars() {
            write!(f, "{}", if ch == '\t' { '\t' } else { ' ' })?;
        }
        let width = snippet[self.marker.clone()].chars().count().max(1);
        write!(f, "{:^<width$}", "")
    }
}

impl ParseError {
    /// Locates `span` within `source`, keeping the lines it opens and closes on.
    pub(super) fn new(cause: RawError, source: &str, span: Range<usize>) -> Self {
        // An end-of-input span starts one past the last byte, which belongs to
        // no line; step back onto the final character so the location lands on
        // real text.
        let offset = if span.start < source.len() {
            span.start
        } else {
            step_back(source, source.len())
        };
        let opening = line_at(source, offset);
        let head = MarkedLine::mark(&opening, &(offset..span.end), Edge::Opens);

        // The span's end is exclusive, so its final character says where it
        // closes, and a line terminator between there and the opening line's
        // start is what puts it on a later line. An empty span has no such
        // character, leaving that range inverted and nothing to close.
        let last = step_back(source, span.end);
        let tail = source
            .get(opening.start..last)
            .is_some_and(|opened| opened.contains('\n'))
            .then(|| {
                let closing = line_at(source, last);
                Box::new(MarkedLine::mark(&closing, &span, Edge::Closes))
            });

        Self {
            cause,
            head,
            tail,
            source_name: None,
        }
    }

    /// The 1-based line the error points at.
    pub fn line(&self) -> usize {
        self.head.line
    }

    /// The 1-based column the error points at, counted in characters.
    pub fn column(&self) -> usize {
        self.head.column
    }

    /// The source line the error opens on, without its line terminator. A line
    /// longer than can be usefully printed is excerpted around the caret.
    ///
    /// A span reaching past that line — a multi-line token — closes on a later
    /// one this does not report; the [`Display`](fmt::Display) rendering is the
    /// complete one.
    pub fn snippet(&self) -> &str {
        &self.head.snippet
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
        writeln!(f, "{}:{}", self.head.line, self.head.column)?;

        // The gutter is sized for the largest line number it will carry.
        let last_line = self.tail.as_ref().map_or(self.head.line, |tail| tail.line);
        let pad = last_line.to_string().len();
        writeln!(f, "{:pad$} |", "")?;
        self.head.write(f, pad)?;

        let Some(tail) = &self.tail else {
            return Ok(());
        };
        writeln!(f)?;
        // Only the two ends of a long span are worth printing; the lines it
        // runs through say nothing the reader cannot see in the source.
        if tail.line > self.head.line + 1 {
            writeln!(f, "{ELIDED_LINES}")?;
        }
        tail.write(f, pad)
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

/// Steps `offset` back onto the previous character, staying on a char boundary
/// and stopping at 0.
fn step_back(source: &str, offset: usize) -> usize {
    let mut offset = offset.min(source.len());
    if offset > 0 {
        offset -= 1;
        while !source.is_char_boundary(offset) {
            offset -= 1;
        }
    }
    offset
}

/// One source line, located by a byte offset falling on it.
struct Line<'a> {
    /// 1-based line number.
    number: usize,
    /// Byte offset the line begins at.
    start: usize,
    /// The line itself, without its terminator.
    text: &'a str,
}

impl Line<'_> {
    /// Byte offset just past the line's last printable character.
    fn end(&self) -> usize {
        self.start + self.text.len()
    }
}

/// The line `offset` falls on.
fn line_at(source: &str, offset: usize) -> Line<'_> {
    let start = source[..offset].rfind('\n').map_or(0, |index| index + 1);
    let end = source[offset..].find('\n').map_or(source.len(), |index| offset + index);
    let text = &source[start..end];
    Line {
        number: source[..start].matches('\n').count() + 1,
        start,
        text: text.strip_suffix('\r').unwrap_or(text),
    }
}

/// Trims `line` to a window around `focus` when it is too long to print,
/// returning the excerpt and `marker` rebased onto it.
fn window(line: &str, marker: Range<usize>, focus: usize) -> (Box<str>, Range<usize>) {
    if line.len() <= SNIPPET_WIDTH {
        return (line.into(), marker);
    }

    let mut start = focus.saturating_sub(SNIPPET_WIDTH / 2);
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
    let rebased = (marker.start.max(start) - start + shift)..(marker.end.min(end) - start + shift);

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
    fn crlf_eof_single_line() {
        // The final `\n` sits past the trimmed line yet still on it, so an
        // end-of-input failure has nothing left to close on a later line.
        let source = "float x = 1\r\n";
        let error = locate(source, source.len()..source.len());

        let rendered = error.to_string();
        assert_eq!(rendered.matches("float x = 1").count(), 1, "{rendered}");
        assert_eq!(rendered.lines().count(), 5, "{rendered}");
    }

    #[test]
    fn column_matches_caret() {
        let source = "  float x = =\n";
        let error = locate(source, 12..13);
        let rendered = error.to_string();
        // The caret under the line the span opens on.
        let caret = rendered.lines().nth(4).expect("caret line");
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

    #[test]
    fn empty_span_at_line_start() {
        // The span's final character sits before the line it opens on, so
        // there is no later line for it to close on.
        let error = locate("a\nb\n", 2..2);

        assert_eq!(error.line(), 2);
        assert_eq!(error.column(), 1);
        assert_eq!(error.to_string().lines().count(), 5);
    }

    #[test]
    fn crlf_multiline_span() {
        let source = "float x = \"\"\"a\r\nb\"\"\"\r\n";
        let error = locate(source, 10..20);

        let rendered = error.to_string();
        let lines: Vec<_> = rendered.lines().collect();
        assert_eq!(lines[3], "1 | float x = \"\"\"a");
        assert_eq!(lines[5], "2 | b\"\"\"");
        assert_eq!(lines[6], "  | ^^^^");
    }

    /// The closing line is windowed around where the span ends, so the
    /// excerpt shows what its caret points at.
    #[test]
    fn long_close_stays_visible() {
        let source = format!("x = \"\"\"a\n{}\"\"\"", "y".repeat(400));
        let end = source.rfind("\"\"\"").expect("token") + 3;
        let error = locate(&source, 4..end);

        let rendered = error.to_string();
        let closing = rendered.lines().nth(5).expect("closing line");
        assert!(closing.starts_with("2 | "), "got: {closing}");
        assert!(closing.ends_with("\"\"\""), "got: {closing}");
        assert!(closing.contains(ELLIPSIS), "got: {closing}");
    }

    /// A span crossing a line boundary renders where it closes as well as where
    /// it opens, so a multi-line token does not report a caret under its first
    /// fragment alone.
    #[test]
    fn multiline_span_shows_close() {
        let source = "float x = \"\"\"a\nb\"\"\"\n";
        let start = source.find("\"\"\"").expect("token");
        let end = source.rfind("\"\"\"").expect("token") + 3;
        let error = locate(source, start..end);

        assert_eq!(error.line(), 1);
        assert_eq!(error.column(), 11);
        let rendered = error.to_string();
        let lines: Vec<_> = rendered.lines().collect();
        // Both ends mark the same thing: whatever of the span falls on the line.
        assert_eq!(lines[3], "1 | float x = \"\"\"a");
        assert_eq!(lines[4], "  |           ^^^^", "the opening line marks to its end");
        assert_eq!(lines[5], "2 | b\"\"\"");
        assert_eq!(lines[6], "  | ^^^^", "the closing line marks from its start");
    }

    /// The lines a long span runs through are elided: only its two ends carry
    /// anything the source does not already show.
    #[test]
    fn long_span_elides_middle() {
        let source = "a\nb\nc\nd\n";
        let error = locate(source, 0..source.len());

        let rendered = error.to_string();
        let lines: Vec<_> = rendered.lines().collect();
        assert_eq!(lines[3], "1 | a");
        assert_eq!(lines[5], ELIDED_LINES);
        assert_eq!(lines[6], "4 | d");

        // A span closing on the line it opened on renders neither end twice.
        let single = locate("float x = 1\n", 6..7).to_string();
        assert!(!single.contains(ELIDED_LINES), "{single}");
        assert_eq!(single.lines().count(), 5);
    }
}
