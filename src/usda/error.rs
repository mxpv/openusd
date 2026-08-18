//! The located error type for `usda` text parsing.

use anyhow::Error;

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
    cause: Error,
    line: usize,
    column: usize,
    snippet: Box<str>,
    /// Byte range of the offending token within `snippet`.
    marker: Range<usize>,
    source_name: Option<Box<str>>,
}

impl ParseError {
    /// Locates `span` within `source`, keeping only the offending line.
    pub(super) fn new(cause: Error, source: &str, span: Range<usize>) -> Self {
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
        Some(self.cause.as_ref())
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
    use anyhow::anyhow;

    fn locate(source: &str, span: Range<usize>) -> ParseError {
        ParseError::new(anyhow!("boom"), source, span)
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
