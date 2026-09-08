//! Turning a schema's documentation into Rust doc comments.
//!
//! A `schema.usda` documents itself for Doxygen, which C++ emits verbatim.
//! Rustdoc reads Markdown, so [`to_markdown`] rewrites the Doxygen commands
//! into it and tidies the prose around them: a word that reads as code is
//! backticked, a bare URL becomes an autolink, and a square bracket is escaped
//! so it is not taken for a broken intra-doc link.
//!
//! Commands and prose are rendered in one pass, because the two cannot be
//! layered. What a command has already rendered is finished — marking it up
//! again would put `*emphasis*` inside a code span — and a code sample reaches
//! the output exactly as the schema wrote it, commands and all.

/// Where a doc comment wraps: the project's 80-column prose width, less the
/// `/// ` every emitted line begins with.
const WIDTH: usize = 76;

/// Punctuation that stays outside markup when it opens a word, so a quoted
/// name is backticked without its quotes. A `[` is absent deliberately:
/// escaping a bracket is [`mark_up`]'s job.
const OPENING: &[char] = &['"', '\'', '('];

/// Punctuation that stays outside markup when it closes a word, so a code span
/// never swallows the full stop ending its sentence. A `)` is absent so that
/// `Compute()` keeps its call parentheses.
const CLOSING: &[char] = &['"', '\'', '.', ',', ';', ':', '!', '?'];

/// One schema's documentation as Markdown, wrapped and ready to emit as a
/// `///` block.
pub fn to_markdown(documentation: &str) -> String {
    let mut out = String::with_capacity(documentation.len() + documentation.len() / 4);

    for segment in segments(documentation) {
        match segment {
            Segment::Code(body) => {
                out.push_str("```text\n");
                out.push_str(body.trim_start_matches(['\r', '\n']).trim_end());
                out.push_str("\n```\n");
            }
            Segment::Prose(text) => {
                for line in text.lines() {
                    // A `\n` command renders as a break, so one source line can
                    // leave several to wrap.
                    for rendered in render_line(line).split('\n') {
                        out.push_str(&wrap(rendered));
                        out.push('\n');
                    }
                }
            }
        }
    }

    out.truncate(out.trim_end().len());
    out
}

/// A run of documentation, and whether it is prose to convert or a sample to
/// leave alone.
enum Segment<'a> {
    Prose(&'a str),
    Code(&'a str),
}

/// Splits documentation at the `\code` … `\endcode` samples, so neither kind of
/// text is put through the other's rules.
///
/// A sample opened and never closed runs to the end, which is what a reader of
/// the source sees too.
fn segments(documentation: &str) -> Vec<Segment<'_>> {
    let mut out = Vec::new();
    let mut rest = documentation;

    while let Some((at, after)) = find_command(rest, "code") {
        out.push(Segment::Prose(&rest[..at]));

        // `\code{.py}` names a language a fenced block does not carry over.
        let body = match after.strip_prefix('{') {
            Some(braced) => braced.split_once('}').map_or(braced, |(_, tail)| tail),
            None => after,
        };
        let Some((end, tail)) = find_command(body, "endcode") else {
            out.push(Segment::Code(body));
            return out;
        };
        out.push(Segment::Code(&body[..end]));
        rest = tail;
    }

    out.push(Segment::Prose(rest));
    out
}

/// Where `name` is next used as a command, and the text after it.
fn find_command<'a>(text: &'a str, name: &str) -> Option<(usize, &'a str)> {
    let mut searched = 0;
    while let Some(command) = next_command(&text[searched..]) {
        if command.name == name {
            return Some((searched + command.at, command.after));
        }
        searched += command.at + 1;
    }
    None
}

/// A Doxygen command: where its marker sits, which marker it is, its name, and
/// the text after the name.
#[derive(Clone, Copy)]
struct Command<'a> {
    at: usize,
    marker: char,
    name: &'a str,
    after: &'a str,
}

/// The next command in `text`.
///
/// A command opens a word and its name ends at whitespace, at the end of the
/// text, or at the `{` of a `\code{.py}`. Both conditions matter: without them
/// an asset path (`@code.usda@`) and an address (`me@example.com`) read as
/// commands, and a schema that documents one has it rewritten out from under
/// it.
fn next_command(text: &str) -> Option<Command<'_>> {
    let mut searched = 0;

    while let Some(offset) = text[searched..].find(['\\', '@']) {
        let at = searched + offset;
        let marker = text[at..].chars().next()?;
        let after_marker = &text[at + marker.len_utf8()..];

        let end = after_marker
            .find(|c: char| !c.is_ascii_alphabetic())
            .unwrap_or(after_marker.len());
        let (name, after) = after_marker.split_at(end);

        let opens_word = text[..at]
            .chars()
            .next_back()
            .is_none_or(|c| c.is_whitespace() || OPENING.contains(&c));
        let ends_name = after.is_empty() || after.starts_with(char::is_whitespace) || after.starts_with('{');

        if opens_word && !name.is_empty() && ends_name {
            return Some(Command {
                at,
                marker,
                name,
                after,
            });
        }
        searched = at + marker.len_utf8();
    }

    None
}

/// One prose line as Markdown: each command rendered where it stands, and the
/// source text between them marked up.
fn render_line(line: &str) -> String {
    let mut out = String::with_capacity(line.len() + line.len() / 8);
    let mut rest = line;

    while let Some(command) = next_command(rest) {
        mark_up(&rest[..command.at], &mut out);
        rest = render_command(&command, &mut out);
    }
    mark_up(rest, &mut out);
    out
}

/// Writes one command's Markdown and returns the text it did not consume.
///
/// Only the commands schema documentation actually reaches for; anything else
/// keeps the spelling it was written with, which reads as prose rather than
/// disappearing.
// TODO: `\section` and `\subsection` take a label before their title, and
// `\snippet` names a file this crate cannot see. Both are rare in schema
// documentation and are left as written until one shows up.
fn render_command<'a>(command: &Command<'a>, out: &mut String) -> &'a str {
    match command.name {
        // An emphasis command takes the one word that follows it.
        "em" | "e" => return wrap_next_word(command, '*', out),
        "p" | "a" | "c" => return wrap_next_word(command, '`', out),
        // `\ref target "text"` reads as its text, `\ref target` as the target
        // itself, which is a symbol name.
        "ref" => return reference(command, out),
        "sa" => out.push_str("See also"),
        "li" => {
            out.push_str("- ");
            return command.after.strip_prefix(' ').unwrap_or(command.after);
        }
        "note" => out.push_str("Note:"),
        "todo" => out.push_str("Todo:"),
        "deprecated" => out.push_str("Deprecated:"),
        "n" => out.push('\n'),
        // Not a command: an escaped backslash, or an `@` opening an asset path
        // or an address. Both keep the marker they were written with.
        _ => {
            out.push(command.marker);
            out.push_str(command.name);
        }
    }
    command.after
}

/// Writes the next word wrapped in `delimiter`, the punctuation around it left
/// outside, and returns what is left.
///
/// A command with no word after it keeps its own text rather than vanishing.
fn wrap_next_word<'a>(command: &Command<'a>, delimiter: char, out: &mut String) -> &'a str {
    let (word, rest) = next_word(command.after);
    let (leading, core, trailing) = split_word(word);
    if core.is_empty() {
        out.push(command.marker);
        out.push_str(command.name);
        return command.after;
    }

    out.push_str(leading);
    out.push(delimiter);
    out.push_str(core);
    out.push(delimiter);
    out.push_str(trailing);
    rest
}

/// Writes a `\ref` as its quoted text when it has one, else as the target.
fn reference<'a>(command: &Command<'a>, out: &mut String) -> &'a str {
    let (target, rest) = next_word(command.after);
    if target.is_empty() {
        out.push(command.marker);
        out.push_str(command.name);
        return command.after;
    }

    let quoted = rest.trim_start_matches(' ');
    if let Some(text) = quoted.strip_prefix('"')
        && let Some(close) = text.find('"')
    {
        out.push_str(&text[..close]);
        return &text[close + 1..];
    }

    let (leading, core, trailing) = split_word(target);
    if core.is_empty() {
        out.push_str(target);
    } else {
        out.push_str(leading);
        out.push('`');
        out.push_str(core);
        out.push('`');
        out.push_str(trailing);
    }
    rest
}

/// The next word after any leading spaces, and the text that follows it.
fn next_word(after: &str) -> (&str, &str) {
    let trimmed = after.trim_start_matches(' ');
    let end = trimmed.find(char::is_whitespace).unwrap_or(trimmed.len());
    trimmed.split_at(end)
}

/// A word split into the punctuation opening it, the part markup wraps, and
/// the punctuation closing it.
fn split_word(word: &str) -> (&str, &str, &str) {
    let after_opening = word.trim_start_matches(OPENING);
    let leading = &word[..word.len() - after_opening.len()];
    let core = after_opening.trim_end_matches(CLOSING);
    (leading, core, &word[leading.len() + core.len()..])
}

/// Writes source prose, marking up each word rustdoc would otherwise render
/// wrongly.
///
/// A word inside a code span the schema wrote itself passes through untouched,
/// its contents being code already.
fn mark_up(text: &str, out: &mut String) {
    // A schema that writes its own Markdown link keeps it: escaping those
    // brackets would render the link as its own source text.
    let links = text.contains("](");
    let mut in_span = false;

    for piece in text.split_inclusive(char::is_whitespace) {
        let word = piece.trim_end();
        let spacing = &piece[word.len()..];

        let ticks = word.matches('`').count();
        if in_span || ticks > 0 {
            if ticks % 2 == 1 {
                in_span = !in_span;
            }
            out.push_str(piece);
            continue;
        }

        let (leading, core, trailing) = split_word(word);
        out.push_str(leading);
        if is_url(core) {
            // A bare URL is a link only inside angle brackets.
            out.push('<');
            out.push_str(core);
            out.push('>');
        } else if reads_as_code(core) {
            out.push('`');
            out.push_str(core);
            out.push('`');
        } else if !links && core.contains(['[', ']']) {
            out.push_str(&core.replace('[', "\\[").replace(']', "\\]"));
        } else {
            out.push_str(core);
        }
        out.push_str(trailing);
        out.push_str(spacing);
    }
}

/// Whether a word is a bare URL.
fn is_url(word: &str) -> bool {
    word.starts_with("http://") || word.starts_with("https://")
}

/// Whether a word reads as code: a path, an underscored or parenthesized name,
/// or one with an inner capital.
// TODO: a word's shape is a guess at what it means. The generator will hold
// every class, property and token name in the libraries it emits, and that
// symbol table is the real answer — backtick a word it knows, link a class
// rather than backtick it, and leave prose such as `OpenUSD` alone.
fn reads_as_code(word: &str) -> bool {
    if word.len() < 2 {
        return false;
    }

    word.contains("::")
        || word.contains('_')
        || word.ends_with("()")
        || word
            .chars()
            .zip(word.chars().skip(1))
            .any(|(previous, c)| previous.is_lowercase() && c.is_uppercase())
}

/// Breaks `line` at spaces so no line runs past [`WIDTH`] columns, keeping its
/// indentation. A word longer than the width stands alone rather than being
/// split.
pub fn wrap(line: &str) -> String {
    if columns(line) <= WIDTH {
        return line.trim_end().to_owned();
    }

    let body = line.trim_start();
    let indent = &line[..line.len() - body.len()];
    let mut out = String::with_capacity(line.len() + 8);
    let mut column = 0;

    for word in body.split_whitespace() {
        if column > 0 && column + 1 + columns(word) > WIDTH {
            out.push('\n');
            column = 0;
        }
        if column == 0 {
            out.push_str(indent);
            column = columns(indent);
        } else {
            out.push(' ');
            column += 1;
        }
        out.push_str(word);
        column += columns(word);
    }
    out
}

/// How wide `text` renders, which is its characters and not its bytes.
fn columns(text: &str) -> usize {
    text.chars().count()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn em_italic() {
        assert_eq!(to_markdown("the \\em only one"), "the *only* one");
        assert_eq!(to_markdown("the \\e only one"), "the *only* one");
    }

    #[test]
    fn code_words_backticked() {
        assert_eq!(to_markdown("pass \\p radius here"), "pass `radius` here");
        assert_eq!(to_markdown("see \\c UsdGeomMesh."), "see `UsdGeomMesh`.");
    }

    /// A command renders once. What it writes is Markdown already, so the
    /// prose pass must not wrap it a second time.
    #[test]
    fn rendered_once() {
        assert_eq!(
            to_markdown("the default is \\em catmullClark."),
            "the default is *catmullClark*."
        );
        assert_eq!(to_markdown("see \\p faceVertexCounts."), "see `faceVertexCounts`.");
    }

    /// A reference reads as its quoted text, or as the symbol it names.
    #[test]
    fn ref_text() {
        assert_eq!(to_markdown("see \\ref Usd_Page \"the page\""), "see the page");
        assert_eq!(to_markdown("see \\ref UsdGeomMesh"), "see `UsdGeomMesh`");
        assert_eq!(
            to_markdown("See \\ref UsdGeomMesh_Subdivision."),
            "See `UsdGeomMesh_Subdivision`.",
            "the full stop ends the sentence, not the code span"
        );
    }

    /// Punctuation around a word stays outside the markup, whichever pass
    /// wrote it.
    #[test]
    fn punctuation_outside() {
        assert_eq!(
            to_markdown("values are \"catmullClark\", or drawMode."),
            "values are \"`catmullClark`\", or `drawMode`."
        );
        assert_eq!(
            to_markdown("See https://openusd.org. done"),
            "See <https://openusd.org>. done"
        );
    }

    /// A code block is fenced, and nothing inside it is rewritten or wrapped —
    /// a command in a sample is part of the sample.
    #[test]
    fn code_fenced() {
        let source = "before\n\\code\nlet x = some_name;\n\\endcode\nafter";
        let converted = to_markdown(source);

        assert!(converted.contains("```text\n"), "{converted}");
        assert!(
            converted.contains("let x = some_name;"),
            "the block is left alone: {converted}"
        );

        let sample = to_markdown("\\code\nprintf(\"a\\n\");\n// \\p foo\n\\endcode");
        assert!(sample.contains("printf(\"a\\n\");"), "the escape survives: {sample}");
        assert!(sample.contains("// \\p foo"), "the command survives: {sample}");
    }

    /// An `@` that opens no command is an asset path or an address, and stays
    /// the character it was written as — even when what follows it happens to
    /// spell a command.
    #[test]
    fn asset_paths_kept() {
        assert_eq!(to_markdown("see @Foo/bar.usd@ now"), "see @Foo/bar.usd@ now");
        assert_eq!(to_markdown("write to me@example.com"), "write to me@example.com");
        assert_eq!(
            to_markdown("Contact @notes.usda@ or @code.usda@ for more."),
            "Contact @notes.usda@ or @code.usda@ for more."
        );

        let example = "\\code\nprototypes = [@MaleGroupA/usd/MaleGroupA.usd@]\n\\endcode";
        let converted = to_markdown(example);
        assert!(
            converted.contains("[@MaleGroupA/usd/MaleGroupA.usd@]"),
            "the asset path lost its delimiters: {converted}"
        );
    }

    /// A command with nothing to act on keeps its own text.
    #[test]
    fn dangling_command() {
        assert_eq!(to_markdown("pass \\p"), "pass \\p");
        assert_eq!(to_markdown("see \\ref"), "see \\ref");
    }

    /// A word that reads as code is backticked; ordinary prose is not.
    #[test]
    fn camel_backticked() {
        assert_eq!(
            to_markdown("the faceVertexCounts array"),
            "the `faceVertexCounts` array"
        );
        assert_eq!(to_markdown("a snake_case name"), "a `snake_case` name");
        assert_eq!(to_markdown("call Compute() now"), "call `Compute()` now");
        assert_eq!(to_markdown("plain english prose"), "plain english prose");
    }

    /// Brackets would read as an intra-doc link and a bare URL as prose; a
    /// link the schema wrote itself is left alone.
    #[test]
    fn links_made_safe() {
        assert_eq!(to_markdown("see [1] below"), "see \\[1\\] below");
        assert_eq!(
            to_markdown("see https://openusd.org here"),
            "see <https://openusd.org> here"
        );
        assert_eq!(
            to_markdown("see [docs](https://openusd.org) now"),
            "see [docs](https://openusd.org) now"
        );
    }

    /// The labels keep their text; a list item becomes a Markdown bullet.
    #[test]
    fn labels_and_bullets() {
        assert_eq!(to_markdown("\\note this matters"), "Note: this matters");
        assert_eq!(to_markdown("\\deprecated use the other"), "Deprecated: use the other");
        assert_eq!(to_markdown("\\li one"), "- one");
        assert_eq!(to_markdown("\\sa the other"), "See also the other");
    }

    /// Prose wraps within the room a `///` line leaves, a long word is not
    /// split, and the measure is characters rather than bytes.
    #[test]
    fn wraps_at_width() {
        let long = "word ".repeat(30);
        for line in to_markdown(&long).lines() {
            assert!(columns(line) <= WIDTH, "{} columns: {line}", columns(line));
        }

        let single = "a".repeat(100);
        assert_eq!(
            to_markdown(&single),
            single,
            "a word longer than the width stands alone"
        );

        let accented = "é".repeat(70);
        assert_eq!(to_markdown(&accented), accented, "140 bytes, but only 70 columns");
    }
}
