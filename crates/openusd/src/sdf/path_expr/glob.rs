//! Anchored glob matching for a single path-component name (C++
//! `Sdf_GlobPattern`).

/// A compiled glob pattern matched against a whole component name.
///
/// `*` matches any run of code points (including none), `?` matches exactly
/// one, and `[...]` matches one code point against a class — literal
/// characters, `-` ranges, and a leading `!` negating the class. A backslash
/// escapes the following character. Matching is anchored at both ends, so the
/// pattern must cover the entire name.
#[derive(Debug, Clone, PartialEq)]
pub struct GlobPattern {
    ops: Vec<GlobOp>,
}

/// One compiled pattern element.
#[derive(Debug, Clone, PartialEq)]
enum GlobOp {
    Literal(char),
    /// `?`
    AnyOne,
    /// `*`
    AnyRun,
    /// `[...]`, holding each admitted code-point range (a lone character is
    /// the degenerate range onto itself).
    Class {
        negated: bool,
        ranges: Vec<(char, char)>,
    },
}

impl GlobPattern {
    /// Compiles `pattern`. Malformed input never fails: an unterminated class
    /// or a trailing backslash compiles as the literal characters, so a
    /// pattern always matches *something* predictable.
    pub fn new(pattern: &str) -> Self {
        let mut ops = Vec::new();
        let mut chars = pattern.chars().peekable();
        while let Some(c) = chars.next() {
            match c {
                '?' => ops.push(GlobOp::AnyOne),
                // Adjacent stars collapse: a run of them admits the same names.
                '*' => {
                    if ops.last() != Some(&GlobOp::AnyRun) {
                        ops.push(GlobOp::AnyRun);
                    }
                }
                '\\' => ops.push(GlobOp::Literal(chars.next().unwrap_or('\\'))),
                '[' => match compile_class(&mut chars) {
                    Some(class) => ops.push(class),
                    None => ops.push(GlobOp::Literal('[')),
                },
                other => ops.push(GlobOp::Literal(other)),
            }
        }
        GlobPattern { ops }
    }

    /// Whether `name` matches the whole pattern.
    pub fn matches(&self, name: &str) -> bool {
        let chars: Vec<char> = name.chars().collect();
        // The classic backtracking walk: remember the position of the most
        // recent `*` and, on a mismatch, retry from it with one more consumed
        // character.
        let mut op = 0;
        let mut chr = 0;
        let mut retry: Option<(usize, usize)> = None;
        while chr < chars.len() {
            match self.ops.get(op) {
                Some(GlobOp::AnyRun) => {
                    retry = Some((op + 1, chr));
                    op += 1;
                }
                Some(single) if matches_one(single, chars[chr]) => {
                    op += 1;
                    chr += 1;
                }
                _ => match retry {
                    Some((retry_op, retry_chr)) => {
                        retry = Some((retry_op, retry_chr + 1));
                        op = retry_op;
                        chr = retry_chr + 1;
                    }
                    None => return false,
                },
            }
        }
        // Only trailing stars may remain unconsumed.
        self.ops[op..].iter().all(|o| *o == GlobOp::AnyRun)
    }
}

/// Whether `op` admits the single code point `c`.
fn matches_one(op: &GlobOp, c: char) -> bool {
    match op {
        GlobOp::Literal(l) => *l == c,
        GlobOp::AnyOne => true,
        GlobOp::AnyRun => false,
        GlobOp::Class { negated, ranges } => {
            let inside = ranges.iter().any(|(lo, hi)| (*lo..=*hi).contains(&c));
            inside != *negated
        }
    }
}

/// Compiles a `[...]` class, with `chars` positioned after the opening
/// bracket. `None` when the class never closes; the caller falls back to a
/// literal `[`.
fn compile_class(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Option<GlobOp> {
    // Peek ahead for the closing bracket first, so an unterminated class does
    // not consume the rest of the pattern.
    if !chars.clone().any(|c| c == ']') {
        return None;
    }

    let negated = chars.peek() == Some(&'!');
    if negated {
        chars.next();
    }

    let mut ranges = Vec::new();
    while let Some(c) = chars.next() {
        if c == ']' {
            break;
        }
        // `a-z` forms a range when a right-hand character follows the dash; a
        // trailing dash is the literal `-`.
        if chars.peek() == Some(&'-') {
            let mut lookahead = chars.clone();
            lookahead.next();
            match lookahead.peek() {
                Some(&hi) if hi != ']' => {
                    chars.next();
                    chars.next();
                    ranges.push((c, hi));
                    continue;
                }
                _ => {}
            }
        }
        ranges.push((c, c));
    }
    Some(GlobOp::Class { negated, ranges })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matches(pattern: &str, name: &str) -> bool {
        GlobPattern::new(pattern).matches(name)
    }

    #[test]
    fn literal_and_anchor() {
        assert!(matches("foo", "foo"));
        assert!(!matches("foo", "foobar"));
        assert!(!matches("foo", "afoo"));
        assert!(!matches("foo", "fo"));
        assert!(matches("", ""));
        assert!(!matches("", "a"));
    }

    #[test]
    fn star_runs() {
        assert!(matches("*", ""));
        assert!(matches("*", "anything"));
        assert!(matches("foo*", "foo"));
        assert!(matches("foo*", "foobar"));
        assert!(matches("*bar", "foobar"));
        assert!(matches("f*o*r", "foobar"));
        assert!(!matches("f*z", "foobar"));
        assert!(matches("**", "x"));
        // Backtracking: the first `*` must give characters back.
        assert!(matches("*ab", "aab"));
        assert!(matches("*a*b", "xaxbxb"));
    }

    #[test]
    fn question_marks() {
        assert!(matches("?", "a"));
        assert!(!matches("?", ""));
        assert!(!matches("?", "ab"));
        assert!(matches("f?o", "foo"));
        assert!(matches("??*", "ab"));
        assert!(!matches("??*", "a"));
    }

    #[test]
    fn classes() {
        assert!(matches("[abc]", "b"));
        assert!(!matches("[abc]", "d"));
        assert!(matches("[a-z]x", "mx"));
        assert!(!matches("[a-z]", "M"));
        assert!(matches("[!a-z]", "M"));
        assert!(!matches("[!a-z]", "m"));
        assert!(matches("[a-zA-Z_]", "_"));
        // A trailing dash is a literal.
        assert!(matches("[a-]", "-"));
        assert!(matches("[a-]", "a"));
    }

    #[test]
    fn escapes_and_malformed() {
        assert!(matches("a\\*b", "a*b"));
        assert!(!matches("a\\*b", "axb"));
        // Unterminated class compiles as literal characters.
        assert!(matches("[ab", "[ab"));
        // Trailing backslash is a literal backslash.
        assert!(matches("a\\", "a\\"));
    }

    #[test]
    fn unicode_points() {
        assert!(matches("?", "é"));
        assert!(matches("gr?ße", "größe"));
        assert!(matches("*ße", "größe"));
    }
}
