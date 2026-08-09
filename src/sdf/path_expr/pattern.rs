//! One path pattern of a path expression (C++ `SdfPathPattern`).

use std::fmt;

use crate::sdf::Path;

use super::predicate::PredicateExpression;

/// A single pattern matching scene paths: a literal [`Path`] prefix followed
/// by match components — literal names, glob components (`*`, `?`, `[...]`),
/// `//` stretches (arbitrary levels of hierarchy), embedded `{predicate}`
/// expressions, and at most one trailing property element.
///
/// Leading literal identifiers (and `..` steps) fold into the prefix, so
/// `/foo/bar/baz` is all prefix with no components while `/foo//bar` keeps
/// prefix `/foo` and components `//`, `bar`. This canonical form is what the
/// pattern's text reproduces.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct PathPattern {
    prefix: Path,
    components: Vec<Component>,
    pred_exprs: Vec<PredicateExpression>,
    is_property: bool,
}

/// One match component past the prefix.
///
/// A component with empty text and no predicate is a stretch (`//`); one with
/// empty text and a predicate is a bare predicate (`{...}`), which matches
/// any name — including, during evaluation, the element the previous segment
/// already matched.
#[derive(Debug, Clone, PartialEq)]
pub struct Component {
    /// The name text, possibly with glob wildcards; empty for stretches and
    /// bare predicates.
    pub text: String,
    /// Index into the pattern's predicate expressions.
    pub predicate_index: Option<usize>,
    /// Whether `text` is a plain identifier with no wildcards.
    pub is_literal: bool,
}

impl Component {
    /// Whether this is a `//` stretch.
    pub fn is_stretch(&self) -> bool {
        self.text.is_empty() && self.predicate_index.is_none()
    }
}

impl PathPattern {
    /// The pattern matching every path: `//`.
    pub fn everything() -> Self {
        PathPattern {
            prefix: Path::abs_root(),
            components: vec![Component {
                text: String::new(),
                predicate_index: None,
                is_literal: false,
            }],
            pred_exprs: Vec::new(),
            is_property: false,
        }
    }

    /// The pattern matching every path descendant to an anchor: `.//`.
    pub fn every_descendant() -> Self {
        let mut pattern = Self::everything();
        pattern.prefix = reflexive_relative();
        pattern
    }

    /// The pattern matching nothing — the default, with an empty prefix.
    pub fn nothing() -> Self {
        Self::default()
    }

    /// Whether this is the nothing pattern.
    pub fn is_nothing(&self) -> bool {
        self.prefix.is_empty()
    }

    /// The literal path every match starts with.
    pub fn prefix(&self) -> &Path {
        &self.prefix
    }

    /// Replaces the prefix. When components exist the prefix must stay a
    /// prim-or-root path; with none, a property path also sets the property
    /// flag (mirroring what folding a literal property produces).
    pub fn set_prefix(&mut self, prefix: Path) {
        if self.components.is_empty() {
            self.is_property = prefix.is_property_path();
        }
        self.prefix = prefix;
    }

    /// The match components past the prefix.
    pub fn components(&self) -> &[Component] {
        &self.components
    }

    /// The predicate expressions the components index into.
    pub fn pred_exprs(&self) -> &[PredicateExpression] {
        &self.pred_exprs
    }

    /// Whether the pattern matches properties (it ends in a property
    /// element, literal or folded into the prefix).
    pub fn is_property(&self) -> bool {
        self.is_property
    }

    /// Whether the pattern opens with `//` directly under the absolute root,
    /// so a match may begin at any depth.
    pub fn has_leading_stretch(&self) -> bool {
        self.prefix.is_abs_root() && self.components.first().is_some_and(Component::is_stretch)
    }

    /// Whether the pattern ends with `//`, so a match extends to every
    /// descendant.
    pub fn has_trailing_stretch(&self) -> bool {
        !self.is_property && self.components.last().is_some_and(Component::is_stretch)
    }

    /// Whether a child element may still be appended: not after the property
    /// element, and never a stretch directly after a stretch.
    pub fn can_append_child(&self, text: &str) -> bool {
        if self.is_property {
            return false;
        }
        !(text.is_empty() && self.components.last().is_some_and(Component::is_stretch))
    }

    /// Appends one prim-level element. A leading literal identifier or `..`
    /// with no predicate folds into the prefix; everything else becomes a
    /// component. Empty text with no predicate appends a stretch.
    pub fn append_child(&mut self, text: impl Into<String>, predicate: Option<PredicateExpression>) {
        let text = text.into();
        if self.prefix.is_empty() {
            self.prefix = reflexive_relative();
        }
        let is_literal = Path::is_valid_identifier(&text);
        if (is_literal || text == "..") && predicate.is_none() && self.components.is_empty() {
            self.prefix = append_prefix_child(&self.prefix, &text);
            return;
        }
        let predicate_index = predicate.map(|expr| {
            self.pred_exprs.push(expr);
            self.pred_exprs.len() - 1
        });
        self.components.push(Component {
            text,
            predicate_index,
            is_literal,
        });
    }

    /// Appends a stretch when one may follow the current tail.
    pub fn append_stretch_if_possible(&mut self) {
        if self.can_append_child("") {
            self.append_child("", None);
        }
    }

    /// Appends the trailing property element. A pattern ending in a stretch
    /// first gains a `*` child, so `/x//` + `.foo` becomes `/x//*.foo`; a
    /// leading literal property with no components folds into the prefix.
    pub fn append_property(&mut self, text: impl Into<String>, predicate: Option<PredicateExpression>) {
        let text = text.into();
        if self.has_trailing_stretch() {
            self.append_child("*", None);
        }
        if self.prefix.is_empty() {
            self.prefix = reflexive_relative();
        }
        let is_literal = Path::is_valid_namespace_identifier(&text);
        if is_literal
            && predicate.is_none()
            && self.components.is_empty()
            && let Some(folded) = append_prefix_property(&self.prefix, &text)
        {
            self.prefix = folded;
            self.is_property = true;
            return;
        }
        let predicate_index = predicate.map(|expr| {
            self.pred_exprs.push(expr);
            self.pred_exprs.len() - 1
        });
        self.components.push(Component {
            text,
            predicate_index,
            is_literal,
        });
        self.is_property = true;
    }
}

impl fmt::Display for PathPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut result = String::new();
        if self.prefix == reflexive_relative() {
            // The reflexive `.` prints only when it stands alone or opens a
            // stretch (`.//`); a relative name run carries its own text.
            if self.components.is_empty() || self.components[0].is_stretch() {
                result.push('.');
            }
        } else {
            result.push_str(self.prefix.as_str());
        }

        let prefix_is_abs_root = self.prefix.is_abs_root();
        for (i, component) in self.components.iter().enumerate() {
            if component.is_stretch() {
                // Under a bare `/` prefix the leading stretch contributes one
                // slash, printing `//` rather than `///`.
                result.push_str(if i == 0 && prefix_is_abs_root { "/" } else { "//" });
                continue;
            }
            if i + 1 == self.components.len() && self.is_property {
                result.push('.');
            } else if !result.is_empty() && !result.ends_with('/') {
                result.push('/');
            }
            result.push_str(&component.text);
            if let Some(index) = component.predicate_index {
                result.push('{');
                result.push_str(&self.pred_exprs[index].to_string());
                result.push('}');
            }
        }
        f.write_str(&result)
    }
}

/// The reflexive relative path `.`, the anchor of a relative pattern.
fn reflexive_relative() -> Path {
    Path::new(".").expect("the reflexive relative path is valid")
}

/// Appends one literal child (or `..`) to a pattern prefix. The reflexive
/// `.` disappears under its first child, and `..` climbs a chain rather than
/// consuming an absolute parent textually.
fn append_prefix_child(prefix: &Path, name: &str) -> Path {
    let base = prefix.as_str();
    let combined = if base == "." {
        name.to_string()
    } else if base.ends_with('/') {
        format!("{base}{name}")
    } else {
        format!("{base}/{name}")
    };
    Path::new(&combined).expect("a pattern prefix concatenation is a valid path string")
}

/// Folds a literal property into the prefix, or `None` when the prefix
/// cannot carry one (already a property path, or a `..` chain, which the
/// grammar cannot spell a property onto).
fn append_prefix_property(prefix: &Path, name: &str) -> Option<Path> {
    let base = prefix.as_str();
    if base == "." {
        return Path::new(&format!(".{name}")).ok();
    }
    if base.ends_with("..") {
        return None;
    }
    prefix.append_property(name).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Builds a pattern through the same calls the parser makes.
    fn build(prefix: &str, children: &[&str]) -> PathPattern {
        let mut pattern = PathPattern::default();
        if !prefix.is_empty() {
            pattern.set_prefix(Path::new(prefix).unwrap());
        }
        for child in children {
            if child.is_empty() {
                pattern.append_stretch_if_possible();
            } else {
                pattern.append_child(*child, None);
            }
        }
        pattern
    }

    #[test]
    fn literal_run_folds() {
        let pattern = build("/", &["foo", "bar", "baz"]);
        assert_eq!(pattern.prefix().as_str(), "/foo/bar/baz");
        assert!(pattern.components().is_empty());
        assert_eq!(pattern.to_string(), "/foo/bar/baz");
    }

    #[test]
    fn glob_stops_folding() {
        let mut pattern = build("/", &["foo"]);
        pattern.append_child("b*r", None);
        pattern.append_child("baz", None);
        assert_eq!(pattern.prefix().as_str(), "/foo");
        assert_eq!(pattern.components().len(), 2);
        assert!(!pattern.components()[0].is_literal);
        assert!(pattern.components()[1].is_literal);
        assert_eq!(pattern.to_string(), "/foo/b*r/baz");
    }

    #[test]
    fn stretch_text() {
        assert_eq!(PathPattern::everything().to_string(), "//");
        assert_eq!(PathPattern::every_descendant().to_string(), ".//");

        let pattern = build("/", &["foo", "", "bar"]);
        assert_eq!(pattern.to_string(), "/foo//bar");
        assert!(!pattern.has_leading_stretch());
        assert!(!pattern.has_trailing_stretch());

        let trailing = build("/", &["foo", ""]);
        assert!(trailing.has_trailing_stretch());
        assert_eq!(trailing.to_string(), "/foo//");
    }

    #[test]
    fn no_double_stretch() {
        let mut pattern = build("/", &["foo", ""]);
        pattern.append_stretch_if_possible();
        assert_eq!(pattern.components().len(), 1, "stretch after stretch is refused");
    }

    #[test]
    fn property_after_stretch_gains_wildcard() {
        let mut pattern = build("/", &["x", ""]);
        pattern.append_property("foo", None);
        assert_eq!(pattern.to_string(), "/x//*.foo");
        assert!(pattern.is_property());
        assert!(!pattern.has_trailing_stretch());
    }

    #[test]
    fn literal_property_folds() {
        let mut pattern = build("/", &["foo"]);
        pattern.append_property("attr:ns", None);
        assert_eq!(pattern.prefix().as_str(), "/foo.attr:ns");
        assert!(pattern.components().is_empty());
        assert!(pattern.is_property());
        assert_eq!(pattern.to_string(), "/foo.attr:ns");
    }

    #[test]
    fn relative_forms() {
        let pattern = build("", &["foo", "bar"]);
        assert_eq!(pattern.prefix().as_str(), "foo/bar");
        assert_eq!(pattern.to_string(), "foo/bar");

        let mut dotted = PathPattern::default();
        dotted.append_child("..", None);
        dotted.append_child("..", None);
        dotted.append_child("sib", None);
        assert_eq!(dotted.prefix().as_str(), "../../sib");
        assert_eq!(dotted.to_string(), "../../sib");
    }

    #[test]
    fn nothing_is_default() {
        assert!(PathPattern::nothing().is_nothing());
        assert!(!PathPattern::everything().is_nothing());
        assert_eq!(PathPattern::nothing().to_string(), "");
    }
}
