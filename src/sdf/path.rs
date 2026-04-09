use std::{fmt, result, str::FromStr};

use anyhow::{bail, ensure, Result};

#[inline]
pub fn path(str: impl AsRef<str>) -> Result<Path> {
    let path = str.as_ref();
    Path::new(path)
}

/// `SdfPath` implementation.
///
/// # Syntax
/// - Two separators are used between parts of a path. A slash ("/")
///   following an identifier is used to introduce a namespace child.
/// - A period (".") following an identifier is used to introduce a property.
/// - A property may also have several non-sequential colons (':') in its name
///   to provide a rudimentary namespace within properties but may not end or
///   begin with a colon.
/// - Brackets ("[" and "]") are used to indicate relationship target paths for
///   relational attributes.
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Path {
    path: String,
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.path)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Path {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.path.serialize(serializer)
    }
}

impl FromStr for Path {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> result::Result<Path, Self::Err> {
        Ok(Path { path: s.to_string() })
    }
}

impl Path {
    pub fn new(path: &str) -> Result<Self> {
        Path::from_str(path)
    }

    #[inline]
    pub fn abs_root() -> Path {
        Path::from_str_unchecked("/")
    }

    fn from_str_unchecked(path: &str) -> Path {
        Path { path: path.to_string() }
    }

    #[inline]
    pub fn is_abs(&self) -> bool {
        self.path.starts_with('/')
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.path.is_empty()
    }

    pub fn append_property(&self, property: &str) -> Result<Path> {
        // TODO: Validate property name more carefully here.
        ensure!(!property.is_empty(), "Property name cannot be empty");
        ensure!(!self.is_property_path(), "Cannot append property to property path");
        ensure!(property != ".", "Property name cannot be '.'");

        let mut new_path = self.path.clone();
        new_path.push('.');
        new_path.push_str(property);

        Ok(Path { path: new_path })
    }

    pub fn append_path(&self, path: impl Into<Path>) -> Result<Path> {
        let append: Path = path.into();

        if self.is_abs() && append.is_abs() {
            bail!("Cannot append absolute path to absolute path");
        }

        ensure!(!self.is_property_path(), "Cannot append path to property path");

        if append.as_str() == "." {
            return Ok(self.clone());
        }

        // If base is slash only.
        // "/" + "foo/bar" => "/foo/bar"
        let combined = if self.path.as_str() == "/" {
            format!("/{}", append.path)
        } else {
            format!("{}/{}", self.path, append.path)
        };

        Ok(Path { path: combined })
    }

    pub fn is_property_path(&self) -> bool {
        let pos = match self.path.rfind('.') {
            Some(index) => index,
            // No dot, not a property path
            None => return false,
        };

        // Make sure path ends with a valid property name (e.g. "xyz.chars").
        let tail = &self.path[pos + 1..];
        tail.chars().all(char::is_alphanumeric)
    }

    pub fn prim_path(&self) -> Path {
        // Split at last slash.
        // "/A/B/C.foo[target].bar:baz" will become "/A/B" and "C.foo[target].bar:baz"
        let Some((before, after)) = self.path.rsplit_once('/') else {
            return self.clone();
        };

        // For cases like ../.foo[target].bar, just return ..
        if after.starts_with('.') {
            return Path::from_str_unchecked(before);
        }

        // "/A/B/C{set=sel}" => "/A/B/C"
        if after.ends_with('}') {
            if let Some(pos) = after.find('{') {
                let sz = before.len() + pos + 1;
                return Path::from_str_unchecked(&self.path[..sz]);
            }
        }

        let first_dot = match after.find('.') {
            Some(dot) => dot,
            // No dots found, so we have a prim path
            None => return self.clone(),
        };

        // Return everything up to the first dot
        let sz = before.len() + first_dot + 1;
        Path::from_str_unchecked(&self.path[..sz])
    }

    /// Returns the parent path, or `None` for the pseudo-root `/` and empty paths.
    ///
    /// ```text
    /// "/A/B/C" -> Some("/A/B")
    /// "/A"     -> Some("/")
    /// "/"      -> None
    /// ""       -> None
    /// ```
    pub fn parent(&self) -> Option<Path> {
        if self.path.is_empty() || self.path == "/" {
            return None;
        }
        match self.path.rsplit_once('/') {
            Some(("", _)) => Some(Path::abs_root()),
            Some((before, _)) => Some(Path::from_str_unchecked(before)),
            None => None,
        }
    }

    /// Returns the final component name, or `None` for the pseudo-root and empty paths.
    ///
    /// ```text
    /// "/A/B/C" -> Some("C")
    /// "/A"     -> Some("A")
    /// "/"      -> None
    /// ""       -> None
    /// ```
    pub fn name(&self) -> Option<&str> {
        if self.path.is_empty() || self.path == "/" {
            return None;
        }
        match self.path.rsplit_once('/') {
            Some((_, after)) => Some(after),
            None => Some(&self.path),
        }
    }

    /// Replaces a prefix path with a new prefix, used for namespace remapping
    /// during composition (e.g. references and inherits).
    ///
    /// Returns `None` if `self` does not start with `old_prefix`.
    ///
    /// ```text
    /// "/Ref/Child".replace_prefix("/Ref", "/MyPrim") -> Some("/MyPrim/Child")
    /// "/Ref".replace_prefix("/Ref", "/MyPrim")       -> Some("/MyPrim")
    /// "/Other".replace_prefix("/Ref", "/MyPrim")     -> None
    /// ```
    pub fn replace_prefix(&self, old_prefix: &Path, new_prefix: &Path) -> Option<Path> {
        let old = old_prefix.as_str();
        let me = self.as_str();

        if me == old {
            return Some(new_prefix.clone());
        }

        // Must start with old_prefix followed by '/'.
        let suffix = me.strip_prefix(old)?;
        if !suffix.starts_with('/') {
            return None;
        }

        let new = new_prefix.as_str();
        if new == "/" {
            Some(Path::from_str_unchecked(suffix))
        } else {
            Some(Path::from_str_unchecked(&format!("{new}{suffix}")))
        }
    }

    /// Appends a variant selection to a prim path, producing a path like
    /// `/MyPrim{variantSet=selection}`.
    pub fn append_variant_selection(&self, set: &str, selection: &str) -> Path {
        Path::from_str_unchecked(&format!("{}{{{set}={selection}}}", self.path))
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        &self.path
    }

    /// Validate identifier
    ///
    /// Rules are:
    /// - Must be 1 char len
    /// - Must start with a letter or underscore
    /// - Must contain only letters, underscores, and numbers.
    pub fn is_valid_identifier(name: &str) -> bool {
        if name.is_empty() {
            return false;
        }

        name.chars()
            .enumerate()
            .all(|(i, c)| c == '_' || if i == 0 { c.is_alphabetic() } else { c.is_alphanumeric() })
    }

    pub fn is_valid_namespace_identifier(name: &str) -> bool {
        name.split(&[':', '.']).all(Self::is_valid_identifier)
    }
}

impl From<&Path> for Path {
    fn from(p: &Path) -> Self {
        p.clone()
    }
}

impl From<&str> for Path {
    fn from(s: &str) -> Self {
        Path { path: s.to_string() }
    }
}

impl From<String> for Path {
    fn from(value: String) -> Self {
        Path { path: value }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_append_property() {
        let base = Path::new("/foo").unwrap();

        assert_eq!(base.append_property("prop").unwrap().as_str(), "/foo.prop");
        assert_eq!(
            base.append_property("prop:foo:bar").unwrap().as_str(),
            "/foo.prop:foo:bar"
        );

        let base = Path::new("/foo.prop").unwrap();
        assert!(base.append_property("prop2").is_err());
        assert!(base.append_property("prop2:foo:bar").is_err());
    }

    #[test]
    fn test_append_path() -> Result<()> {
        assert_eq!(Path::new("/prim")?.append_path(".")?.as_str(), "/prim");

        assert_eq!(Path::new("/")?.append_path("foo/bar.attr")?.as_str(), "/foo/bar.attr");
        assert_eq!(
            Path::new("/")?.append_path("foo/bar.attr:argle:bargle")?.as_str(),
            "/foo/bar.attr:argle:bargle"
        );

        assert_eq!(Path::new("/foo")?.append_path("bar.attr")?.as_str(), "/foo/bar.attr");
        assert_eq!(
            Path::new("/foo")?.append_path("bar.attr:argle:bargle")?.as_str(),
            "/foo/bar.attr:argle:bargle"
        );
        assert_eq!(
            Path::new("/foo")?.append_path("bar.rel[/target].attr")?.as_str(),
            "/foo/bar.rel[/target].attr"
        );

        assert_eq!(
            Path::new("/foo")?
                .append_path("bar.rel[/target].attr:argle:bargle")?
                .as_str(),
            "/foo/bar.rel[/target].attr:argle:bargle"
        );

        assert_eq!(
            Path::new("/foo")?.append_path("bar.attr[/target.attr]")?.as_str(),
            "/foo/bar.attr[/target.attr]"
        );

        assert_eq!(
            Path::new("/foo")?
                .append_path("bar.attr[/target.attr:argle:bargle]")?
                .as_str(),
            "/foo/bar.attr[/target.attr:argle:bargle]"
        );

        assert_eq!(
            Path::new("/foo")?.append_path("bar.attr.mapper[/target].arg")?.as_str(),
            "/foo/bar.attr.mapper[/target].arg"
        );

        Ok(())
    }

    #[test]
    fn test_append_invalid_path() -> Result<()> {
        assert!(Path::new("/prim")?.append_path("/abs").is_err());
        assert!(Path::new("/prim.attr")?.append_path("abs").is_err());

        Ok(())
    }

    #[test]
    fn test_prim_path() {
        #[rustfmt::skip]
        let cases = [
            ("/A/B/C", "/A/B/C"),

            ("/A/B{set=sel}C", "/A/B{set=sel}C"),
            ("/A/B/C{set=sel}", "/A/B/C"),

            ("/A/B/C.foo", "/A/B/C"),
            ("/A/B/C.foo:bar:baz", "/A/B/C"),

            ("/A/B/C.foo[target].bar", "/A/B/C"),
            ("/A/B/C.foo[target].bar:baz", "/A/B/C"),

            ("A/B/C.foo[target].bar", "A/B/C"),
            ("A/B/C.foo[target].bar:baz", "A/B/C"),

            ("../C.foo", "../C"),
            ("../C.foo:bar:baz", "../C"),

            ("../.foo[target].bar", ".."),
            ("../.foo[target].bar:baz", ".."),
        ];

        for (path, expected) in cases {
            assert_eq!(
                Path::new(path).unwrap().prim_path().as_str(),
                expected,
                "Unable to parse: {path}",
            );
        }
    }

    #[test]
    fn test_is_property() {
        #[rustfmt::skip]
        let cases = [
            ("/Foo/Bar.baz", true),
            ("Foo", false),
            ("Foo/Bar", false),
            ("Foo.bar", true),
            ("Foo/Bar.bar", true),
            (".bar", true),
            ("/Some/Kinda/Long/Path/Just/To/Make/Sure", false),
            ("Some/Kinda/Long/Path/Just/To/Make/Sure.property", true),
            ("../Some/Kinda/Long/Path/Just/To/Make/Sure", false),
            ("../../Some/Kinda/Long/Path/Just/To/Make/Sure.property", true),
            ("/Foo/Bar.baz[targ].boom", true),
            ("Foo.bar[targ].boom", true),
            (".bar[targ].boom", true),
            ("Foo.bar[targ.attr].boom", true),
            ("/A/B/C.rel3[/Blah].attr3", true),
            ("A/B.rel2[/A/B/C.rel3[/Blah].attr3].attr2", true),
            ("/A.rel1[/A/B.rel2[/A/B/C.rel3[/Blah].attr3].attr2].attr1", true),
        ];

        for (path, expected) in cases {
            assert_eq!(Path::new(path).unwrap().is_property_path(), expected);
        }
    }

    #[test]
    fn test_path_cmp() {
        // Less then
        assert!(Path::from_str("aaa").unwrap() < Path::from_str("aab").unwrap());
        assert!(Path::from_str("/").unwrap() < Path::from_str("/a").unwrap());

        // Greater then
        assert!(Path::from_str("aab").unwrap() > Path::from_str("aaa").unwrap());

        // Less equal
        assert!(Path::from_str("aaa").unwrap() <= Path::from_str("aab").unwrap());
        assert!(Path::from_str("aaa").unwrap() <= Path::from_str("aaa").unwrap());

        // Greater equal
        assert!(Path::from_str("aab").unwrap() >= Path::from_str("aaa").unwrap());
        assert!(Path::from_str("aaa").unwrap() >= Path::from_str("aaa").unwrap());
    }

    #[test]
    fn test_parent() {
        #[rustfmt::skip]
        let cases: &[(&str, Option<&str>)] = &[
            ("/A/B/C", Some("/A/B")),
            ("/A/B",   Some("/A")),
            ("/A",     Some("/")),
            ("/",      None),
            ("",       None),
        ];

        for &(path, expected) in cases {
            assert_eq!(
                Path::new(path).unwrap().parent().as_ref().map(|p| p.as_str()),
                expected,
                "parent of {path:?}",
            );
        }
    }

    #[test]
    fn test_name() {
        #[rustfmt::skip]
        let cases: &[(&str, Option<&str>)] = &[
            ("/A/B/C", Some("C")),
            ("/A/B",   Some("B")),
            ("/A",     Some("A")),
            ("/",      None),
            ("",       None),
            ("Foo",    Some("Foo")),
        ];

        for &(path, expected) in cases {
            assert_eq!(Path::new(path).unwrap().name(), expected, "name of {path:?}",);
        }
    }

    #[test]
    fn test_replace_prefix() {
        let p = |s| Path::new(s).unwrap();

        // Exact match.
        assert_eq!(
            p("/Ref").replace_prefix(&p("/Ref"), &p("/MyPrim")).unwrap().as_str(),
            "/MyPrim"
        );

        // Child remapping.
        assert_eq!(
            p("/Ref/Child")
                .replace_prefix(&p("/Ref"), &p("/MyPrim"))
                .unwrap()
                .as_str(),
            "/MyPrim/Child"
        );

        // Deeper nesting.
        assert_eq!(
            p("/Ref/A/B").replace_prefix(&p("/Ref"), &p("/X")).unwrap().as_str(),
            "/X/A/B"
        );

        // Remap to root.
        assert_eq!(
            p("/Ref/Child").replace_prefix(&p("/Ref"), &p("/")).unwrap().as_str(),
            "/Child"
        );

        // No match.
        assert!(p("/Other").replace_prefix(&p("/Ref"), &p("/MyPrim")).is_none());

        // Partial name overlap must not match (e.g. /RefExtra should not match /Ref).
        assert!(p("/RefExtra").replace_prefix(&p("/Ref"), &p("/X")).is_none());
    }

    #[test]
    fn test_append_variant_selection() {
        let p = Path::new("/MyPrim").unwrap();
        assert_eq!(
            p.append_variant_selection("model", "high").as_str(),
            "/MyPrim{model=high}"
        );

        let root = Path::new("/").unwrap();
        assert_eq!(root.append_variant_selection("s", "v").as_str(), "/{s=v}");
    }

    #[test]
    fn validate_identifier() {
        // Valid identifiers
        assert!(Path::is_valid_identifier("_"));
        assert!(Path::is_valid_identifier("x"));
        assert!(Path::is_valid_identifier("_1"));
        assert!(Path::is_valid_identifier("a1"));
        assert!(Path::is_valid_identifier("test"));
        assert!(Path::is_valid_identifier("_test"));
        assert!(Path::is_valid_identifier("test123"));
        assert!(Path::is_valid_identifier("Test"));
        assert!(Path::is_valid_identifier("teST"));
        assert!(Path::is_valid_identifier("TEST"));

        // Invalid ones
        assert!(!Path::is_valid_identifier(""));
        assert!(!Path::is_valid_identifier(" "));
        assert!(!Path::is_valid_identifier("?"));
        assert!(!Path::is_valid_identifier("1"));
        assert!(!Path::is_valid_identifier("x!"));
        assert!(!Path::is_valid_identifier("_abc?"));
        assert!(!Path::is_valid_identifier("_!"));
        assert!(!Path::is_valid_identifier("test "));
        assert!(!Path::is_valid_identifier(" test"));
        assert!(!Path::is_valid_identifier("te st"));
        assert!(!Path::is_valid_identifier("te.st"));
        assert!(!Path::is_valid_identifier("te:st"));
    }
}
