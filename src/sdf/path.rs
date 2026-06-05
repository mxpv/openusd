use std::{fmt, result, str::FromStr};

use anyhow::{bail, ensure, Result};

#[inline]
pub fn path(str: impl AsRef<str>) -> Result<Path> {
    let path = str.as_ref();
    Path::new(path)
}

/// A character that may appear in a prim name (an alphanumeric or `_`). Used to
/// detect where a prim child attaches directly to a variant selection.
fn is_prim_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
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

    /// Returns `true` if this is the absolute root path `/` (pseudo-root).
    #[inline]
    pub fn is_abs_root(&self) -> bool {
        self.path == "/"
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
        } else if self.is_prim_variant_selection_path() {
            // A prim child attaches directly to a variant selection with no
            // separator: "/A{v=s}" + "B" => "/A{v=s}B" (C++ SdfPath::AppendChild).
            format!("{}{}", self.path, append.path)
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

        // Make sure the dot is preceded by a prim name character (not a variant
        // selection closing brace or another dot) and followed by a valid
        // property name. Property names may contain alphanumerics, underscores,
        // and colons (for namespaced properties like `primvars:displayColor`).
        let tail = &self.path[pos + 1..];
        !tail.is_empty() && tail.chars().all(|c| c.is_alphanumeric() || c == '_' || c == ':')
    }

    /// Returns `true` if this path's final component is a variant selection,
    /// e.g. `/Prim{set=sel}` — as opposed to a prim, property, or the root.
    ///
    /// Mirrors C++ `SdfPath::IsPrimVariantSelectionPath`. A variant selection
    /// path identifies a variant spec, not a prim, so it is not a valid target
    /// for prim authoring.
    pub fn is_prim_variant_selection_path(&self) -> bool {
        self.path.ends_with('}')
    }

    /// Returns `true` if any component of this path is a variant selection,
    /// e.g. both `/Prim{set=sel}` and `/Prim{set=sel}/Child`.
    ///
    /// Mirrors C++ `SdfPath::ContainsPrimVariantSelection`. Unlike
    /// [`is_prim_variant_selection_path`](Self::is_prim_variant_selection_path),
    /// which only inspects the final component, this finds a selection embedded
    /// anywhere in the prim namespace.
    pub fn contains_prim_variant_selection(&self) -> bool {
        // A `{` outside the prim namespace (e.g. inside a relationship-target
        // bracket) is not a prim variant selection, so confirm it via the
        // structured components after the cheap reject.
        self.path.contains('{') && self.components().any(|c| matches!(c, PathComponent::Variant { .. }))
    }

    pub fn prim_path(&self) -> Path {
        // Split at last slash.
        // "/A/B/C.foo[target].bar:baz" will become "/A/B" and "C.foo[target].bar:baz"
        let Some((before, after)) = self.path.rsplit_once('/') else {
            // Relative single segment (no slash): strip a trailing property or
            // variant selection. `is_property_path` separates `Foo.bar` from a
            // relative `..`, which has no property tail and is its own prim.
            if self.is_property_path() {
                if let Some(dot) = self.path.find('.') {
                    return Path::from_str_unchecked(&self.path[..dot]);
                }
            }
            if self.path.ends_with('}') {
                if let Some(open) = self.path.rfind('{') {
                    return Path::from_str_unchecked(&self.path[..open]);
                }
            }
            return self.clone();
        };

        // For cases like ../.foo[target].bar, just return ..
        if after.starts_with('.') {
            return Path::from_str_unchecked(before);
        }

        // Strip the trailing variant selection, keeping any earlier variants on
        // the same component: "/A/B/C{set=sel}" => "/A/B/C" and a nested
        // "/A{x=y}B{p=q}" => "/A{x=y}B" (the last `{` opens the trailing variant).
        if after.ends_with('}') {
            if let Some(pos) = after.rfind('{') {
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

    /// Returns the property portion of this path — the trailing segment after
    /// the owning prim, beginning with `.` (e.g. `.radius` in `/Light.radius`,
    /// `.foo[/T].bar` for a target/namespaced property). Empty for a prim
    /// (non-property) path.
    pub fn property_suffix(&self) -> &str {
        &self.path[self.prim_path().as_str().len()..]
    }

    /// Splits a property path into its owning prim and the property name (the
    /// portion after the `.`), or `None` if this is not a property path. The
    /// inverse of [`append_property`](Self::append_property).
    ///
    /// The property name is returned verbatim and may carry namespaces (`:`)
    /// or further target/connection syntax (`[..]`, `.`); callers that require
    /// a plain property name should validate it.
    ///
    /// ```text
    /// "/World/Mesh.points"   -> Some(("/World/Mesh", "points"))
    /// "/Mat.inputs:diffuse"  -> Some(("/Mat", "inputs:diffuse"))
    /// "/World/Mesh"          -> None
    /// ```
    pub fn split_property(&self) -> Option<(Path, &str)> {
        if !self.is_property_path() {
            return None;
        }
        let prim = self.prim_path();
        let name = self.path[prim.as_str().len()..].strip_prefix('.')?;
        Some((prim, name))
    }

    /// Returns the final namespace element of this path and its kind, or `None`
    /// for the pseudo-root `/` and empty paths. The inverse of the
    /// `append_property` / `append_variant_selection` / child-`append_path`
    /// family: an element appended to [`parent`](Self::parent) reconstructs the
    /// path.
    ///
    /// ```text
    /// "/A/B"          -> Some(Prim("B"))
    /// "/A.points"     -> Some(Property("points"))
    /// "/A{set=sel}"   -> Some(Variant { set: "set", selection: "sel" })
    /// ```
    pub fn last_element(&self) -> Option<PathElement<'_>> {
        if self.path.is_empty() || self.path == "/" {
            return None;
        }
        // A property's element is the whole property name (everything after
        // the owning prim's `.`), matching `parent()`/`split_property()` so an
        // element appended to `parent()` reconstructs the path — including
        // names that themselves contain dots, e.g. `append_property("foo.bar")`.
        if let Some((_, name)) = self.split_property() {
            return Some(PathElement::Property(name));
        }
        // For a prim or variant path the last element is the last component;
        // reuse the single variant-grammar definition in `components`. A
        // non-empty remainder means the path has an unparsed tail (malformed,
        // or syntax this method doesn't model), so there is no clean final
        // element.
        let mut components = self.components();
        let last = components.by_ref().last();
        if !components.remainder().is_empty() {
            return None;
        }
        last.map(|c| match c {
            PathComponent::Prim(name) => PathElement::Prim(name),
            PathComponent::Variant { set, selection } => PathElement::Variant { set, selection },
        })
    }

    /// Returns the parent path, or `None` for the pseudo-root `/` and empty
    /// paths. Mirrors C++ `SdfPath::GetParentPath`: a property's parent is its
    /// owning prim, a variant selection's parent is the prim (or enclosing
    /// variant) it qualifies, and a prim's parent is its namespace parent.
    ///
    /// ```text
    /// "/A/B/C"      -> Some("/A/B")
    /// "/A"          -> Some("/")
    /// "/A.attr"     -> Some("/A")
    /// "/A{x=y}"     -> Some("/A")
    /// "/A{x=y}{p=q}"-> Some("/A{x=y}")
    /// "/"           -> None
    /// ""            -> None
    /// ```
    pub fn parent(&self) -> Option<Path> {
        if self.path.is_empty() || self.path == "/" {
            return None;
        }
        // Drop a trailing `{set=sel}` variant selection.
        if self.is_prim_variant_selection_path() {
            if let Some(open) = self.path.rfind('{') {
                return Some(Path::from_str_unchecked(&self.path[..open]));
            }
        }
        if self.is_property_path() {
            return Some(self.prim_path());
        }
        // Prim path: drop the final prim name. It is introduced either by a `/`
        // (a child of another prim) or directly by a `}` (a child of a variant
        // selection, `/A{v=s}B`), whichever is rightmost.
        match self.path.rfind(['/', '}']) {
            // Child of a variant selection: keep up to and including the `}`.
            Some(i) if self.path.as_bytes()[i] == b'}' => Some(Path::from_str_unchecked(&self.path[..i + 1])),
            Some(0) => Some(Path::abs_root()),
            // Child of another prim: drop the `/` and the name.
            Some(i) => Some(Path::from_str_unchecked(&self.path[..i])),
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
        // The final prim name begins after the rightmost `/` or `}` (a child of
        // a variant selection attaches directly, `/A{v=s}B`). A path that *ends*
        // in a variant selection (`/A{v=s}`) has no prim after the `}`, so its
        // final component is the prim-plus-selection segment after the last `/`.
        let start = self.path.rfind(['/', '}']).map_or(0, |i| i + 1);
        if start < self.path.len() {
            Some(&self.path[start..])
        } else {
            Some(self.path.rsplit_once('/').map_or(self.path.as_str(), |(_, name)| name))
        }
    }

    /// Iterates the prim-namespace components of this path — prim names and
    /// `{set=sel}` variant selections — in root → leaf order.
    ///
    /// The iterator is lenient and does no validation: it yields the raw
    /// slices between delimiters and stops at the first thing it cannot parse
    /// as a prim/variant component (a property suffix, a malformed variant, or
    /// a stray separator), leaving that tail in
    /// [`remainder`](PathComponents::remainder). It is the single definition of
    /// the prim-path grammar; validating consumers layer their checks on top.
    ///
    /// Unlike [`strip_all_variant_selections`](Self::strip_all_variant_selections),
    /// which is a blunt string strip that also removes variant segments
    /// embedded inside relationship-target brackets, this models only the
    /// structured prim namespace.
    ///
    /// ```text
    /// "/A{x=y}B" -> [Prim("A"), Variant{x, y}, Prim("B")]
    /// "/A.attr"  -> [Prim("A")]  (remainder ".attr")
    /// ```
    pub fn components(&self) -> PathComponents<'_> {
        PathComponents {
            rest: self.path.strip_prefix('/').unwrap_or(&self.path),
            expect_slash: false,
            emitted: false,
        }
    }

    /// Counts the prim-name components of this path, skipping variant
    /// selections (C++ `PcpNode_GetNonVariantPathElementCount`).
    ///
    /// This is the namespace depth used to compare composition-node strength:
    /// a `{set=sel}` segment is part of the same prim, so it does not deepen
    /// the count.
    ///
    /// ```text
    /// "/A{x=y}B" -> 2
    /// "/A/B"     -> 2
    /// "/"        -> 0
    /// ```
    pub fn prim_element_count(&self) -> usize {
        self.components()
            .filter(|c| matches!(c, PathComponent::Prim(_)))
            .count()
    }

    /// Counts every prim-namespace component of this path, including `{set=sel}`
    /// variant selections (C++ `SdfPath::GetPathElementCount`).
    ///
    /// Unlike [`prim_element_count`](Self::prim_element_count), which counts only
    /// prim names, a variant selection counts as its own element here, so
    /// `/A{x=y}B` is 3.
    pub fn element_count(&self) -> usize {
        self.components().count()
    }

    /// Returns this path with every `{set=sel}` variant segment removed.
    ///
    /// Equivalent to C++ `SdfPath::StripAllVariantSelections`. Both trailing
    /// and interior variant segments are stripped, so
    /// `/A{x=y}B{p=q}C` becomes `/A/B/C`.
    pub fn strip_all_variant_selections(&self) -> Path {
        if !self.path.contains('{') {
            return self.clone();
        }
        let mut out = String::with_capacity(self.path.len());
        let mut rest = self.path.as_str();
        while let Some(open) = rest.find('{') {
            out.push_str(&rest[..open]);
            match rest[open..].find('}') {
                Some(close) => {
                    rest = &rest[open + close + 1..];
                    // In canonical form a prim child attaches directly to the
                    // variant (`/A{v=s}B`); reintroduce the `/` separator when
                    // the stripped variant is followed by a prim name. A `{`
                    // (next variant), `.` (property), or end needs no separator.
                    if rest.starts_with(is_prim_name_char) {
                        out.push('/');
                    }
                }
                None => {
                    out.push_str(&rest[open..]);
                    rest = "";
                    break;
                }
            }
        }
        out.push_str(rest);
        Path::from_str_unchecked(&out)
    }

    /// Returns `true` if this path starts with `prefix` at a path boundary.
    ///
    /// A match requires either equality with `prefix` or that the suffix
    /// following `prefix` begins with a path separator (`/`), property
    /// separator (`.`), or variant segment opener (`{`). This avoids false positives like
    /// `/Foobar` starting with `/Foo`.
    ///
    /// ```text
    /// "/A/B".has_prefix("/A")       -> true
    /// "/A".has_prefix("/A")         -> true
    /// "/A{set=sel}".has_prefix("/A")-> true
    /// "/A.attr".has_prefix("/A")    -> true
    /// "/Ab".has_prefix("/A")        -> false
    /// "/X".has_prefix("/")          -> true
    /// ```
    pub fn has_prefix(&self, prefix: &Path) -> bool {
        let old = prefix.as_str();
        let me = self.as_str();
        if me == old {
            return true;
        }
        let Some(suffix) = me.strip_prefix(old) else {
            return false;
        };
        old == "/"
            || suffix.starts_with('/')
            || suffix.starts_with('.')
            || suffix.starts_with('{')
            // A prim child attaches directly after a variant selection
            // (`/A{v=s}B`), so a `}`-terminated prefix is a boundary too.
            || prefix.is_prim_variant_selection_path()
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

        // Must start with old_prefix followed by '/', '.', or '{'. Property
        // targets in connection/relationship list ops rely on prim-prefix
        // mappings crossing the property separator, e.g.
        // `/Asset.outputs:out` -> `/Instance.outputs:out`.
        let suffix = me.strip_prefix(old)?;
        // The absolute root "/" is a prefix of all absolute paths; after
        // stripping it the remainder won't start with '/' (e.g. "Foo/Bar"). A
        // prim child attaches directly after a variant selection (`/A{v=s}B`),
        // so a `}`-terminated prefix is a boundary too.
        if old != "/"
            && !suffix.starts_with('/')
            && !suffix.starts_with('.')
            && !suffix.starts_with('{')
            && !old_prefix.is_prim_variant_selection_path()
        {
            return None;
        }
        // Ensure a separator between new prefix and suffix for non-root.
        if old == "/" && !suffix.is_empty() {
            let new = new_prefix.as_str();
            if new == "/" {
                return Some(Path::from_str_unchecked(&format!("/{suffix}")));
            }
            return Some(Path::from_str_unchecked(&format!("{new}/{suffix}")));
        }

        let new = new_prefix.as_str();
        // Separate the child body from its old-namespace separator. A prim child
        // carries a leading `/` (child of a non-variant prim) or attaches
        // directly to a variant selection (a bare name, `/A{v=s}B`); a property
        // `.` or nested variant `{` attaches directly in any namespace.
        let (body, is_prim_child) = if let Some(rest) = suffix.strip_prefix('/') {
            (rest, true)
        } else if old_prefix.is_prim_variant_selection_path() && suffix.starts_with(is_prim_name_char) {
            (suffix, true)
        } else {
            (suffix, false)
        };
        // Re-attach with the separator the new namespace needs: a prim child gets
        // a `/`, unless the new prefix is the root (the `/` is already there) or a
        // variant selection (the child attaches directly, `/Prim{set=sel}child`).
        let separator = if is_prim_child && new != "/" && !new_prefix.is_prim_variant_selection_path() {
            "/"
        } else {
            ""
        };
        Some(Path::from_str_unchecked(&format!("{new}{separator}{body}")))
    }

    /// Appends a variant selection to a prim path, producing a path like
    /// `/MyPrim{variantSet=selection}`.
    pub fn append_variant_selection(&self, set: &str, selection: &str) -> Path {
        Path::from_str_unchecked(&format!("{}{{{set}={selection}}}", self.path))
    }

    /// Appends a raw variant segment (e.g. `{set=sel}`) directly to this path.
    ///
    /// Unlike [`append_path`], no `/` separator is inserted — variant segments
    /// attach directly to the prim path to produce canonical forms like
    /// `/Prim{set=sel}`.
    pub fn append_variant_segment(&self, segment: &str) -> Path {
        Path::from_str_unchecked(&format!("{}{segment}", self.path))
    }

    /// Resolve a relative path against this path as anchor.
    ///
    /// Absolute paths are returned as-is. Relative segments (`..`) walk up
    /// from the anchor's prim path.
    ///
    /// Equivalent to C++ `SdfPath::MakeAbsolutePath`.
    ///
    /// ```text
    /// "/A/B".make_absolute("../C")   -> "/A/C"
    /// "/A/B".make_absolute("C/D")    -> "/A/B/C/D"
    /// "/A".make_absolute("/X")       -> "/X"
    /// ```
    pub fn make_absolute(&self, target: &Path) -> Path {
        let s = target.as_str();
        if s.starts_with('/') {
            return target.clone();
        }

        // Walk up from the anchor prim for each leading `..`, using `parent` so
        // the variant-selection boundary is respected (`/A{v=s}B` → `/A{v=s}`),
        // unlike a plain `/` split.
        let mut anchor = self.prim_path();
        let mut rest = s;
        while let Some(tail) = rest.strip_prefix("..") {
            anchor = anchor.parent().unwrap_or_else(Path::abs_root);
            rest = tail.strip_prefix('/').unwrap_or(tail);
        }

        if rest.is_empty() {
            return anchor;
        }
        // A property/relational tail (`.attr`, `.outputs:surface`) attaches to
        // the prim directly via its own `.` — no separator. A prim child
        // attaches to a variant selection directly (`/A{v=s}child`) but is
        // otherwise separated by `/`; the root already carries its slash.
        let anchor = anchor.as_str();
        let sep = if rest.starts_with('.') || anchor == "/" || anchor.ends_with('}') {
            ""
        } else {
            "/"
        };
        Path::from_str_unchecked(&format!("{anchor}{sep}{rest}"))
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

/// A prim-namespace component of a [`Path`], yielded by [`Path::components`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathComponent<'a> {
    /// A prim name (registered under its parent's `primChildren`).
    Prim(&'a str),
    /// A `{set=sel}` variant selection on the current prim.
    Variant {
        /// The variant set name (between `{` and `=`).
        set: &'a str,
        /// The selected variant (between `=` and `}`); may be empty for a
        /// variant-set path like `/Prim{set=}`.
        selection: &'a str,
    },
}

/// The final namespace element of a [`Path`], returned by
/// [`Path::last_element`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathElement<'a> {
    /// A prim name.
    Prim(&'a str),
    /// A property name (the segment after the final `.`).
    Property(&'a str),
    /// A `{set=sel}` variant selection.
    Variant {
        /// The variant set name.
        set: &'a str,
        /// The selected variant.
        selection: &'a str,
    },
}

/// Iterator over the prim-namespace components of a [`Path`]. See
/// [`Path::components`].
pub struct PathComponents<'a> {
    /// Unparsed remainder of the path string.
    rest: &'a str,
    /// `true` once a prim name has been yielded, so the *next* prim child is
    /// introduced by a `/` separator. Reset to `false` after a variant
    /// selection, whose following prim child attaches directly (`/A{v=s}B`).
    expect_slash: bool,
    /// `true` once any component has been yielded. A variant selection must
    /// attach to a prim, so a leading `{` (e.g. `/{x=y}`) is malformed.
    emitted: bool,
}

impl<'a> PathComponents<'a> {
    /// The unparsed tail left after iteration: empty for a well-formed prim
    /// path, otherwise the property suffix or the malformed segment at which
    /// parsing stopped.
    pub fn remainder(&self) -> &'a str {
        self.rest
    }
}

impl<'a> Iterator for PathComponents<'a> {
    type Item = PathComponent<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.rest.is_empty() {
            return None;
        }

        // A variant selection attaches directly to the preceding prim or
        // variant, with no separator. Its following prim child also attaches
        // directly, so clear `expect_slash`. A leading variant (no prim to
        // attach to, e.g. `/{x=y}`) is malformed and left in the remainder.
        if let Some(after_open) = self.rest.strip_prefix('{') {
            if !self.emitted {
                return None;
            }
            let Some(close) = after_open.find('}') else {
                return None; // unterminated; left in `rest`
            };
            let Some((set, selection)) = after_open[..close].split_once('=') else {
                return None; // missing `=`; left in `rest`
            };
            self.rest = &after_open[close + 1..];
            self.expect_slash = false;
            return Some(PathComponent::Variant { set, selection });
        }

        // A prim child of another prim is introduced by a single `/`. A prim
        // child of a variant attaches directly (no separator, `expect_slash`
        // already cleared). Anything else (a property `.`, trailing or doubled
        // `/`, junk) ends the prim namespace.
        if self.expect_slash {
            match self.rest.strip_prefix('/') {
                Some(next) if !next.is_empty() && !next.starts_with('/') && !next.starts_with('.') => {
                    self.rest = next;
                }
                _ => return None,
            }
        }

        let end = self.rest.find(['/', '{', '.']).unwrap_or(self.rest.len());
        let name = &self.rest[..end];
        if name.is_empty() {
            return None;
        }
        self.rest = &self.rest[end..];
        self.expect_slash = true;
        self.emitted = true;
        Some(PathComponent::Prim(name))
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
    fn prim_element_count() {
        assert_eq!(Path::new("/A/B").unwrap().prim_element_count(), 2);
        assert_eq!(Path::new("/A{x=y}B").unwrap().prim_element_count(), 2);
        assert_eq!(Path::new("/A{x=y}").unwrap().prim_element_count(), 1);
        assert_eq!(Path::abs_root().prim_element_count(), 0);
    }

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

            // A variant set on a variant-direct child: strip only the trailing
            // variant, keeping the earlier one on the same component.
            ("/A{x=y}B{p=q}", "/A{x=y}B"),

            // A property authored on a variant-direct child or on the variant.
            ("/A{x=y}B.attr", "/A{x=y}B"),
            ("/A{x=y}.attr", "/A{x=y}"),

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

            // Relative single segment (no slash): strip the property/variant.
            ("Foo.bar", "Foo"),
            ("Foo{x=y}", "Foo"),
            ("Foo", "Foo"),
            (".bar", ""),
            ("..", ".."),
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
    fn test_strip_all_variant_selections() {
        let cases: &[(&str, &str)] = &[
            ("/A/B/C", "/A/B/C"),
            ("/A{set=sel}", "/A"),
            ("/A{set=sel}B", "/A/B"),
            ("/A{x=y}B{p=q}C", "/A/B/C"),
            ("/A/B{p=q}C.attr", "/A/B/C.attr"),
            ("/", "/"),
        ];
        for (input, expected) in cases {
            let p = Path::new(input).unwrap();
            assert_eq!(p.strip_all_variant_selections().as_str(), *expected, "input {input}");
        }
    }

    #[test]
    fn contains_prim_variant_selection() {
        // A selection anywhere in the prim namespace counts; a `{` that is not a
        // prim-namespace variant (a relationship-target bracket) does not.
        let cases: &[(&str, bool)] = &[
            ("/A/B", false),
            ("/A{set=sel}", true),
            ("/A{set=sel}/Child", true),
            ("/A{x=y}B{p=q}C", true),
            ("/A.rel[/B{x=y}]", false),
        ];
        for (input, expected) in cases {
            assert_eq!(
                Path::from_str_unchecked(input).contains_prim_variant_selection(),
                *expected,
                "input {input}"
            );
        }
    }

    #[test]
    fn test_last_element() {
        // Render the element as an owned string so it doesn't borrow the
        // temporary `Path`: `name`, `.name` for a property, `{set=sel}`.
        let last = |s: &str| -> Option<String> {
            Path::from_str_unchecked(s).last_element().map(|e| match e {
                PathElement::Prim(name) => name.to_owned(),
                PathElement::Property(name) => format!(".{name}"),
                PathElement::Variant { set, selection } => format!("{{{set}={selection}}}"),
            })
        };

        assert_eq!(last("/A/B").as_deref(), Some("B"));
        assert_eq!(last("/A").as_deref(), Some("A"));
        assert_eq!(last("/A.points").as_deref(), Some(".points"));
        assert_eq!(last("/A.inputs:diffuse").as_deref(), Some(".inputs:diffuse"));
        // The whole property name, even one containing dots (so parent() plus
        // this element reconstruct the path) — `append_property("foo.bar")`.
        assert_eq!(last("/A.foo.bar").as_deref(), Some(".foo.bar"));
        assert_eq!(last("/A{set=sel}").as_deref(), Some("{set=sel}"));
        assert_eq!(last("/A{x=y}{p=q}").as_deref(), Some("{p=q}"));
        assert_eq!(last("/"), None);
        assert_eq!(last(""), None);
        // An unparsed tail (malformed, or target syntax this method doesn't
        // model) has no clean final element — None, not the last parsed prim.
        assert_eq!(last("/A{bad"), None);
        assert_eq!(last("/A.rel[/Target]"), None);
        assert_eq!(last("/{x=y}"), None);
    }

    #[test]
    fn test_split_property() {
        let split = |s: &str| {
            Path::from_str_unchecked(s)
                .split_property()
                .map(|(p, n)| (p.path, n.to_owned()))
        };
        let owned = |p: &str, n: &str| Some((p.to_owned(), n.to_owned()));

        assert_eq!(split("/World/Mesh.points"), owned("/World/Mesh", "points"));
        assert_eq!(split("/Mat.inputs:diffuse"), owned("/Mat", "inputs:diffuse"));
        // Relative property (no slash) decomposes too — the inverse of
        // append_property.
        assert_eq!(split("Foo.bar"), owned("Foo", "bar"));
        // Not a property path.
        assert_eq!(split("/World/Mesh"), None);
        assert_eq!(split("/"), None);
    }

    #[test]
    fn test_property_suffix() {
        let suffix = |s: &str| Path::from_str_unchecked(s).property_suffix().to_owned();

        assert_eq!(suffix("/A.points"), ".points");
        assert_eq!(suffix("/A/B.inputs:diffuse"), ".inputs:diffuse");
        // Relative property (no slash).
        assert_eq!(suffix("Foo.bar"), ".bar");
        // A prim path has no property suffix.
        assert_eq!(suffix("/A"), "");
    }

    #[test]
    fn test_components() {
        // Render each component as an owned string so the result doesn't borrow
        // the temporary `Path`: a prim is its name, a variant is `{set=sel}`.
        let parse = |s: &str| -> (Vec<String>, String) {
            let p = Path::from_str_unchecked(s);
            let mut it = p.components();
            let items = it
                .by_ref()
                .map(|c| match c {
                    PathComponent::Prim(name) => name.to_owned(),
                    PathComponent::Variant { set, selection } => format!("{{{set}={selection}}}"),
                })
                .collect();
            (items, it.remainder().to_owned())
        };
        let case = |items: &[&str]| items.iter().map(|s| s.to_string()).collect::<Vec<_>>();

        // Prim names and variant selections, in order, fully consumed. A prim
        // child attaches directly to a variant selection (canonical form).
        assert_eq!(parse("/A/B/C"), (case(&["A", "B", "C"]), String::new()));
        assert_eq!(parse("/A{x=y}B"), (case(&["A", "{x=y}", "B"]), String::new()));
        assert_eq!(parse("/A{x=y}B/C"), (case(&["A", "{x=y}", "B", "C"]), String::new()));
        assert_eq!(
            parse("/A{x=y}{p=q}C"),
            (case(&["A", "{x=y}", "{p=q}", "C"]), String::new())
        );
        assert_eq!(parse("/A{x=y}{p=q}"), (case(&["A", "{x=y}", "{p=q}"]), String::new()));
        // An empty selection (variant-set path) is yielded verbatim.
        assert_eq!(parse("/A{x=}"), (case(&["A", "{x=}"]), String::new()));

        // A property suffix ends the prim namespace and stays in the remainder.
        assert_eq!(parse("/A.attr"), (case(&["A"]), ".attr".to_owned()));
        assert_eq!(parse("/A{x=y}B.attr"), (case(&["A", "{x=y}", "B"]), ".attr".to_owned()));
        // The non-canonical slash-after-variant form is not consumed past the
        // variant: the stray `/B` is left in the remainder.
        assert_eq!(parse("/A{x=y}/B"), (case(&["A", "{x=y}"]), "/B".to_owned()));

        // Malformed input stops parsing, leaving the bad tail in the remainder.
        assert_eq!(parse("/A{x=y"), (case(&["A"]), "{x=y".to_owned()));
        assert_eq!(parse("/A{x}"), (case(&["A"]), "{x}".to_owned()));
        assert_eq!(parse("/A/"), (case(&["A"]), "/".to_owned()));
        assert_eq!(parse("/A//B"), (case(&["A"]), "//B".to_owned()));

        // The root and empty paths have no components.
        assert_eq!(parse("/"), (Vec::<String>::new(), String::new()));
    }

    #[test]
    fn test_has_prefix() {
        let cases: &[(&str, &str, bool)] = &[
            ("/A/B/C", "/A", true),
            ("/A/B/C", "/A/B", true),
            ("/A/B/C", "/A/B/C", true),
            ("/A/B/C", "/A/B/D", false),
            ("/Foobar", "/Foo", false),
            ("/A{set=sel}", "/A", true),
            // A child attaches directly to a variant selection (canonical form).
            ("/A{set=sel}B", "/A{set=sel}", true),
            ("/A{set=sel}B", "/A", true),
            ("/A.attr", "/A", true),
            ("/A", "/", true),
            ("/", "/", true),
            ("/A/B", "/A/B/C", false),
        ];
        for (path, prefix, expected) in cases {
            let p = Path::new(path).unwrap();
            let pre = Path::new(prefix).unwrap();
            assert_eq!(p.has_prefix(&pre), *expected, "{path}.has_prefix({prefix})");
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
            ("/A/B/C",       Some("/A/B")),
            ("/A/B",         Some("/A")),
            ("/A",           Some("/")),
            ("/",            None),
            ("",             None),
            // A property's parent is its owning prim.
            ("/A.attr",      Some("/A")),
            ("/A/B.attr",    Some("/A/B")),
            ("/A.foo:bar",   Some("/A")),
            // A variant selection's parent is the prim (or enclosing variant).
            ("/A{x=y}",      Some("/A")),
            ("/A/B{x=y}",    Some("/A/B")),
            ("/A{x=y}{p=q}",  Some("/A{x=y}")),
            // A child attaches directly to a variant selection (canonical form).
            ("/A{x=y}B",     Some("/A{x=y}")),
            ("/A{x=y}B/C",   Some("/A{x=y}B")),
            ("/A{x=y}.attr", Some("/A{x=y}")),
            // Relative paths must not self-parent (would loop a parent walk).
            ("Foo.bar",      Some("Foo")),
            ("Foo",          None),
            ("..",           None),
        ];

        for &(path, expected) in cases {
            let parent = Path::new(path).unwrap().parent();
            let parent = parent.as_ref().map(|p| p.as_str());
            assert_eq!(parent, expected, "parent of {path:?}");
            // A parent must make progress — never return the path itself.
            assert_ne!(parent, Some(path), "self-parent on {path:?}");
        }
    }

    #[test]
    fn test_name() {
        #[rustfmt::skip]
        let cases: &[(&str, Option<&str>)] = &[
            ("/A/B/C", Some("C")),
            ("/A/B",   Some("B")),
            ("/A",     Some("A")),
            // A child attaches directly to a variant selection (canonical form).
            ("/A{x=y}B", Some("B")),
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

        // Property paths still live under the owning prim namespace for
        // composition maps; the `.` separator must count as a prefix boundary.
        assert_eq!(
            p("/Ref.outputs:out")
                .replace_prefix(&p("/Ref"), &p("/MyPrim"))
                .unwrap()
                .as_str(),
            "/MyPrim.outputs:out"
        );

        // No match.
        assert!(p("/Other").replace_prefix(&p("/Ref"), &p("/MyPrim")).is_none());

        // Partial name overlap must not match (e.g. /RefExtra should not match /Ref).
        assert!(p("/RefExtra").replace_prefix(&p("/Ref"), &p("/X")).is_none());

        // A variant-direct child (`/A{v=s}B`) remapped off the variant regains a
        // `/` separator; remapped onto another variant it still attaches directly.
        assert_eq!(
            p("/A{v=s}B").replace_prefix(&p("/A{v=s}"), &p("/A")).unwrap().as_str(),
            "/A/B"
        );
        assert_eq!(
            p("/A{v=s}B")
                .replace_prefix(&p("/A{v=s}"), &p("/X{w=t}"))
                .unwrap()
                .as_str(),
            "/X{w=t}B"
        );
        // A deeper child under the variant-direct prim keeps its own `/`.
        assert_eq!(
            p("/A{v=s}B/C")
                .replace_prefix(&p("/A{v=s}"), &p("/A"))
                .unwrap()
                .as_str(),
            "/A/B/C"
        );
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

    #[test]
    fn make_absolute() {
        let abs = |anchor, target| Path::from_str_unchecked(anchor).make_absolute(&Path::from_str_unchecked(target));

        assert_eq!(abs("/A/B", "/X/Y").as_str(), "/X/Y");
        assert_eq!(abs("/A/B", "../C").as_str(), "/A/C");
        assert_eq!(abs("/A/B/C", "../../D").as_str(), "/A/D");
        assert_eq!(abs("/A", "../X").as_str(), "/X");
        assert_eq!(abs("/A/B", "..").as_str(), "/A");
        assert_eq!(abs("/A/B", "C/D").as_str(), "/A/B/C/D");

        // The `..` walk respects the variant-selection boundary: the parent of
        // `/A{v=s}B` is `/A{v=s}`, and a child reattaches directly after `}`.
        assert_eq!(abs("/A{v=s}B", "../C").as_str(), "/A{v=s}C");
        assert_eq!(abs("/A{v=s}B", "C").as_str(), "/A{v=s}B/C");
        assert_eq!(abs("/A{v=s}B", "..").as_str(), "/A{v=s}");

        // A property-relative tail attaches to the prim via `.`, not `/`.
        assert_eq!(abs("/Shader", ".outputs:surface").as_str(), "/Shader.outputs:surface");
        assert_eq!(abs("/A/B", "../.attr").as_str(), "/A.attr");
    }

    #[test]
    fn append_variant_segment() {
        let p = |s| Path::from_str_unchecked(s);

        // Variant set and selection attach directly without a slash separator.
        assert_eq!(p("/A").append_variant_segment("{v=sel}").as_str(), "/A{v=sel}");
        assert_eq!(
            p("/A/B").append_variant_segment("{color=red}").as_str(),
            "/A/B{color=red}"
        );
        // Empty selection (variant set path).
        assert_eq!(p("/A").append_variant_segment("{v=}").as_str(), "/A{v=}");
        // Nested variant segments stack.
        assert_eq!(p("/A{v=x}").append_variant_segment("{w=y}").as_str(), "/A{v=x}{w=y}");
    }
}
