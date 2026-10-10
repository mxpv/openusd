//! Kinds (C++ `Kind`): the classification a prim's `kind` metadata selects, and
//! the hierarchy that says which kinds are models, groups and components.
//!
//! [`Registry`] is the table of known kinds (C++ `KindRegistry`). It always
//! holds the built-in kinds named in [`tokens`], and a [`RegistryBuilder`] adds
//! the kinds a site declares, each a [`Decl`] naming its base kind.

use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;

use bitflags::bitflags;

use crate::tf;

/// The known kinds and the base kind each derives from (C++ `KindRegistry`).
///
/// Immutable once built. [`Registry::default`] holds the built-in hierarchy:
/// `assembly` is a `group`, `group` and `component` are `model`s, and
/// `subcomponent` stands alone.
#[derive(Debug, Clone)]
pub struct Registry {
    kinds: HashMap<String, Kind>,
}

impl Registry {
    /// Starts a registry of the built-in kinds plus whatever is declared on
    /// the builder.
    pub fn builder() -> RegistryBuilder {
        RegistryBuilder::default()
    }

    /// Whether `kind` is registered (C++ `KindRegistry::HasKind`).
    pub fn has_kind(&self, kind: &str) -> bool {
        self.kinds.contains_key(kind)
    }

    /// The kind `kind` derives from (C++ `KindRegistry::GetBaseKind`). `None`
    /// for a root kind, and for a kind that is not registered.
    pub fn base_kind(&self, kind: &str) -> Option<&str> {
        self.kinds.get(kind)?.base.as_deref()
    }

    /// Whether `derived` is `base` or derives from it (C++
    /// `KindRegistry::IsA`).
    ///
    /// Equal names answer `true` whether or not the kind is registered. A
    /// `derived` that is not registered is otherwise not a `base`.
    pub fn is_a(&self, derived: &str, base: &str) -> bool {
        let mut current = derived;
        loop {
            if current == base {
                return true;
            }
            match self.base_kind(current) {
                Some(next) => current = next,
                None => return false,
            }
        }
    }

    /// Every registered kind, sorted by name (C++ `KindRegistry::GetAllKinds`).
    pub fn all_kinds(&self) -> Vec<&str> {
        let mut kinds: Vec<&str> = self.kinds.keys().map(String::as_str).collect();
        kinds.sort_unstable();
        kinds
    }

    /// Whether `kind` is `model` or derives from it (C++
    /// `KindRegistry::IsModel`).
    pub fn is_model(&self, kind: &str) -> bool {
        self.lineage(kind).contains(Lineage::MODEL)
    }

    /// Whether `kind` is `group` or derives from it (C++
    /// `KindRegistry::IsGroup`).
    pub fn is_group(&self, kind: &str) -> bool {
        self.lineage(kind).contains(Lineage::GROUP)
    }

    /// Whether `kind` is `assembly` or derives from it (C++
    /// `KindRegistry::IsAssembly`).
    pub fn is_assembly(&self, kind: &str) -> bool {
        self.lineage(kind).contains(Lineage::ASSEMBLY)
    }

    /// Whether `kind` is `component` or derives from it (C++
    /// `KindRegistry::IsComponent`).
    pub fn is_component(&self, kind: &str) -> bool {
        self.lineage(kind).contains(Lineage::COMPONENT)
    }

    /// Whether `kind` is `subcomponent` or derives from it (C++
    /// `KindRegistry::IsSubComponent`).
    pub fn is_subcomponent(&self, kind: &str) -> bool {
        self.lineage(kind).contains(Lineage::SUBCOMPONENT)
    }

    /// The built-in kinds `kind` is or derives from; none for a kind that is
    /// not registered.
    fn lineage(&self, kind: &str) -> Lineage {
        self.kinds.get(kind).map_or(Lineage::empty(), |kind| kind.lineage)
    }
}

impl Default for Registry {
    fn default() -> Self {
        Registry {
            kinds: resolve(&built_in()),
        }
    }
}

/// Collects kind declarations and checks them into a [`Registry`].
///
/// Declarations are checked together by [`build`](Self::build), so a kind may
/// name a base declared after it, or by another source.
#[derive(Debug, Clone, Default)]
pub struct RegistryBuilder {
    declared: Vec<(String, Declared)>,
}

impl RegistryBuilder {
    /// Declares one kind.
    #[must_use]
    pub fn kind(mut self, decl: Decl<'_>) -> Self {
        self.declared.push(decl.declared(Origin::Direct));
        self
    }

    /// Declares the kinds of one named source, such as a schema family. The
    /// name is what a [`RegistryError`] reports the declarations by.
    #[must_use]
    pub fn kinds(mut self, source: &str, decls: &[Decl<'_>]) -> Self {
        if decls.is_empty() {
            return self;
        }
        let origin = Origin::Source(source.to_owned());
        self.declared
            .extend(decls.iter().map(|decl| decl.declared(origin.clone())));
        self
    }

    /// Checks every declaration and builds the registry.
    ///
    /// C++ `KindRegistry` reports a bad name or a repeated kind and carries
    /// on, and accepts a base kind that is never declared and a base-kind
    /// cycle. All four are errors here.
    pub fn build(self) -> Result<Registry, RegistryError> {
        let mut kinds = built_in();
        for (name, declared) in self.declared {
            if !tf::is_valid_identifier(&name) {
                return Err(RegistryError::InvalidName {
                    kind: name,
                    origin: declared.origin,
                });
            }
            match kinds.entry(name) {
                Entry::Occupied(first) => {
                    return Err(RegistryError::Duplicate {
                        kind: first.key().clone(),
                        first: first.get().origin.clone(),
                        second: declared.origin,
                    });
                }
                Entry::Vacant(slot) => {
                    slot.insert(declared);
                }
            }
        }

        // Sorted, so the kind an error names does not depend on hash order.
        let mut names: Vec<&String> = kinds.keys().collect();
        names.sort_unstable();
        for name in names {
            // A chain of registered bases either ends at a root kind or runs
            // longer than there are kinds, which is a cycle.
            let mut current = name;
            let mut length = 0;
            while let Some(base) = &kinds[current].base {
                if !kinds.contains_key(base) {
                    return Err(RegistryError::UnknownBase {
                        kind: current.clone(),
                        base: base.clone(),
                        origin: kinds[current].origin.clone(),
                    });
                }
                length += 1;
                if length > kinds.len() {
                    return Err(RegistryError::Cycle {
                        kind: name.clone(),
                        origin: kinds[name].origin.clone(),
                    });
                }
                current = base;
            }
        }

        Ok(Registry { kinds: resolve(&kinds) })
    }
}

/// One kind's declaration: its name and the kind it derives from, as a
/// plugin's `plugInfo.json` declares it in its `Kinds` block.
///
/// ```
/// use openusd::kind;
///
/// const CHARACTER_GROUP: kind::Decl<'_> = kind::Decl::new("chargroup").base("assembly");
/// const SITE_ROOT: kind::Decl<'_> = kind::Decl::new("site_root");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Decl<'a> {
    name: &'a str,
    base: Option<&'a str>,
}

impl<'a> Decl<'a> {
    /// Declares the root kind `name`, which derives from nothing.
    pub const fn new(name: &'a str) -> Self {
        Decl { name, base: None }
    }

    /// Declares `base` as the kind this one derives from. An empty `base` is
    /// no base, as C++ `KindRegistry` stores a root kind.
    #[must_use]
    pub const fn base(mut self, base: &'a str) -> Self {
        self.base = if base.is_empty() { None } else { Some(base) };
        self
    }

    /// The kind's name.
    pub const fn name(&self) -> &'a str {
        self.name
    }

    /// The kind this one is declared to derive from, if any.
    pub const fn declared_base(&self) -> Option<&'a str> {
        self.base
    }

    /// The declaration as the builder holds it, made by `origin`.
    fn declared(&self, origin: Origin) -> (String, Declared) {
        let declared = Declared {
            base: self.base.map(str::to_owned),
            origin,
        };
        (self.name.to_owned(), declared)
    }
}

/// Where a kind's declaration came from, as a [`RegistryError`] names it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Origin {
    /// The built-in hierarchy.
    BuiltIn,
    /// A named source of declarations (see [`RegistryBuilder::kinds`]).
    Source(String),
    /// A single declaration (see [`RegistryBuilder::kind`]).
    Direct,
}

impl fmt::Display for Origin {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Origin::BuiltIn => f.write_str("the built-in hierarchy"),
            Origin::Source(name) => write!(f, "`{name}`"),
            Origin::Direct => f.write_str("a direct declaration"),
        }
    }
}

/// A set of kind declarations that does not form a hierarchy.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum RegistryError {
    /// A kind's name is not an identifier (see [`tf::is_valid_identifier`]).
    #[error("kind `{kind}`, declared by {origin}, is not a valid identifier")]
    InvalidName {
        /// The name as declared.
        kind: String,
        /// Who declared it.
        origin: Origin,
    },

    /// A kind is declared more than once. A built-in kind counts as declared.
    #[error("kind `{kind}` is declared by {first} and again by {second}")]
    Duplicate {
        /// The repeated kind.
        kind: String,
        /// Who declared it first.
        first: Origin,
        /// Who declared it again.
        second: Origin,
    },

    /// A kind derives from a kind nothing declares.
    #[error("kind `{kind}`, declared by {origin}, derives from the undeclared kind `{base}`")]
    UnknownBase {
        /// The deriving kind.
        kind: String,
        /// The base kind it names.
        base: String,
        /// Who declared the deriving kind.
        origin: Origin,
    },

    /// A kind derives from itself through its base kinds.
    #[error("kind `{kind}`, declared by {origin}, derives from itself")]
    Cycle {
        /// A kind on the cycle, or deriving from one on it.
        kind: String,
        /// Who declared it.
        origin: Origin,
    },
}

/// The built-in kinds (C++ `KindTokens`).
pub mod tokens {
    /// `"model"`: the base of every kind a model hierarchy is made of.
    pub const MODEL: &str = "model";
    /// `"group"`: a model that may hold other models.
    pub const GROUP: &str = "group";
    /// `"assembly"`: a group that is a published asset.
    pub const ASSEMBLY: &str = "assembly";
    /// `"component"`: a leaf model, which holds no other model.
    pub const COMPONENT: &str = "component";
    /// `"subcomponent"`: an identified part inside a component.
    pub const SUBCOMPONENT: &str = "subcomponent";
}

/// A registered kind.
#[derive(Debug, Clone)]
struct Kind {
    base: Option<String>,
    lineage: Lineage,
}

bitflags! {
    /// The built-in kinds a kind is or derives from, so a hierarchy question
    /// about one is a lookup.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct Lineage: u8 {
        const MODEL = 1 << 0;
        const GROUP = 1 << 1;
        const ASSEMBLY = 1 << 2;
        const COMPONENT = 1 << 3;
        const SUBCOMPONENT = 1 << 4;
    }
}

impl Lineage {
    /// The flag of the built-in kind called `kind`, or none.
    fn of(kind: &str) -> Lineage {
        match kind {
            tokens::MODEL => Lineage::MODEL,
            tokens::GROUP => Lineage::GROUP,
            tokens::ASSEMBLY => Lineage::ASSEMBLY,
            tokens::COMPONENT => Lineage::COMPONENT,
            tokens::SUBCOMPONENT => Lineage::SUBCOMPONENT,
            _ => Lineage::empty(),
        }
    }
}

/// A kind as declared, before its base is checked.
#[derive(Debug, Clone)]
struct Declared {
    base: Option<String>,
    origin: Origin,
}

/// The built-in hierarchy, as C++ `KindRegistry::_RegisterDefaults` seeds it.
fn built_in() -> HashMap<String, Declared> {
    [
        (tokens::SUBCOMPONENT, None),
        (tokens::MODEL, None),
        (tokens::COMPONENT, Some(tokens::MODEL)),
        (tokens::GROUP, Some(tokens::MODEL)),
        (tokens::ASSEMBLY, Some(tokens::GROUP)),
    ]
    .into_iter()
    .map(|(kind, base)| {
        let declared = Declared {
            base: base.map(str::to_owned),
            origin: Origin::BuiltIn,
        };
        (kind.to_owned(), declared)
    })
    .collect()
}

/// Each kind of `declared` with the built-in kinds on its chain of bases.
/// Every base must be registered and no chain may cycle.
fn resolve(declared: &HashMap<String, Declared>) -> HashMap<String, Kind> {
    declared
        .iter()
        .map(|(name, kind)| {
            let mut lineage = Lineage::empty();
            let mut current = Some(name);
            while let Some(kind) = current {
                lineage |= Lineage::of(kind);
                current = declared[kind].base.as_ref();
            }
            let resolved = Kind {
                base: kind.base.clone(),
                lineage,
            };
            (name.clone(), resolved)
        })
        .collect()
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    /// The kinds a site might declare, one under each built-in kind and one
    /// under none, for tests of what reads a registry.
    pub(crate) const SITE: &[Decl<'static>] = &[
        Decl::new("chargroup").base("assembly"),
        Decl::new("prop").base("component"),
        Decl::new("rig").base("model"),
        Decl::new("rivet").base("subcomponent"),
        Decl::new("site_root"),
    ];

    fn registry(decls: &[Decl<'_>]) -> Result<Registry, RegistryError> {
        Registry::builder().kinds("site", decls).build()
    }

    #[test]
    fn built_in_hierarchy() {
        let kinds = Registry::default();
        assert_eq!(
            kinds.all_kinds(),
            ["assembly", "component", "group", "model", "subcomponent"]
        );

        assert_eq!(kinds.base_kind(tokens::ASSEMBLY), Some(tokens::GROUP));
        assert_eq!(kinds.base_kind(tokens::GROUP), Some(tokens::MODEL));
        assert_eq!(kinds.base_kind(tokens::COMPONENT), Some(tokens::MODEL));
        assert_eq!(kinds.base_kind(tokens::MODEL), None);
        assert_eq!(kinds.base_kind(tokens::SUBCOMPONENT), None);

        assert!(kinds.is_model(tokens::ASSEMBLY) && kinds.is_group(tokens::ASSEMBLY));
        assert!(kinds.is_assembly(tokens::ASSEMBLY) && !kinds.is_assembly(tokens::GROUP));
        assert!(kinds.is_model(tokens::GROUP) && !kinds.is_component(tokens::GROUP));
        assert!(kinds.is_model(tokens::COMPONENT) && !kinds.is_group(tokens::COMPONENT));
        assert!(kinds.is_model(tokens::MODEL) && !kinds.is_group(tokens::MODEL));
        assert!(kinds.is_subcomponent(tokens::SUBCOMPONENT) && !kinds.is_model(tokens::SUBCOMPONENT));
    }

    #[test]
    fn unknown_kind_queries() {
        let kinds = Registry::default();
        assert!(!kinds.has_kind("chargroup"));
        assert_eq!(kinds.base_kind("chargroup"), None);
        assert!(!kinds.is_model("chargroup") && !kinds.is_subcomponent("chargroup"));
        assert!(kinds.is_a("chargroup", "chargroup"), "equal names need no registration");
        assert!(!kinds.is_a("chargroup", tokens::MODEL));
        assert!(!kinds.is_a(tokens::MODEL, "chargroup"));
    }

    /// The two kinds C++ `testKindRegistry` declares.
    #[test]
    fn declared_kinds() -> Result<(), RegistryError> {
        let kinds = registry(&[Decl::new("test_model_kind").base("model"), Decl::new("test_root_kind")])?;
        for kind in ["group", "model", "test_model_kind", "test_root_kind"] {
            assert!(kinds.has_kind(kind), "{kind}");
            assert!(kinds.all_kinds().contains(&kind), "{kind}");
        }
        assert_eq!(kinds.base_kind("test_root_kind"), None);
        assert_eq!(kinds.base_kind("test_model_kind"), Some("model"));

        assert!(kinds.is_model("test_model_kind"));
        assert!(!kinds.is_group("test_model_kind") && !kinds.is_component("test_model_kind"));
        assert!(!kinds.is_model("test_root_kind"));
        Ok(())
    }

    #[test]
    fn derived_lineage() -> Result<(), RegistryError> {
        let kinds = registry(&[
            Decl::new("chargroup").base("assembly"),
            Decl::new("hero").base("chargroup"),
            Decl::new("prop").base("component"),
            Decl::new("rivet").base("subcomponent"),
        ])?;
        assert!(kinds.is_assembly("hero") && kinds.is_group("hero") && kinds.is_model("hero"));
        assert!(kinds.is_a("hero", "chargroup") && !kinds.is_a("chargroup", "hero"));
        assert!(kinds.is_component("prop") && !kinds.is_group("prop"));
        assert!(kinds.is_subcomponent("rivet") && !kinds.is_model("rivet"));
        Ok(())
    }

    #[test]
    fn empty_base_is_root() -> Result<(), RegistryError> {
        assert_eq!(Decl::new("a").base(""), Decl::new("a"));
        let kinds = registry(&[Decl::new("absent"), Decl::new("empty").base("")])?;
        assert_eq!(kinds.base_kind("absent"), None);
        assert_eq!(kinds.base_kind("empty"), None);
        assert!(kinds.has_kind("absent") && kinds.has_kind("empty"));
        Ok(())
    }

    #[test]
    fn base_declared_later() -> Result<(), RegistryError> {
        let kinds = Registry::builder()
            .kinds("characters", &[Decl::new("hero").base("chargroup")])
            .kinds("site", &[Decl::new("chargroup").base("assembly")])
            .build()?;
        assert!(kinds.is_group("hero"));
        Ok(())
    }

    #[test]
    fn invalid_name_refused() {
        for name in ["", "9lives", "my:kind", "my-kind", "caf\u{e9}"] {
            assert_eq!(
                registry(&[Decl::new(name)]).unwrap_err(),
                RegistryError::InvalidName {
                    kind: name.to_owned(),
                    origin: Origin::Source("site".to_owned()),
                },
            );
        }
    }

    #[test]
    fn duplicate_refused() {
        let twice = Registry::builder()
            .kinds("site", &[Decl::new("prop").base("component")])
            .kind(Decl::new("prop").base("component"))
            .build();
        assert_eq!(
            twice.unwrap_err(),
            RegistryError::Duplicate {
                kind: "prop".to_owned(),
                first: Origin::Source("site".to_owned()),
                second: Origin::Direct,
            },
        );

        let built_in = registry(&[Decl::new("group").base("model")]);
        assert_eq!(
            built_in.unwrap_err(),
            RegistryError::Duplicate {
                kind: "group".to_owned(),
                first: Origin::BuiltIn,
                second: Origin::Source("site".to_owned()),
            },
        );
    }

    #[test]
    fn unknown_base_refused() {
        assert_eq!(
            registry(&[Decl::new("hero").base("chargroup")]).unwrap_err(),
            RegistryError::UnknownBase {
                kind: "hero".to_owned(),
                base: "chargroup".to_owned(),
                origin: Origin::Source("site".to_owned()),
            },
        );
    }

    #[test]
    fn cycle_refused() {
        let own_base = registry(&[Decl::new("a").base("a")]);
        assert!(matches!(own_base, Err(RegistryError::Cycle { kind, .. }) if kind == "a"));

        let pair = registry(&[
            Decl::new("a").base("b"),
            Decl::new("b").base("a"),
            Decl::new("c").base("model"),
        ]);
        assert!(matches!(pair, Err(RegistryError::Cycle { kind, .. }) if kind == "a"));
    }

    #[test]
    fn error_names_origins() {
        let error = Registry::builder()
            .kinds("site", &[Decl::new("group")])
            .build()
            .unwrap_err();
        assert_eq!(
            error.to_string(),
            "kind `group` is declared by the built-in hierarchy and again by `site`"
        );
    }
}
