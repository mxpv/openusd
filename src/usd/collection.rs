//! `UsdCollectionAPI` — named working sets over a stage (spec §15).
//!
//! A collection is a multiple-apply API schema applied to a prim with an
//! *instance name*; its properties live under `collection:<name>:`. A
//! collection names a set of paths via the relationship-linking language —
//! `includes` / `excludes` relationships, an `expansionRule`, and an
//! `includeRoot` flag — which a [`MembershipQuery`](membership::MembershipQuery)
//! resolves into actual membership.
//!
//! Collections are a *core* USD feature (not tied to any one schema
//! family): UsdShade material binding, UsdRender render passes, UsdPhysics
//! collision groups, and UsdLux light-linking all consume them. This
//! module is therefore always compiled, like
//! [`ConnectionGraph`](super::ConnectionGraph).
//!
//! Membership resolution lives in [`membership`]; this file is the schema
//! surface — locating collections on a prim and reading their authored
//! opinions.
//!
//! The newer pattern-based `membershipExpression` mode (an
//! `SdfPathExpression` predicate) is read here as a raw string but is not
//! yet *evaluated* — that engine is a separate effort. Relationship-mode
//! collections are fully supported.

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

/// Multiple-apply API schema name; instances appear in `apiSchemas` as
/// `CollectionAPI:<name>`.
const API_COLLECTION: &str = "CollectionAPI";
/// Property namespace prefix for every collection property.
const NS_COLLECTION: &str = "collection:";

// Property base names (suffixes after `collection:<name>:`).
const EXPANSION_RULE: &str = "expansionRule";
const INCLUDE_ROOT: &str = "includeRoot";
const INCLUDES: &str = "includes";
const EXCLUDES: &str = "excludes";
const MEMBERSHIP_EXPRESSION: &str = "membershipExpression";

// `expansionRule` token values.
const TOK_EXPLICIT_ONLY: &str = "explicitOnly";
const TOK_EXPAND_PRIMS: &str = "expandPrims";
const TOK_EXPAND_PRIMS_AND_PROPERTIES: &str = "expandPrimsAndProperties";

/// How a collection's `includes`/`excludes` targets expand to members
/// (`collection:<name>:expansionRule`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ExpansionRule {
    /// Only the exact included paths are members; no descendant expansion.
    ExplicitOnly,
    /// Every prim descendant of an included path is a member (the default).
    #[default]
    ExpandPrims,
    /// Like [`ExpandPrims`](Self::ExpandPrims), and every included prim's
    /// properties are members too.
    ExpandPrimsAndProperties,
}

impl ExpansionRule {
    pub fn as_token(self) -> &'static str {
        match self {
            ExpansionRule::ExplicitOnly => TOK_EXPLICIT_ONLY,
            ExpansionRule::ExpandPrims => TOK_EXPAND_PRIMS,
            ExpansionRule::ExpandPrimsAndProperties => TOK_EXPAND_PRIMS_AND_PROPERTIES,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            TOK_EXPLICIT_ONLY => ExpansionRule::ExplicitOnly,
            TOK_EXPAND_PRIMS => ExpansionRule::ExpandPrims,
            TOK_EXPAND_PRIMS_AND_PROPERTIES => ExpansionRule::ExpandPrimsAndProperties,
            _ => return None,
        })
    }
}

/// A handle to one `UsdCollectionAPI` instance: the prim it is applied to
/// plus the instance name. Cheap to construct and clone; reads pull from
/// the stage on demand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Collection {
    prim: Path,
    name: String,
}

impl Collection {
    /// A handle to the collection named `name` on `prim`. Does not check
    /// that the collection is actually applied — use [`collections_on`] to
    /// enumerate authored collections.
    pub fn new(prim: impl Into<Path>, name: impl Into<String>) -> Self {
        Collection {
            prim: prim.into(),
            name: name.into(),
        }
    }

    /// The prim the collection is applied to.
    pub fn prim(&self) -> &Path {
        &self.prim
    }

    /// The collection's instance name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The `<prim>.collection:<name>` property path — the collection's
    /// identity, used as a target when one collection includes another.
    pub fn collection_path(&self) -> Result<Path> {
        self.prim.append_property(&format!("{NS_COLLECTION}{}", self.name))
    }

    /// `collection:<name>:<suffix>` property path on the prim.
    fn prop(&self, suffix: &str) -> Result<Path> {
        self.prim
            .append_property(&format!("{NS_COLLECTION}{}:{suffix}", self.name))
    }

    /// `expansionRule` — defaults to [`ExpansionRule::ExpandPrims`].
    pub fn expansion_rule(&self, stage: &Stage) -> Result<ExpansionRule> {
        Ok(
            match stage.field::<Value>(self.prop(EXPANSION_RULE)?, FieldKey::Default)? {
                Some(Value::Token(t) | Value::String(t)) => ExpansionRule::from_token(&t).unwrap_or_default(),
                _ => ExpansionRule::default(),
            },
        )
    }

    /// `includeRoot` — whether the pseudo-root `</>` counts as included.
    /// Defaults to `false`.
    pub fn include_root(&self, stage: &Stage) -> Result<bool> {
        Ok(matches!(
            stage.field::<Value>(self.prop(INCLUDE_ROOT)?, FieldKey::Default)?,
            Some(Value::Bool(true))
        ))
    }

    /// The authored `includes` relationship targets.
    pub fn includes(&self, stage: &Stage) -> Result<Vec<Path>> {
        stage.relationship_targets(&self.prop(INCLUDES)?)
    }

    /// The authored `excludes` relationship targets.
    pub fn excludes(&self, stage: &Stage) -> Result<Vec<Path>> {
        stage.relationship_targets(&self.prop(EXCLUDES)?)
    }

    /// The raw `membershipExpression` string, if authored. Read-only —
    /// expression-mode evaluation is not implemented yet.
    pub fn membership_expression(&self, stage: &Stage) -> Result<Option<String>> {
        Ok(
            match stage.field::<Value>(self.prop(MEMBERSHIP_EXPRESSION)?, FieldKey::Default)? {
                Some(Value::PathExpression(s) | Value::String(s) | Value::Token(s)) => Some(s),
                _ => None,
            },
        )
    }

    /// Whether this collection is authored in expression mode (a
    /// `membershipExpression` with no `includes`/`excludes`/`includeRoot`).
    /// Such collections are not yet evaluated.
    pub fn has_expression(&self, stage: &Stage) -> Result<bool> {
        Ok(self.membership_expression(stage)?.is_some()
            && self.includes(stage)?.is_empty()
            && self.excludes(stage)?.is_empty()
            && !self.include_root(stage)?)
    }
}

/// Every `UsdCollectionAPI` instance applied to `prim`, decoded from its
/// `apiSchemas` (`CollectionAPI:<name>`).
pub fn collections_on(stage: &Stage, prim: &Path) -> Result<Vec<Collection>> {
    let mut out = Vec::new();
    for schema in stage.api_schemas(prim)? {
        if let Some(name) = instance_name(&schema) {
            out.push(Collection::new(prim.clone(), name));
        }
    }
    Ok(out)
}

/// Decode the instance name from a `CollectionAPI:<name>` apiSchema entry.
fn instance_name(api_schema: &str) -> Option<String> {
    api_schema
        .strip_prefix(API_COLLECTION)?
        .strip_prefix(':')
        .map(str::to_string)
}

/// If `path` is a collection identity path `<prim>.collection:<name>`,
/// return `(prim, name)`. Used to detect when an `includes` target points
/// at another collection (chained collections). A deeper property path like
/// `collection:<name>:includes` is *not* a collection identity and yields
/// `None`.
pub fn is_collection_api_path(path: &Path) -> Option<(Path, String)> {
    let (prim, property) = path.split_property()?;
    let rest = property.strip_prefix(NS_COLLECTION)?;
    if rest.is_empty() || rest.contains(':') {
        return None;
    }
    Some((prim, rest.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;
    use crate::sdf::Variability;

    fn author_collection(stage: &Stage, prim: &str, name: &str) -> Result<()> {
        stage
            .define_prim(sdf::path(prim)?)?
            .set_type_name("Scope")?
            .add_applied_schema(format!("{API_COLLECTION}:{name}"))?;
        Ok(())
    }

    #[test]
    fn expansion_rule_round_trips() {
        for r in [
            ExpansionRule::ExplicitOnly,
            ExpansionRule::ExpandPrims,
            ExpansionRule::ExpandPrimsAndProperties,
        ] {
            assert_eq!(ExpansionRule::from_token(r.as_token()), Some(r));
        }
        assert_eq!(ExpansionRule::from_token("nope"), None);
        assert_eq!(ExpansionRule::default(), ExpansionRule::ExpandPrims);
    }

    #[test]
    fn decodes_collection_paths() -> Result<()> {
        assert_eq!(
            is_collection_api_path(&sdf::path("/W.collection:render")?),
            Some((sdf::path("/W")?, "render".to_string()))
        );
        // A deeper property (the includes rel) is not a collection identity.
        assert_eq!(
            is_collection_api_path(&sdf::path("/W.collection:render:includes")?),
            None
        );
        // A non-collection property / a prim path.
        assert_eq!(is_collection_api_path(&sdf::path("/W.foo")?), None);
        assert_eq!(is_collection_api_path(&sdf::path("/W")?), None);
        Ok(())
    }

    #[test]
    fn enumerates_collections_on_prim() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage
            .define_prim(sdf::path("/W")?)?
            .set_type_name("Scope")?
            .add_applied_schema("CollectionAPI:render")?
            .add_applied_schema("CollectionAPI:proxy")?
            .add_applied_schema("MaterialBindingAPI")?; // not a collection — ignored

        let names: Vec<String> = collections_on(&stage, &sdf::path("/W")?)?
            .into_iter()
            .map(|c| c.name().to_string())
            .collect();
        assert_eq!(names, vec!["render".to_string(), "proxy".to_string()]);
        Ok(())
    }

    #[test]
    fn reads_authored_opinions() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        author_collection(&stage, "/W", "render")?;
        let w = sdf::path("/W")?;
        let coll = Collection::new(w.clone(), "render");

        // expansionRule (uniform token), includeRoot (uniform bool), includes rel.
        stage
            .create_attribute(coll.prop(EXPANSION_RULE)?, "token")?
            .set_variability(Variability::Uniform)?
            .set(Value::Token(ExpansionRule::ExplicitOnly.as_token().to_string()))?;
        stage
            .create_attribute(coll.prop(INCLUDE_ROOT)?, "bool")?
            .set_variability(Variability::Uniform)?
            .set(Value::Bool(true))?;
        crate::usd::Prim::new(&stage, w.clone())
            .author_relationship_targets(&format!("collection:render:{INCLUDES}"), [sdf::path("/W/A")?])?;

        assert_eq!(coll.expansion_rule(&stage)?, ExpansionRule::ExplicitOnly);
        assert!(coll.include_root(&stage)?);
        assert_eq!(coll.includes(&stage)?, vec![sdf::path("/W/A")?]);
        assert!(coll.excludes(&stage)?.is_empty());

        // Unauthored collection falls back to spec defaults.
        author_collection(&stage, "/X", "c")?;
        let bare = Collection::new(sdf::path("/X")?, "c");
        assert_eq!(bare.expansion_rule(&stage)?, ExpansionRule::ExpandPrims);
        assert!(!bare.include_root(&stage)?);
        Ok(())
    }
}
