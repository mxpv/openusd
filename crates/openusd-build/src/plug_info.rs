//! The metadata fields and kinds a plugin declares beside its schemas.
//!
//! C++ reads the fields from the `SdfMetadata` block of every plugin's
//! `plugInfo.json` before it opens a layer (`SdfSchemaBase::_AddFieldsFromPlugins`),
//! so a layer authoring one is authoring a registered field, and the kinds
//! from its `Kinds` block when the kind registry is first asked
//! (`KindRegistry::_RegisterDefaults`). A file holds one or more plugins, each
//! named after the library whose declarations it carries.

use std::fs;
use std::path::{Path, PathBuf};

use openusd::{kind, sdf, tf, usd};
use serde_json::Value as Json;

use crate::error::Error;
use crate::model::{KindDecl, MetadataField};

/// One plugin a `plugInfo.json` declares.
#[derive(Debug)]
pub struct Plugin {
    /// Its `Name`, which is the `libraryName` of the library its fields
    /// belong to.
    pub name: String,
    /// The file declaring it.
    pub path: PathBuf,
    /// The fields its `SdfMetadata` block declares.
    pub fields: Vec<MetadataField>,
    /// The kinds its `Kinds` block declares, in name order.
    pub kinds: Vec<KindDecl>,
}

/// Every plugin the `plugInfo.json` at `path` declares, in the order the file
/// lists them.
pub fn read(path: &Path) -> Result<Vec<Plugin>, Error> {
    let text = fs::read_to_string(path).map_err(|source| Error::Io {
        path: path.to_path_buf(),
        source,
    })?;
    // The files upstream ships open with `#` comment lines, which Pixar's
    // plugin reader skips and JSON does not allow.
    let json: Vec<&str> = text
        .lines()
        .filter(|line| !line.trim_start().starts_with('#'))
        .collect();
    let root: Json = serde_json::from_str(&json.join("\n")).map_err(|error| invalid(path, error.to_string()))?;

    let plugins = root
        .get("Plugins")
        .and_then(Json::as_array)
        .ok_or_else(|| invalid(path, "no `Plugins` array".to_owned()))?;
    plugins
        .iter()
        .map(|plugin| {
            let name = plugin
                .get("Name")
                .and_then(Json::as_str)
                .ok_or_else(|| invalid(path, "a plugin has no `Name`".to_owned()))?;
            let refused = |cause| invalid(path, format!("{name}: {cause}"));
            Ok(Plugin {
                name: name.to_owned(),
                path: path.to_path_buf(),
                fields: declarations(plugin, "SdfMetadata", field).map_err(refused)?,
                kinds: declarations(plugin, "Kinds", kind_decl).map_err(refused)?,
            })
        })
        .collect()
}

/// What the block called `key` of a plugin's `Info` declares, each entry read
/// by `read`. An absent block declares nothing.
fn declarations<T>(plugin: &Json, key: &str, read: fn(&str, &Json) -> Result<T, String>) -> Result<Vec<T>, String> {
    match plugin.get("Info").and_then(|info| info.get(key)) {
        None => Ok(Vec::new()),
        Some(Json::Object(entries)) => entries
            .iter()
            .map(|(name, declaration)| read(name, declaration))
            .collect(),
        Some(_) => Err(format!("`{key}` is not an object")),
    }
}

/// One kind's declaration. `baseKind` is the only key read, as in C++, and an
/// absent or empty one declares a root kind.
fn kind_decl(name: &str, declaration: &Json) -> Result<KindDecl, String> {
    if !tf::is_valid_identifier(name) {
        return Err(format!("kind `{name}` is not a valid identifier"));
    }
    if matches!(
        name,
        kind::tokens::MODEL
            | kind::tokens::GROUP
            | kind::tokens::ASSEMBLY
            | kind::tokens::COMPONENT
            | kind::tokens::SUBCOMPONENT
    ) {
        return Err(format!("kind `{name}` redeclares a built-in kind"));
    }
    let Json::Object(declaration) = declaration else {
        return Err(format!("kind `{name}` is not declared as an object"));
    };
    let base = match declaration.get("baseKind") {
        None => None,
        Some(Json::String(base)) => Some(base.clone()).filter(|base| !base.is_empty()),
        Some(_) => return Err(format!("kind `{name}` declares a `baseKind` that is not a string")),
    };
    Ok(KindDecl {
        name: name.to_owned(),
        base,
    })
}

/// One field's declaration.
fn field(name: &str, declaration: &Json) -> Result<MetadataField, String> {
    let spelling = declaration
        .get("type")
        .and_then(Json::as_str)
        .ok_or_else(|| format!("`{name}` declares no `type`"))?;
    let type_name = sdf::ValueTypeName::from(spelling);
    // A dictionary and the list-op types are metadata-only, so the value-type
    // table does not know them, and a field may still be declared with one.
    if type_name.kind().is_none() && spelling != "dictionary" && !spelling.ends_with("listop") {
        return Err(format!("`{name}` declares an unknown type `{spelling}`"));
    }

    let applies_to = match declaration.get("appliesTo") {
        None => usd::MetadataTargets::all(),
        Some(Json::String(target)) => target_of(name, target)?,
        Some(Json::Array(targets)) => targets.iter().try_fold(usd::MetadataTargets::empty(), |all, target| {
            let target = target
                .as_str()
                .ok_or_else(|| format!("`{name}` lists a non-string `appliesTo` entry"))?;
            Ok::<_, String>(all | target_of(name, target)?)
        })?,
        Some(_) => return Err(format!("`{name}` declares `appliesTo` as neither a string nor a list")),
    };

    let fallback = declaration
        .get("default")
        .map(|default| {
            default_value(&type_name, default)
                .map_err(|cause| format!("`{name}` declares a default that is not a `{spelling}`: {cause}"))
        })
        .transpose()?;

    Ok(MetadataField {
        name: tf::Token::from(name),
        type_name,
        applies_to,
        fallback,
        documentation: declaration
            .get("documentation")
            .and_then(Json::as_str)
            .map(str::to_owned),
    })
}

/// A declared default as a value of the type it is declared with.
///
/// The JSON is spelled as that type's `usda` literal and read back through the
/// text format, so a default decodes exactly as one authored in a layer would:
/// a list is an array at the top of an array type and a tuple everywhere else,
/// so `[0, 1, 0]` is a `double3` and `[[0, 1, 0]]` a `double3[]`.
fn default_value(type_name: &sdf::ValueTypeName, default: &Json) -> Result<sdf::Value, String> {
    let kind = type_name.kind().ok_or_else(|| "its type takes no default".to_owned())?;
    let asset = matches!(kind, sdf::ValueKind::AssetPath | sdf::ValueKind::AssetPathVec);
    let mut literal = String::new();
    spell(default, kind.element_kind().is_some(), asset, &mut literal)?;

    let text = format!(
        "#usda 1.0\n\nover \"Default\"\n{{\n    {} value = {literal}\n}}\n",
        type_name.as_str()
    );
    let layer = sdf::Layer::from_bytes("plugInfo default", text.into_bytes()).map_err(|error| error.to_string())?;
    let path = sdf::path("/Default.value").map_err(|error| error.to_string())?;
    layer
        .data()
        .try_field(&path, sdf::FieldKey::Default.as_str())
        .map_err(|error| error.to_string())?
        .map(|value| value.into_owned())
        .ok_or_else(|| "it reads as no value".to_owned())
}

/// Appends `json` as a `usda` literal: a list opening an array type as `[…]`,
/// any other list as `(…)`, and a string as an asset path where the type is
/// one.
fn spell(json: &Json, array: bool, asset: bool, out: &mut String) -> Result<(), String> {
    match json {
        Json::Array(items) => {
            let (open, close) = if array { ('[', ']') } else { ('(', ')') };
            out.push(open);
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                spell(item, false, asset, out)?;
            }
            out.push(close);
        }
        Json::String(text) if asset => out.push_str(&format!("@{text}@")),
        Json::String(text) => {
            out.push('"');
            for c in text.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    c => out.push(c),
                }
            }
            out.push('"');
        }
        Json::Number(number) => out.push_str(&number.to_string()),
        Json::Bool(flag) => out.push_str(if *flag { "1" } else { "0" }),
        Json::Null | Json::Object(_) => return Err("JSON null or an object spells no value".to_owned()),
    }
    Ok(())
}

/// The specs one `appliesTo` entry names.
fn target_of(name: &str, target: &str) -> Result<usd::MetadataTargets, String> {
    Ok(match target {
        "layers" => usd::MetadataTargets::LAYERS,
        "prims" => usd::MetadataTargets::PRIMS,
        "attributes" => usd::MetadataTargets::ATTRIBUTES,
        "relationships" => usd::MetadataTargets::RELATIONSHIPS,
        "properties" => usd::MetadataTargets::PROPERTIES,
        other => return Err(format!("`{name}` applies to an unknown kind of spec `{other}`")),
    })
}

/// A `plugInfo.json` that does not read as one.
fn invalid(path: &Path, cause: String) -> Error {
    Error::PlugInfo {
        path: path.to_path_buf(),
        cause,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::gf;

    /// A file written as upstream writes one: comment lines first, and
    /// `appliesTo` as a list or a single string.
    const PLUG_INFO: &str = r##"# Portions of this file auto-generated by usdGenSchema.
{
    "Plugins": [
        {
            "Info": {
                "SdfMetadata": {
                    "connectability": {
                        "appliesTo": ["attributes"],
                        "default": "full",
                        "documentation": "What an input connects to.",
                        "type": "token"
                    },
                    "weight": {
                        "appliesTo": ["attributes"],
                        "default": 0,
                        "type": "float"
                    },
                    "settingsPath": {
                        "appliesTo": "layers",
                        "type": "string"
                    },
                    "hints": {
                        "type": "dictionary"
                    }
                }
            },
            "Name": "testPlug"
        }
    ]
}
"##;

    fn fields(text: &str) -> Result<Vec<Plugin>, Error> {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("plugInfo.json");
        fs::write(&path, text).expect("writes");
        read(&path)
    }

    /// Every field reads with its type, targets and default, the default
    /// converted to the type it is declared with.
    #[test]
    fn upstream_shape_reads() {
        let plugins = fields(PLUG_INFO).expect("reads");
        assert_eq!(plugins.len(), 1);
        let Plugin { name, fields, .. } = &plugins[0];
        assert_eq!(name, "testPlug");
        let field = |name: &str| fields.iter().find(|field| field.name == name).expect("declared");

        let connectability = field("connectability");
        assert_eq!(connectability.applies_to, usd::MetadataTargets::ATTRIBUTES);
        assert_eq!(connectability.fallback, Some(sdf::Value::token("full")));
        assert_eq!(
            connectability.documentation.as_deref(),
            Some("What an input connects to.")
        );

        assert_eq!(
            field("weight").fallback,
            Some(sdf::Value::Float(0.0)),
            "an integer default widens"
        );
        assert_eq!(field("settingsPath").applies_to, usd::MetadataTargets::LAYERS);
        let hints = field("hints");
        assert_eq!(
            hints.applies_to,
            usd::MetadataTargets::all(),
            "no `appliesTo` is every spec"
        );
        assert_eq!(hints.type_name.as_str(), "dictionary");
    }

    /// A list default decodes as the type declares it: an array at the top of
    /// an array type, a tuple elsewhere, each converted to the element's
    /// precision.
    #[test]
    fn list_defaults_decode() {
        let declared = |ty: &str, default: &str| {
            let text = format!(
                r#"{{"Plugins": [{{"Name": "p", "Info": {{"SdfMetadata": {{"f": {{"type": "{ty}", "default": {default}}}}}}}}}]}}"#
            );
            let plugins = fields(&text).unwrap_or_else(|error| panic!("{ty}: {error}"));
            plugins[0].fields[0].fallback.clone().expect("a default")
        };
        assert_eq!(
            declared("double[]", "[0.0, 1.0]"),
            sdf::Value::DoubleVec(vec![0.0, 1.0])
        );
        assert_eq!(declared("float[]", "[0, 1]"), sdf::Value::FloatVec(vec![0.0, 1.0]));
        assert_eq!(declared("token[]", r#"["a", "b"]"#), sdf::Value::token_vec(["a", "b"]));
        assert_eq!(
            declared("double3", "[0, 1, 0]"),
            sdf::Value::Vec3d(gf::vec3d(0.0, 1.0, 0.0))
        );
        assert_eq!(
            declared("float3[]", "[[0, 1, 0], [1, 0, 0]]"),
            sdf::Value::Vec3fVec(vec![gf::vec3f(0.0, 1.0, 0.0), gf::vec3f(1.0, 0.0, 0.0)])
        );
        assert_eq!(
            declared("asset", r#""./a.png""#),
            sdf::Value::AssetPath("./a.png".into())
        );
        assert_eq!(declared("bool", "true"), sdf::Value::Bool(true));
        assert_eq!(
            declared("string", r#""say \"hi\"""#),
            sdf::Value::String("say \"hi\"".to_owned())
        );
    }

    /// A kind reads with its base, and both spellings of no base are a root.
    #[test]
    fn kinds_read() {
        let text = r#"{"Plugins": [{"Name": "p", "Info": {"Kinds": {
            "chargroup": {"baseKind": "assembly", "description": "ignored"},
            "absent": {},
            "empty": {"baseKind": ""}
        }}}]}"#;
        let plugins = fields(text).expect("reads");
        let kinds: Vec<(&str, Option<&str>)> = plugins[0]
            .kinds
            .iter()
            .map(|kind| (kind.name.as_str(), kind.base.as_deref()))
            .collect();
        assert_eq!(
            kinds,
            [("absent", None), ("chargroup", Some("assembly")), ("empty", None)]
        );
        assert!(plugins[0].fields.is_empty());
    }

    #[test]
    fn malformed_kinds_refused() {
        for (kinds, expected) in [
            (r#"["chargroup"]"#, "`Kinds` is not an object"),
            (r#"{"chargroup": "assembly"}"#, "is not declared as an object"),
            (r#"{"chargroup": {"baseKind": 3}}"#, "`baseKind` that is not a string"),
            (r#"{"char-group": {}}"#, "is not a valid identifier"),
            (r#"{"group": {"baseKind": "model"}}"#, "redeclares a built-in kind"),
        ] {
            let text = format!(r#"{{"Plugins": [{{"Name": "p", "Info": {{"Kinds": {kinds}}}}}]}}"#);
            match fields(&text) {
                Err(Error::PlugInfo { cause, .. }) => assert!(cause.contains(expected), "{cause}"),
                other => panic!("{kinds}: {other:?}"),
            }
        }
    }

    /// A declaration nothing can use is refused, naming the field.
    #[test]
    fn malformed_refused() {
        for (declaration, expected) in [
            (r#"{"type": "vec9"}"#, "unknown type `vec9`"),
            (
                r#"{"type": "token", "appliesTo": ["specs"]}"#,
                "unknown kind of spec `specs`",
            ),
            (r#"{"type": "int", "default": "many"}"#, "not a `int`"),
            (r#"{"type": "double3", "default": [1, 2]}"#, "not a `double3`"),
            (r#"{"appliesTo": ["prims"]}"#, "declares no `type`"),
        ] {
            let text =
                format!(r#"{{"Plugins": [{{"Name": "p", "Info": {{"SdfMetadata": {{"bad": {declaration}}}}}}}]}}"#);
            match fields(&text) {
                Err(Error::PlugInfo { cause, .. }) => assert!(cause.contains(expected), "{cause}"),
                other => panic!("{declaration}: {other:?}"),
            }
        }
    }
}
