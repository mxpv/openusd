//! Shader-node interfaces, read from a layer of `def Shader` prims.
//!
//! A shader node is defined outside any schema: upstream declares
//! `UsdPreviewSurface` and its companions in `usdShaders`'s `shaderDefs.usda`,
//! which Sdr discovers at run time. Each prim there names a node by its
//! `info:id` and declares the inputs and outputs a shader of that id takes,
//! with the values a renderer uses where a shader authors none.

use std::path::{Path, PathBuf};

use openusd::{sdf, tf};

use crate::Builder;
use crate::error::Error;
use crate::load;
use crate::model;

/// Every node one shader-definition layer declares.
#[derive(Debug)]
pub struct NodeLibrary {
    /// What the configuration named the library, which names its file.
    pub name: String,
    /// The layer it was read from.
    pub path: PathBuf,
    /// Where every layer it composed from was found, for a build script to
    /// watch.
    pub layers: Vec<PathBuf>,
    /// Its nodes, in the order the layer declares them.
    pub nodes: Vec<Node>,
}

/// One shader node.
#[derive(Debug)]
pub struct Node {
    /// The prim that defines it, which is the node's name upstream.
    pub prim_name: String,
    /// The `info:id` a shader of this node authors.
    pub id: tf::Token,
    /// What the definition says the node is.
    pub documentation: Option<String>,
    /// Its inputs, in the order the definition declares them.
    pub inputs: Vec<Port>,
    /// Its outputs, likewise.
    pub outputs: Vec<Port>,
}

/// One input or output of a node.
#[derive(Debug)]
pub struct Port {
    /// The name after `inputs:` or `outputs:`.
    pub base_name: String,
    /// The value type it is declared with.
    pub type_name: sdf::ValueTypeName,
    /// The value a renderer uses where a shader authors none.
    pub fallback: Option<sdf::Value>,
    /// What the definition says it is for.
    pub documentation: Option<String>,
    /// The values it admits, where the definition restricts them.
    pub allowed_tokens: Vec<tf::Token>,
    /// Whether it connects only to an interface input
    /// (`connectability = "interfaceOnly"`).
    pub interface_only: bool,
}

/// Reads the node library `name` from the layer at `path`, opened as the
/// builder opens a schema.
///
/// A prim that is not a `Shader`, or that authors no `info:id`, defines no
/// node and is passed over.
pub fn read(builder: &Builder, name: &str, path: &Path) -> Result<NodeLibrary, Error> {
    let invalid = |cause: String| Error::ShaderDefs {
        path: path.to_path_buf(),
        cause,
    };
    let stage = load::open_stage(builder, path)?;

    let mut nodes = Vec::new();
    for prim in stage.prim(sdf::Path::abs_root())?.children()? {
        if prim.type_name()?.as_deref() != Some("Shader") {
            continue;
        }
        let Some(id) = stage.field::<tf::Token>(prim.path().append_property("info:id")?, sdf::FieldKey::Default)?
        else {
            continue;
        };
        let prim_name = prim.path().name().unwrap_or_default().to_owned();

        let mut inputs = Vec::new();
        let mut outputs = Vec::new();
        for property in prim.authored_property_names()? {
            let (ports, base_name) = if let Some(base) = property.strip_prefix("inputs:") {
                (&mut inputs, base)
            } else if let Some(base) = property.strip_prefix("outputs:") {
                (&mut outputs, base)
            } else {
                continue;
            };
            let attr = prim.attribute(property.as_str());
            let Some(type_name) = attr.type_name()? else {
                return Err(invalid(format!("{prim_name}.{property} declares no type")));
            };
            ports.push(Port {
                base_name: base_name.to_owned(),
                type_name,
                fallback: stage.field::<sdf::Value>(attr.path(), sdf::FieldKey::Default)?,
                documentation: attr.get_metadata::<String>(sdf::FieldKey::Documentation.as_str())?,
                allowed_tokens: model::allowed_tokens(
                    attr.get_metadata::<sdf::Value>(sdf::FieldKey::AllowedTokens.as_str())?
                        .as_ref(),
                ),
                interface_only: attr.get_metadata::<tf::Token>("connectability")?.as_deref() == Some("interfaceOnly"),
            });
        }

        nodes.push(Node {
            documentation: prim.get_metadata::<String>(sdf::FieldKey::Documentation.as_str())?,
            prim_name,
            id,
            inputs,
            outputs,
        });
    }
    if nodes.is_empty() {
        return Err(invalid("it defines no shader node".to_owned()));
    }
    // A node's prim index is built when it is read, so a diagnostic an arc of
    // it raises — a reference to a layer that is not there — exists only now.
    if let Some(error) = Error::composition(path, &stage) {
        return Err(error);
    }

    Ok(NodeLibrary {
        name: name.to_owned(),
        path: path.to_path_buf(),
        layers: load::watched_layers(&stage),
        nodes,
    })
}
