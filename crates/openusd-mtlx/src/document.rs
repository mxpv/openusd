//! A MaterialX document as the translation reads it: its nodes, node graphs
//! and outputs, with the attributes `usdMtlx` carries into USD.

use std::borrow::Cow;

use crate::nodedefs::NodeDef;

/// A parsed `.mtlx` document.
#[derive(Debug, Default)]
pub(crate) struct Document {
    /// The `version` the document declares.
    pub version: String,
    /// The document's `colorspace`.
    pub colorspace: Option<String>,
    /// The document's `fileprefix`.
    pub fileprefix: Option<String>,
    /// The nodes at the document's own level, in document order.
    pub nodes: Vec<Node>,
    /// The `<nodegraph>`s.
    pub graphs: Vec<Graph>,
    /// The `<output>`s at the document's own level.
    pub outputs: Vec<Output>,
    /// The `<nodedef>`s the document declares.
    pub nodedefs: Vec<NodeDef>,
    /// The elements the translation leaves out (`<look>`, …), one entry per
    /// kind, for the layer's warnings.
    pub skipped: Vec<String>,
}

/// A `<nodegraph>`.
#[derive(Debug, Default)]
pub(crate) struct Graph {
    pub name: String,
    /// The nodedef the graph implements, for a custom node's graph.
    pub nodedef: Option<String>,
    pub colorspace: Option<String>,
    pub fileprefix: Option<String>,
    /// The graph's interface inputs.
    pub inputs: Vec<Input>,
    pub nodes: Vec<Node>,
    pub outputs: Vec<Output>,
}

/// A node: an element whose tag is its category.
#[derive(Debug, Default)]
pub(crate) struct Node {
    pub category: String,
    pub name: String,
    /// The `type` it is instantiated with (`color3`, `BSDF`, `multioutput`).
    pub type_name: String,
    pub version: Option<String>,
    /// The `nodedef` it names, when it names one.
    pub nodedef: Option<String>,
    pub colorspace: Option<String>,
    pub fileprefix: Option<String>,
    pub inputs: Vec<Input>,
}

/// An `<input>` of a node or a node graph.
#[derive(Debug, Default)]
pub(crate) struct Input {
    pub name: String,
    pub type_name: String,
    pub value: Option<String>,
    /// The node it reads, at its own level.
    pub nodename: Option<String>,
    /// The node graph it reads an output of.
    pub nodegraph: Option<String>,
    /// The output it reads, of `nodename`'s node or `nodegraph`'s graph.
    pub output: Option<String>,
    /// The enclosing graph's interface input it reads.
    pub interfacename: Option<String>,
    pub colorspace: Option<String>,
    pub fileprefix: Option<String>,
}

/// An `<output>` of a node graph or of the document.
#[derive(Debug, Default)]
pub(crate) struct Output {
    pub name: String,
    pub type_name: String,
    pub nodename: Option<String>,
    /// The output of `nodename`'s node it forwards.
    pub output: Option<String>,
}

impl Document {
    /// The node graph called `name`.
    pub fn graph(&self, name: &str) -> Option<&Graph> {
        self.graphs.iter().find(|g| g.name == name)
    }
}

/// Why a document could not be read.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum ReadError {
    /// The text is not well-formed XML.
    #[error("{source_name}: {error}")]
    Xml {
        /// Where the text came from.
        source_name: String,
        /// The parser's diagnostic.
        error: roxmltree::Error,
    },
    /// The document's root element is not `<materialx>`.
    #[error("{source_name}: the root element is <{root}>, not <materialx>")]
    NotMaterialX {
        /// Where the text came from.
        source_name: String,
        /// The root element's tag.
        root: String,
    },
    /// The translated layer could not be authored.
    #[error(transparent)]
    Authoring(#[from] openusd::sdf::AuthoringError),
    /// A translated name does not form a path.
    #[error(transparent)]
    Path(#[from] openusd::sdf::PathParseError),
}

/// The elements of a document or node graph that are not nodes. Those the
/// translation reads are handled by name; the others are left out.
const NOT_NODES: &[&str] = &[
    "nodegraph",
    "nodedef",
    "implementation",
    "typedef",
    "output",
    "input",
    "token",
    "look",
    "lookgroup",
    "collection",
    "geominfo",
    "geompropdef",
    "propertyset",
    "variantset",
    "backdrop",
    "unitdef",
    "unittypedef",
    "targetdef",
    "attributedef",
    "comment",
];

/// The elements left out that carry meaning, reported in the layer's
/// warnings.
const REPORTED: &[&str] = &[
    "look",
    "lookgroup",
    "collection",
    "geominfo",
    "propertyset",
    "variantset",
];

/// Parses `text`, read from `source_name`.
///
/// A `<UDIM>` or `<UVTILE>` token inside an attribute value, a bare `<` that
/// MaterialX's own reader accepts though XML does not, reads as written.
pub(crate) fn parse(text: &str, source_name: &str) -> Result<Document, ReadError> {
    let text = escape_tile_tokens(text);
    let xml = roxmltree::Document::parse(&text).map_err(|error| ReadError::Xml {
        source_name: source_name.to_owned(),
        error,
    })?;
    let root = xml.root_element();
    if root.tag_name().name() != "materialx" {
        return Err(ReadError::NotMaterialX {
            source_name: source_name.to_owned(),
            root: root.tag_name().name().to_owned(),
        });
    }
    let mut doc = Document {
        version: root.attribute("version").unwrap_or("1.39").to_owned(),
        colorspace: attr(root, "colorspace"),
        fileprefix: attr(root, "fileprefix"),
        ..Document::default()
    };
    for el in root.children().filter(roxmltree::Node::is_element) {
        match el.tag_name().name() {
            "nodegraph" => doc.graphs.push(graph(el)),
            "nodedef" => doc.nodedefs.push(NodeDef::from_element(el)),
            "output" => doc.outputs.push(output(el)),
            tag if REPORTED.contains(&tag) => {
                let note = format!("<{tag}> elements are not translated");
                if !doc.skipped.contains(&note) {
                    doc.skipped.push(note);
                }
            }
            tag if NOT_NODES.contains(&tag) => {}
            _ => doc.nodes.push(node(el)),
        }
    }
    Ok(doc)
}

/// `text` with each `<UDIM>` and `<UVTILE>` escaped, so an attribute holding
/// one parses and reads it back as written.
fn escape_tile_tokens(text: &str) -> Cow<'_, str> {
    if !text.contains("<UDIM>") && !text.contains("<UVTILE>") {
        return Cow::Borrowed(text);
    }
    Cow::Owned(
        text.replace("<UDIM>", "&lt;UDIM&gt;")
            .replace("<UVTILE>", "&lt;UVTILE&gt;"),
    )
}

fn attr(el: roxmltree::Node<'_, '_>, name: &str) -> Option<String> {
    el.attribute(name).map(str::to_owned)
}

fn graph(el: roxmltree::Node<'_, '_>) -> Graph {
    let mut g = Graph {
        name: el.attribute("name").unwrap_or_default().to_owned(),
        nodedef: attr(el, "nodedef"),
        colorspace: attr(el, "colorspace"),
        fileprefix: attr(el, "fileprefix"),
        ..Graph::default()
    };
    for child in el.children().filter(roxmltree::Node::is_element) {
        match child.tag_name().name() {
            "input" => g.inputs.push(input(child)),
            "output" => g.outputs.push(output(child)),
            tag if NOT_NODES.contains(&tag) => {}
            _ => g.nodes.push(node(child)),
        }
    }
    g
}

fn node(el: roxmltree::Node<'_, '_>) -> Node {
    Node {
        category: el.tag_name().name().to_owned(),
        name: el.attribute("name").unwrap_or_default().to_owned(),
        type_name: el.attribute("type").unwrap_or_default().to_owned(),
        version: attr(el, "version"),
        nodedef: attr(el, "nodedef"),
        colorspace: attr(el, "colorspace"),
        fileprefix: attr(el, "fileprefix"),
        inputs: el.children().filter(|c| c.has_tag_name("input")).map(input).collect(),
    }
}

fn input(el: roxmltree::Node<'_, '_>) -> Input {
    Input {
        name: el.attribute("name").unwrap_or_default().to_owned(),
        type_name: el.attribute("type").unwrap_or_default().to_owned(),
        value: attr(el, "value"),
        nodename: attr(el, "nodename").filter(|n| !n.is_empty()),
        nodegraph: attr(el, "nodegraph").filter(|n| !n.is_empty()),
        output: attr(el, "output").filter(|n| !n.is_empty()),
        interfacename: attr(el, "interfacename").filter(|n| !n.is_empty()),
        colorspace: attr(el, "colorspace"),
        fileprefix: attr(el, "fileprefix"),
    }
}

fn output(el: roxmltree::Node<'_, '_>) -> Output {
    Output {
        name: el.attribute("name").unwrap_or_default().to_owned(),
        type_name: el.attribute("type").unwrap_or_default().to_owned(),
        nodename: attr(el, "nodename").filter(|n| !n.is_empty()),
        output: attr(el, "output").filter(|n| !n.is_empty()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn udim_reads_back() {
        let doc = parse(
            r#"<materialx version="1.38"><image name="i" type="color3"><input name="file" type="filename" value="a.<UDIM>.png" /></image></materialx>"#,
            "t",
        )
        .expect("parses");
        let file = &doc.nodes[0].inputs[0];
        assert_eq!(file.value.as_deref(), Some("a.<UDIM>.png"));
    }

    #[test]
    fn looks_reported() {
        let doc = parse(
            r#"<materialx version="1.39"><look name="a" /><look name="b" /><nodegraph name="g"><output name="out" type="float" /></nodegraph></materialx>"#,
            "t",
        )
        .expect("parses");
        assert_eq!(doc.skipped, ["<look> elements are not translated"]);
        assert!(doc.nodes.is_empty());
        assert_eq!(doc.graphs[0].outputs[0].name, "out");
    }

    #[test]
    fn not_materialx() {
        assert!(matches!(parse("<x/>", "t"), Err(ReadError::NotMaterialX { .. })));
        assert!(matches!(parse("<materialx", "t"), Err(ReadError::Xml { .. })));
    }
}
