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
    first_of_each_name(&mut doc);
    Ok(doc)
}

/// `doc` with each scope's elements unique by name, the first of a name
/// kept, as MaterialX's reader keeps it (it skips a child whose name its
/// parent already holds): a node's inputs, a node graph's interface inputs,
/// nodes and outputs, and the document's nodes, node graphs and outputs. Each
/// element dropped is noted in [`Document::skipped`].
fn first_of_each_name(doc: &mut Document) {
    let mut notes = Vec::new();
    for node in &mut doc.nodes {
        dedup(&mut node.inputs, |i| &i.name, &node.name, &mut notes);
    }
    for graph in &mut doc.graphs {
        for node in &mut graph.nodes {
            let scope = format!("{}/{}", graph.name, node.name);
            dedup(&mut node.inputs, |i| &i.name, &scope, &mut notes);
        }
        dedup(&mut graph.inputs, |i| &i.name, &graph.name, &mut notes);
        dedup(&mut graph.nodes, |n| &n.name, &graph.name, &mut notes);
        dedup(&mut graph.outputs, |o| &o.name, &graph.name, &mut notes);
    }
    dedup(&mut doc.nodes, |n| &n.name, "the document", &mut notes);
    dedup(&mut doc.graphs, |g| &g.name, "the document", &mut notes);
    dedup(&mut doc.outputs, |o| &o.name, "the document", &mut notes);
    doc.skipped.extend(notes);
}

/// `items` without each item whose `name` an earlier one has, a note in
/// `notes` for each, naming `scope`.
fn dedup<T>(items: &mut Vec<T>, name: fn(&T) -> &String, scope: &str, notes: &mut Vec<String>) {
    let mut seen: Vec<String> = Vec::new();
    items.retain(|item| {
        let n = name(item);
        if seen.contains(n) {
            notes.push(format!(
                "{scope}: a second element named {n} is ignored, as MaterialX reads the first"
            ));
            false
        } else {
            seen.push(n.clone());
            true
        }
    });
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
    fn first_input_wins() {
        let doc = parse(
            r#"<materialx version="1.39">
                 <constant name="c" type="color3"><input name="value" type="color3" value="1, 0, 0" /></constant>
                 <open_pbr_surface name="s" type="surfaceshader">
                   <input name="base_color" type="color3" value="0, 0, 1" />
                   <input name="base_color" type="color3" nodename="c" />
                 </open_pbr_surface>
               </materialx>"#,
            "t",
        )
        .expect("parses");
        let inputs = &doc.nodes[1].inputs;
        assert_eq!(inputs.len(), 1);
        assert_eq!(inputs[0].value.as_deref(), Some("0, 0, 1"));
        assert!(inputs[0].nodename.is_none());
        assert_eq!(
            doc.skipped,
            ["s: a second element named base_color is ignored, as MaterialX reads the first"]
        );
    }

    #[test]
    fn not_materialx() {
        assert!(matches!(parse("<x/>", "t"), Err(ReadError::NotMaterialX { .. })));
        assert!(matches!(parse("<materialx", "t"), Err(ReadError::Xml { .. })));
    }
}
