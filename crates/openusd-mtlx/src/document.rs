//! A MaterialX document as the translation reads it: its nodes, node graphs
//! and outputs, with the attributes `usdMtlx` carries into USD.

use std::borrow::Cow;
use std::collections::HashSet;
use std::io;
use std::str::Utf8Error;

use openusd::sdf;

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
    /// The document's `cms`, its colour management system.
    pub cms: Option<String>,
    /// The document's `cmsconfig`, the configuration of its `cms`.
    pub cmsconfig: Option<String>,
    /// The nodes at the document's own level, in document order.
    pub nodes: Vec<Node>,
    /// The `<nodegraph>`s.
    pub graphs: Vec<Graph>,
    /// The `<output>`s at the document's own level.
    pub outputs: Vec<Output>,
    /// The `<nodedef>`s the document declares.
    pub nodedefs: Vec<NodeDef>,
    /// What the read left out: one entry per kind of element the translation
    /// has no counterpart for (`<look>`, …), and one per element skipped, for
    /// the layer's warnings.
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
    pub doc: Option<String>,
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
    /// The node it inherits from, for a material node.
    pub inherit: Option<String>,
    pub colorspace: Option<String>,
    pub fileprefix: Option<String>,
    pub doc: Option<String>,
    pub inputs: Vec<Input>,
    /// Its `<token>`s, as `(name, value)`.
    pub tokens: Vec<(String, String)>,
}

/// An `<input>` of a node or a node graph.
#[derive(Debug, Default)]
pub(crate) struct Input {
    pub name: String,
    pub type_name: String,
    /// The value it authors, when it holds one.
    pub value: Option<String>,
    /// The values it takes over a range of frames.
    pub valuecurve: Option<String>,
    /// The node it reads, at its own level.
    pub nodename: Option<String>,
    /// The node graph it reads an output of.
    pub nodegraph: Option<String>,
    /// The output it reads, of `nodename`'s node or `nodegraph`'s graph.
    pub output: Option<String>,
    /// The enclosing graph's interface input it reads.
    pub interfacename: Option<String>,
    /// The channels it reads of its source, a swizzle.
    pub channels: Option<String>,
    /// The member it reads of its source.
    pub member: Option<String>,
    pub colorspace: Option<String>,
    pub fileprefix: Option<String>,
    pub doc: Option<String>,
    pub helptext: Option<String>,
    /// The values its `enum` lists.
    pub enums: Vec<String>,
    pub uifolder: Option<String>,
    pub uiname: Option<String>,
}

/// An `<output>` of a node graph or of the document.
#[derive(Debug, Default)]
pub(crate) struct Output {
    pub name: String,
    pub type_name: String,
    pub nodename: Option<String>,
    /// The output of `nodename`'s node it forwards.
    pub output: Option<String>,
    pub doc: Option<String>,
}

impl Document {
    /// The node graph called `name`.
    pub fn graph(&self, name: &str) -> Option<&Graph> {
        self.graphs.iter().find(|g| g.name == name)
    }

    /// Rewrites each `filename` value the document's nodes and node graphs
    /// author as `anchor` gives it, its `fileprefix` folded in first, for a
    /// document about to be imported by one that sits elsewhere: the layer
    /// anchors every asset path at the document that was opened.
    pub(crate) fn anchor_filenames(&mut self, anchor: &dyn Fn(&str) -> String) {
        let document = self.fileprefix.as_deref();
        for node in &mut self.nodes {
            let outer = node.fileprefix.as_deref().or(document);
            node.inputs.iter_mut().for_each(|input| input.anchor(outer, anchor));
        }
        for graph in &mut self.graphs {
            let outer = graph.fileprefix.as_deref().or(document);
            graph.inputs.iter_mut().for_each(|input| input.anchor(outer, anchor));
            for node in &mut graph.nodes {
                let outer = node.fileprefix.as_deref().or(outer);
                node.inputs.iter_mut().for_each(|input| input.anchor(outer, anchor));
            }
        }
    }

    /// Takes the elements of `library`, a document this one includes
    /// (MaterialX `Document::importLibrary`): each one whose name is not in
    /// `taken`, which then holds it. A node or node graph that sets no
    /// `fileprefix` or `colorspace` of its own keeps the library's.
    // TODO: qualify each imported name with the library's `namespace`
    // (MaterialX `getQualifiedName`), and look a node's nodedef up by its
    // qualified category first; a namespace is not read.
    fn import(&mut self, library: Document, taken: &mut HashSet<String>) {
        let mut free = |name: &str| taken.insert(name.to_owned());
        for mut node in library.nodes {
            if free(&node.name) {
                node.fileprefix = node.fileprefix.or_else(|| library.fileprefix.clone());
                node.colorspace = node.colorspace.or_else(|| library.colorspace.clone());
                self.nodes.push(node);
            }
        }
        for mut graph in library.graphs {
            if free(&graph.name) {
                graph.fileprefix = graph.fileprefix.or_else(|| library.fileprefix.clone());
                graph.colorspace = graph.colorspace.or_else(|| library.colorspace.clone());
                self.graphs.push(graph);
            }
        }
        self.outputs
            .extend(library.outputs.into_iter().filter(|o| free(&o.name)));
        self.nodedefs
            .extend(library.nodedefs.into_iter().filter(|d| free(&d.name)));
        self.skipped.extend(library.skipped);
    }
}

impl Input {
    /// Rewrites the `filename` value the input authors as `anchor` gives
    /// it, with the `fileprefix` in effect folded in first: its own, or
    /// `outer`, that of the elements around it.
    fn anchor(&mut self, outer: Option<&str>, anchor: &dyn Fn(&str) -> String) {
        if self.type_name != "filename" {
            return;
        }
        let Some(value) = &self.value else {
            return;
        };
        let prefix = self.fileprefix.as_deref().or(outer).unwrap_or_default();
        self.value = Some(anchor(&with_prefix(prefix, value)));
        self.fileprefix = Some(String::new());
    }
}

/// `text`, a `filename` value, with the `fileprefix` in effect folded in
/// (MaterialX `flattenFilenames`): an absolute name takes none.
pub(crate) fn with_prefix(prefix: &str, text: &str) -> String {
    match is_absolute(text) {
        true => text.to_owned(),
        false => format!("{prefix}{text}"),
    }
}

/// Whether a `filename` value is absolute: rooted, or on a drive.
pub(crate) fn is_absolute(text: &str) -> bool {
    text.starts_with(['/', '\\']) || matches!(text.get(1..3), Some(":/" | ":\\"))
}

/// Reads the document an `xi:include` names by its `href`, or returns
/// says why it adds none.
pub(crate) type Include<'a> = dyn FnMut(&str) -> Result<Included, ReadError> + 'a;

/// What an `xi:include` brings into the document that holds it.
pub(crate) enum Included {
    /// The document it names.
    Document(Box<Document>),
    /// Nothing: the document it names is included already.
    Already,
    /// Nothing: the document it names cannot be found from the including
    /// one.
    Unfound,
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
    /// A document is not UTF-8 text.
    #[error("{source_name}: {error}")]
    Encoding {
        /// Where the bytes came from.
        source_name: String,
        /// Where the text stops being UTF-8.
        error: Utf8Error,
    },
    /// A document could not be opened.
    #[error("{source_name}: {error}")]
    Open {
        /// The document.
        source_name: String,
        /// Why it did not open.
        error: io::Error,
    },
    /// A document an `xi:include` names does not resolve.
    #[error("{source_name}: the included document {href} does not resolve")]
    IncludeUnresolved {
        /// The including document.
        source_name: String,
        /// The `href` of the include.
        href: String,
    },
    /// A document's includes nest deeper than MaterialX reads.
    #[error("{source_name}: including {href} nests too deep")]
    IncludeDepth {
        /// The including document.
        source_name: String,
        /// The `href` of the include one level too deep.
        href: String,
    },
    /// A document includes itself, directly or through its includes.
    #[error("{source_name}: including {href} forms a cycle")]
    IncludeCycle {
        /// The including document.
        source_name: String,
        /// The `href` of the include that closes the cycle.
        href: String,
    },
    /// The translated layer could not be authored.
    #[error(transparent)]
    Authoring(#[from] sdf::AuthoringError),
    /// A translated name does not form a path.
    #[error(transparent)]
    Path(#[from] sdf::PathParseError),
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
    // A material of a document older than MaterialX 1.38.
    "material",
    "look",
    "lookgroup",
    "collection",
    "geominfo",
    "propertyset",
    "variantset",
];

/// The namespace of an `xi:include` element.
const XINCLUDE: &str = "http://www.w3.org/2001/XInclude";

/// How an `xi:include` element opens, as MaterialX writes and matches it.
const INCLUDE_TAG: &str = "<xi:include";

/// Parses `text`, read from `source_name`, reading each document it
/// includes through `include`.
///
/// The elements of an included document come first and keep their names,
/// as MaterialX reads the includes before the document's own elements. An
/// element of `text` that repeats one of those names is left out.
pub(crate) fn parse(text: &str, source_name: &str, include: &mut Include<'_>) -> Result<Document, ReadError> {
    let text = lenient(text);
    let options = roxmltree::ParsingOptions {
        allow_dtd: true,
        ..roxmltree::ParsingOptions::default()
    };
    let xml = roxmltree::Document::parse_with_options(&text, options).map_err(|error| ReadError::Xml {
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
    // TODO: upgrade a document older than the embedded libraries as
    // MaterialX does on read (`Document::upgradeVersion`): `<material>` and
    // `<shaderref>` elements, renamed nodes and inputs.
    let mut doc = Document {
        version: root.attribute("version").unwrap_or("1.39").to_owned(),
        colorspace: attr(root, "colorspace"),
        fileprefix: attr(root, "fileprefix"),
        cms: attr(root, "cms"),
        cmsconfig: attr(root, "cmsconfig"),
        ..Document::default()
    };
    let mut skipped = Vec::new();
    let mut taken = HashSet::new();
    for el in root.children().filter(is_include) {
        let href = el.attribute("href").unwrap_or_default();
        match include(href)? {
            Included::Document(library) => doc.import(*library, &mut taken),
            Included::Already => {}
            Included::Unfound => skipped.push(format!(
                "the document {href} is not included: it cannot be found from the including one"
            )),
        }
    }
    for (el, name) in children(root, "the document", taken, &mut skipped) {
        match el.tag_name().name() {
            "nodegraph" => doc.graphs.push(graph(el, name, &mut skipped)),
            "nodedef" => doc.nodedefs.push(NodeDef::from_element(el, name, &mut skipped)),
            "output" => doc.outputs.push(output(el, name)),
            tag if REPORTED.contains(&tag) => {
                let note = format!("<{tag}> elements are not translated");
                if !skipped.contains(&note) {
                    skipped.push(note);
                }
            }
            tag if NOT_NODES.contains(&tag) => {}
            _ => doc.nodes.push(node(el, name, None, &mut skipped)),
        }
    }
    doc.skipped.extend(skipped);
    Ok(doc)
}

/// The child elements of `el` that MaterialX's reader keeps (its
/// `elementFromXml`), each with its name: every one but an `xi:include`, and
/// but one whose name is in `taken` or an earlier child has, whatever the
/// two are. An unnamed child is named for its tag and a number no sibling
/// has (`constant1`), as MaterialX names it. Each child left out is noted in
/// `notes`, naming `scope`.
pub(crate) fn children<'a, 'input>(
    el: roxmltree::Node<'a, 'input>,
    scope: &str,
    mut taken: HashSet<String>,
    notes: &mut Vec<String>,
) -> Vec<(roxmltree::Node<'a, 'input>, String)> {
    let mut kept = Vec::new();
    for child in el.children().filter(|child| child.is_element() && !is_include(child)) {
        let name = match child.attribute("name").unwrap_or_default() {
            "" => {
                let tag = child.tag_name().name();
                (1u32..)
                    .map(|n| format!("{tag}{n}"))
                    .find(|name| !taken.contains(name))
                    .unwrap_or_default()
            }
            name => name.to_owned(),
        };
        if taken.insert(name.clone()) {
            kept.push((child, name));
        } else {
            notes.push(format!(
                "{scope}: a second element named {name} is ignored, as MaterialX reads the first"
            ));
        }
    }
    kept
}

/// Whether `el` is an `xi:include`.
fn is_include(el: &roxmltree::Node<'_, '_>) -> bool {
    el.tag_name().namespace() == Some(XINCLUDE) && el.tag_name().name() == "include"
}

/// `text` as XML a strict parser reads the way MaterialX's own reader
/// does: inside an attribute value, a `<` escaped (a `<UDIM>` token in a file
/// name) and an `&` that starts no reference; and the `xi` prefix declared
/// on each `xi:include` that no tag before it declares it for, an element
/// MaterialX matches by its tag as written.
fn lenient(text: &str) -> Cow<'_, str> {
    /// Where the scan is.
    enum At {
        /// Between tags.
        Content,
        /// Inside a tag, outside its attribute values.
        Tag,
        /// Inside an attribute value closed by this quote.
        Value(u8),
    }
    /// Markup that holds no attribute, as `(opening, closing)`.
    const OPAQUE: &[(&str, &str)] = &[("<!--", "-->"), ("<![CDATA[", "]]>"), ("<?", "?>")];
    const DECLARATION: &str = " xmlns:xi=\"http://www.w3.org/2001/XInclude\"";

    // Whether a tag read so far declares the `xi` prefix.
    let mut declared = false;
    let bytes = text.as_bytes();
    let mut out = String::new();
    // Where the text not yet copied to `out` starts.
    let mut pending = 0;
    let mut at = At::Content;
    let mut i = 0;
    while i < bytes.len() {
        match at {
            At::Content if bytes[i] == b'<' => {
                let rest = &text[i..];
                if let Some((opening, closing)) = OPAQUE.iter().find(|(opening, _)| rest.starts_with(opening)) {
                    let body = &rest[opening.len()..];
                    i += opening.len() + body.find(closing).map_or(body.len(), |end| end + closing.len());
                    continue;
                }
                at = At::Tag;
                let include = rest
                    .strip_prefix(INCLUDE_TAG)
                    .is_some_and(|after| after.starts_with(|c: char| c.is_ascii_whitespace() || c == '/' || c == '>'));
                declared = declared || rest[..rest.find('>').unwrap_or(rest.len())].contains("xmlns:xi");
                if !declared && include {
                    let end = i + INCLUDE_TAG.len();
                    out.push_str(&text[pending..end]);
                    out.push_str(DECLARATION);
                    pending = end;
                    i = end;
                    continue;
                }
            }
            At::Tag => match bytes[i] {
                quote @ (b'"' | b'\'') => at = At::Value(quote),
                b'>' => at = At::Content,
                _ => {}
            },
            At::Value(quote) if bytes[i] == quote => at = At::Tag,
            At::Value(_) if bytes[i] == b'<' => {
                out.push_str(&text[pending..i]);
                out.push_str("&lt;");
                pending = i + 1;
            }
            At::Value(_) if bytes[i] == b'&' && !is_reference(&text[i..]) => {
                out.push_str(&text[pending..i]);
                out.push_str("&amp;");
                pending = i + 1;
            }
            At::Content | At::Value(_) => {}
        }
        i += 1;
    }
    if pending == 0 {
        return Cow::Borrowed(text);
    }
    out.push_str(&text[pending..]);
    Cow::Owned(out)
}

/// Whether `text`, which starts at an `&`, starts a character reference or
/// a reference to one of XML's own entities.
fn is_reference(text: &str) -> bool {
    /// The bytes a reference runs to at most, past its `&`: `#x10FFFF;`.
    const LONGEST: usize = 9;
    let Some(end) = text.bytes().skip(1).take(LONGEST).position(|b| b == b';') else {
        return false;
    };
    let name = &text[1..=end];
    match name.strip_prefix('#') {
        Some(code) => match code.strip_prefix('x') {
            Some(hex) => !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()),
            None => !code.is_empty() && code.bytes().all(|b| b.is_ascii_digit()),
        },
        None => matches!(name, "amp" | "lt" | "gt" | "quot" | "apos"),
    }
}

fn attr(el: roxmltree::Node<'_, '_>, name: &str) -> Option<String> {
    el.attribute(name).map(str::to_owned)
}

/// The attribute `name` of `el`, when it holds something.
fn filled(el: roxmltree::Node<'_, '_>, name: &str) -> Option<String> {
    attr(el, name).filter(|value| !value.is_empty())
}

fn graph(el: roxmltree::Node<'_, '_>, name: String, notes: &mut Vec<String>) -> Graph {
    let mut g = Graph {
        name,
        nodedef: attr(el, "nodedef"),
        colorspace: attr(el, "colorspace"),
        fileprefix: attr(el, "fileprefix"),
        doc: filled(el, "doc"),
        ..Graph::default()
    };
    for (child, name) in children(el, &g.name, HashSet::new(), notes) {
        match child.tag_name().name() {
            "input" if untyped(child) => {
                notes.push(format!("{}: the input {name} has no type and is left out", g.name));
            }
            "input" => g.inputs.push(input(child, name)),
            "output" => g.outputs.push(output(child, name)),
            tag if NOT_NODES.contains(&tag) => {}
            _ => g.nodes.push(node(child, name, Some(&g.name), notes)),
        }
    }
    g
}

/// The node `el` declares as `name`, in the node graph called `graph` when
/// it is in one.
fn node(el: roxmltree::Node<'_, '_>, name: String, graph: Option<&str>, notes: &mut Vec<String>) -> Node {
    let mut n = Node {
        category: el.tag_name().name().to_owned(),
        name,
        type_name: el.attribute("type").unwrap_or_default().to_owned(),
        version: filled(el, "version"),
        nodedef: attr(el, "nodedef"),
        inherit: filled(el, "inherit"),
        colorspace: attr(el, "colorspace"),
        fileprefix: attr(el, "fileprefix"),
        doc: filled(el, "doc"),
        ..Node::default()
    };
    let scope = match graph {
        Some(graph) => format!("{graph}/{}", n.name),
        None => n.name.clone(),
    };
    for (child, name) in children(el, &scope, HashSet::new(), notes) {
        match child.tag_name().name() {
            "input" if untyped(child) => notes.push(format!("{scope}: the input {name} has no type and is left out")),
            "input" => n.inputs.push(input(child, name)),
            "token" => n
                .tokens
                .push((name, child.attribute("value").unwrap_or_default().to_owned())),
            _ => {}
        }
    }
    n
}

/// Whether `el` declares no `type`. C++ `usdMtlx` skips such an input.
fn untyped(el: roxmltree::Node<'_, '_>) -> bool {
    el.attribute("type").unwrap_or_default().is_empty()
}

fn input(el: roxmltree::Node<'_, '_>, name: String) -> Input {
    Input {
        name,
        type_name: el.attribute("type").unwrap_or_default().to_owned(),
        value: filled(el, "value"),
        valuecurve: filled(el, "valuecurve"),
        nodename: filled(el, "nodename"),
        nodegraph: filled(el, "nodegraph"),
        output: filled(el, "output"),
        interfacename: filled(el, "interfacename"),
        channels: filled(el, "channels"),
        member: filled(el, "member"),
        colorspace: attr(el, "colorspace"),
        fileprefix: attr(el, "fileprefix"),
        doc: filled(el, "doc"),
        helptext: filled(el, "helptext"),
        enums: el
            .attribute("enum")
            .into_iter()
            .flat_map(|list| list.split(','))
            .map(|value| value.trim().to_owned())
            .filter(|value| !value.is_empty())
            .collect(),
        uifolder: filled(el, "uifolder"),
        uiname: filled(el, "uiname"),
    }
}

fn output(el: roxmltree::Node<'_, '_>, name: String) -> Output {
    Output {
        name,
        type_name: el.attribute("type").unwrap_or_default().to_owned(),
        nodename: filled(el, "nodename"),
        output: filled(el, "output"),
        doc: filled(el, "doc"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `text` parsed as a document with no location.
    fn read(text: &str) -> Result<Document, ReadError> {
        parse(text, "t", &mut |_| Ok(Included::Unfound))
    }

    #[test]
    fn udim_reads_back() {
        let doc = read(
            r#"<materialx version="1.38"><image name="i" type="color3"><input name="file" type="filename" value="a.<UDIM>.png" /></image></materialx>"#,
        )
        .expect("parses");
        let file = &doc.nodes[0].inputs[0];
        assert_eq!(file.value.as_deref(), Some("a.<UDIM>.png"));
    }

    /// Any `<` in an attribute value reads back, in either quote, as does an
    /// `&` beside a reference, and a comment holding quotes and tags, or a
    /// document type, changes nothing after it.
    #[test]
    fn angle_in_value() {
        let doc = read(
            r#"<!DOCTYPE materialx><materialx version="1.38"><!-- a "<b" --><image name="i" type="color3"><input name="file" type="filename" value="<diff_albedo>" /><input name='x' type='string' value='a<"b' /><input name="y" type="string" value="wood & metal &amp; &#65;" /></image></materialx>"#,
        )
        .expect("parses");
        let inputs = &doc.nodes[0].inputs;
        assert_eq!(inputs[0].value.as_deref(), Some("<diff_albedo>"));
        assert_eq!(inputs[1].value.as_deref(), Some("a<\"b"));
        assert_eq!(inputs[2].value.as_deref(), Some("wood & metal & A"));
    }

    #[test]
    fn looks_reported() {
        let doc = read(
            r#"<materialx version="1.39"><look name="a" /><look name="b" /><nodegraph name="g"><output name="out" type="float" /></nodegraph></materialx>"#,
        )
        .expect("parses");
        assert_eq!(doc.skipped, ["<look> elements are not translated"]);
        assert!(doc.nodes.is_empty());
        assert_eq!(doc.graphs[0].outputs[0].name, "out");
    }

    #[test]
    fn first_input_wins() {
        let doc = read(
            r#"<materialx version="1.39">
                 <constant name="c" type="color3"><input name="value" type="color3" value="1, 0, 0" /></constant>
                 <open_pbr_surface name="s" type="surfaceshader">
                   <input name="base_color" type="color3" value="0, 0, 1" />
                   <input name="base_color" type="color3" nodename="c" />
                 </open_pbr_surface>
               </materialx>"#,
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

    /// The prefix an `xi:include` lacks is declared for it though a comment
    /// spells the declaration, and an input with no type is left out.
    #[test]
    fn comment_declares_nothing() {
        let doc = read(
            r#"<!-- no xmlns:xi here --><materialx version="1.39"><xi:include href="lib.mtlx" /><constant name="c" type="float"><input name="value" value="3" /></constant></materialx>"#,
        )
        .expect("parses");
        assert!(doc.nodes[0].inputs.is_empty());
        assert_eq!(doc.skipped.len(), 2, "{:?}", doc.skipped);
        assert_eq!(doc.skipped[1], "c: the input value has no type and is left out");
    }

    /// A name is taken by the first element of any kind, and an unnamed
    /// element is named for its tag.
    #[test]
    fn first_of_any_kind() {
        let doc = read(
            r#"<materialx version="1.39">
                 <constant name="a" type="float" />
                 <nodegraph name="a" />
                 <constant type="float" />
                 <constant type="float" />
               </materialx>"#,
        )
        .expect("parses");
        assert!(doc.graphs.is_empty());
        let names: Vec<_> = doc.nodes.iter().map(|n| n.name.as_str()).collect();
        assert_eq!(names, ["a", "constant1", "constant2"]);
        assert_eq!(
            doc.skipped,
            ["the document: a second element named a is ignored, as MaterialX reads the first"]
        );
    }

    /// An `xi:include` is no node, whether or not the document declares the
    /// prefix, and is reported where the document has no location.
    #[test]
    fn include_reported() {
        for root in [
            r#"<materialx version="1.38">"#,
            r#"<materialx version="1.38" xmlns:xi="http://www.w3.org/2001/XInclude">"#,
        ] {
            let doc = read(&format!(r#"{root}<xi:include href="lib.mtlx" /></materialx>"#)).expect("parses");
            assert!(doc.nodes.is_empty());
            assert_eq!(
                doc.skipped,
                ["the document lib.mtlx is not included: it cannot be found from the including one"]
            );
        }
    }

    /// An included document's elements come first and keep their names, and
    /// take its `fileprefix` and `colorspace` where they set none.
    #[test]
    fn include_imports() {
        let mut include = |href: &str| {
            assert_eq!(href, "lib.mtlx");
            read(
                r#"<materialx version="1.39" fileprefix="lib/" colorspace="acescg">
                     <image name="a" type="color3" />
                     <image name="b" type="color3" fileprefix="own/" />
                   </materialx>"#,
            )
            .map(|library| Included::Document(Box::new(library)))
        };
        let doc = parse(
            r#"<materialx version="1.39">
                 <constant name="a" type="float" />
                 <constant name="c" type="float" />
                 <xi:include href="lib.mtlx" />
               </materialx>"#,
            "t",
            &mut include,
        )
        .expect("parses");
        let nodes: Vec<_> = doc
            .nodes
            .iter()
            .map(|n| (n.name.as_str(), n.category.as_str(), n.fileprefix.as_deref()))
            .collect();
        assert_eq!(
            nodes,
            [
                ("a", "image", Some("lib/")),
                ("b", "image", Some("own/")),
                ("c", "constant", None)
            ]
        );
        assert_eq!(doc.nodes[0].colorspace.as_deref(), Some("acescg"));
        assert_eq!(
            doc.skipped,
            ["the document: a second element named a is ignored, as MaterialX reads the first"]
        );
    }

    #[test]
    fn not_materialx() {
        assert!(matches!(read("<x/>"), Err(ReadError::NotMaterialX { .. })));
        assert!(matches!(read("<materialx"), Err(ReadError::Xml { .. })));
    }
}
