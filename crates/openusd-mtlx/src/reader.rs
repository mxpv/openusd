//! The translation of a [`Document`] into `UsdShade` specs (C++ `usdMtlx`'s
//! `reader.cpp`).
//!
//! Prims and properties are collected first, as the reader's `_Context`
//! creates them, and authored once at the end, so each attribute is declared
//! with its type, value, metadata and connection together.

use std::collections::{BTreeMap, HashMap};
use std::str::FromStr;

use openusd::{gf, sdf, vt};

use crate::document::{self, Document, Graph, Input, Node, Output, ReadError};
use crate::nodedefs::{self, Library, Match, NodeDef};

/// Where the layer roots everything (C++ `usdMtlx`'s internal path).
const ROOT: &str = "/MaterialX";

/// The shader types a material reads, each with the output a shader of the
/// type has and the material output that one drives (C++ `_AddShaderOutput`
/// and the end of `_Context::AddShaderNode`).
const SHADER_TYPES: &[(&str, &str, &str)] = &[
    ("surfaceshader", "surface", "mtlx:surface"),
    ("volumeshader", "volume", "mtlx:volume"),
    ("displacementshader", "displacement", "mtlx:displacement"),
    ("lightshader", "light", "light"),
];

/// The layer `doc` translates into.
pub(crate) fn translate(doc: &Document) -> Result<sdf::Data, ReadError> {
    let root = sdf::Path::new(ROOT)?;
    let local = Library::local(doc.nodedefs.clone());
    let mut cx = Context {
        doc,
        local: &local,
        materials: root.append_child("Materials")?,
        shaders: root.append_child("Shaders")?,
        node_graphs: root.append_child("NodeGraphs")?,
        prims: Vec::new(),
        index: sdf::PathMap::default(),
        graphs: HashMap::new(),
        named: sdf::PathMap::default(),
        warnings: doc.skipped.clone(),
    };
    // TODO: translate a node graph that implements a nodedef as the custom
    // node's `NodeGraph` (C++ `ReadNodeGraphsWithDefs`, `_IsLocalCustomNode`),
    // with the `sourceAsset` of the shaders that instantiate it.
    for graph in &doc.graphs {
        if let Some(nodedef) = &graph.nodedef {
            cx.warn(format!(
                "{}: the node graph implementing {nodedef} is not translated, so its custom node is not",
                graph.name
            ));
        }
    }
    // TODO: translate `<look>`s, `<collection>`s and `<variantset>`s: the
    // material variants, the collections and the `LookVariant` set of C++
    // `UsdMtlxRead` after its `ReadMaterials`.
    let materials = || doc.nodes.iter().filter(|n| n.type_name == "material");
    for material in materials() {
        cx.material(material)?;
    }
    // A material's base may come after it. Every material has its prim by
    // the time the bases are read.
    for material in materials() {
        cx.inherit(material)?;
    }
    cx.author()
}

/// The prims collected so far, in creation order, and the state the
/// translation keeps across materials.
struct Context<'d> {
    doc: &'d Document,
    /// The document's own nodedefs.
    local: &'d Library,
    /// Where the materials go.
    materials: sdf::Path,
    /// Where the shader nodes' implementations go.
    shaders: sdf::Path,
    /// The node graph of the document's own nodes, and where the
    /// `<nodegraph>`s go.
    node_graphs: sdf::Path,
    prims: Vec<Prim>,
    /// Prim path → its index in `prims`.
    index: sdf::PathMap<usize>,
    /// Node graph (`None` for the document's own nodes) → its prim path and
    /// its nodes that have a prim, once built.
    graphs: HashMap<Option<&'d str>, (sdf::Path, Vec<&'d Node>)>,
    /// Prim path → the MaterialX name of the element it is made for.
    named: sdf::PathMap<&'d str>,
    warnings: Vec<String>,
}

/// A prim to author.
#[derive(Debug)]
struct Prim {
    path: sdf::Path,
    type_name: &'static str,
    api_schemas: Vec<&'static str>,
    /// The prim it internally references.
    reference: Option<sdf::Path>,
    /// The prim it specializes.
    specializes: Option<sdf::Path>,
    doc: Option<String>,
    /// Property name → the attribute, authored in name order.
    attrs: BTreeMap<String, Attr>,
}

/// An attribute to author.
#[derive(Debug, Default)]
struct Attr {
    type_name: &'static str,
    uniform: bool,
    value: Option<vt::Value>,
    connect: Option<sdf::Path>,
    /// The MaterialX type of a value USD has no type for (`BSDF`).
    render_type: Option<String>,
    color_space: Option<String>,
    doc: Option<String>,
    display_name: Option<String>,
    display_group: Option<String>,
    allowed_tokens: Vec<String>,
}

impl<'d> Context<'d> {
    /// The prim at `path`, created as a `def` of `type_name` if it is not
    /// yet, under untyped `def`s for the ancestors it lacks; an untyped prim
    /// takes a type given later.
    fn prim(&mut self, path: &sdf::Path, type_name: &'static str) -> &mut Prim {
        let i = if let Some(&i) = self.index.get(path) {
            i
        } else {
            if let Some(parent) = path.parent().filter(|parent| !parent.is_abs_root()) {
                self.prim(&parent, "");
            }
            self.prims.push(Prim {
                path: path.clone(),
                type_name: "",
                api_schemas: Vec::new(),
                reference: None,
                specializes: None,
                doc: None,
                attrs: BTreeMap::new(),
            });
            self.index.insert(path.clone(), self.prims.len() - 1);
            self.prims.len() - 1
        };
        let prim = &mut self.prims[i];
        if prim.type_name.is_empty() {
            prim.type_name = type_name;
        }
        prim
    }

    /// Whether the element called `name` gets the prim at `path`: no element
    /// of another name has it, two MaterialX names having one USD name
    /// (`ns:a` and `ns__a`). Warns where one has.
    fn claim(&mut self, path: &sdf::Path, name: &'d str) -> bool {
        let owner = *self.named.entry(path.clone()).or_insert(name);
        if owner != name {
            self.warn(format!("{name}: not translated, its USD name is that of {owner}"));
        }
        owner == name
    }

    /// The attribute `name` of the prim at `path`, declared with the
    /// MaterialX type `mtype` unless it already is.
    fn attr(&mut self, path: &sdf::Path, name: &str, mtype: &str) -> &mut Attr {
        let (type_name, render_type) = usd_type(mtype);
        self.declare(path, name, type_name, render_type)
    }

    /// The attribute `name` of the prim at `path`, declared a `token` unless
    /// it is declared already: an attribute USD defines, or a port of a
    /// shader type (C++ `_AddShaderOutput`).
    fn token(&mut self, path: &sdf::Path, name: &str) -> &mut Attr {
        self.declare(path, name, "token", None)
    }

    fn declare(
        &mut self,
        path: &sdf::Path,
        name: &str,
        type_name: &'static str,
        render_type: Option<String>,
    ) -> &mut Attr {
        self.prim(path, "")
            .attrs
            .entry(name.to_owned())
            .or_insert_with(|| Attr {
                type_name,
                render_type,
                ..Attr::default()
            })
    }

    fn warn(&mut self, warning: String) {
        if !self.warnings.contains(&warning) {
            self.warnings.push(warning);
        }
    }

    /// The nodedef `node` instantiates, with a warning where none matches
    /// exactly. `without` is what becomes of a node no nodedef matches at
    /// all, for that warning.
    fn nodedef(&mut self, node: &Node, without: &str) -> Option<&'d NodeDef> {
        let (def, exact) = match nodedefs::find(self.local, node) {
            Some(Match::Exact(def)) => (def, true),
            Some(Match::Closest(def)) => (def, false),
            None => {
                self.warn(format!(
                    "{}: no {} nodedef of type {}; {without}",
                    node.name, node.category, node.type_name
                ));
                return None;
            }
        };
        if !exact {
            let wrong: Vec<String> = node
                .inputs
                .iter()
                .filter(|i| def.input_type(&i.name) != Some(i.type_name.as_str()))
                .map(|i| format!("{} ({})", i.name, i.type_name))
                .collect();
            self.warn(format!(
                "{}: no {} nodedef takes {}; written as {}",
                node.name,
                node.category,
                wrong.join(", "),
                def.name
            ));
        }
        Some(def)
    }

    /// The output of `node` a connection naming `output` reads (C++
    /// `_NodeGraphBuilder::_ConnectPorts`): the node's only output whatever
    /// the connection names, or the one of several it names. `None` for a
    /// node with no nodedef, which has no outputs, and where the connection
    /// names none of several.
    fn output_of(&self, node: &Node, output: Option<&str>) -> Option<&'d str> {
        let (Match::Exact(def) | Match::Closest(def)) = nodedefs::find(self.local, node)?;
        match def.outputs.as_slice() {
            [(only, _)] => Some(only),
            outputs => outputs
                .iter()
                .map(|(name, _)| name.as_str())
                .find(|name| Some(*name) == output),
        }
    }

    /// The attribute a connection reads `output` through, of the node
    /// called `nodename` among those of `graph` that have a prim, which is
    /// the child of `parent` named for it. Warns, naming the reader `from`,
    /// where there is no such node or it has no such output.
    fn source(
        &mut self,
        parent: &sdf::Path,
        graph: Option<&'d Graph>,
        nodename: &str,
        output: Option<&str>,
        from: &str,
    ) -> Result<Option<sdf::Path>, ReadError> {
        let upstream = self
            .graphs
            .get(&graph.map(|g| g.name.as_str()))
            .and_then(|(_, nodes)| nodes.iter().copied().find(|node| node.name == nodename));
        let Some(upstream) = upstream else {
            self.warn(format!("{from}: no node {nodename}"));
            return Ok(None);
        };
        let Some(output) = self.output_of(upstream, output) else {
            self.warn(format!("{from}: {} has no output to read", upstream.name));
            return Ok(None);
        };
        let prim = parent.append_child(make_name(&upstream.name))?;
        Ok(Some(prim.append_property(output_name(output))?))
    }

    /// A material node: its `Material` and the shader nodes its inputs read
    /// (C++ `_Context::BeginMaterial` and `_TranslateShaderNodes`).
    fn material(&mut self, material: &'d Node) -> Result<(), ReadError> {
        let doc = self.doc;
        let path = self.materials.append_child(make_name(&material.name))?;
        if !self.claim(&path, &material.name) {
            return Ok(());
        }
        let prim = self.prim(&path, "Material");
        prim.api_schemas.push("MaterialXConfigAPI");
        prim.doc.clone_from(&material.doc);
        self.attr(&path, "config:mtlx:version", "string").value = Some(vt::Value::String(doc.version.clone()));
        for input in &material.inputs {
            if let Some(nodename) = &input.nodename
                && !doc.nodes.iter().any(|node| node.name == *nodename)
            {
                self.warn(format!("{}.{}: no node {nodename}", material.name, input.name));
            }
        }
        for &(shader_type, ..) in SHADER_TYPES {
            let mut seen: Vec<&str> = Vec::new();
            for input in &material.inputs {
                // TODO: read a shader node that sits inside a node graph
                // (MaterialX `getShaderNodes` follows the graph's output).
                if input.nodegraph.is_some() && input.type_name == shader_type {
                    self.warn(format!(
                        "{}.{}: a shader inside a node graph is not translated",
                        material.name, input.name
                    ));
                }
                let Some(node) = input
                    .nodename
                    .as_deref()
                    .and_then(|n| doc.nodes.iter().find(|x| x.name == n))
                    .filter(|n| n.type_name == shader_type)
                else {
                    continue;
                };
                if !seen.contains(&node.name.as_str()) {
                    seen.push(&node.name);
                    self.shader_node(&path, node)?;
                }
            }
        }
        Ok(())
    }

    /// The base a material node inherits from, which its `Material`
    /// specializes (C++ `ReadMaterials`).
    fn inherit(&mut self, material: &Node) -> Result<(), ReadError> {
        let Some(base) = &material.inherit else {
            return Ok(());
        };
        let path = self.materials.append_child(make_name(&material.name))?;
        // A material left out for its USD name has no prim of its own.
        if self.named.get(&path) != Some(&material.name.as_str()) {
            return Ok(());
        }
        let base_path = self.materials.append_child(make_name(base))?;
        if self.named.get(&base_path) == Some(&base.as_str()) {
            self.prim(&path, "").specializes = Some(base_path);
        } else {
            self.warn(format!("{}: no material {base} to inherit from", material.name));
        }
        Ok(())
    }

    /// A shader node of the material at `mat` (C++ `_Context::AddShaderNode`).
    fn shader_node(&mut self, mat: &sdf::Path, node: &'d Node) -> Result<(), ReadError> {
        let doc = self.doc;
        let Some(def) = self.nodedef(node, "not translated") else {
            return Ok(());
        };
        let name = make_name(&node.name);
        let implementation = self.shaders.append_child(&name)?;
        if !self.claim(&implementation, &node.name) {
            return Ok(());
        }
        if !self.index.contains_key(&implementation) {
            self.prim(&implementation, "Shader").doc.clone_from(&node.doc);
            self.token(&implementation, "info:id")
                .uniform_value(vt::Value::token(def.name.clone()));
            for (_, ty) in &def.outputs {
                if let Some(output) = shader_output(ty) {
                    self.token(&implementation, &output_name(output));
                }
            }
        }
        let shader = mat.append_child(&name)?;
        if !self.claim(&shader, &node.name) {
            return Ok(());
        }
        self.prim(&shader, "Shader").reference = Some(implementation);
        // Every nodedef input is an interface input of the material, which
        // the shader's input reads.
        for (input, ty) in &def.inputs {
            let name = input_name(input);
            self.attr(mat, &name, ty);
            self.attr(&shader, &name, ty).connect = Some(mat.append_property(&name)?);
        }
        for input in &node.inputs {
            self.input(mat, Some(node), input, Some(def), None);
            let source = match (&input.nodegraph, &input.output, &input.nodename) {
                (Some(graph), Some(_), _) => {
                    if let Some(graph) = doc.graph(graph) {
                        self.bind(mat, Some(graph), input)?
                    } else {
                        self.warn(format!("{}.{}: no node graph {graph}", node.name, input.name));
                        None
                    }
                }
                (None, Some(_), _) | (_, None, Some(_)) => self.bind(mat, None, input)?,
                (Some(graph), None, None) => {
                    self.warn(format!(
                        "{}.{}: reads the node graph {graph} without naming an output of it",
                        node.name, input.name
                    ));
                    None
                }
                (None, None, None) => None,
            };
            if let Some(source) = source {
                let attr = self.attr(&shader, &input_name(&input.name), &input.type_name);
                attr.connect = Some(source);
                attr.doc.clone_from(&input.doc);
            }
        }
        // A token is a string primvar of the material.
        for (token, value) in &node.tokens {
            self.attr(mat, &format!("primvars:{}", make_name(token)), "string")
                .value = Some(vt::Value::String(value.clone()));
        }
        // TODO: connect an output whose type a `<typedef>` gives a shader
        // semantic to a material output of its name (the end of C++
        // `_Context::AddShaderNode`); typedefs are not read.
        // The shader's output of a shader type drives the material's.
        for &(shader_type, output, terminal) in SHADER_TYPES {
            if def.outputs.iter().any(|(_, ty)| ty == shader_type) {
                self.token(mat, &format!("outputs:{terminal}")).connect =
                    Some(shader.append_property(output_name(output))?);
            }
        }
        Ok(())
    }

    /// Brings `graph` (the document's own nodes for `None`) under the
    /// material at `mat` and returns the output `input` reads of it (C++
    /// `_Context::_BindNodeGraph`).
    fn bind(
        &mut self,
        mat: &sdf::Path,
        graph: Option<&'d Graph>,
        input: &Input,
    ) -> Result<Option<sdf::Path>, ReadError> {
        let doc = self.doc;
        let Some(graph_path) = self.graph(graph)? else {
            return Ok(None);
        };
        let referencing = mat.append_child(graph_path.name().unwrap_or_default())?;
        // A shader node of the material may have the name already.
        if !self.claim(&referencing, graph.map_or("the document's node graph", |g| &g.name)) {
            return Ok(None);
        }
        self.prim(&referencing, "").reference.get_or_insert(graph_path);
        let outputs = outputs_of(doc, graph);
        if let Some(output) = input.output.as_deref().filter(|o| outputs.iter().any(|x| x.name == *o)) {
            return Ok(Some(referencing.append_property(output_name(output))?));
        }
        let Some(nodename) = input.nodename.as_deref() else {
            self.warn(format!(
                "{}: no output {} to read",
                input.name,
                input.output.as_deref().unwrap_or_default()
            ));
            return Ok(None);
        };
        self.source(&referencing, graph, nodename, input.output.as_deref(), &input.name)
    }

    /// The prim path of `graph` (the document's own nodes for `None`), built
    /// on first use (C++ `_NodeGraphBuilder::Build`), or `None` for a node
    /// graph whose USD name another has.
    fn graph(&mut self, graph: Option<&'d Graph>) -> Result<Option<sdf::Path>, ReadError> {
        let doc = self.doc;
        let key = graph.map(|g| g.name.as_str());
        if let Some((path, _)) = self.graphs.get(&key) {
            return Ok(Some(path.clone()));
        }
        let path = match graph {
            Some(g) => {
                let path = self.node_graphs.append_child(make_name(&g.name))?;
                if !self.claim(&path, &g.name) {
                    return Ok(None);
                }
                path
            }
            None => self.node_graphs.clone(),
        };
        self.prim(&path, "NodeGraph");
        // A node whose USD name an earlier one has is left out before any
        // connection is made. A connection naming it then finds no node,
        // where it would have read the earlier one.
        let mut nodes = Vec::new();
        for node in nodes_of(doc, graph) {
            if self.claim(&path.append_child(make_name(&node.name))?, &node.name) {
                nodes.push(node);
            }
        }
        self.graphs.insert(key, (path.clone(), nodes.clone()));
        if let Some(g) = graph {
            self.prim(&path, "").doc.clone_from(&g.doc);
            for input in &g.inputs {
                self.input(&path, None, input, None, graph);
                self.ui(&path, input);
            }
        }
        for node in nodes {
            self.graph_node(&path, node, graph)?;
        }
        for output in outputs_of(doc, graph) {
            let source = match output.nodename.as_deref() {
                Some(upstream) => self.source(&path, graph, upstream, output.output.as_deref(), &output.name)?,
                None => None,
            };
            let attr = self.output(&path, &output.name, &output.type_name);
            attr.connect = source;
            attr.doc.clone_from(&output.doc);
        }
        Ok(Some(path))
    }

    /// A node of `graph` (the document's own nodes for `None`), whose prim
    /// is at `parent` (C++ `_NodeGraphBuilder::_AddNode`).
    fn graph_node(&mut self, parent: &sdf::Path, node: &'d Node, graph: Option<&'d Graph>) -> Result<(), ReadError> {
        let path = parent.append_child(make_name(&node.name))?;
        let def = self.nodedef(node, "written with no info:id");
        self.prim(&path, "Shader").doc.clone_from(&node.doc);
        if let Some(def) = def {
            self.token(&path, "info:id")
                .uniform_value(vt::Value::token(def.name.clone()));
        }
        for input in &node.inputs {
            self.input(&path, Some(node), input, def, graph);
            self.ui(&path, input);
            let from = format!("{}.{}", node.name, input.name);
            if let Some(read) = &input.nodegraph {
                self.warn(format!(
                    "{from}: a node graph ({read}) read inside a node graph is not translated"
                ));
            }
            let source = if let Some(interface) = &input.interfacename {
                if graph.is_some_and(|g| g.inputs.iter().any(|i| i.name == *interface)) {
                    Some(parent.append_property(input_name(interface))?)
                } else {
                    self.warn(format!("{from}: no interface input {interface}"));
                    None
                }
            } else if let Some(upstream) = &input.nodename {
                self.source(parent, graph, upstream, input.output.as_deref(), &from)?
            } else {
                None
            };
            if source.is_some() {
                self.attr(&path, &input_name(&input.name), &input.type_name).connect = source;
            }
        }
        for (output, ty) in def.iter().flat_map(|d| &d.outputs) {
            self.output(&path, output, ty);
        }
        Ok(())
    }

    /// The output the MaterialX element at `path` calls `name`, declared
    /// with the type `mtype` unless it already is: a `token` for a shader
    /// type (C++ `_NodeGraphBuilder::_AddOutput`).
    fn output(&mut self, path: &sdf::Path, name: &str, mtype: &str) -> &mut Attr {
        let name = output_name(name);
        match shader_output(mtype) {
            Some(_) => self.token(path, &name),
            None => self.attr(path, &name, mtype),
        }
    }

    /// Declares `input` on the prim at `path`, with the value it authors,
    /// its colour space where that is to be written, and its documentation
    /// (C++ `_Context::_AddInputWithValue`). `node` is the node the input is
    /// on, `None` for a node graph's interface input, and `graph` the node
    /// graph it is in. A value that is none
    /// of the type the attribute is declared with, which the nodedef of a
    /// shader node decides, is left out. Its `channels` and `member` have no
    /// counterpart, which C++ warns of where it connects the input.
    fn input(
        &mut self,
        path: &sdf::Path,
        node: Option<&Node>,
        input: &Input,
        def: Option<&NodeDef>,
        graph: Option<&Graph>,
    ) {
        // TODO: author a `valuecurve` over its `valuerange` as time samples
        // (C++ `_CopyValue`).
        let dropped = [
            ("channels", &input.channels),
            ("member", &input.member),
            ("valuecurve", &input.valuecurve),
        ];
        for (what, dropped) in dropped {
            if let Some(dropped) = dropped {
                self.warn(format!("{}: its {what} {dropped} is not translated", input.name));
            }
        }
        let value = input
            .value
            .as_deref()
            .and_then(|text| self.value_text(text, input, node, graph));
        let color_space = self.colorspace(node, input, def, graph);
        let attr = self.attr(path, &input_name(&input.name), &input.type_name);
        let declared = attr.type_name;
        if declared != usd_type(&input.type_name).0 {
            if value.is_some() {
                self.warn(format!(
                    "{}: its {} value is left out of an input declared {declared}",
                    input.name, input.type_name
                ));
            }
            return;
        }
        if value.is_some() {
            attr.value = value;
        }
        if color_space.is_some() {
            attr.color_space = color_space;
        }
        if input.doc.is_some() {
            attr.doc.clone_from(&input.doc);
        }
    }

    /// The metadata an interface shows `input` with, on its attribute of the
    /// prim at `path` (C++ `_SetUIAttributes`): its `helptext` as the
    /// documentation where it has no `doc`, its `enum` as the allowed
    /// tokens, its `uifolder` as the display group and its `uiname` as the
    /// display name.
    fn ui(&mut self, path: &sdf::Path, input: &Input) {
        let attr = self.attr(path, &input_name(&input.name), &input.type_name);
        if attr.doc.is_none() {
            attr.doc.clone_from(&input.helptext);
        }
        attr.allowed_tokens.clone_from(&input.enums);
        attr.display_group = input.uifolder.as_deref().map(|folder| folder.replace('/', ":"));
        attr.display_name.clone_from(&input.uiname);
    }

    /// The value `text` that `input` authors, a `filename` with its
    /// effective `fileprefix` folded in (MaterialX `flattenFilenames`).
    fn value_text(
        &mut self,
        text: &str,
        input: &Input,
        node: Option<&Node>,
        graph: Option<&Graph>,
    ) -> Option<vt::Value> {
        let doc = self.doc;
        let mtype = input.type_name.as_str();
        let prefixed;
        let text = if mtype == "filename" {
            let prefix = input
                .fileprefix
                .as_deref()
                .or_else(|| node.and_then(|n| n.fileprefix.as_deref()))
                .or_else(|| graph.and_then(|g| g.fileprefix.as_deref()))
                .or(doc.fileprefix.as_deref())
                .unwrap_or_default();
            prefixed = document::with_prefix(prefix, text);
            prefixed.as_str()
        } else {
            text
        };
        let value = parse_value(text, mtype);
        if value.is_none() && !text.is_empty() {
            self.warn(format!("{}: {text:?} is not a {mtype} value", input.name));
        }
        value
    }

    /// The colour space to write on `input` of `node`: its effective one,
    /// where that differs from the document's (C++ `_SetColorSpace`), on the
    /// inputs that carry one: colours, and the file of an image with a
    /// colour output (C++ `_TypeSupportsColorSpace`).
    fn colorspace(
        &self,
        node: Option<&Node>,
        input: &Input,
        def: Option<&NodeDef>,
        graph: Option<&Graph>,
    ) -> Option<String> {
        let colour = |t: &str| t == "color3" || t == "color4";
        let carries = colour(&input.type_name)
            || (input.type_name == "filename" && def.is_some_and(|d| d.outputs.iter().any(|(_, t)| colour(t))));
        if !carries {
            return None;
        }
        let document = self.doc.colorspace.as_deref();
        input
            .colorspace
            .as_deref()
            .or_else(|| node.and_then(|n| n.colorspace.as_deref()))
            .or_else(|| graph.and_then(|g| g.colorspace.as_deref()))
            .or(document)
            .filter(|space| !space.is_empty() && Some(*space) != document)
            .map(str::to_owned)
    }

    /// The collected prims as layer data.
    fn author(self) -> Result<sdf::Data, ReadError> {
        let doc = self.doc;
        let mut data = sdf::Data::rooted();
        let root = sdf::Path::abs_root();
        let filled = |text: &'d Option<String>| text.as_deref().filter(|text| !text.is_empty());
        if let Some(cms) = filled(&doc.cms) {
            sdf::AbstractData::set_field(
                &mut data,
                &root,
                sdf::FieldKey::ColorManagementSystem.as_str(),
                vt::Value::token(cms),
            );
        }
        if let Some(config) = filled(&doc.cmsconfig) {
            sdf::AbstractData::set_field(
                &mut data,
                &root,
                sdf::FieldKey::ColorConfiguration.as_str(),
                vt::Value::AssetPath(sdf::AssetPath::new(config)),
            );
        }
        let mut entries = Vec::new();
        if let Some(space) = filled(&doc.colorspace) {
            entries.push(("colorSpace".to_owned(), vt::Value::String(space.to_owned())));
        }
        if !self.warnings.is_empty() {
            let mtlx: vt::Dictionary = [("warnings".to_owned(), vt::Value::StringVec(self.warnings))].into();
            entries.push(("mtlx".to_owned(), vt::Value::Dictionary(mtlx)));
        }
        if !entries.is_empty() {
            let layer_data: vt::Dictionary = entries.into_iter().collect();
            sdf::AbstractData::set_field(
                &mut data,
                &root,
                sdf::FieldKey::CustomLayerData.as_str(),
                vt::Value::Dictionary(layer_data),
            );
        }
        for prim in &self.prims {
            let mut spec = sdf::PrimSpec::new(&mut data, &prim.path, sdf::Specifier::Def, prim.type_name)?;
            for schema in &prim.api_schemas {
                spec.add_applied_schema(*schema)?;
            }
            if let Some(doc) = &prim.doc {
                spec.set(sdf::FieldKey::Documentation.as_str(), vt::Value::String(doc.clone()));
            }
            if let Some(target) = &prim.reference {
                let reference = sdf::Reference {
                    prim_path: target.clone(),
                    ..sdf::Reference::default()
                };
                spec.edit_list::<sdf::Reference, _>(sdf::FieldKey::References, |op| op.prepend(reference))?;
            }
            if let Some(base) = &prim.specializes {
                spec.edit_specializes().prepend(base)?;
            }
            for (name, attr) in &prim.attrs {
                let variability = match attr.uniform {
                    true => sdf::Variability::Uniform,
                    false => sdf::Variability::Varying,
                };
                let path = prim.path.append_property(name)?;
                let mut spec = sdf::AttributeSpec::new(&mut data, &path, attr.type_name, variability, false)?;
                if let Some(value) = &attr.value {
                    spec.set_default(value.clone())?;
                }
                if let Some(space) = &attr.color_space {
                    spec.set_color_space(space.as_str());
                }
                if let Some(render_type) = &attr.render_type {
                    spec.set("renderType", vt::Value::token(render_type.as_str()));
                }
                let text = [
                    (sdf::FieldKey::Documentation, &attr.doc),
                    (sdf::FieldKey::DisplayName, &attr.display_name),
                    (sdf::FieldKey::DisplayGroup, &attr.display_group),
                ];
                for (key, text) in text {
                    if let Some(text) = text {
                        spec.set(key.as_str(), vt::Value::String(text.clone()));
                    }
                }
                if !attr.allowed_tokens.is_empty() {
                    spec.set_allowed_tokens(&attr.allowed_tokens);
                }
                if let Some(source) = &attr.connect {
                    spec.edit_connections().set([source])?;
                }
            }
        }
        Ok(data)
    }
}

impl Attr {
    /// A uniform attribute holding `value`.
    fn uniform_value(&mut self, value: vt::Value) {
        self.uniform = true;
        self.value = Some(value);
    }
}

/// The name of the output a shader of the MaterialX type `mtype` has, for a
/// shader type (C++ `_AddShaderOutput`).
fn shader_output(mtype: &str) -> Option<&'static str> {
    SHADER_TYPES
        .iter()
        .find(|(shader_type, ..)| *shader_type == mtype)
        .map(|&(_, output, _)| output)
}

/// The property name of the input a MaterialX element calls `name`.
// TODO: two ports of one element whose names make one USD name (`ns:gain`
// and `ns__gain`) share a property; keep the first and report the second, as
// `Context::claim` does for prims.
fn input_name(name: &str) -> String {
    format!("inputs:{}", make_name(name))
}

/// The property name of the output a MaterialX element calls `name`.
fn output_name(name: &str) -> String {
    format!("outputs:{}", make_name(name))
}

/// The USD value type of the MaterialX type `mtype` (C++
/// `UsdMtlxGetUsdType`), and the MaterialX type as the render type where USD
/// has none and the attribute is a `token`.
fn usd_type(mtype: &str) -> (&'static str, Option<String>) {
    let ty = match mtype {
        "boolean" => "bool",
        "integer" => "int",
        "float" => "float",
        "string" | "geomname" => "string",
        "filename" => "asset",
        "color3" => "color3f",
        "color4" => "color4f",
        "vector2" => "float2",
        "vector3" => "float3",
        "vector4" => "float4",
        "matrix33" => "matrix3d",
        "matrix44" => "matrix4d",
        "integerarray" => "int[]",
        "floatarray" => "float[]",
        "stringarray" | "geomnamearray" => "string[]",
        "color3array" => "color3f[]",
        "color4array" => "color4f[]",
        "vector2array" => "float2[]",
        "vector3array" => "float3[]",
        "vector4array" => "float4[]",
        "surfaceshader" => "token",
        other => return ("token", Some(other.to_owned())),
    };
    (ty, None)
}

/// The nodes of `graph`, or for `None` those of the document's own node
/// graph: the nodes at its level but for its materials and surface shaders,
/// which a material translates itself.
fn nodes_of<'d>(doc: &'d Document, graph: Option<&'d Graph>) -> Vec<&'d Node> {
    match graph {
        Some(graph) => graph.nodes.iter().collect(),
        None => doc
            .nodes
            .iter()
            .filter(|n| n.type_name != "material" && n.type_name != "surfaceshader")
            .collect(),
    }
}

/// The outputs of `graph`, or for `None` those at the document's own level.
fn outputs_of<'d>(doc: &'d Document, graph: Option<&'d Graph>) -> &'d [Output] {
    match graph {
        Some(graph) => &graph.outputs,
        None => &doc.outputs,
    }
}

/// The number `text` starts with, after any spaces, as a C++ stream
/// extracts one: whatever follows the number is left unread.
fn leading<T: FromStr>(text: &str) -> Option<T> {
    let text = text.trim_start();
    let numeric = |c: char| c.is_ascii_digit() || matches!(c, '+' | '-' | '.' | 'e' | 'E');
    let end = text.find(|c| !numeric(c)).unwrap_or(text.len());
    (1..=end).rev().find_map(|len| text[..len].parse().ok())
}

/// The integer `text` starts with, after any spaces: a sign and the digits
/// that follow it, whatever comes after left unread. `None` for one an
/// `int` cannot hold.
fn leading_int(text: &str) -> Option<i32> {
    let text = text.trim_start();
    let digits = text.strip_prefix(['+', '-']).unwrap_or(text);
    let end = digits.find(|c: char| !c.is_ascii_digit()).unwrap_or(digits.len());
    text[..text.len() - digits.len() + end].parse().ok()
}

/// `text` as a value of the MaterialX type `mtype`, or `None` when it is not
/// one (MaterialX `fromValueString`): the components of a vector or matrix
/// are set apart by commas or spaces, the elements of an array by commas.
fn parse_value(text: &str, mtype: &str) -> Option<vt::Value> {
    /// The `N` components `text` holds, and no other number of them.
    fn components<const N: usize>(text: &str) -> Option<[f32; N]> {
        let v: Vec<f32> = text
            .split([',', ' '])
            .filter(|s| !s.is_empty())
            .map(leading)
            .collect::<Option<_>>()?;
        v.try_into().ok()
    }
    let elements = || text.split(',').filter(|s| !s.is_empty()).map(str::trim);
    let floats = || -> Option<Vec<f32>> { elements().map(leading).collect() };
    /// `floats` as elements of `N` components each, none left over.
    fn chunks<const N: usize, T: From<[f32; N]>>(floats: Vec<f32>) -> Option<Vec<T>> {
        let (chunks, rest) = floats.as_chunks::<N>();
        rest.is_empty()
            .then(|| chunks.iter().map(|&chunk| T::from(chunk)).collect())
    }
    Some(match mtype {
        "float" => vt::Value::Float(leading(text)?),
        "integer" => vt::Value::Int(leading_int(text)?),
        "boolean" => vt::Value::Bool(match text.trim() {
            "true" => true,
            "false" => false,
            _ => return None,
        }),
        "string" | "geomname" => vt::Value::String(text.to_owned()),
        "filename" => vt::Value::AssetPath(sdf::AssetPath::new(text)),
        "color3" | "vector3" => vt::Value::Vec3f(components::<3>(text)?.into()),
        "color4" | "vector4" => vt::Value::Vec4f(components::<4>(text)?.into()),
        "vector2" => vt::Value::Vec2f(components::<2>(text)?.into()),
        // A matrix is read in single precision, as MaterialX holds one, and
        // widened for the `matrix3d` or `matrix4d` C++ writes.
        "matrix33" => vt::Value::Matrix3d(gf::Mat3d(components::<9>(text)?.map(f64::from))),
        "matrix44" => vt::Value::Matrix4d(gf::Mat4d(components::<16>(text)?.map(f64::from))),
        "floatarray" => vt::Value::FloatVec(floats()?),
        "integerarray" => vt::Value::IntVec(elements().map(leading_int).collect::<Option<_>>()?),
        "stringarray" | "geomnamearray" => vt::Value::StringVec(elements().map(str::to_owned).collect()),
        "color3array" | "vector3array" => vt::Value::Vec3fVec(chunks::<3, _>(floats()?)?),
        "color4array" | "vector4array" => vt::Value::Vec4fVec(chunks::<4, _>(floats()?)?),
        "vector2array" => vt::Value::Vec2fVec(chunks::<2, _>(floats()?)?),
        _ => return None,
    })
}

/// A MaterialX element name as a USD name (C++ `_MakeName`): the colon
/// after a MaterialX namespace as `__`. A name that is still no identifier
/// has each character an identifier cannot hold, and a leading digit, as an
/// underscore, where C++ fails to create the prim.
fn make_name(name: &str) -> String {
    let name = name.replace(':', "__");
    if sdf::Path::is_valid_identifier(&name) {
        return name;
    }
    let mut out: String = name
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    if out.is_empty() || out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

#[cfg(test)]
mod tests {
    use openusd::usda;

    use super::*;

    /// The layer `text` translates into, as `usda`.
    fn translated(text: &str) -> String {
        let doc = document::parse(text, "t", &mut |_| Ok(document::Included::Unfound)).expect("parses");
        let data = translate(&doc).expect("translates");
        let mut out = Vec::new();
        usda::TextWriter::write(&data, &mut out).expect("writes");
        String::from_utf8(out).expect("utf-8")
    }

    #[test]
    fn values_parse() {
        assert_eq!(parse_value("0.5", "float"), Some(vt::Value::Float(0.5)));
        assert_eq!(
            parse_value("1, 0, 0.25", "color3"),
            Some(vt::Value::Vec3f(gf::Vec3f::from([1.0, 0.0, 0.25])))
        );
        assert_eq!(parse_value("true", "boolean"), Some(vt::Value::Bool(true)));
        assert_eq!(parse_value("fast", "float"), None);
        // A matrix component is a single-precision number, widened.
        assert_eq!(
            parse_value("0.1, 0, 0, 0, 1, 0, 0, 0, 1", "matrix33"),
            Some(vt::Value::Matrix3d(gf::Mat3d([
                f64::from(0.1f32),
                0.0,
                0.0,
                0.0,
                1.0,
                0.0,
                0.0,
                0.0,
                1.0
            ])))
        );
        // Spaces set components apart as commas do, and a number ends where
        // it stops being one.
        assert_eq!(
            parse_value("0.5 0.5", "vector2"),
            Some(vt::Value::Vec2f(gf::Vec2f::from([0.5, 0.5])))
        );
        assert_eq!(
            parse_value("1,2,3,", "vector3"),
            Some(vt::Value::Vec3f(gf::Vec3f::from([1.0, 2.0, 3.0])))
        );
        assert_eq!(parse_value("1.5f", "float"), Some(vt::Value::Float(1.5)));
        assert_eq!(parse_value("7.5", "integer"), Some(vt::Value::Int(7)));
        assert_eq!(parse_value("-2147483648", "integer"), Some(vt::Value::Int(i32::MIN)));
        assert_eq!(parse_value("2147483648", "integer"), None);
        assert_eq!(
            parse_value("a b, c", "stringarray"),
            Some(vt::Value::StringVec(vec!["a b".into(), "c".into()]))
        );
        assert_eq!(parse_value("1, 2", "vector3"), None);
    }

    #[test]
    fn names_made_valid() {
        assert_eq!(make_name("node_1"), "node_1");
        assert_eq!(make_name("ns:node"), "ns__node");
        assert_eq!(make_name("1node"), "_1node");
        assert_eq!(make_name("a-b.c"), "a_b_c");
    }

    #[test]
    fn closures_are_render_types() {
        assert_eq!(usd_type("BSDF"), ("token", Some("BSDF".to_owned())));
        assert_eq!(usd_type("surfaceshader"), ("token", None));
        assert_eq!(
            usd_type("displacementshader"),
            ("token", Some("displacementshader".to_owned()))
        );
        assert_eq!(usd_type("vector2"), ("float2", None));
    }

    /// A value of another type than the nodedef's input opens the layer
    /// without it, an empty value is no value, and a surface shader read by
    /// another is no node of the document's graph: each is reported.
    #[test]
    fn mismatches_reported() {
        let text = translated(
            r#"<materialx version="1.39" fileprefix="textures/">
                 <standard_surface name="under" type="surfaceshader" />
                 <image name="i" type="color3"><input name="file" type="filename" value="" /></image>
                 <open_pbr_surface name="s" type="surfaceshader">
                   <input name="geometry_opacity" type="color3" value="1, 1, 1" />
                   <input name="base_color" type="color3" nodename="i" />
                   <input name="geometry_coat_normal" type="vector3" nodename="under" />
                 </open_pbr_surface>
                 <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s" /></surfacematerial>
               </materialx>"#,
        );
        assert!(
            text.contains(
                "float inputs:geometry_opacity
"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "asset inputs:file
"
            ),
            "{text}"
        );
        assert!(!text.contains("NodeGraphs/under"), "{text}");
        for warning in [
            "geometry_opacity: its color3 value is left out of an input declared float",
            "geometry_coat_normal: no node under",
        ] {
            assert!(
                text.contains(warning),
                "no {warning} in:
{text}"
            );
        }
    }

    /// Two nodes whose names make one USD name are one prim, the first
    /// node's, and the second is reported.
    #[test]
    fn name_collision_reported() {
        let text = translated(
            r#"<materialx version="1.39">
                 <nodegraph name="g">
                   <constant name="ns:c" type="float"><input name="value" type="float" value="1" /></constant>
                   <constant name="ns__c" type="float"><input name="value" type="float" value="2" /></constant>
                   <output name="out" type="float" nodename="ns:c" />
                   <output name="other" type="float" nodename="ns__c" />
                 </nodegraph>
                 <standard_surface name="s" type="surfaceshader"><input name="base" type="float" nodegraph="g" output="out" /></standard_surface>
                 <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s" /></surfacematerial>
               </materialx>"#,
        );
        assert!(text.contains("float inputs:value = 1"), "{text}");
        assert!(!text.contains("float inputs:value = 2"), "{text}");
        // The output naming the node left out reads nothing.
        assert!(text.contains("float outputs:other\n"), "{text}");
        assert!(text.contains("other: no node ns__c"), "{text}");
        assert!(
            text.contains("ns__c: not translated, its USD name is that of ns:c"),
            "{text}"
        );
    }

    /// A document with no material is a layer with no prim.
    #[test]
    fn empty_document() {
        let text = translated(r#"<materialx version="1.39"><constant name="c" type="float" /></materialx>"#);
        assert!(!text.contains("def "), "{text}");
    }
}
