//! The translation of a [`Document`] into `UsdShade` specs (C++ `usdMtlx`'s
//! `reader.cpp`).
//!
//! Prims and properties are collected first, as the reader's `_Context`
//! creates them, and authored once at the end, so each attribute is declared
//! with its type, value, metadata and connection together.

use std::collections::{BTreeMap, HashMap};

use openusd::{gf, sdf, vt};

use crate::document::{Document, Graph, Input, Node, Output, ReadError};
use crate::nodedefs::{self, Library, Match, NodeDef};

/// Where the layer roots everything (C++ `usdMtlx`'s internal path).
const ROOT: &str = "/MaterialX";
const MATERIALS: &str = "/MaterialX/Materials";
const SHADERS: &str = "/MaterialX/Shaders";
const NODE_GRAPHS: &str = "/MaterialX/NodeGraphs";

/// The shader types a material's terminals read, with the terminal each
/// drives (`outputs:mtlx:<terminal>`). A light shader has no USD terminal.
const SHADER_TYPES: &[(&str, Option<&str>)] = &[
    ("surfaceshader", Some("surface")),
    ("volumeshader", Some("volume")),
    ("displacementshader", Some("displacement")),
    ("lightshader", None),
];

/// The layer `doc` translates into.
pub(crate) fn translate(doc: &Document) -> Result<sdf::Data, ReadError> {
    let mut cx = Context {
        doc,
        local: Library::local(doc.nodedefs.clone()),
        prims: Vec::new(),
        index: HashMap::new(),
        graphs: HashMap::new(),
        warnings: doc.skipped.clone(),
    };
    cx.prim(ROOT, "");
    cx.prim(MATERIALS, "");
    for graph in doc.graphs.iter().filter(|g| g.nodedef.is_some()) {
        cx.warn(format!(
            "{}: the node graph implementing {} is not translated, so its custom node is not",
            graph.name,
            graph.nodedef.as_deref().unwrap_or_default()
        ));
    }
    for material in doc.nodes.iter().filter(|n| n.type_name == "material") {
        cx.material(material);
    }
    cx.author()
}

/// The prims collected so far, in creation order, and the state the
/// translation keeps across materials.
struct Context<'d> {
    doc: &'d Document,
    /// The document's own nodedefs.
    local: Library,
    prims: Vec<Prim>,
    /// Prim path → its index in `prims`.
    index: HashMap<String, usize>,
    /// Node graph (`None` for the document's own nodes) → its prim path,
    /// once built.
    graphs: HashMap<Option<String>, String>,
    warnings: Vec<String>,
}

/// A prim to author.
#[derive(Debug, Default)]
struct Prim {
    path: String,
    type_name: &'static str,
    api_schemas: Vec<&'static str>,
    /// The prim it internally references.
    reference: Option<String>,
    /// Property name → the attribute, authored in name order.
    attrs: BTreeMap<String, Attr>,
}

/// An attribute to author.
#[derive(Debug, Default)]
struct Attr {
    type_name: String,
    uniform: bool,
    value: Option<vt::Value>,
    connect: Option<String>,
    /// The MaterialX type of a value USD has no type for (`BSDF`).
    render_type: Option<String>,
    color_space: Option<String>,
}

/// The scope a node sits in, for the attributes it inherits.
#[derive(Clone, Copy)]
struct Scope<'d> {
    graph: Option<&'d Graph>,
}

impl<'d> Context<'d> {
    /// The prim at `path`, created as a `def` of `type_name` if it is not yet;
    /// an untyped prim takes a type given later.
    fn prim(&mut self, path: &str, type_name: &'static str) -> &mut Prim {
        let i = if let Some(&i) = self.index.get(path) {
            i
        } else {
            self.prims.push(Prim {
                path: path.to_owned(),
                ..Prim::default()
            });
            self.index.insert(path.to_owned(), self.prims.len() - 1);
            self.prims.len() - 1
        };
        let prim = &mut self.prims[i];
        if prim.type_name.is_empty() {
            prim.type_name = type_name;
        }
        prim
    }

    fn has_prim(&self, path: &str) -> bool {
        self.index.contains_key(path)
    }

    /// The attribute `name` of the prim at `path`, declared with the
    /// MaterialX type `mtype` unless it already is.
    fn attr(&mut self, path: &str, name: &str, mtype: &str) -> &mut Attr {
        let prim = self.prim(path, "");
        prim.attrs.entry(name.to_owned()).or_insert_with(|| {
            let (type_name, render_type) = usd_type(mtype);
            Attr {
                type_name: type_name.to_owned(),
                render_type,
                ..Attr::default()
            }
        })
    }

    fn warn(&mut self, warning: String) {
        if !self.warnings.contains(&warning) {
            self.warnings.push(warning);
        }
    }

    /// The nodedef `node` instantiates, with a warning where none matches
    /// exactly (C++ writes such a node with no `info:id`).
    fn nodedef(&mut self, node: &Node) -> Option<NodeDef> {
        let (def, exact) = match nodedefs::find(&self.local, node) {
            Some(Match::Exact(def)) => (def.clone(), true),
            Some(Match::Closest(def)) => (def.clone(), false),
            None => {
                self.warn(format!(
                    "{}: no {} nodedef of type {}; written with no info:id",
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

    /// The output of `node` a connection naming `output` reads: that one, or
    /// the node's only output whatever its name.
    fn output_of(&self, node: &Node, output: Option<&str>) -> String {
        match output {
            Some(output) => output.to_owned(),
            None => match nodedefs::find(&self.local, node) {
                Some(Match::Exact(def) | Match::Closest(def)) => def.default_output().to_owned(),
                None => "out".to_owned(),
            },
        }
    }

    /// A material node: its `Material` and the shader nodes its inputs read
    /// (C++ `_Context::BeginMaterial` and `_TranslateShaderNodes`).
    fn material(&mut self, material: &'d Node) {
        let doc = self.doc;
        let path = format!("{MATERIALS}/{}", make_name(&material.name));
        self.prim(&path, "Material").api_schemas.push("MaterialXConfigAPI");
        self.attr(&path, "config:mtlx:version", "string").value = Some(vt::Value::String(doc.version.clone()));
        for &(shader_type, terminal) in SHADER_TYPES {
            let mut seen: Vec<&str> = Vec::new();
            for input in &material.inputs {
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
                    self.shader_node(&path, node, terminal);
                }
            }
        }
    }

    /// A shader node of the material at `mat` (C++ `_Context::AddShaderNode`).
    fn shader_node(&mut self, mat: &str, node: &'d Node, terminal: Option<&str>) {
        let doc = self.doc;
        let Some(def) = self.nodedef(node) else {
            return;
        };
        let name = make_name(&node.name);
        let implementation = format!("{SHADERS}/{name}");
        if !self.has_prim(&implementation) {
            self.prim(SHADERS, "");
            self.prim(&implementation, "Shader");
            self.attr(&implementation, "info:id", "token")
                .uniform_value(vt::Value::token(def.name.clone()));
            for (output, ty) in &def.outputs {
                let (output, mtype) = shader_output(output, ty);
                self.attr(&implementation, &format!("outputs:{output}"), mtype);
            }
        }
        let shader = format!("{mat}/{name}");
        self.prim(&shader, "Shader").reference = Some(implementation);
        // Every nodedef input is an interface input of the material, which
        // the shader's input reads.
        for (input, ty) in &def.inputs {
            self.attr(mat, &format!("inputs:{input}"), ty);
            self.attr(&shader, &format!("inputs:{input}"), ty).connect = Some(format!("{mat}.inputs:{input}"));
        }
        let scope = Scope { graph: None };
        for input in &node.inputs {
            self.value(mat, node, input, Some(&def), scope);
            let source = match (&input.nodegraph, &input.output, &input.nodename) {
                (Some(graph), Some(_), _) => {
                    if let Some(graph) = doc.graph(graph) {
                        self.bind(mat, Some(graph), input)
                    } else {
                        self.warn(format!("{}.{}: no node graph {graph}", node.name, input.name));
                        None
                    }
                }
                (None, Some(_), _) | (_, None, Some(_)) => self.bind(mat, None, input),
                _ => None,
            };
            if let Some(source) = source {
                self.attr(&shader, &format!("inputs:{}", input.name), &input.type_name)
                    .connect = Some(source);
            }
        }
        // The shader's terminal output drives the material's.
        if let Some(terminal) = terminal
            && def
                .outputs
                .iter()
                .any(|(output, ty)| shader_output(output, ty).0 == terminal)
        {
            self.attr(mat, &format!("outputs:mtlx:{terminal}"), "token").connect =
                Some(format!("{shader}.outputs:{terminal}"));
        }
    }

    /// Brings `graph` (the document's own nodes for `None`) under the
    /// material at `mat` and returns the output `input` reads of it (C++
    /// `_Context::_BindNodeGraph`).
    fn bind(&mut self, mat: &str, graph: Option<&'d Graph>, input: &Input) -> Option<String> {
        let doc = self.doc;
        let graph_path = self.graph(graph)?;
        let leaf = graph_path.rsplit('/').next().unwrap_or_default();
        let referencing = format!("{mat}/{leaf}");
        self.prim(&referencing, "").reference.get_or_insert(graph_path.clone());
        let (nodes, outputs) = match graph {
            Some(g) => (&g.nodes, &g.outputs),
            None => (&doc.nodes, &doc.outputs),
        };
        if let Some(output) = input.output.as_deref().filter(|o| outputs.iter().any(|x| x.name == *o)) {
            return Some(format!("{referencing}.outputs:{output}"));
        }
        let nodename = input.nodename.as_deref()?;
        let Some(upstream) = nodes.iter().find(|n| n.name == nodename) else {
            self.warn(format!("{}: no node {nodename}", input.name));
            return None;
        };
        let output = self.output_of(upstream, input.output.as_deref());
        Some(format!("{referencing}/{}.outputs:{output}", make_name(nodename)))
    }

    /// The prim path of `graph` (the document's own nodes for `None`), built
    /// on first use (C++ `_NodeGraphBuilder::Build`).
    fn graph(&mut self, graph: Option<&'d Graph>) -> Option<String> {
        let doc = self.doc;
        let key = graph.map(|g| g.name.clone());
        if let Some(path) = self.graphs.get(&key) {
            return Some(path.clone());
        }
        let path = match graph {
            Some(g) => {
                self.prim(NODE_GRAPHS, "");
                format!("{NODE_GRAPHS}/{}", make_name(&g.name))
            }
            None => NODE_GRAPHS.to_owned(),
        };
        self.graphs.insert(key, path.clone());
        self.prim(&path, "NodeGraph");
        let scope = Scope { graph };
        let (nodes, outputs): (Vec<&'d Node>, &'d [Output]) = match graph {
            Some(g) => {
                for input in &g.inputs {
                    let value = match &input.value {
                        Some(text) => self.value_text(text, &input.type_name, input, None, scope),
                        None => None,
                    };
                    self.attr(&path, &format!("inputs:{}", input.name), &input.type_name)
                        .value = value;
                }
                (g.nodes.iter().collect(), &g.outputs)
            }
            // The document's own nodes, but for its materials and surface
            // shaders, which a material translates itself.
            None => (
                doc.nodes
                    .iter()
                    .filter(|n| n.type_name != "material" && n.type_name != "surfaceshader")
                    .collect(),
                &doc.outputs,
            ),
        };
        for node in &nodes {
            self.graph_node(&path, node, &nodes, scope);
        }
        for output in outputs {
            let source = output
                .nodename
                .as_deref()
                .and_then(|n| nodes.iter().find(|x| x.name == n))
                .map(|n| {
                    let out = self.output_of(n, output.output.as_deref());
                    format!("{path}/{}.outputs:{out}", make_name(&n.name))
                });
            let (_, mtype) = shader_output(&output.name, &output.type_name);
            self.attr(&path, &format!("outputs:{}", output.name), mtype).connect = source;
        }
        Some(path)
    }

    /// A node of the node graph at `graph`, among `siblings` (C++
    /// `_NodeGraphBuilder::_AddNode`).
    fn graph_node(&mut self, graph: &str, node: &'d Node, siblings: &[&'d Node], scope: Scope<'d>) {
        let def = self.nodedef(node);
        let path = format!("{graph}/{}", make_name(&node.name));
        self.prim(&path, "Shader");
        if let Some(def) = &def {
            self.attr(&path, "info:id", "token")
                .uniform_value(vt::Value::token(def.name.clone()));
        }
        for input in &node.inputs {
            let name = format!("inputs:{}", input.name);
            self.attr(&path, &name, &input.type_name);
            self.value(&path, node, input, def.as_ref(), scope);
            let source = if let Some(interface) = &input.interfacename {
                Some(format!("{graph}.inputs:{interface}"))
            } else if let Some(upstream) = &input.nodename {
                if let Some(up) = siblings.iter().find(|n| n.name == *upstream) {
                    let output = self.output_of(up, input.output.as_deref());
                    Some(format!("{graph}/{}.outputs:{output}", make_name(upstream)))
                } else {
                    self.warn(format!("{}.{}: no node {upstream}", node.name, input.name));
                    None
                }
            } else {
                None
            };
            if source.is_some() {
                self.attr(&path, &name, &input.type_name).connect = source;
            }
        }
        for (output, ty) in def.iter().flat_map(|d| &d.outputs) {
            let (_, mtype) = shader_output(output, ty);
            self.attr(&path, &format!("outputs:{output}"), mtype);
        }
    }

    /// `input`'s value, if it authors one, on the prim at `path`, with its
    /// effective colour space where it has one (C++ `_CopyValue`).
    fn value(&mut self, path: &str, node: &Node, input: &Input, def: Option<&NodeDef>, scope: Scope<'d>) {
        let Some(text) = &input.value else {
            return;
        };
        let value = self.value_text(text, &input.type_name, input, Some(node), scope);
        let color_space = self.colorspace(node, input, def, scope);
        let attr = self.attr(path, &format!("inputs:{}", input.name), &input.type_name);
        attr.value = value;
        attr.color_space = color_space;
    }

    /// `text` as a value of the MaterialX type `mtype`, a `filename` with its
    /// effective `fileprefix` folded in (MaterialX `flattenFilenames`).
    fn value_text(
        &mut self,
        text: &str,
        mtype: &str,
        input: &Input,
        node: Option<&Node>,
        scope: Scope<'d>,
    ) -> Option<vt::Value> {
        let doc = self.doc;
        let prefixed;
        let text = if mtype == "filename" {
            let prefix = input
                .fileprefix
                .as_deref()
                .or_else(|| node.and_then(|n| n.fileprefix.as_deref()))
                .or_else(|| scope.graph.and_then(|g| g.fileprefix.as_deref()))
                .or(doc.fileprefix.as_deref())
                .unwrap_or_default();
            prefixed = match prefix.is_empty() || is_absolute(text) {
                true => text.to_owned(),
                false => format!("{prefix}{text}"),
            };
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

    /// The effective colour space of `input` on `node`, on the inputs that
    /// carry one: colours, and the file of an image with a colour output
    /// (C++ `_TypeSupportsColorSpace`). Written wherever it is set, the
    /// document's included, which a reference would otherwise lose.
    fn colorspace(&self, node: &Node, input: &Input, def: Option<&NodeDef>, scope: Scope<'d>) -> Option<String> {
        let colour = |t: &str| t == "color3" || t == "color4";
        let carries = colour(&input.type_name)
            || (input.type_name == "filename" && def.is_some_and(|d| d.outputs.iter().any(|(_, t)| colour(t))));
        if !carries {
            return None;
        }
        input
            .colorspace
            .as_deref()
            .or(node.colorspace.as_deref())
            .or_else(|| scope.graph.and_then(|g| g.colorspace.as_deref()))
            .or(self.doc.colorspace.as_deref())
            .filter(|s| !s.is_empty())
            .map(str::to_owned)
    }

    /// The collected prims as layer data.
    fn author(self) -> Result<sdf::Data, ReadError> {
        let mut data = sdf::Data::rooted();
        let mut entries = Vec::new();
        if let Some(space) = &self.doc.colorspace {
            entries.push(("colorSpace".to_owned(), vt::Value::String(space.clone())));
        }
        if !self.warnings.is_empty() {
            let mtlx: vt::Dictionary = [("warnings".to_owned(), vt::Value::StringVec(self.warnings.clone()))].into();
            entries.push(("mtlx".to_owned(), vt::Value::Dictionary(mtlx)));
        }
        if !entries.is_empty() {
            let layer_data: vt::Dictionary = entries.into_iter().collect();
            sdf::AbstractData::set_field(
                &mut data,
                &sdf::Path::abs_root(),
                sdf::FieldKey::CustomLayerData.as_str(),
                vt::Value::Dictionary(layer_data),
            );
        }
        for prim in &self.prims {
            let mut spec = sdf::PrimSpec::new(&mut data, prim.path.as_str(), sdf::Specifier::Def, prim.type_name)?;
            for schema in &prim.api_schemas {
                spec.add_applied_schema(*schema)?;
            }
            if let Some(target) = &prim.reference {
                let reference = sdf::Reference {
                    prim_path: sdf::Path::new(target)?,
                    ..sdf::Reference::default()
                };
                spec.edit_list::<sdf::Reference, _>(sdf::FieldKey::References, |op| op.prepend(reference))?;
            }
            for (name, attr) in &prim.attrs {
                let variability = match attr.uniform {
                    true => sdf::Variability::Uniform,
                    false => sdf::Variability::Varying,
                };
                let path = format!("{}.{name}", prim.path);
                let mut spec =
                    sdf::AttributeSpec::new(&mut data, path.as_str(), attr.type_name.as_str(), variability, false)?;
                if let Some(value) = &attr.value {
                    spec.set_default(value.clone())?;
                }
                if let Some(space) = &attr.color_space {
                    spec.set_color_space(space.as_str());
                }
                if let Some(render_type) = &attr.render_type {
                    spec.set("renderType", vt::Value::token(render_type.as_str()));
                }
                if let Some(source) = &attr.connect {
                    spec.edit_connections().set([source.as_str()])?;
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

/// The name and MaterialX type of a shader's output declared as `name` of
/// type `mtype`: a shader type's is its terminal, a `token`
/// (C++ `_AddShaderOutput`).
fn shader_output<'a>(name: &'a str, mtype: &'a str) -> (&'a str, &'a str) {
    match SHADER_TYPES.iter().find(|(t, _)| *t == mtype) {
        Some((_, Some(terminal))) => (terminal, "surfaceshader"),
        Some((_, None)) => ("light", "surfaceshader"),
        None => (name, mtype),
    }
}

/// The USD value type of the MaterialX type `mtype` (C++
/// `UsdMtlxGetUsdType`), and the MaterialX type as the render type where USD
/// has none and the attribute is a `token`. A shader type is a `token` with
/// no render type.
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
        "token" | "surfaceshader" | "volumeshader" | "displacementshader" | "lightshader" => "token",
        other => return ("token", Some(other.to_owned())),
    };
    (ty, None)
}

/// `text` as a value of the MaterialX type `mtype`, or `None` when it is not
/// one (C++ `mx::Value::createValueFromStrings`).
fn parse_value(text: &str, mtype: &str) -> Option<vt::Value> {
    let floats = |n: usize| -> Option<Vec<f32>> {
        let v: Vec<f32> = text.split(',').map(|s| s.trim().parse().ok()).collect::<Option<_>>()?;
        (v.len() == n || n == 0).then_some(v)
    };
    let doubles = |n: usize| -> Option<Vec<f64>> {
        let v: Vec<f64> = text.split(',').map(|s| s.trim().parse().ok()).collect::<Option<_>>()?;
        (v.len() == n).then_some(v)
    };
    let chunks = |n: usize| -> Option<Vec<Vec<f32>>> {
        let v = floats(0)?;
        (v.len() % n == 0).then(|| v.chunks(n).map(<[f32]>::to_vec).collect())
    };
    Some(match mtype {
        "float" => vt::Value::Float(text.trim().parse().ok()?),
        "integer" => vt::Value::Int(text.trim().parse().ok()?),
        "boolean" => vt::Value::Bool(match text.trim() {
            "true" => true,
            "false" => false,
            _ => return None,
        }),
        "string" | "geomname" | "token" => vt::Value::String(text.to_owned()),
        "filename" => vt::Value::AssetPath(sdf::AssetPath::new(text)),
        "color3" | "vector3" => {
            let v = floats(3)?;
            vt::Value::Vec3f(gf::Vec3f::from([v[0], v[1], v[2]]))
        }
        "color4" | "vector4" => {
            let v = floats(4)?;
            vt::Value::Vec4f(gf::Vec4f::from([v[0], v[1], v[2], v[3]]))
        }
        "vector2" => {
            let v = floats(2)?;
            vt::Value::Vec2f(gf::Vec2f::from([v[0], v[1]]))
        }
        "matrix33" => vt::Value::Matrix3d(gf::Mat3d(doubles(9)?.try_into().ok()?)),
        "matrix44" => vt::Value::Matrix4d(gf::Mat4d(doubles(16)?.try_into().ok()?)),
        "floatarray" => vt::Value::FloatVec(floats(0)?),
        "integerarray" => vt::Value::IntVec(text.split(',').map(|s| s.trim().parse().ok()).collect::<Option<_>>()?),
        "stringarray" | "geomnamearray" => vt::Value::StringVec(text.split(',').map(|s| s.trim().to_owned()).collect()),
        "color3array" | "vector3array" => vt::Value::Vec3fVec(
            chunks(3)?
                .into_iter()
                .map(|c| gf::Vec3f::from([c[0], c[1], c[2]]))
                .collect(),
        ),
        "color4array" | "vector4array" => vt::Value::Vec4fVec(
            chunks(4)?
                .into_iter()
                .map(|c| gf::Vec4f::from([c[0], c[1], c[2], c[3]]))
                .collect(),
        ),
        "vector2array" => vt::Value::Vec2fVec(chunks(2)?.into_iter().map(|c| gf::Vec2f::from([c[0], c[1]])).collect()),
        _ => return None,
    })
}

/// Whether a `filename` is absolute, so no `fileprefix` applies.
fn is_absolute(text: &str) -> bool {
    text.starts_with('/') || text.starts_with('\\') || text.get(1..3) == Some(":/") || text.get(1..3) == Some(":\\")
}

/// A MaterialX element name as a USD prim name (C++
/// `TfMakeValidIdentifier`): each character an identifier cannot hold, and a
/// leading digit, an underscore.
fn make_name(name: &str) -> String {
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
    use super::*;

    #[test]
    fn values_parse() {
        assert_eq!(parse_value("0.5", "float"), Some(vt::Value::Float(0.5)));
        assert_eq!(
            parse_value("1, 0, 0.25", "color3"),
            Some(vt::Value::Vec3f(gf::Vec3f::from([1.0, 0.0, 0.25])))
        );
        assert_eq!(parse_value("true", "boolean"), Some(vt::Value::Bool(true)));
        assert_eq!(parse_value("fast", "float"), None);
        assert_eq!(parse_value("1, 2", "vector3"), None);
    }

    #[test]
    fn names_made_valid() {
        assert_eq!(make_name("node_1"), "node_1");
        assert_eq!(make_name("1node"), "_1node");
        assert_eq!(make_name("a-b.c"), "a_b_c");
    }

    #[test]
    fn closures_are_render_types() {
        assert_eq!(usd_type("BSDF"), ("token", Some("BSDF".to_owned())));
        assert_eq!(usd_type("surfaceshader"), ("token", None));
        assert_eq!(usd_type("vector2"), ("float2", None));
    }
}
