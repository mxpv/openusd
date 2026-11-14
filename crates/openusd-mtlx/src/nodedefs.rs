//! Node definitions: the signatures a node's `info:id`, its inputs' types and
//! its outputs come from.
//!
//! The standard ones are MaterialX 1.39's `stdlib`, `pbrlib`, `nprlib` and
//! `bxdf` libraries, embedded and parsed once; a document's own `<nodedef>`s come
//! before them for that document. C++ `usdMtlx` reads the same libraries
//! through `UsdMtlxGetDocument("")`.

use std::collections::HashMap;
use std::sync::OnceLock;

use crate::document::Node;

/// The embedded definition documents, in the order a lookup reads them.
const LIBRARIES: &[&str] = &[
    include_str!("../libraries/stdlib/stdlib_defs.mtlx"),
    include_str!("../libraries/pbrlib/pbrlib_defs.mtlx"),
    include_str!("../libraries/nprlib/nprlib_defs.mtlx"),
    include_str!("../libraries/bxdf/standard_surface.mtlx"),
    include_str!("../libraries/bxdf/open_pbr_surface.mtlx"),
    include_str!("../libraries/bxdf/gltf_pbr.mtlx"),
    include_str!("../libraries/bxdf/usd_preview_surface.mtlx"),
    include_str!("../libraries/bxdf/disney_principled.mtlx"),
];

/// A `<nodedef>`: a node category's signature.
#[derive(Debug, Clone, Default)]
pub(crate) struct NodeDef {
    /// `ND_…` by convention.
    pub name: String,
    /// The category its instances are written as.
    pub node: String,
    pub version: Option<String>,
    /// `isdefaultversion="true"`.
    pub default_version: bool,
    /// The nodedef it inherits ports from.
    pub inherit: Option<String>,
    /// `(name, type)`, the inherited ones first once a [`Library`] resolves
    /// them.
    pub inputs: Vec<(String, String)>,
    pub outputs: Vec<(String, String)>,
}

/// The nodedefs one lookup reads: a document's own, or the standard ones.
#[derive(Debug, Default)]
pub(crate) struct Library {
    defs: Vec<NodeDef>,
    by_name: HashMap<String, usize>,
}

/// How well a nodedef matches a node.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Match<'d> {
    /// Its category, type and version, and the type of every input the node
    /// authors.
    Exact(&'d NodeDef),
    /// Its category, type and version only: the node authors an input the
    /// nodedef lacks, or with another type.
    Closest(&'d NodeDef),
}

impl NodeDef {
    /// The nodedef `el` declares, its own ports only.
    pub(crate) fn from_element(el: roxmltree::Node<'_, '_>) -> Self {
        let ports = |tag: &str| {
            el.children()
                .filter(|c| c.has_tag_name(tag))
                .map(|c| {
                    (
                        c.attribute("name").unwrap_or_default().to_owned(),
                        c.attribute("type").unwrap_or_default().to_owned(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let mut outputs = ports("output");
        // A pre-1.38 nodedef declares its one output by its own `type`.
        if outputs.is_empty()
            && let Some(ty) = el.attribute("type")
        {
            outputs.push(("out".to_owned(), ty.to_owned()));
        }
        Self {
            name: el.attribute("name").unwrap_or_default().to_owned(),
            node: el.attribute("node").unwrap_or_default().to_owned(),
            version: el.attribute("version").map(str::to_owned),
            default_version: el.attribute("isdefaultversion") == Some("true"),
            inherit: el.attribute("inherit").map(str::to_owned),
            inputs: ports("input"),
            outputs,
        }
    }

    /// The type an instance is written with: its one output's, or
    /// `multioutput`.
    pub(crate) fn type_name(&self) -> &str {
        match self.outputs.as_slice() {
            [(_, ty)] => ty,
            _ => "multioutput",
        }
    }

    /// The type of the input called `name`.
    pub(crate) fn input_type(&self, name: &str) -> Option<&str> {
        self.inputs.iter().find(|(n, _)| n == name).map(|(_, t)| t.as_str())
    }

    /// The output a connection naming none reads: the only one, whatever
    /// it is called, else `out`.
    pub(crate) fn default_output(&self) -> &str {
        match self.outputs.as_slice() {
            [(name, _)] => name,
            _ => "out",
        }
    }

    /// Whether the node instantiates this nodedef's category at this type and
    /// version: the nodedef the node's own version names, or else the
    /// category's default version.
    fn fits(&self, node: &Node) -> bool {
        self.node == node.category
            && self.type_name() == node.type_name
            && match &node.version {
                Some(version) => self.version.as_ref() == Some(version),
                None => self.version.is_none() || self.default_version,
            }
    }

    /// Whether every input `node` authors is one of this nodedef's, of the
    /// same type.
    fn takes_inputs(&self, node: &Node) -> bool {
        node.inputs
            .iter()
            .all(|i| self.input_type(&i.name) == Some(i.type_name.as_str()))
    }
}

impl Library {
    /// The standard nodedefs, parsed on first use.
    pub(crate) fn standard() -> &'static Library {
        static STANDARD: OnceLock<Library> = OnceLock::new();
        STANDARD.get_or_init(|| {
            let defs = LIBRARIES
                .iter()
                .filter_map(|text| roxmltree::Document::parse(text).ok())
                .flat_map(|doc| {
                    doc.root_element()
                        .children()
                        .filter(|c| c.has_tag_name("nodedef"))
                        .map(NodeDef::from_element)
                        .collect::<Vec<_>>()
                })
                .collect();
            Library::new(defs)
        })
    }

    /// A library of `defs`, each one's inherited ports resolved over the
    /// others and `base`'s.
    pub(crate) fn new(defs: Vec<NodeDef>) -> Self {
        Self::with_base(defs, None)
    }

    /// A document's library: its `defs`, inheriting from the standard ones
    /// too.
    pub(crate) fn local(defs: Vec<NodeDef>) -> Self {
        Self::with_base(defs, Some(Self::standard()))
    }

    fn with_base(mut defs: Vec<NodeDef>, base: Option<&Library>) -> Self {
        let own: HashMap<String, NodeDef> = defs.iter().map(|d| (d.name.clone(), d.clone())).collect();
        let lookup = |name: &str| own.get(name).or_else(|| base.and_then(|b| b.by_name(name)));
        for def in &mut defs {
            // The chain from the most derived, a cycle cut where it repeats.
            let mut chain = vec![def.clone()];
            let mut seen = vec![def.name.clone()];
            while let Some(parent) = chain.last().and_then(|d| d.inherit.as_deref()).and_then(lookup) {
                if seen.contains(&parent.name) {
                    break;
                }
                seen.push(parent.name.clone());
                chain.push(parent.clone());
            }
            let mut inputs: Vec<(String, String)> = Vec::new();
            let mut outputs: Vec<(String, String)> = Vec::new();
            for d in chain.iter().rev() {
                for (port, into) in [(&d.inputs, &mut inputs), (&d.outputs, &mut outputs)] {
                    for p in port {
                        if !into.iter().any(|(n, _)| *n == p.0) {
                            into.push(p.clone());
                        }
                    }
                }
            }
            def.inputs = inputs;
            def.outputs = outputs;
        }
        let by_name = defs.iter().enumerate().map(|(i, d)| (d.name.clone(), i)).collect();
        Self { defs, by_name }
    }

    /// The nodedef called `name`.
    pub(crate) fn by_name(&self, name: &str) -> Option<&NodeDef> {
        self.by_name.get(name).map(|&i| &self.defs[i])
    }

    /// The nodedef `node` instantiates (C++ `usdMtlx`'s `_FindMatchingNodeDef`
    /// over a document, then over the standard library): the one it names,
    /// or the first of its category, type and version whose inputs take every
    /// input it authors. Failing that, the first of its category, type and
    /// version, as [`Match::Closest`].
    pub(crate) fn find(&self, node: &Node) -> Option<Match<'_>> {
        if let Some(def) = node.nodedef.as_deref().and_then(|n| self.by_name(n)) {
            return Some(Match::Exact(def));
        }
        let mut candidates: Vec<&NodeDef> = self.defs.iter().filter(|d| d.fits(node)).collect();
        // An unversioned node means its category's default version: a
        // nodedef marked so comes before one that declares no version.
        candidates.sort_by_key(|d| node.version.is_none() && !d.default_version);
        candidates
            .iter()
            .find(|d| d.takes_inputs(node))
            .map(|d| Match::Exact(d))
            .or_else(|| candidates.first().map(|d| Match::Closest(d)))
    }
}

/// The nodedef `node` instantiates, looked up in the document's `local`
/// library and then the standard one: an exact match in either before a
/// closest one.
pub(crate) fn find<'d>(local: &'d Library, node: &Node) -> Option<Match<'d>> {
    let standard = Library::standard();
    match (local.find(node), standard.find(node)) {
        (Some(Match::Exact(def)), _) | (_, Some(Match::Exact(def))) => Some(Match::Exact(def)),
        (Some(closest), _) => Some(closest),
        (None, standard) => standard,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::document::Input;

    fn node(category: &str, type_name: &str, inputs: &[(&str, &str)]) -> Node {
        Node {
            category: category.into(),
            name: "n".into(),
            type_name: type_name.into(),
            inputs: inputs
                .iter()
                .map(|(name, ty)| Input {
                    name: (*name).into(),
                    type_name: (*ty).into(),
                    ..Input::default()
                })
                .collect(),
            ..Node::default()
        }
    }

    fn exact(node: &Node) -> String {
        match find(&Library::default(), node) {
            Some(Match::Exact(def)) => def.name.clone(),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn standard_parses() {
        let lib = Library::standard();
        assert!(lib.defs.len() > 700, "{}", lib.defs.len());
        // The default `standard_surface` inherits every port.
        let ss = lib.by_name("ND_standard_surface_surfaceshader").expect("defined");
        assert_eq!(ss.type_name(), "surfaceshader");
        assert!(ss.input_type("base_color").is_some() && ss.input_type("coat").is_some());
    }

    #[test]
    fn inputs_pick_signature() {
        assert_eq!(
            exact(&node(
                "displacement",
                "displacementshader",
                &[("displacement", "float")]
            )),
            "ND_displacement_float"
        );
        assert_eq!(
            exact(&node(
                "displacement",
                "displacementshader",
                &[("displacement", "vector3")]
            )),
            "ND_displacement_vector3"
        );
        assert_eq!(
            exact(&node("convert", "vector2", &[("in", "float")])),
            "ND_convert_float_vector2"
        );
        // Both `normalmap` nodedefs take `in` alone: the first declared wins.
        assert_eq!(
            exact(&node("normalmap", "vector3", &[("in", "vector3")])),
            "ND_normalmap_float"
        );
        assert_eq!(
            exact(&node("standard_surface", "surfaceshader", &[])),
            "ND_standard_surface_surfaceshader"
        );
    }

    #[test]
    fn closest_fallback() {
        let n = node("subsurface_bsdf", "BSDF", &[("radius", "vector3")]);
        match find(&Library::default(), &n) {
            Some(Match::Closest(def)) => assert_eq!(def.name, "ND_subsurface_bsdf"),
            other => panic!("{other:?}"),
        }
        assert!(find(&Library::default(), &node("no_such", "float", &[])).is_none());
    }

    #[test]
    fn single_output_default() {
        let lib = Library::standard();
        let absorption = lib.by_name("ND_chiang_hair_absorption_from_color").expect("defined");
        assert_eq!(absorption.default_output(), "absorption");
        assert_eq!(lib.by_name("ND_artistic_ior").expect("defined").default_output(), "out");
    }
}
