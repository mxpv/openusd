//! Node definitions: the signatures a node's `info:id`, its inputs' types and
//! its outputs come from.
//!
//! The standard ones are those of MaterialX 1.39's libraries (`stdlib`,
//! `pbrlib`, `nprlib`, `cmlib`, `lights` and `bxdf`), embedded and parsed
//! once; a document's own `<nodedef>`s come before them for that document.
//! C++ `usdMtlx` reads the same libraries through `UsdMtlxGetDocument("")`.

use std::collections::{HashMap, HashSet};
use std::sync::OnceLock;

use crate::document::{self, Included, Node};

/// The embedded definition documents, in the order a lookup reads them.
const LIBRARIES: &[&str] = &[
    include_str!("../libraries/stdlib/stdlib_defs.mtlx"),
    include_str!("../libraries/pbrlib/pbrlib_defs.mtlx"),
    include_str!("../libraries/nprlib/nprlib_defs.mtlx"),
    include_str!("../libraries/cmlib/cmlib_defs.mtlx"),
    include_str!("../libraries/lights/lights_defs.mtlx"),
    include_str!("../libraries/bxdf/standard_surface.mtlx"),
    include_str!("../libraries/bxdf/open_pbr_surface.mtlx"),
    include_str!("../libraries/bxdf/gltf_pbr.mtlx"),
    include_str!("../libraries/bxdf/usd_preview_surface.mtlx"),
    include_str!("../libraries/bxdf/disney_principled.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_add.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_conductor.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_dielectric.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_diffuse.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_emission.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_generalized_schlick.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_iridescence.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_layer.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_mix.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_sheen.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_sss.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_surface.mtlx"),
    include_str!("../libraries/bxdf/lama/lama_translucent.mtlx"),
    include_str!("../libraries/bxdf/translation/open_pbr_to_standard_surface.mtlx"),
    include_str!("../libraries/bxdf/translation/standard_surface_to_gltf_pbr.mtlx"),
    include_str!("../libraries/bxdf/translation/standard_surface_to_open_pbr.mtlx"),
    include_str!("../libraries/bxdf/translation/standard_surface_to_usd.mtlx"),
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
    /// Nodedef name → its index in `defs`.
    by_name: HashMap<String, usize>,
    /// Node category → the indices in `defs` of its nodedefs, in order.
    by_category: HashMap<String, Vec<usize>>,
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
    /// The nodedef `el` declares, its own ports only. Each child the read
    /// leaves out is noted in `notes`.
    pub(crate) fn from_element(el: roxmltree::Node<'_, '_>, name: String, notes: &mut Vec<String>) -> Self {
        let children = document::children(el, &name, HashSet::new(), notes);
        let ports = |tag: &str| {
            children
                .iter()
                .filter(|(c, _)| c.has_tag_name(tag))
                .map(|(c, name)| (name.clone(), c.attribute("type").unwrap_or_default().to_owned()))
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
            name,
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

    /// Whether every input `node` authors is one of this nodedef's, of the
    /// same type (MaterialX `hasExactInputMatch`).
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
            // TODO(rayon): the libraries are independent and can be parsed
            // in parallel.
            let defs = LIBRARIES
                .iter()
                .filter_map(|text| document::parse(text, "an embedded library", &mut |_| Ok(Included::Unfound)).ok())
                .flat_map(|doc| doc.nodedefs)
                .collect();
            Self::with_base(defs, None)
        })
    }

    /// A document's library: its `defs`, inheriting from the standard ones
    /// too.
    pub(crate) fn local(defs: Vec<NodeDef>) -> Self {
        Self::with_base(defs, Some(Self::standard()))
    }

    /// A library of `defs`, each one's inherited ports resolved over the
    /// others and `base`'s.
    fn with_base(mut defs: Vec<NodeDef>, base: Option<&Library>) -> Self {
        let by_name: HashMap<String, usize> = defs.iter().enumerate().map(|(i, d)| (d.name.clone(), i)).collect();
        let lookup = |name: &str| {
            let own = by_name.get(name).map(|&i| &defs[i]);
            own.or_else(|| base.and_then(|b| b.by_name(name)))
        };
        // Each nodedef's ports are worked out from the declared ones of its
        // chain before any is replaced.
        let ports: Vec<_> = defs
            .iter()
            .map(|def| {
                // The chain from the most derived, a cycle cut where it
                // repeats.
                let mut chain = vec![def];
                while let Some(parent) = chain.last().and_then(|d| d.inherit.as_deref()).and_then(lookup) {
                    if chain.iter().any(|d| d.name == parent.name) {
                        break;
                    }
                    chain.push(parent);
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
                (inputs, outputs)
            })
            .collect();
        for (def, (inputs, outputs)) in defs.iter_mut().zip(ports) {
            def.inputs = inputs;
            def.outputs = outputs;
        }
        let mut by_category: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, def) in defs.iter().enumerate() {
            by_category.entry(def.node.clone()).or_default().push(i);
        }
        Self {
            defs,
            by_name,
            by_category,
        }
    }

    /// The nodedefs `node` may be written as an instance of, in the order
    /// they are declared.
    fn instantiated_by<'a>(&'a self, node: &Node) -> impl Iterator<Item = &'a NodeDef> {
        self.by_category
            .get(&node.category)
            .into_iter()
            .flatten()
            .map(|&i| &self.defs[i])
            .filter(|def| def.type_name() == node.type_name)
    }

    /// The nodedef called `name`.
    pub(crate) fn by_name(&self, name: &str) -> Option<&NodeDef> {
        self.by_name.get(name).map(|&i| &self.defs[i])
    }

    /// The nodedef `node` resolves to among these alone, as MaterialX
    /// resolves it (`Node::getNodeDef`): the one it names, or the first it
    /// instantiates at its version whose inputs take every input it authors.
    /// An unversioned node is at a nodedef's version when the nodedef has
    /// none or is its category's default.
    fn declared(&self, node: &Node) -> Option<&NodeDef> {
        if let Some(name) = &node.nodedef {
            return self.by_name(name);
        }
        self.instantiated_by(node).find(|d| {
            (d.version == node.version || (d.default_version && node.version.is_none())) && d.takes_inputs(node)
        })
    }

    /// The nodedef `node` instantiates among these (C++ `usdMtlx`'s
    /// `_FindMatchingNodeDef` over one document), with `inputs` only one
    /// whose inputs take every input the node authors. A versioned node
    /// takes the first nodedef of its version. An unversioned one, or one
    /// whose version is none C++ reads, takes the first marked its
    /// category's default version, or else the last not marked so.
    fn matching(&self, node: &Node, inputs: bool) -> Option<&NodeDef> {
        let mut found = None;
        // TODO: match the `target` of the node against the nodedef's too
        // (MaterialX `targetStringsMatch`); neither is read.
        let candidates = self.instantiated_by(node).filter(|d| !inputs || d.takes_inputs(node));
        let version = node.version.as_deref().and_then(parse_version);
        for def in candidates {
            match version {
                None if def.default_version => return Some(def),
                None => found = Some(def),
                Some(_) if def.version.as_deref().and_then(parse_version) == version => return Some(def),
                Some(_) => {}
            }
        }
        found
    }
}

/// The nodedef `node` instantiates, in the order C++ `usdMtlx` looks
/// (`_GetNodeDef`): what the node resolves to in the document's `local`
/// library, the nodedef matching it there, the standard nodedef it names,
/// then the standard nodedef matching it. Failing all four, the nodedef
/// matching it but for its inputs, as [`Match::Closest`].
pub(crate) fn find<'d>(local: &'d Library, node: &Node) -> Option<Match<'d>> {
    // TODO(perf): a node is looked up once for its own prim and once for
    // each connection reading it; the result depends on the node alone and
    // could be kept per node.
    let standard = Library::standard();
    let named = || node.nodedef.as_deref().and_then(|name| standard.by_name(name));
    local
        .declared(node)
        .or_else(|| local.matching(node, true))
        .or_else(named)
        .or_else(|| standard.matching(node, true))
        .map(Match::Exact)
        .or_else(|| {
            local
                .matching(node, false)
                .or_else(|| standard.matching(node, false))
                .map(Match::Closest)
        })
}

/// `text` as the version C++ reads it as (`SdrVersion`): `major` or
/// `major.minor`, not both zero. `None` for anything else, `1.0.1` included.
fn parse_version(text: &str) -> Option<(u32, u32)> {
    let (major, minor) = text.split_once('.').unwrap_or((text, "0"));
    let version = (major.parse().ok()?, minor.parse().ok()?);
    (version != (0, 0)).then_some(version)
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
        // Both `normalmap` nodedefs take `in` alone, and neither is marked
        // the default version: the last declared wins.
        assert_eq!(
            exact(&node("normalmap", "vector3", &[("in", "vector3")])),
            "ND_normalmap_vector2"
        );
        // `UsdUVTexture` has a nodedef marked the default version.
        assert_eq!(exact(&node("UsdUVTexture", "multioutput", &[])), "ND_UsdUVTexture_23");
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

    /// A document's own nodedefs resolve as MaterialX resolves them, the
    /// first match winning, and come before the standard ones.
    #[test]
    fn local_first_match() {
        let def = |name: &str| NodeDef {
            name: name.into(),
            node: "normalmap".into(),
            inputs: vec![("in".into(), "vector3".into())],
            outputs: vec![("out".into(), "vector3".into())],
            ..NodeDef::default()
        };
        let local = Library::local(vec![def("ND_mine_a"), def("ND_mine_b")]);
        match find(&local, &node("normalmap", "vector3", &[("in", "vector3")])) {
            Some(Match::Exact(def)) => assert_eq!(def.name, "ND_mine_a"),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn versions_compare() {
        assert_eq!(parse_version("1"), parse_version("1.0"));
        assert_eq!(parse_version("2.3"), Some((2, 3)));
        assert_eq!(parse_version("1.0.1"), None);
        assert_eq!(parse_version("beta"), None);
        let mut texture = node("UsdUVTexture", "multioutput", &[]);
        texture.version = Some("2.2".into());
        assert_eq!(exact(&texture), "ND_UsdUVTexture");
    }

    /// Every embedded library parses, and the libraries beside `stdlib`
    /// contribute their nodedefs.
    #[test]
    fn libraries_parse() {
        for text in LIBRARIES {
            roxmltree::Document::parse(text).expect("an embedded library parses");
        }
        let lib = Library::standard();
        for name in [
            "ND_point_light",
            "ND_lama_conductor",
            "ND_g22_rec709_to_lin_rec709_color3",
            "ND_standard_surface_to_open_pbr_surface",
        ] {
            assert!(lib.by_name(name).is_some(), "{name}");
        }
    }
}
