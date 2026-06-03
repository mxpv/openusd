//! Task-queue prim indexer (C++ `Pcp_PrimIndexer` port).
//!
//! [`Indexer`] is the replacement for the recursive `IndexBuilder`: it grows a
//! [`PrimIndexGraph`] node-by-node, following composition arcs without the
//! global `(layer, path, arc)` dedup set the recursive builder uses. That
//! structural model keeps reference/payload diamonds — a shared target reached
//! by two arc paths contributes a node on each path — which the global set
//! collapsed to one (the recursive builder's long-standing bug).
//!
//! The indexer is being ported arc-by-arc. `build_with_cache_in` composes a
//! prim with the indexer when [`Indexer::build`] reports support and otherwise
//! falls back to the recursive builder, so each phase composes one more arc
//! type while the byte-exact `pcp.txt` composition goldens validate the result.
//! Whenever the indexer meets a composition feature a later phase ports, it
//! abandons the prim ([`Indexer::build`] returns `None`) and the recursive
//! builder composes it.
//!
//! Ported so far: the root local site, external reference/payload arcs (with an
//! explicit root-level prim target), and propagation of reference/payload
//! ancestor arcs to a child prim. Any other feature defers to the recursive
//! builder; each deferral point carries its reason inline.

use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::schema::FieldKey;
use crate::sdf::{AbstractData, LayerOffset, Path};

use super::graph::{ArcType, NodeId, PrimIndexGraph};
use super::index::{collect_payloads_in, compose_references_in, find_layer, CompositionContext, PrimIndex};
use super::mapping::MapFunction;
use super::{Error, LayerStack};

/// Maximum composition-arc nesting before the prim is abandoned to the
/// recursive builder (which reports it as a cycle). Matches the builder's
/// `MAX_COMPOSITION_DEPTH`.
const MAX_DEPTH: usize = 100;

/// Fields whose presence at a composed site means the prim pulls in an arc or
/// variant a later phase ports. While any is authored the indexer abandons the
/// prim to the recursive builder rather than composing a half-resolved result.
const UNSUPPORTED_FIELDS: [FieldKey; 4] = [
    FieldKey::InheritPaths,
    FieldKey::Specializes,
    FieldKey::VariantSetNames,
    FieldKey::VariantSelection,
];

/// Composes a single prim by growing the composition graph node-by-node from
/// its arcs (C++ `Pcp_PrimIndexer`).
///
/// All borrowed inputs are shared references, so each build is an independent
/// pure function over the layer stack and incoming context (Rayon-friendly —
/// see the `TODO(rayon)` on the cross-prim driver in `cache.rs`).
pub(crate) struct Indexer<'a> {
    stack: &'a LayerStack,
    ctx: &'a CompositionContext,
    /// Cached prim indices from the composition cache, consulted when an arc
    /// target resolves to an already-composed stage prim. Unused until the
    /// class-arc phases land.
    #[allow(dead_code)]
    cached_indices: &'a HashMap<Path, PrimIndex>,
    /// Layer stack the root `L` site scans (the stage root layer stack for a
    /// stage prim, or a referenced asset's sublayer stack for an arc target).
    ambient: &'a [(usize, LayerOffset)],
    /// Whether [`ambient`](Self::ambient) is the stage's root layer stack, the
    /// only case where the stage-keyed `cached_indices` apply. Unused until the
    /// class-arc phases land.
    #[allow(dead_code)]
    ambient_is_root: bool,
    /// The graph grown so far.
    output: PrimIndexGraph,
    /// Cleared the moment composition meets a feature a later phase ports; the
    /// build is then abandoned and the recursive builder composes the prim.
    supported: bool,
}

impl<'a> Indexer<'a> {
    pub(crate) fn new(
        stack: &'a LayerStack,
        ctx: &'a CompositionContext,
        cached_indices: &'a HashMap<Path, PrimIndex>,
        ambient: &'a [(usize, LayerOffset)],
        ambient_is_root: bool,
    ) -> Self {
        Self {
            stack,
            ctx,
            cached_indices,
            ambient,
            ambient_is_root,
            output: PrimIndexGraph::default(),
            supported: true,
        }
    }

    /// Composes `path`, returning the graph when the prim's composition is
    /// fully within the ported feature set, or `None` when it relies on a
    /// feature a later phase ports (the caller then uses the recursive builder).
    pub(crate) fn build(mut self, path: &Path) -> Result<Option<PrimIndexGraph>, Error> {
        // Instance composition is a later phase.
        if self.ctx.within_instance {
            return Ok(None);
        }
        // The indexer can extend reference/payload ancestor arcs to a child; a
        // class/variant/relocate ancestor arc needs a later phase.
        if self
            .ctx
            .ancestor_arcs
            .iter()
            .any(|a| !matches!(a.arc, ArcType::Reference | ArcType::Payload))
        {
            return Ok(None);
        }
        self.output.init_root(path.clone());
        let ambient = self.ambient.to_vec();
        self.compose(
            path,
            &ambient,
            ArcType::Root,
            NodeId::INVALID,
            MapFunction::identity(),
            0,
        )?;
        if self.supported {
            self.propagate_ancestor_arcs(path)?;
        }
        if !self.supported {
            return Ok(None);
        }
        self.output.finalize_strength_order();
        Ok(Some(self.output))
    }

    /// Extends the direct parent prim's nodes to this child prim (C++
    /// `AppendChildNameToAllSites`), the ancestral arcs in the no-dedup model.
    ///
    /// Only the parent's own nodes are propagated (`ancestor_arcs[own_arcs_start..]`):
    /// they already encode everything the inherited grandparent arcs produced,
    /// so propagating the inherited arcs too would compose a grandparent arc and
    /// the parent node it produced as two nodes. For each parent node the parent
    /// path is mapped back into the node's source namespace and the child name
    /// appended, then that site is composed under the node's already-composed
    /// child node (so a nested arc keeps the parent prim's tree). Composing
    /// through [`compose`](Self::compose) — which never dedups — is what keeps a
    /// target reached by both a local arc and an ancestral one (a payload
    /// diamond through ancestry) as two nodes.
    fn propagate_ancestor_arcs(&mut self, path: &Path) -> Result<(), Error> {
        let Some(child_name) = path.name() else {
            return Ok(());
        };
        let parent_path = path.parent();
        let ctx = self.ctx;
        // The node each parent node composed to, keyed by its index in
        // `ancestor_arcs`, so a nested arc attaches under its parent's child.
        let mut composed: HashMap<usize, NodeId> = HashMap::new();
        for i in ctx.own_arcs_start..ctx.ancestor_arcs.len() {
            if !self.supported {
                return Ok(());
            }
            let a = &ctx.ancestor_arcs[i];
            // Only nodes whose target prefix matches the parent reach this child.
            let Some(parent_in_source) = parent_path.as_ref().and_then(|p| a.map.map_target_to_source(p)) else {
                continue;
            };
            let Ok(rpath) = parent_in_source.append_path(child_name) else {
                continue;
            };
            // Nest under the parent node's composed child and map relative to it;
            // a node directly on the parent prim maps straight to the root.
            let parent_node = a
                .parent
                .and_then(|p| composed.get(&p).copied())
                .unwrap_or(NodeId::INVALID);
            let map = if parent_node.is_valid() {
                a.map_to_parent.clone()
            } else {
                a.map.clone()
            };
            let before = self.output.len();
            self.compose(&rpath, &a.layer_stack, a.arc, parent_node, map, 0)?;
            if self.output.len() > before {
                let node = NodeId(before as u32);
                // Inherit the parent node's namespace depth so the parent's
                // relative strength order survives the deeper child path.
                self.output.nodes[node.idx()].namespace_depth = a.namespace_depth;
                composed.insert(i, node);
            }
        }
        Ok(())
    }

    /// Composes the site `(layer_stack, path)` introduced by `arc` under
    /// `parent`, then follows the reference and payload arcs it authors.
    ///
    /// Adds one site node folding every `layer_stack` sublayer that authors a
    /// spec, strongest first, then recurses into each reference and payload. Any
    /// feature outside the ported set clears [`supported`](Self::supported),
    /// which unwinds the recursion and abandons the prim.
    fn compose(
        &mut self,
        path: &Path,
        layer_stack: &[(usize, LayerOffset)],
        arc: ArcType,
        parent: NodeId,
        map_to_parent: MapFunction,
        depth: usize,
    ) -> Result<(), Error> {
        if !self.supported {
            return Ok(());
        }
        let Some(&(root_layer, _)) = layer_stack.first() else {
            return Ok(());
        };
        // Deep nesting or a site already on the parent chain is a cycle the
        // recursive builder reports; abandon the prim so it raises the error.
        if depth > MAX_DEPTH || self.on_parent_chain(parent, root_layer, path) {
            self.supported = false;
            return Ok(());
        }

        // Local opinions: every sublayer that authors a spec at `path`,
        // strongest first, paired with its sublayer offset.
        let members: Vec<(usize, LayerOffset)> = layer_stack
            .iter()
            .copied()
            .filter(|&(li, _)| self.stack.layer(li).has_spec(path))
            .collect();
        // No opinion at this site contributes no node; the caller decides
        // whether that is acceptable (a legitimately empty root or ancestral
        // site) or a culled arc target that must defer to the recursive builder.
        if members.is_empty() {
            return Ok(());
        }
        let node = self
            .output
            .add_site_child(parent, members, path.clone(), arc, map_to_parent, false);

        // An inherit/specialize/variant field needs a later phase.
        if self.site_authors_unsupported(path, node)? {
            self.supported = false;
            return Ok(());
        }

        // R — References, then P — Payloads, each composed in authored order.
        let references = compose_references_in(self.node_slice(node), &self.stack.layers, &*self.stack.resolver)?;
        for reference in &references {
            self.compose_arc_target(
                &reference.asset_path,
                &reference.prim_path,
                ArcType::Reference,
                path,
                node,
                reference.layer_offset.sanitized(),
                depth,
            )?;
            if !self.supported {
                return Ok(());
            }
        }
        if self.stack.load_payloads {
            let payloads = collect_payloads_in(self.node_slice(node), &self.stack.layers, &*self.stack.resolver)?;
            for payload in &payloads {
                self.compose_arc_target(
                    &payload.asset_path,
                    &payload.prim_path,
                    ArcType::Payload,
                    path,
                    node,
                    payload.layer_offset.unwrap_or_default().sanitized(),
                    depth,
                )?;
                if !self.supported {
                    return Ok(());
                }
            }
        }
        Ok(())
    }

    /// Resolves a reference or payload to its target layer stack and composes
    /// it under `parent`. Targets outside the ported set (internal references,
    /// `defaultPrim` resolution, sub-root targets, unresolved layers) abandon
    /// the prim to the recursive builder.
    #[allow(clippy::too_many_arguments)]
    fn compose_arc_target(
        &mut self,
        asset_path: &str,
        prim_path: &Path,
        arc: ArcType,
        context_path: &Path,
        parent: NodeId,
        arc_offset: LayerOffset,
        depth: usize,
    ) -> Result<(), Error> {
        // Internal references (empty asset path) and `defaultPrim` targets
        // (empty prim path) are later phases.
        if asset_path.is_empty() || prim_path.is_empty() {
            self.supported = false;
            return Ok(());
        }
        // A sub-root target sits under a prim that may carry ancestral arcs; its
        // namespace-parent composition is a later phase.
        if prim_path.parent().is_some_and(|p| p != Path::abs_root()) {
            self.supported = false;
            return Ok(());
        }
        let Some(layer_index) = find_layer(asset_path, &self.stack.layers, &*self.stack.resolver) else {
            // The recursive builder raises `UnresolvedLayer`; let it.
            self.supported = false;
            return Ok(());
        };
        let target_stack = self.stack.sublayer_stack(layer_index);
        let map = MapFunction::from_pair(prim_path.clone(), context_path.clone()).with_time_offset(arc_offset);
        let before = self.output.len();
        self.compose(prim_path, &target_stack, arc, parent, map, depth + 1)?;
        // An arc to an empty target is culled by the recursive builder, which
        // the indexer does not reproduce yet; defer the whole prim.
        if self.supported && self.output.len() == before {
            self.supported = false;
        }
        Ok(())
    }

    /// Returns `true` when an ancestor of `node` (walking the parent chain to
    /// the synthetic root) is the same `(root_layer, path)` site — a
    /// composition cycle.
    fn on_parent_chain(&self, node: NodeId, root_layer: usize, path: &Path) -> bool {
        let mut cur = node;
        while cur.is_valid() {
            let n = &self.output[cur.idx()];
            if n.layer_index() == root_layer && &n.path == path {
                return true;
            }
            cur = n.parent().unwrap_or(NodeId::INVALID);
        }
        false
    }

    /// Returns `true` when any member layer of `node` authors an
    /// inherit/specialize/variant field at `path` (see [`UNSUPPORTED_FIELDS`]).
    fn site_authors_unsupported(&self, path: &Path, node: NodeId) -> Result<bool, Error> {
        for &(li, _) in self.output[node.idx()].layer_stack() {
            let layer = self.stack.layer(li);
            for field in UNSUPPORTED_FIELDS {
                if layer.try_get(path, field.as_str())?.is_some() {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// A one-element slice over `node`, for the `compose_*_in` helpers that read
    /// a field across a node's member layers.
    fn node_slice(&self, node: NodeId) -> &[super::graph::Node] {
        &self.output[node.idx()..=node.idx()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;

    fn stack(text: &str) -> LayerStack {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        let layer = crate::sdf::Layer::new("root.usd", Box::new(crate::usda::TextReader::from_data(data)));
        LayerStack::new(vec![layer], 0, Box::new(DefaultResolver::new()), true)
    }

    fn build(stack: &LayerStack, prim: &str) -> Option<PrimIndexGraph> {
        let ctx = CompositionContext::default();
        let ambient = stack.root_layer_stack();
        Indexer::new(stack, &ctx, &HashMap::new(), &ambient, true)
            .build(&Path::from(prim))
            .expect("indexer build")
    }

    #[test]
    fn local_prim_supported() {
        let s = stack("#usda 1.0\ndef \"World\" {\n  def \"Sphere\" {}\n}\n");
        let graph = build(&s, "/World").expect("a purely local prim is supported");
        // The synthetic inert root plus one Root-arc site node.
        let arcs: Vec<ArcType> = graph.iter().filter(|n| !n.is_inert()).map(|n| n.arc).collect();
        assert_eq!(arcs, vec![ArcType::Root]);
    }

    #[test]
    fn inherit_prim_deferred() {
        let s = stack("#usda 1.0\nclass \"C\" {}\ndef \"World\" (\n    inherits = </C>\n) {\n}\n");
        assert!(
            build(&s, "/World").is_none(),
            "a prim authoring an inherit defers to the recursive builder"
        );
    }

    #[test]
    fn internal_reference_deferred() {
        let s = stack("#usda 1.0\ndef \"Base\" {}\ndef \"World\" (\n    references = </Base>\n) {\n}\n");
        assert!(
            build(&s, "/World").is_none(),
            "an internal reference defers to the recursive builder"
        );
    }

    #[test]
    fn class_ancestor_arc_deferred() {
        let s = stack("#usda 1.0\ndef \"World\" {\n}\n");
        let ctx = CompositionContext {
            ancestor_arcs: vec![super::super::index::AncestorArc {
                map: MapFunction::identity(),
                map_to_parent: MapFunction::identity(),
                layer_stack: vec![(0, LayerOffset::IDENTITY)],
                arc: ArcType::Inherit,
                namespace_depth: 1,
                parent: None,
            }],
            ..Default::default()
        };
        let ambient = s.root_layer_stack();
        let result = Indexer::new(&s, &ctx, &HashMap::new(), &ambient, true)
            .build(&Path::from("/World"))
            .expect("indexer build");
        assert!(result.is_none(), "a class ancestor arc defers to the recursive builder");
    }
}
