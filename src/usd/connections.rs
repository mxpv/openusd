//! Stage-wide attribute connection graph.
//!
//! Attribute connections (`connectionPaths`, authored via `.connect`)
//! form a directed graph over a stage's properties: an attribute is
//! wired to one or more *source* properties that drive its value.
//! UsdShade is the heaviest user (shader inputs ← outputs), but
//! connections are a core attribute feature any schema may use.
//!
//! [`ConnectionGraph`] indexes every authored connection edge on a
//! stage in one traversal, then answers repeated queries without
//! re-walking:
//!
//! - [`sources`](ConnectionGraph::sources) — what an attribute reads from.
//! - [`sinks`](ConnectionGraph::sinks) — what reads from an attribute
//!   (the reverse edges).
//! - [`resolve_chain`](ConnectionGraph::resolve_chain) — follow
//!   connections to their terminal sources (the leaves that aren't
//!   themselves connected onward).
//!
//! Edge direction: for `A.connect = [B]`, the edge is **A → B** (B is a
//! source of A; A is a sink of B), matching the dataflow direction
//! (values flow from B into A).

use std::collections::HashMap;
use std::collections::HashSet;

use anyhow::Result;

use crate::sdf::Path;
use crate::usd::{PrimPredicate, Stage};

/// A directed index of every authored attribute connection on a stage.
///
/// Build once with [`ConnectionGraph::from_stage`], then query
/// repeatedly. The graph is a static snapshot — re-build it after
/// authoring new connections.
#[derive(Debug, Clone, Default)]
pub struct ConnectionGraph {
    /// `attr -> its connection sources` (what the attr reads from).
    forward: HashMap<Path, Vec<Path>>,
    /// `source -> attrs that connect to it` (reverse edges).
    reverse: HashMap<Path, Vec<Path>>,
}

impl ConnectionGraph {
    /// Walk `stage` once and index every attribute carrying authored
    /// `connectionPaths`. Visits the default traversal region (active,
    /// loaded, defined, non-abstract prims), descending into instance
    /// proxies so connections inside instances are indexed too.
    pub fn from_stage(stage: &Stage) -> Result<Self> {
        let mut graph = ConnectionGraph::default();
        let mut first_err: Result<()> = Ok(());
        stage.traverse(PrimPredicate::DEFAULT_PROXIES, |prim| {
            if first_err.is_err() {
                return;
            }
            if let Err(e) = graph.index_prim(stage, prim) {
                first_err = Err(e);
            }
        })?;
        first_err?;
        Ok(graph)
    }

    fn index_prim(&mut self, stage: &Stage, prim: &Path) -> Result<()> {
        for prop in stage.prim(prim.clone()).property_names()? {
            let attr = prim.append_property(&prop)?;
            let sources = stage.attribute(attr.clone()).connections()?;
            if sources.is_empty() {
                continue;
            }
            for source in &sources {
                self.reverse.entry(source.clone()).or_default().push(attr.clone());
            }
            self.forward.insert(attr, sources);
        }
        Ok(())
    }

    /// The connection sources of `attr` — the properties it reads from.
    /// Empty when `attr` has no authored connection.
    pub fn sources(&self, attr: &Path) -> &[Path] {
        self.forward.get(attr).map_or(&[], Vec::as_slice)
    }

    /// The sinks of `attr` — every property that connects *to* it.
    /// Empty when nothing reads from `attr`.
    pub fn sinks(&self, attr: &Path) -> &[Path] {
        self.reverse.get(attr).map_or(&[], Vec::as_slice)
    }

    /// `true` when `attr` has at least one authored connection source.
    pub fn is_connected(&self, attr: &Path) -> bool {
        self.forward.contains_key(attr)
    }

    /// Total number of connected attributes (edges' tail count).
    pub fn len(&self) -> usize {
        self.forward.len()
    }

    /// `true` when no connection is authored anywhere on the stage.
    pub fn is_empty(&self) -> bool {
        self.forward.is_empty()
    }

    /// Every connection edge as `(from, to)` pairs, where `from`
    /// connects to source `to`. Order is unspecified.
    pub fn edges(&self) -> impl Iterator<Item = (&Path, &Path)> {
        self.forward
            .iter()
            .flat_map(|(from, tos)| tos.iter().map(move |to| (from, to)))
    }

    /// Follow `attr`'s connections to their terminal sources — the
    /// properties reached by chasing edges that are not themselves
    /// connected onward. Branching chains yield multiple terminals;
    /// cycles are broken (each property visited once). Returns `attr`
    /// itself when it has no outgoing connection.
    pub fn resolve_chain(&self, attr: &Path) -> Vec<Path> {
        // Iterative depth-first walk over the `forward` graph. An explicit
        // stack keeps deep chains from blowing the call stack.
        let mut terminals = Vec::new();
        let mut visited = HashSet::new();
        let mut stack: Vec<&Path> = vec![attr];
        while let Some(node) = stack.pop() {
            if !visited.insert(node.clone()) {
                continue;
            }
            match self.forward.get(node) {
                // Terminal: nothing further to chase.
                None => {
                    terminals.push(node.clone());
                }
                // Push reversed so the first source is explored first
                // (matches the original recursive order).
                Some(sources) => stack.extend(sources.iter().rev()),
            }
        }
        terminals
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    /// Build a tiny three-node chain: `A.in <- B.out`, `B.in <- C.out`.
    fn chain_stage() -> Result<Stage> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/G")?.set_type_name("Scope")?;
        let c = stage.define_prim("/G/C")?.set_type_name("Shader")?;
        c.create_attribute("outputs:out", "float")?;
        let b = stage.define_prim("/G/B")?.set_type_name("Shader")?;
        b.create_attribute("outputs:out", "float")?;
        b.create_attribute("inputs:in", "float")?
            .set_connections([sdf::path("/G/C.outputs:out")?])?;
        let a = stage.define_prim("/G/A")?.set_type_name("Shader")?;
        a.create_attribute("inputs:in", "float")?
            .set_connections([sdf::path("/G/B.outputs:out")?])?;
        Ok(stage)
    }

    #[test]
    fn sources_and_sinks() -> Result<()> {
        let stage = chain_stage()?;
        let graph = ConnectionGraph::from_stage(&stage)?;

        assert_eq!(
            graph.sources(&sdf::path("/G/A.inputs:in")?),
            &[sdf::path("/G/B.outputs:out")?]
        );
        // Nothing reads from A's input.
        assert!(graph.sinks(&sdf::path("/G/A.inputs:in")?).is_empty());
        // B.outputs:out is read by A.inputs:in.
        assert_eq!(
            graph.sinks(&sdf::path("/G/B.outputs:out")?),
            &[sdf::path("/G/A.inputs:in")?]
        );
        assert!(graph.is_connected(&sdf::path("/G/A.inputs:in")?));
        assert!(!graph.is_connected(&sdf::path("/G/C.outputs:out")?));
        assert_eq!(graph.len(), 2);
        Ok(())
    }

    #[test]
    fn resolve_chain_to_terminal() -> Result<()> {
        let stage = chain_stage()?;
        let graph = ConnectionGraph::from_stage(&stage)?;

        // A.inputs:in -> B.outputs:out. Shader outputs don't auto-wire
        // to inputs on the same prim, so B.outputs:out is the terminal.
        let terminals = graph.resolve_chain(&sdf::path("/G/A.inputs:in")?);
        assert_eq!(terminals, vec![sdf::path("/G/B.outputs:out")?]);
        Ok(())
    }

    #[test]
    fn resolve_chain_deep() -> Result<()> {
        // Deep chain — the iterative walk must finish without overflowing
        // the call stack the recursive form would on a long chain.
        let stage = Stage::builder().in_memory("anon.usda")?;
        let host = stage.define_prim("/Host")?.set_type_name("Shader")?;
        const N: usize = 2_000;
        for i in 0..N - 1 {
            host.create_attribute(format!("inputs:n{i}"), "float")?
                .set_connections([sdf::path(format!("/Host.inputs:n{}", i + 1))?])?;
        }
        host.create_attribute(format!("inputs:n{}", N - 1), "float")?;
        let graph = ConnectionGraph::from_stage(&stage)?;
        let terminals = graph.resolve_chain(&sdf::path("/Host.inputs:n0")?);
        assert_eq!(terminals, vec![sdf::path(format!("/Host.inputs:n{}", N - 1))?]);
        Ok(())
    }

    #[test]
    fn cycle_is_broken() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let p = stage.define_prim("/P")?.set_type_name("Shader")?;
        p.create_attribute("inputs:a", "float")?
            .set_connections([sdf::path("/P.inputs:b")?])?;
        p.create_attribute("inputs:b", "float")?
            .set_connections([sdf::path("/P.inputs:a")?])?;
        let graph = ConnectionGraph::from_stage(&stage)?;
        // Resolving a cycle terminates (no terminal reached, but no hang).
        let terminals = graph.resolve_chain(&sdf::path("/P.inputs:a")?);
        assert!(terminals.is_empty());
        Ok(())
    }

    #[test]
    fn empty_stage_has_no_edges() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/X")?.set_type_name("Scope")?;
        let graph = ConnectionGraph::from_stage(&stage)?;
        assert!(graph.is_empty());
        assert_eq!(graph.edges().count(), 0);
        Ok(())
    }
}
