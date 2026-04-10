//! Prim Cache Population (PCP) — the composition engine.
//!
//! This module implements USD's composition algorithm, which merges opinions
//! from multiple layers into a single composed scene graph. It is the Rust
//! equivalent of [Pixar's PCP module](https://openusd.org/dev/api/pcp_page_front.html).
//!
//! # LIVRPS strength ordering
//!
//! USD composes opinions using six arc types, ordered by strength:
//!
//! 1. **L**ocal — direct opinions in the root layer stack (sublayers)
//! 2. **I**nherits — opinions from class prims (`inherits = </Class>`)
//! 3. **V**ariants — opinions from the selected variant (`variants = { string v = "sel" }`)
//! 4. **R**eferences — opinions from referenced layers (`references = @model.usd@</Prim>`)
//! 5. **P**ayloads — like references but deferred (`payload = @heavy.usd@</Prim>`)
//! 6. **S**pecializes — like inherits but weakest (`specializes = </Base>`)
//!
//! Within each arc type, opinions are ordered by layer strength (root layer
//! strongest, deepest sublayer weakest).
//!
//! # Module structure
//!
//! | Module | C++ equivalent | Description |
//! |--------|---------------|-------------|
//! | [`cache`] | `PcpCache` | Lazily-built composition cache. Main interface for [`Stage`](crate::Stage). Precomputes sublayer stacks. |
//! | [`error`] | `PcpErrorBase` | Composition errors: arc cycles, unresolved layers, missing/invalid `defaultPrim`. |
//! | [`index`] | `PcpPrimIndex` | Per-prim composition graph: arena-based DAG of [`Node`]s with parent/child/sibling and origin links. |
//!
//! Layer collection lives in [`crate::layer`] (analogous to `PcpLayerStack`).
//!
//! # Architecture
//!
//! Each [`PrimIndex`](index::PrimIndex) is an arena-based graph of [`Node`]s.
//! Nodes carry parent/child/sibling links (forming a tree) and an `origin`
//! link (forming a DAG for implied-inherit tracking). After construction,
//! nodes are ordered strongest-to-weakest so value resolution is a linear scan.
//!
//! Composition is driven by a [`CompositionContext`](index::CompositionContext)
//! that flows from parent prims to children. The context carries:
//!
//! - **Variant selections** from all ancestors, so descendant prims resolve
//!   variant sets without recomputing ancestor composition.
//! - **Arc mappings** from ancestors, recording how composed paths map to
//!   paths in other layers. Used for descendant namespace remapping and
//!   implied inherit propagation.
//!
//! The [`Cache`](cache::Cache) stores both the [`PrimIndex`](index::PrimIndex)
//! and the [`CompositionContext`](index::CompositionContext) for each composed
//! prim. During depth-first traversal, parents are always composed before
//! children, so the context chain is always populated. Each per-prim build
//! takes only shared references, making it suitable for future parallel
//! execution.
//!
//! Composition errors ([`Error`]) are returned from [`Cache`](cache::Cache)
//! methods and handled by the [`Stage`](crate::Stage)'s error callback.
//! The callback decides whether to skip the broken arc and continue or
//! abort composition entirely.
//!
//! See <https://openusd.org/release/glossary.html#livrps-strength-ordering>

pub(crate) mod cache;
mod error;
pub(crate) mod index;

pub(crate) use cache::Cache;
pub use error::Error;
pub use index::{ArcType, Node, NodeIndex, PrimIndex};
