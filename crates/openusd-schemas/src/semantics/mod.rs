//! UsdSemantics schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdSemantics` family — what a prim *is*, said in labels a pipeline agrees
//! on rather than in prim names or paths.
//!
//! [`LabelsAPI`] is applied once per taxonomy, and the instance name *is* the
//! taxonomy: applying it as `category` gives the prim a
//! `semantics:labels:category` array to hold that taxonomy's labels. A prim can
//! carry as many taxonomies at once as a pipeline has questions to ask of it.
//!
//! [`LabelsAPI::direct_taxonomies`] and [`LabelsAPI::inherited_taxonomies`]
//! answer which taxonomies a prim can be asked about. The labels it answers
//! with, resolved down namespace and over time, are C++
//! `UsdSemanticsLabelsQuery`, which this crate does not have yet.
//!
//! # Example
//!
//! ```
//! use openusd::tf;
//! use openusd::usd::Stage;
//! use openusd_schemas::semantics::LabelsAPI;
//!
//! let stage = Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda")
//!     .unwrap();
//! let prim = stage.define_prim("/World/Chair").unwrap();
//!
//! // One application per taxonomy, named by it.
//! let category = LabelsAPI::apply(&prim, "category").unwrap();
//! category.create_labels_attr().unwrap().set(vec![tf::Token::new("furniture")]).unwrap();
//!
//! assert_eq!(
//!     category.labels_attr().get::<Vec<tf::Token>>().unwrap(),
//!     Some(vec![tf::Token::new("furniture")]),
//! );
//! ```

openusd::include_schema!("usdSemantics");

mod taxonomies;
