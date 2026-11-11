//! MaterialX documents as USD layers: the read-only `.mtlx` file format of C++
//! OpenUSD's `usdMtlx` plugin.
//!
//! [`MtlxFileFormat`] reads a MaterialX document into a layer of `UsdShade`
//! specs, so a reference, payload or sublayer naming a `.mtlx`, or a `.mtlx`
//! opened as a stage's root layer, composes like any other layer. A stage
//! reads the format once a builder is given it:
//!
//! ```no_run
//! use openusd::usd;
//!
//! let stage = usd::Stage::builder()
//!     .format(&openusd_mtlx::MTLX)
//!     .open("shot.usda")?;
//! # Ok::<(), openusd::Error>(())
//! ```
//!
//! The layer is laid out as `usdMtlx`'s reader (`reader.cpp`) lays it out:
//!
//! - each material node (`surfacematerial`, `volumematerial`) is a `Material`
//!   at `/MaterialX/Materials/<name>`, with the `MaterialXConfigAPI` schema
//!   and its document's version, and one interface input per input of its
//!   shader nodes' nodedefs, carrying the values the document authors on
//!   them;
//! - each shader node of a material is a `Shader` under it, referencing its
//!   implementation at `/MaterialX/Shaders/<name>` (its `info:id` and
//!   outputs), its inputs connected to the material's interface inputs, or to
//!   the node graph output that feeds them; the material's
//!   `outputs:mtlx:surface`, `outputs:mtlx:displacement` and
//!   `outputs:mtlx:volume` terminals connect to the shaders' outputs;
//! - a `<nodegraph>` is a `NodeGraph` at `/MaterialX/NodeGraphs/<name>`, and
//!   the nodes at the document's own level are the `NodeGraph` at
//!   `/MaterialX/NodeGraphs`; a material reading one brings it under itself
//!   by an internal reference.
//!
//! A node's `info:id` is the name of its nodedef: the one the document
//! declares, or one of MaterialX 1.39's `stdlib`, `pbrlib` and `bxdf`
//! libraries, which the crate embeds. Each input of a colour type, and the
//! `file` of an image with a colour output, carries its effective
//! `colorspace` as `colorSpace` metadata, and a `fileprefix` is folded into
//! each `filename` value; asset paths stay as authored, so they anchor at the
//! `.mtlx` that authors them.
//!
//! What the translation cannot represent faithfully it reports in the
//! layer's `customLayerData`, as the strings of `mtlx:warnings` (a key path:
//! `warnings` in the `mtlx` dictionary), beside the document's `colorSpace`
//! as `usdMtlx` writes it there.
//!
//! The format reads; it does not write. Shading a translated document is a
//! renderer's work, as it is in C++.

mod document;
mod nodedefs;
mod reader;

use std::str;

use openusd::{ar, sdf, tf};

pub use document::ReadError;

/// The `.mtlx` file format (C++ `UsdMtlxFileFormat`).
///
/// Stateless: a registry is given the one [`MTLX`].
#[derive(Debug, Default, Clone, Copy)]
pub struct MtlxFileFormat;

/// The `.mtlx` format, for [`sdf::LayerRegistry::with_format`] or
/// [`StageBuilder::format`](openusd::usd::StageBuilder::format).
pub static MTLX: MtlxFileFormat = MtlxFileFormat;

impl sdf::FileFormat for MtlxFileFormat {
    fn format_id(&self) -> tf::Token {
        "mtlx".into()
    }

    fn extensions(&self) -> &[&str] {
        &["mtlx"]
    }

    fn caps(&self) -> sdf::FileFormatCaps {
        sdf::FileFormatCaps::READ
    }

    fn read_bytes(&self, bytes: ar::AssetBuffer, source_name: &str) -> Result<sdf::LayerData, sdf::FormatError> {
        let text = str::from_utf8(&bytes).map_err(|error| sdf::FormatError::Decode(Box::new(error)))?;
        let doc = document::parse(text, source_name).map_err(|error| sdf::FormatError::Decode(Box::new(error)))?;
        let data = reader::translate(&doc).map_err(|error| sdf::FormatError::Decode(Box::new(error)))?;
        Ok(Box::new(data))
    }

    fn write(&self, _: &dyn sdf::AbstractData, _: &mut dyn sdf::WriteSeek) -> Result<(), sdf::FormatError> {
        Err(sdf::FormatError::Encode {
            reason: "the mtlx format is read-only".into(),
        })
    }
}
