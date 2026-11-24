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
//!   them; a material node that inherits from another specializes it;
//! - each shader node of a material is a `Shader` under it, referencing its
//!   implementation at `/MaterialX/Shaders/<name>` (its `info:id` and
//!   outputs), its inputs connected to the material's interface inputs, or to
//!   the node graph output that feeds them; the material's
//!   `outputs:mtlx:surface`, `outputs:mtlx:displacement`,
//!   `outputs:mtlx:volume` and `outputs:light` connect to the shaders'
//!   outputs, and a shader node's `<token>`s are string primvars of the
//!   material;
//! - a `<nodegraph>` is a `NodeGraph` at `/MaterialX/NodeGraphs/<name>`, and
//!   the nodes at the document's own level are the `NodeGraph` at
//!   `/MaterialX/NodeGraphs`; a material reading one brings it under itself
//!   by an internal reference.
//!
//! A node's `info:id` is the name of its nodedef: one the document declares
//! or includes, or one of MaterialX 1.39's libraries, which the crate embeds.
//! A document's `xi:include`s are read with it, each found from the document
//! that includes it. A `fileprefix` is folded into each `filename` value;
//! asset paths stay as authored, so they anchor at the `.mtlx` that authors
//! them.
//!
//! The document's `colorspace` is the `colorSpace` of the layer's
//! `customLayerData`, as `usdMtlx` writes it there, and its `cms` and
//! `cmsconfig` are the layer's `colorManagementSystem` and
//! `colorConfiguration`. An input of a colour type, or the `file` of an image
//! with a colour output, carries its `colorspace` as `colorSpace` metadata
//! where that is not the document's. A layer referencing a material does not
//! compose the document's own `colorspace`, in C++ as here.
//!
//! The layer differs from the one `usdMtlx` writes in three ways:
//!
//! - `config:mtlx:version` is the version the document declares. MaterialX
//!   upgrades a document to its own version as it reads it, and `usdMtlx`
//!   writes that one; this crate translates the document as written.
//! - A node no nodedef matches by its inputs is given the nodedef of its
//!   category and type, where `usdMtlx` writes it with no `info:id`. A
//!   document older than the libraries is the usual cause.
//! - What the translation leaves out it lists in the layer's
//!   `customLayerData`, as the strings of `mtlx:warnings` (a key path:
//!   `warnings` in the `mtlx` dictionary), where `usdMtlx` posts warnings.
//!
//! The format reads; it does not write. Shading a translated document is a
//! renderer's work, as it is in C++.

mod document;
mod nodedefs;
mod reader;

use std::collections::HashSet;
use std::str;

use openusd::{ar, sdf, tf};

use document::Included;
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

    /// Decodes a document that has no location. The documents it includes
    /// are reported in the layer's warnings and not read.
    fn read_bytes(&self, bytes: ar::AssetBuffer, source_name: &str) -> Result<sdf::LayerData, sdf::FormatError> {
        layer(decode(&bytes, source_name, &mut |_| Ok(Included::Unfound)))
    }

    /// Reads the document at `resolved` and the documents it includes.
    ///
    /// The layer does not record which documents it included. A reload that
    /// is not forced reads it again only when the document at `resolved`
    /// itself changed.
    // TODO: report the included documents as the layer's external asset
    // dependencies (C++ `SdfFileFormat::GetExternalAssetDependencies`), a
    // seam `sdf::FileFormat` and `sdf::Layer::reload` do not have yet.
    fn read(
        &self,
        resolver: &dyn ar::Resolver,
        resolved: &ar::ResolvedPath,
    ) -> Result<sdf::LayerData, sdf::FormatError> {
        let bytes = resolver.open_asset(resolved)?.into_buffer()?;
        layer(located(
            resolver,
            resolved,
            &bytes,
            &mut Vec::new(),
            &mut HashSet::new(),
        ))
    }

    fn write(&self, _: &dyn sdf::AbstractData, _: &mut dyn sdf::WriteSeek) -> Result<(), sdf::FormatError> {
        Err(sdf::FormatError::Encode {
            reason: "the mtlx format is read-only".into(),
        })
    }
}

/// The layer a read document translates into.
fn layer(doc: Result<document::Document, ReadError>) -> Result<sdf::LayerData, sdf::FormatError> {
    let data = doc
        .and_then(|doc| reader::translate(&doc))
        .map_err(|error| sdf::FormatError::Decode(Box::new(error)))?;
    Ok(Box::new(data))
}

/// The document `bytes` hold, read from `source_name`.
fn decode(
    bytes: &[u8],
    source_name: &str,
    include: &mut document::Include<'_>,
) -> Result<document::Document, ReadError> {
    // TODO: decode the encoding the XML declaration names (MaterialX's
    // reader converts Latin-1 and UTF-16 documents); only UTF-8 reads.
    let text = str::from_utf8(bytes).map_err(|error| ReadError::Encoding {
        source_name: source_name.to_owned(),
        error,
    })?;
    document::parse(text, source_name, include)
}

/// How deep includes nest (MaterialX `MAX_XINCLUDE_DEPTH`).
const MAX_INCLUDE_DEPTH: usize = 256;

/// The document `bytes` hold, read from `resolved`, with the documents it
/// includes: each is found from the document including it and opened
/// through `resolver` (C++ `UsdMtlxReadDocument`). `parents` are the
/// documents being read, the outermost first, and `included` every document
/// included so far. One of those is not read again: its elements' names are
/// taken, and a second copy would add nothing.
fn located(
    resolver: &dyn ar::Resolver,
    resolved: &ar::ResolvedPath,
    bytes: &[u8],
    parents: &mut Vec<String>,
    included: &mut HashSet<String>,
) -> Result<document::Document, ReadError> {
    let source_name = resolved.to_string();
    parents.push(source_name.clone());
    let doc = decode(bytes, &source_name, &mut |href| {
        // TODO: read the includes of a document inside a package. C++ joins
        // the `href` onto the document's packaged path
        // (`ArJoinPackageRelativePath`); `ar::create_identifier` anchors at
        // the package file, where another document of the name may sit.
        if ar::is_package_relative_path(&source_name) {
            return Ok(Included::Unfound);
        }
        if parents.len() >= MAX_INCLUDE_DEPTH {
            return Err(ReadError::IncludeDepth {
                source_name: source_name.clone(),
                href: href.to_owned(),
            });
        }
        let identifier = ar::create_identifier(resolver, href, Some(resolved));
        let target = resolver
            .resolve(&identifier)
            .ok_or_else(|| ReadError::IncludeUnresolved {
                source_name: source_name.clone(),
                href: href.to_owned(),
            })?;
        let included_name = target.to_string();
        if parents.contains(&included_name) {
            return Err(ReadError::IncludeCycle {
                source_name: source_name.clone(),
                href: href.to_owned(),
            });
        }
        if !included.insert(included_name.clone()) {
            return Ok(Included::Already);
        }
        let bytes = resolver
            .open_asset(&target)
            .and_then(|asset| asset.into_buffer())
            .map_err(|error| ReadError::Open {
                source_name: included_name,
                error,
            })?;
        let mut library = located(resolver, &target, &bytes, parents, included)?;
        // A file the library names beside itself is not beside this
        // document when the two sit apart. The directory part of an `href`
        // found beside this document leads from here to the library, and
        // goes before each such name as a `fileprefix` would. A library
        // found another way has its names anchored by the resolver, each as
        // a path beside the library whether or not a file is there: a
        // `<UDIM>` pattern names none.
        // TODO: an `href` that is a symbolic link leads to the link, and
        // the names anchor beside the link where the library they belong to
        // sits elsewhere; compare the resolved location with the anchored
        // `href`.
        let directory = href.rfind(['/', '\\']).map_or("", |end| &href[..=end]);
        let beside = identifier != href && !document::is_absolute(href);
        library.anchor_filenames(&|path| {
            if ar::is_uri(resolver, path) || document::is_absolute(path) {
                path.to_owned()
            } else if beside {
                document::with_prefix(directory, path)
            } else if path.starts_with("./") || path.starts_with("../") {
                ar::create_identifier(resolver, path, Some(&target))
            } else {
                ar::create_identifier(resolver, &format!("./{path}"), Some(&target))
            }
        });
        Ok(Included::Document(Box::new(library)))
    });
    parents.pop();
    doc
}
