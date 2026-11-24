# openusd-mtlx

[![Crates.io Version](https://img.shields.io/crates/v/openusd-mtlx)](https://crates.io/crates/openusd-mtlx)
[![docs.rs](https://img.shields.io/docsrs/openusd-mtlx)](https://docs.rs/crate/openusd-mtlx/latest)
[![CI](https://github.com/mxpv/openusd/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/mxpv/openusd/actions/workflows/ci.yml)

A read-only `.mtlx` file format for [openusd](https://github.com/mxpv/openusd/tree/main/crates/openusd): a MaterialX
document opens as a USD layer laid out the way C++ OpenUSD's `usdMtlx`
plugin lays it out, so a reference, payload or sublayer naming a `.mtlx`
composes into ordinary `UsdShade` prims.

```rust,no_run
use openusd::usd;

let stage = usd::Stage::builder()
    .format(&openusd_mtlx::MTLX)
    .open("shot.usda")?;
# Ok::<(), openusd::Error>(())
```

Shading the result is a renderer's work, as it is in C++: this crate
translates the document and evaluates nothing.

## What it reads

- Material nodes, each a `Material` at `/MaterialX/Materials/<name>` with
  the `MaterialXConfigAPI` schema and one interface input per input of its
  shaders' nodedefs. A material that inherits from another specializes it.
- Surface, volume, displacement and light shader nodes, each a `Shader`
  under its material whose `info:id` names its MaterialX nodedef, connected
  to the material's `outputs:mtlx:surface`, `outputs:mtlx:volume`,
  `outputs:mtlx:displacement` or `outputs:light`.
- `<nodegraph>`s and the nodes at the document's own level, as `NodeGraph`s
  under `/MaterialX/NodeGraphs` that a material brings under itself by an
  internal reference.
- Nodedefs from MaterialX 1.39's libraries (`stdlib`, `pbrlib`, `nprlib`,
  `cmlib`, `lights` and `bxdf`), embedded under `libraries/` (Apache-2.0,
  see `libraries/LICENSE`), and from those the document declares.
- `xi:include`, each included document found from the one including it.
- Values of every MaterialX type USD has a value type for; a type it has
  none for (`BSDF`) is a `token` with the type as its `renderType`.
- `fileprefix`, folded into each `filename` value.
- `colorspace`, as `colorSpace` metadata on an input where it is not the
  document's, and the document's `colorspace`, `cms` and `cmsconfig` as
  layer metadata.
- `<token>`s of a shader node, as string primvars of its material.
- `doc`, `helptext`, `enum`, `uifolder` and `uiname`, as documentation,
  allowed tokens, display group and display name.

Whatever the translation leaves out is listed in the layer's
`customLayerData`, as the strings of `mtlx:warnings`.

## What it does not read yet

- `<look>`s as material variants, and collections.
- Custom nodedefs implemented by a `<nodegraph>`, and a shader node inside
  a node graph.
- A document older than MaterialX 1.39 is not upgraded before it is read.
- `valuecurve` animation.
- An `xi:include` in a document inside a package.
- The `namespace` of an included document: its elements keep their plain
  names.
- The `target` of a node or nodedef, and `<typedef>`s.
- A reload that is not forced does not notice a change in an included
  document; only the document that was opened is checked.
- A document in an encoding other than UTF-8.

## Differences from `usdMtlx`

- `config:mtlx:version` is the version the document declares. `usdMtlx`
  writes the version MaterialX upgraded the document to.
- A node no nodedef matches by its inputs is given the nodedef of its
  category and type, with a warning. `usdMtlx` writes it with no `info:id`.
