//! Binary crate file writer.
//!
//! Inverse of [`CrateFile`](crate::usdc::CrateFile): walks an [`AbstractData`]
//! layer, interns tokens/strings/paths/fields/fieldsets, and emits the six
//! structural sections (`TOKENS`, `STRINGS`, `FIELDS`, `FIELDSETS`, `PATHS`,
//! `SPECS`) followed by the table of contents, then rewrites the bootstrap
//! header at offset 0 with the final TOC offset.

use std::collections::HashMap;
use std::io::{Seek, SeekFrom, Write};

use anyhow::{bail, Context, Result};
use bytemuck::{bytes_of, Pod};
use half::f16;
use num_traits::{AsPrimitive, PrimInt};

use crate::sdf::{AbstractData, LayerOffset, ListOp, Path, Payload, Reference, Value};

use super::coding;
use super::layout::{
    version, Bootstrap, ListOpHeader, Section, Spec as FileSpec, Type, ValueRep, Version, SECTION_NAME_MAX_LENGTH,
};

/// Crate format version this writer emits. Supports all features the reader
/// handles (time samples, relocates, path expressions, etc.).
const WRITER_VERSION: Version = version(0, 12, 0);

/// Emits `.usdc` binary from an [`AbstractData`].
pub struct CrateWriter;

impl CrateWriter {
    /// Write the layer to a file on disk.
    pub fn write_to_file(data: &dyn AbstractData, path: impl AsRef<std::path::Path>) -> Result<()> {
        let mut file = std::fs::File::create(path).context("failed to create usdc file")?;
        Self::write(data, &mut file)?;
        file.sync_all().context("failed to sync usdc file to disk")?;
        Ok(())
    }

    /// Write the layer to any seekable writer.
    pub fn write<W: Write + Seek>(data: &dyn AbstractData, out: &mut W) -> Result<()> {
        let mut packer = Packer::new(out);
        packer.pack(data)?;
        packer.finish()
    }
}

// ---------------------------------------------------------------------------
// Packer
// ---------------------------------------------------------------------------

struct Packer<'w, W: Write + Seek> {
    out: &'w mut W,

    // Interning tables.
    tokens: Interner<String>,
    /// Each entry is an index into `tokens`.
    strings: Interner<u32>,
    paths: Interner<Path>,
    /// Fields are keyed by `(token_idx, value_rep_raw)` — `ValueRep` has no
    /// `Hash` impl so we hash the underlying `u64`.
    fields: Interner<(u32, u64)>,

    /// Flat, None-terminated sequence of field indices (one run per spec).
    fieldsets: Vec<Option<u32>>,
    specs: Vec<FileSpec>,

    /// Accumulated section offsets (for TOC).
    sections_written: Vec<(String, u64, u64)>,
}

impl<'w, W: Write + Seek> Packer<'w, W> {
    fn new(out: &'w mut W) -> Self {
        Self {
            out,
            tokens: Interner::new(),
            strings: Interner::new(),
            paths: Interner::new(),
            fields: Interner::new(),
            fieldsets: Vec::new(),
            specs: Vec::new(),
            sections_written: Vec::new(),
        }
    }

    /// Build the in-memory tables and write out-of-line values to the file.
    fn pack(&mut self, data: &dyn AbstractData) -> Result<()> {
        // Reserve bootstrap header; heap data starts immediately after.
        self.out
            .seek(SeekFrom::Start(std::mem::size_of::<Bootstrap>() as u64))?;

        // Pre-intern the root path at index 0 (always `/`).
        let root = Path::abs_root();
        debug_assert_eq!(self.intern_path(root.clone()), 0);

        // Intern every path referenced by the data in one sweep. This seeds
        // `paths` before any field that may reference paths is serialized.
        let paths = data.paths();
        for path in &paths {
            self.intern_path(path.clone());
        }

        // Walk specs and build the fieldsets + specs tables.
        for path in &paths {
            let ty = data
                .spec_type(path)
                .ok_or_else(|| anyhow::anyhow!("path {path} reported by paths() has no spec"))?;
            let path_idx = self.intern_path(path.clone());

            let fieldset_idx = self.fieldsets.len() as u32;
            if let Some(field_names) = data.list(path) {
                for name in field_names {
                    let value = data.get(path, &name)?.into_owned();
                    let token_idx = self.tokens.intern(name);
                    let rep = self.write_value(&value)?;
                    let field_idx = self.fields.intern((token_idx, rep.0));
                    self.fieldsets.push(Some(field_idx));
                }
            }
            self.fieldsets.push(None);

            self.specs.push(FileSpec {
                path_index: path_idx as usize,
                fieldset_index: fieldset_idx as usize,
                spec_type: ty,
            });
        }

        // Pre-intern the path-segment tokens so they exist in `self.tokens`
        // before the TOKENS section is written. `encode_paths` would intern
        // them later otherwise, and those extra tokens would never make it
        // into the file.
        for i in 0..self.paths.items.len() {
            let segment = {
                let p = &self.paths.items[i];
                if p.as_str() == "/" {
                    continue;
                }
                let (segment, _) = last_segment(p);
                segment.to_owned()
            };
            self.tokens.intern(segment);
        }

        Ok(())
    }

    /// Intern a path and all its ancestors so the path tree is complete by the
    /// time [`encode_paths`] DFSes from the root.
    fn intern_path(&mut self, path: Path) -> u32 {
        if !self.paths.index.contains_key(&path) {
            if let Some(parent) = parent_of(&path) {
                self.intern_path(parent);
            }
        }
        self.paths.intern(path)
    }

    /// Emit all sections then the TOC then the bootstrap header.
    fn finish(mut self) -> Result<()> {
        self.write_tokens_section()?;
        self.write_strings_section()?;
        self.write_fields_section()?;
        self.write_fieldsets_section()?;
        self.write_paths_section()?;
        self.write_specs_section()?;

        let toc_offset = self.pos()?;
        self.write_toc()?;

        self.write_bootstrap(toc_offset)?;
        Ok(())
    }

    // -----------------------------------------------------------------
    // Low-level positioning
    // -----------------------------------------------------------------

    fn pos(&mut self) -> Result<u64> {
        Ok(self.out.stream_position()?)
    }

    fn write_pod<T: Pod>(&mut self, v: &T) -> Result<()> {
        self.out.write_all(bytes_of(v))?;
        Ok(())
    }

    fn write_count(&mut self, n: u64) -> Result<()> {
        self.write_pod(&n)
    }

    fn write_bytes(&mut self, b: &[u8]) -> Result<()> {
        self.out.write_all(b)?;
        Ok(())
    }

    // -----------------------------------------------------------------
    // Sections
    // -----------------------------------------------------------------

    fn begin_section(&mut self, name: &str) -> Result<u64> {
        let start = self.pos()?;
        self.sections_written.push((name.to_owned(), start, 0));
        Ok(start)
    }

    fn end_section(&mut self) -> Result<()> {
        let end = self.pos()?;
        if let Some(last) = self.sections_written.last_mut() {
            last.2 = end - last.1;
        }
        Ok(())
    }

    fn write_tokens_section(&mut self) -> Result<()> {
        self.begin_section(Section::TOKENS)?;
        self.write_count(self.tokens.items.len() as u64)?;

        // Concatenate tokens with null terminators, plus trailing null.
        let mut buf = Vec::new();
        for t in &self.tokens.items {
            buf.extend_from_slice(t.as_bytes());
            buf.push(b'\0');
        }
        // `buffer.last() == Some(b'\0')` is enforced by the reader — that's
        // already the case because every token ends with a `\0`.

        self.write_count(buf.len() as u64)?;
        self.write_lz4_compressed(&buf)?;
        self.end_section()
    }

    fn write_strings_section(&mut self) -> Result<()> {
        self.begin_section(Section::STRINGS)?;
        let n = self.strings.items.len();
        self.write_count(n as u64)?;
        for i in 0..n {
            let idx = self.strings.items[i];
            self.write_pod(&idx)?;
        }
        self.end_section()
    }

    fn write_fields_section(&mut self) -> Result<()> {
        self.begin_section(Section::FIELDS)?;
        let field_count = self.fields.items.len();
        self.write_count(field_count as u64)?;

        // Compressed token-index array.
        let indexes: Vec<u32> = self.fields.items.iter().map(|(tok, _)| *tok).collect();
        let encoded = coding::encode_ints(&indexes);
        self.write_lz4_compressed(&encoded)?;

        // Compressed value-rep array (raw LZ4 over the bytes).
        let mut reps_buf = Vec::with_capacity(field_count * 8);
        for (_, rep) in &self.fields.items {
            reps_buf.extend_from_slice(&rep.to_le_bytes());
        }
        self.write_lz4_compressed(&reps_buf)?;

        self.end_section()
    }

    fn write_fieldsets_section(&mut self) -> Result<()> {
        self.begin_section(Section::FIELDSETS)?;
        self.write_count(self.fieldsets.len() as u64)?;

        let vec: Vec<u32> = self.fieldsets.iter().map(|o| o.unwrap_or(u32::MAX)).collect();
        let encoded = coding::encode_ints(&vec);
        self.write_lz4_compressed(&encoded)?;
        self.end_section()
    }

    fn write_paths_section(&mut self) -> Result<()> {
        self.begin_section(Section::PATHS)?;
        let path_count = self.paths.items.len();
        self.write_count(path_count as u64)?;

        let (path_indexes, element_token_indexes, jumps) = self.encode_paths()?;

        self.write_count(path_indexes.len() as u64)?;
        self.write_lz4_compressed(&coding::encode_ints(&path_indexes))?;
        self.write_lz4_compressed(&coding::encode_ints(&element_token_indexes))?;
        self.write_lz4_compressed(&coding::encode_ints(&jumps))?;

        self.end_section()
    }

    fn write_specs_section(&mut self) -> Result<()> {
        self.begin_section(Section::SPECS)?;
        let n = self.specs.len();
        self.write_count(n as u64)?;

        let path_ids: Vec<u32> = self.specs.iter().map(|s| s.path_index as u32).collect();
        let fs_ids: Vec<u32> = self.specs.iter().map(|s| s.fieldset_index as u32).collect();
        let type_ids: Vec<u32> = self.specs.iter().map(|s| s.spec_type as u32).collect();

        self.write_lz4_compressed(&coding::encode_ints(&path_ids))?;
        self.write_lz4_compressed(&coding::encode_ints(&fs_ids))?;
        self.write_lz4_compressed(&coding::encode_ints(&type_ids))?;

        self.end_section()
    }

    fn write_toc(&mut self) -> Result<()> {
        // `finish()` consumes `self` immediately after this call, so taking
        // the vec out is fine; it lets us iterate without a pre-copy.
        let sections = std::mem::take(&mut self.sections_written);
        self.write_count(sections.len() as u64)?;
        for (name, start, size) in &sections {
            let mut name_buf = [0_u8; SECTION_NAME_MAX_LENGTH + 1];
            let bytes = name.as_bytes();
            let n = bytes.len().min(SECTION_NAME_MAX_LENGTH);
            name_buf[..n].copy_from_slice(&bytes[..n]);
            self.write_bytes(&name_buf)?;
            self.write_pod(start)?;
            self.write_pod(size)?;
        }
        Ok(())
    }

    fn write_bootstrap(&mut self, toc_offset: u64) -> Result<()> {
        let mut boot = Bootstrap::default();
        boot.ident = *b"PXR-USDC";
        boot.version[0] = WRITER_VERSION.major;
        boot.version[1] = WRITER_VERSION.minor;
        boot.version[2] = WRITER_VERSION.patch;
        boot.toc_offset = toc_offset;

        self.out.seek(SeekFrom::Start(0))?;
        self.write_pod(&boot)?;
        Ok(())
    }

    // -----------------------------------------------------------------
    // Paths — DFS over the prim/property tree.
    // -----------------------------------------------------------------

    fn encode_paths(&mut self) -> Result<(Vec<u32>, Vec<i32>, Vec<i32>)> {
        let paths = self.paths.items.clone();
        let by_index: HashMap<Path, u32> = paths.iter().enumerate().map(|(i, p)| (p.clone(), i as u32)).collect();

        // Build parent → children map. Skip empty paths — they can appear in
        // `Value::Path` / ListOp items as placeholders (e.g. internal payload
        // paths) and are represented by the reader as the default empty slot
        // in the paths array.
        let mut children: HashMap<Path, Vec<Path>> = HashMap::new();
        for p in &paths {
            if p.as_str() == "/" || p.is_empty() {
                continue;
            }
            let parent = parent_of(p).ok_or_else(|| anyhow::anyhow!("path {p} has no parent but is not root"))?;
            children.entry(parent).or_default().push(p.clone());
        }
        for list in children.values_mut() {
            list.sort();
        }

        let root = Path::abs_root();
        let mut path_indexes = Vec::with_capacity(paths.len());
        let mut tokens = Vec::with_capacity(paths.len());
        let mut jumps = Vec::with_capacity(paths.len());

        self.emit_path_node(
            &root,
            &children,
            &by_index,
            true,
            &mut path_indexes,
            &mut tokens,
            &mut jumps,
        )?;

        Ok((path_indexes, tokens, jumps))
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_path_node(
        &mut self,
        node: &Path,
        children_map: &HashMap<Path, Vec<Path>>,
        by_index: &HashMap<Path, u32>,
        is_root_chain_root: bool,
        path_indexes: &mut Vec<u32>,
        tokens: &mut Vec<i32>,
        jumps: &mut Vec<i32>,
    ) -> Result<()> {
        let this_idx = path_indexes.len();

        let path_index = *by_index
            .get(node)
            .ok_or_else(|| anyhow::anyhow!("path {node} not interned"))?;
        path_indexes.push(path_index);

        // element_token_indexes: token index of the element name, negative if
        // the path is a prim-property path (so the reader appends via `.`).
        if is_root_chain_root {
            tokens.push(0);
        } else {
            let (segment, is_prop) = last_segment(node);
            let tok_idx = self.tokens.intern(segment.to_owned()) as i32;
            tokens.push(if is_prop { -tok_idx } else { tok_idx });
        }

        // Placeholder; will be set after subtree is emitted.
        jumps.push(0);

        let empty = Vec::new();
        let kids = children_map.get(node).unwrap_or(&empty);
        let has_child = !kids.is_empty();

        // Emit each child in order. Each child takes responsibility for
        // emitting its own subtree and its own sibling (via recursion).
        for (i, kid) in kids.iter().enumerate() {
            let kid_start = path_indexes.len() as i32;
            self.emit_path_node(kid, children_map, by_index, false, path_indexes, tokens, jumps)?;

            // Patch the kid's jump to point at the next sibling if there is one.
            let end = path_indexes.len() as i32;
            let has_sibling = i + 1 < kids.len();
            let kid_jump_slot = kid_start as usize;
            // Determine what `jump` the child should have. `emit_path_node`
            // wrote a provisional value based on its own children; we must
            // combine with sibling info here.
            let kid_has_child = kid_had_child(&jumps[kid_jump_slot]);
            jumps[kid_jump_slot] = compute_jump(kid_has_child, has_sibling, end - kid_start);
        }

        // Root (node=`/`): its own jump depends only on children, no siblings.
        // Non-root with siblings gets patched by the caller; non-root leaves
        // need the right final value now.
        jumps[this_idx] = compute_jump(has_child, false, 0);

        Ok(())
    }

    // -----------------------------------------------------------------
    // Value encoding
    // -----------------------------------------------------------------

    fn write_value(&mut self, value: &Value) -> Result<ValueRep> {
        match value {
            Value::None => Ok(rep_inline(Type::Invalid, 0)),
            Value::ValueBlock => Ok(rep_inline(Type::ValueBlock, 0)),
            Value::Value => Ok(rep_inline(Type::Value, 0)),

            Value::Bool(b) => Ok(rep_inline(Type::Bool, if *b { 1 } else { 0 })),
            Value::Uchar(v) => Ok(rep_inline(Type::Uchar, *v as u64)),
            Value::Int(v) => Ok(rep_inline(Type::Int, *v as u32 as u64)),
            Value::Uint(v) => Ok(rep_inline(Type::Uint, *v as u64)),
            Value::Float(f) => Ok(rep_inline(Type::Float, f.to_bits() as u64)),
            Value::Half(h) => Ok(rep_inline(Type::Half, h.to_bits() as u64)),

            Value::Specifier(s) => Ok(rep_inline(Type::Specifier, *s as u32 as u64)),
            Value::Permission(p) => Ok(rep_inline(Type::Permission, *p as u32 as u64)),
            Value::Variability(v) => Ok(rep_inline(Type::Variability, *v as u32 as u64)),

            Value::Token(s) => {
                let idx = self.tokens.intern(s.clone());
                Ok(rep_inline(Type::Token, idx as u64))
            }
            Value::AssetPath(s) => {
                let idx = self.tokens.intern(s.clone());
                Ok(rep_inline(Type::AssetPath, idx as u64))
            }
            Value::String(s) => {
                let sidx = self.intern_string(s);
                Ok(rep_inline(Type::String, sidx as u64))
            }

            // Out-of-line scalars
            Value::Int64(v) => self.write_pod_out(Type::Int64, v),
            Value::Uint64(v) => self.write_pod_out(Type::Uint64, v),
            Value::Double(v) => self.write_pod_out(Type::Double, v),
            Value::TimeCode(v) => self.write_pod_out(Type::TimeCode, v),

            // Inline vectors when all components fit in i8.
            Value::Vec2h(a) => self.write_pod_out(Type::Vec2h, a),
            Value::Vec3h(a) => self.write_pod_out(Type::Vec3h, a),
            Value::Vec4h(a) => self.write_pod_out(Type::Vec4h, a),
            Value::Quath(a) => self.write_pod_out(Type::Quath, a),

            Value::Vec2f(a) => self.write_pod_out(Type::Vec2f, a),
            Value::Vec3f(a) => self.write_pod_out(Type::Vec3f, a),
            Value::Vec4f(a) => self.write_pod_out(Type::Vec4f, a),
            Value::Quatf(a) => self.write_pod_out(Type::Quatf, a),

            Value::Vec2d(a) => self.write_pod_out(Type::Vec2d, a),
            Value::Vec3d(a) => self.write_pod_out(Type::Vec3d, a),
            Value::Vec4d(a) => self.write_pod_out(Type::Vec4d, a),
            Value::Quatd(a) => self.write_pod_out(Type::Quatd, a),

            Value::Vec2i(a) => self.write_pod_out(Type::Vec2i, a),
            Value::Vec3i(a) => self.write_pod_out(Type::Vec3i, a),
            Value::Vec4i(a) => self.write_pod_out(Type::Vec4i, a),

            Value::Matrix2d(a) => self.write_pod_out(Type::Matrix2d, a),
            Value::Matrix3d(a) => self.write_pod_out(Type::Matrix3d, a),
            Value::Matrix4d(a) => self.write_pod_out(Type::Matrix4d, a),

            // Arrays — all out-of-line, uncompressed.
            Value::BoolVec(v) => {
                let bytes: Vec<u8> = v.iter().map(|b| if *b { 1 } else { 0 }).collect();
                self.write_array(Type::Bool, v.len(), &bytes)
            }
            Value::UcharVec(v) => self.write_array(Type::Uchar, v.len(), v),
            Value::IntVec(v) => self.write_array_ints::<i32>(Type::Int, v),
            Value::UintVec(v) => self.write_array_ints::<u32>(Type::Uint, v),
            Value::Int64Vec(v) => self.write_array_ints::<i64>(Type::Int64, v),
            Value::Uint64Vec(v) => self.write_array_ints::<u64>(Type::Uint64, v),
            Value::HalfVec(v) => self.write_array_le_half(v),
            Value::FloatVec(v) => self.write_array_f32(v),
            Value::DoubleVec(v) => self.write_array_f64_type(Type::Double, v),

            Value::Vec2hVec(v) => self.write_array_arr_half::<2>(Type::Vec2h, v),
            Value::Vec3hVec(v) => self.write_array_arr_half::<3>(Type::Vec3h, v),
            Value::Vec4hVec(v) => self.write_array_arr_half::<4>(Type::Vec4h, v),
            Value::QuathVec(v) => self.write_array_arr_half::<4>(Type::Quath, v),
            Value::Vec2fVec(v) => self.write_array_arr_f32::<2>(Type::Vec2f, v),
            Value::Vec3fVec(v) => self.write_array_arr_f32::<3>(Type::Vec3f, v),
            Value::Vec4fVec(v) => self.write_array_arr_f32::<4>(Type::Vec4f, v),
            Value::QuatfVec(v) => self.write_array_arr_f32::<4>(Type::Quatf, v),
            Value::Vec2dVec(v) => self.write_array_arr_f64::<2>(Type::Vec2d, v),
            Value::Vec3dVec(v) => self.write_array_arr_f64::<3>(Type::Vec3d, v),
            Value::Vec4dVec(v) => self.write_array_arr_f64::<4>(Type::Vec4d, v),
            Value::QuatdVec(v) => self.write_array_arr_f64::<4>(Type::Quatd, v),
            Value::Vec2iVec(v) => self.write_array_arr_i32::<2>(Type::Vec2i, v),
            Value::Vec3iVec(v) => self.write_array_arr_i32::<3>(Type::Vec3i, v),
            Value::Vec4iVec(v) => self.write_array_arr_i32::<4>(Type::Vec4i, v),
            Value::Matrix2dVec(v) => self.write_array_arr_f64::<4>(Type::Matrix2d, v),
            Value::Matrix3dVec(v) => self.write_array_arr_f64::<9>(Type::Matrix3d, v),
            Value::Matrix4dVec(v) => self.write_array_arr_f64::<16>(Type::Matrix4d, v),
            Value::TimeCodeVec(v) => self.write_array_f64_type(Type::TimeCode, v),

            // Strings stored in their own arrays (StringVec also via token lookup).
            Value::StringVec(v) => self.write_string_vec(Type::String, v),
            Value::TokenVec(v) => self.write_token_vec(Type::Token, v),

            // Complex heap types.
            Value::Dictionary(d) => self.write_dictionary(d),
            Value::PathVec(v) => self.write_path_vec(v),
            Value::LayerOffsetVec(v) => self.write_layer_offset_vec(v),
            Value::VariantSelectionMap(m) => self.write_variant_selection_map(m),
            Value::Relocates(v) => self.write_relocates(v),

            Value::Payload(p) => self.write_payload(p),

            Value::TokenListOp(op) => self.write_listop(Type::TokenListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for t in items {
                    let idx = w.tokens.intern(t.clone());
                    w.write_pod(&idx)?;
                }
                Ok(())
            }),
            Value::StringListOp(op) => self.write_listop(Type::StringListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for t in items {
                    let sidx = w.intern_string(t);
                    w.write_pod(&sidx)?;
                }
                Ok(())
            }),
            Value::PathListOp(op) => self.write_listop(Type::PathListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for p in items {
                    let idx = w.intern_path(p.clone());
                    w.write_pod(&idx)?;
                }
                Ok(())
            }),
            Value::ReferenceListOp(op) => self.write_listop(Type::ReferenceListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for r in items {
                    w.write_reference(r)?;
                }
                Ok(())
            }),
            Value::PayloadListOp(op) => self.write_listop(Type::PayloadListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for p in items {
                    w.write_payload_inline(p)?;
                }
                Ok(())
            }),
            Value::IntListOp(op) => self.write_listop(Type::IntListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for v in items {
                    w.write_pod(v)?;
                }
                Ok(())
            }),
            Value::Int64ListOp(op) => self.write_listop(Type::Int64ListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for v in items {
                    w.write_pod(v)?;
                }
                Ok(())
            }),
            Value::UIntListOp(op) => self.write_listop(Type::UIntListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for v in items {
                    w.write_pod(v)?;
                }
                Ok(())
            }),
            Value::UInt64ListOp(op) => self.write_listop(Type::UInt64ListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for v in items {
                    w.write_pod(v)?;
                }
                Ok(())
            }),
            Value::UnregisteredValueListOp(op) => self.write_listop(Type::UnregisteredValueListOp, op, |w, items| {
                w.write_count(items.len() as u64)?;
                for s in items {
                    let sidx = w.intern_string(s);
                    w.write_pod(&sidx)?;
                }
                Ok(())
            }),

            Value::TimeSamples(samples) => self.write_time_samples(samples),

            Value::UnregisteredValue(s) => {
                let idx = self.tokens.intern(s.clone());
                Ok(rep_inline(Type::UnregisteredValue, idx as u64))
            }
            Value::PathExpression(s) => {
                let idx = self.tokens.intern(s.clone());
                Ok(rep_inline(Type::PathExpression, idx as u64))
            }

            // Heterogeneous arrays are produced only by the USDA spline parser;
            // the USDC binary format has no native representation for them.
            Value::ValueVec(_) => bail!(
                "Value::ValueVec cannot be serialized to USDC (the binary format lacks a heterogeneous-array type)"
            ),
        }
    }

    // -----------------------------------------------------------------
    // Heap helpers
    // -----------------------------------------------------------------

    fn intern_string(&mut self, s: &str) -> u32 {
        let tok = self.tokens.intern(s.to_owned());
        self.strings.intern(tok)
    }

    /// Write a POD value at the current position and return a heap ValueRep.
    fn write_pod_out<T: Pod>(&mut self, ty: Type, v: &T) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_pod(v)?;
        Ok(rep_heap(ty, off, false))
    }

    fn write_array<T>(&mut self, ty: Type, count: usize, bytes: &[T]) -> Result<ValueRep>
    where
        T: Pod,
    {
        let off = self.pos()?;
        self.write_count(count as u64)?;
        self.write_bytes(bytemuck::cast_slice(bytes))?;
        Ok(rep_heap(ty, off, true))
    }

    /// Write an integer array, applying the crate format's integer-coding +
    /// LZ4 compression when the array is large enough for the reader to treat
    /// it as compressed (see [`MIN_COMPRESSED_ARRAY_SIZE`]).
    fn write_array_ints<T>(&mut self, ty: Type, v: &[T]) -> Result<ValueRep>
    where
        T: Pod + PrimInt + 'static + AsPrimitive<i64>,
    {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        if v.len() >= MIN_COMPRESSED_ARRAY_SIZE {
            let encoded = coding::encode_ints(v);
            self.write_lz4_compressed(&encoded)?;
            Ok(rep_heap_compressed(ty, off))
        } else {
            for item in v {
                self.write_pod(item)?;
            }
            Ok(rep_heap(ty, off, true))
        }
    }

    fn write_array_le_half(&mut self, v: &[f16]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for h in v {
            self.write_pod(&h.to_bits())?;
        }
        Ok(rep_heap(Type::Half, off, true))
    }

    fn write_array_f32(&mut self, v: &[f32]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for f in v {
            self.write_pod(f)?;
        }
        Ok(rep_heap(Type::Float, off, true))
    }

    fn write_array_f64_type(&mut self, ty: Type, v: &[f64]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for f in v {
            self.write_pod(f)?;
        }
        Ok(rep_heap(ty, off, true))
    }

    fn write_array_arr_half<const N: usize>(&mut self, ty: Type, v: &[[f16; N]]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for arr in v {
            for h in arr {
                self.write_pod(&h.to_bits())?;
            }
        }
        Ok(rep_heap(ty, off, true))
    }

    fn write_array_arr_f32<const N: usize>(&mut self, ty: Type, v: &[[f32; N]]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for arr in v {
            for f in arr {
                self.write_pod(f)?;
            }
        }
        Ok(rep_heap(ty, off, true))
    }

    fn write_array_arr_f64<const N: usize>(&mut self, ty: Type, v: &[[f64; N]]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for arr in v {
            for f in arr {
                self.write_pod(f)?;
            }
        }
        Ok(rep_heap(ty, off, true))
    }

    fn write_array_arr_i32<const N: usize>(&mut self, ty: Type, v: &[[i32; N]]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for arr in v {
            for i in arr {
                self.write_pod(i)?;
            }
        }
        Ok(rep_heap(ty, off, true))
    }

    fn write_token_vec(&mut self, ty: Type, v: &[String]) -> Result<ValueRep> {
        let off = self.pos()?;
        // Token arrays: just write the indices (no inner count for the
        // Type::Token array path — reader does `unpack_array_len` then
        // `read_vec::<u32>(count)`).
        self.write_count(v.len() as u64)?;
        for t in v {
            let idx = self.tokens.intern(t.clone());
            self.write_pod(&idx)?;
        }
        Ok(rep_heap(ty, off, true))
    }

    fn write_string_vec(&mut self, ty: Type, v: &[String]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for s in v {
            let sidx = self.intern_string(s);
            self.write_pod(&sidx)?;
        }
        Ok(rep_heap(ty, off, true))
    }

    fn write_dictionary(&mut self, d: &HashMap<String, Value>) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_dictionary_entries(d)?;
        Ok(rep_heap(Type::Dictionary, off, false))
    }

    /// Serialize a dictionary payload: `count (u64)` followed by
    /// `(string_idx (u32), recursive_offset (i64), ValueRep)` per entry in
    /// sorted key order. Used both for standalone dictionaries and inlined
    /// under a reference's `customData`.
    fn write_dictionary_entries(&mut self, d: &HashMap<String, Value>) -> Result<()> {
        self.write_count(d.len() as u64)?;

        // Stable order for determinism (HashMap is unordered).
        let mut keys: Vec<&String> = d.keys().collect();
        keys.sort();

        for k in keys {
            let sidx = self.intern_string(k);
            self.write_pod(&sidx)?;

            // Layout per entry: i64 recursive_offset, then ValueRep at the
            // target. The reader does `seek(Current(offset - 8))` after
            // consuming the i64, so `recursive_offset = pre_rep - offset_slot`.
            let offset_slot = self.pos()?;
            self.write_pod(&0_i64)?; // placeholder

            let rep = self.write_value(&d[k.as_str()])?;

            let pre_rep = self.pos()?;
            self.write_pod(&rep.0)?;

            let end = self.pos()?;
            let recursive_offset = (pre_rep as i64) - (offset_slot as i64);
            self.out.seek(SeekFrom::Start(offset_slot))?;
            self.write_pod(&recursive_offset)?;
            self.out.seek(SeekFrom::Start(end))?;
        }

        Ok(())
    }

    fn write_path_vec(&mut self, v: &[Path]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for p in v {
            let idx = self.intern_path(p.clone());
            self.write_pod(&idx)?;
        }
        Ok(rep_heap(Type::PathVector, off, false))
    }

    fn write_layer_offset_vec(&mut self, v: &[LayerOffset]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for o in v {
            self.write_pod(o)?;
        }
        Ok(rep_heap(Type::LayerOffsetVector, off, false))
    }

    fn write_variant_selection_map(&mut self, m: &HashMap<String, String>) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(m.len() as u64)?;
        let mut keys: Vec<&String> = m.keys().collect();
        keys.sort();
        for k in keys {
            let ki = self.intern_string(k);
            let vi = self.intern_string(&m[k.as_str()]);
            self.write_pod(&ki)?;
            self.write_pod(&vi)?;
        }
        Ok(rep_heap(Type::VariantSelectionMap, off, false))
    }

    fn write_relocates(&mut self, v: &[(Path, Path)]) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_count(v.len() as u64)?;
        for (src, tgt) in v {
            let sidx = self.intern_path(src.clone());
            let tidx = self.intern_path(tgt.clone());
            self.write_pod(&sidx)?;
            self.write_pod(&tidx)?;
        }
        Ok(rep_heap(Type::Relocates, off, false))
    }

    fn write_payload(&mut self, p: &Payload) -> Result<ValueRep> {
        let off = self.pos()?;
        self.write_payload_inline(p)?;
        Ok(rep_heap(Type::Payload, off, false))
    }

    fn write_payload_inline(&mut self, p: &Payload) -> Result<()> {
        let asset_idx = self.intern_string(&p.asset_path);
        self.write_pod(&asset_idx)?;
        let prim_idx = self.intern_path(p.prim_path.clone());
        self.write_pod(&prim_idx)?;
        let offset = p.layer_offset.unwrap_or_default();
        self.write_pod(&offset)?;
        Ok(())
    }

    fn write_reference(&mut self, r: &Reference) -> Result<()> {
        let asset_idx = self.intern_string(&r.asset_path);
        self.write_pod(&asset_idx)?;
        let prim_idx = self.intern_path(r.prim_path.clone());
        self.write_pod(&prim_idx)?;
        self.write_pod(&r.layer_offset)?;
        self.write_dictionary_entries(&r.custom_data)
    }

    fn write_listop<T, F>(&mut self, ty: Type, op: &ListOp<T>, mut write_items: F) -> Result<ValueRep>
    where
        T: Default + Clone + PartialEq,
        F: FnMut(&mut Self, &[T]) -> Result<()>,
    {
        let off = self.pos()?;

        let mut bits: u8 = 0;
        if op.explicit {
            bits |= ListOpHeader::IS_EXPLICIT;
        }
        if !op.explicit_items.is_empty() {
            bits |= ListOpHeader::HAS_EXPLICIT_ITEMS;
        }
        if !op.added_items.is_empty() {
            bits |= ListOpHeader::HAS_ADDED_ITEMS;
        }
        if !op.deleted_items.is_empty() {
            bits |= ListOpHeader::HAS_DELETED_ITEMS;
        }
        if !op.ordered_items.is_empty() {
            bits |= ListOpHeader::HAS_ORDERED_ITEMS;
        }
        if !op.prepended_items.is_empty() {
            bits |= ListOpHeader::HAS_PREPEND_ITEMS;
        }
        if !op.appended_items.is_empty() {
            bits |= ListOpHeader::HAS_APPENDED_ITEMS;
        }
        self.write_pod(&bits)?;

        if !op.explicit_items.is_empty() {
            write_items(self, &op.explicit_items)?;
        }
        if !op.added_items.is_empty() {
            write_items(self, &op.added_items)?;
        }
        if !op.prepended_items.is_empty() {
            write_items(self, &op.prepended_items)?;
        }
        if !op.appended_items.is_empty() {
            write_items(self, &op.appended_items)?;
        }
        if !op.deleted_items.is_empty() {
            write_items(self, &op.deleted_items)?;
        }
        if !op.ordered_items.is_empty() {
            write_items(self, &op.ordered_items)?;
        }

        Ok(rep_heap(ty, off, false))
    }

    fn write_time_samples(&mut self, samples: &[(f64, Value)]) -> Result<ValueRep> {
        // Layout (matches reader/crateFile.cpp):
        //   [i64 rel1]                         — relative offset to times_rep
        //   ...                                — intervening heap for the times array
        //   [ValueRep times_rep]               — ValueRep of the times double array
        //   [i64 rel2]                         — relative offset to the values block
        //   ...                                — intervening heap for sample values
        //   [u64 count] [ValueRep * count]     — values block
        let off = self.pos()?;

        let rel1_slot = self.pos()?;
        self.write_pod(&0_i64)?;

        // Write the times array heap and capture its ValueRep.
        let times: Vec<f64> = samples.iter().map(|(t, _)| *t).collect();
        let times_rep = self.write_array_f64_type(Type::Double, &times)?;

        // Inline ValueRep for the times array, reachable by rel1.
        let times_rep_pos = self.pos()?;
        self.write_pod(&times_rep.0)?;

        // rel2 sits immediately after the times_rep.
        let rel2_slot = self.pos()?;
        self.write_pod(&0_i64)?;

        // Values block: count followed by ValueRep per sample. Reserve the rep
        // slots first, then write heap data, then overwrite the slots.
        let values_block_pos = self.pos()?;
        self.write_count(samples.len() as u64)?;
        let reps_start = self.pos()?;
        for _ in samples {
            self.write_pod(&0_u64)?;
        }

        let mut reps = Vec::with_capacity(samples.len());
        for (_, v) in samples {
            reps.push(self.write_value(v)?);
        }
        let heap_end = self.pos()?;

        self.out.seek(SeekFrom::Start(reps_start))?;
        for rep in &reps {
            self.write_pod(&rep.0)?;
        }
        self.out.seek(SeekFrom::Start(heap_end))?;

        let rel1 = (times_rep_pos as i64) - (rel1_slot as i64);
        let rel2 = (values_block_pos as i64) - (rel2_slot as i64);
        self.out.seek(SeekFrom::Start(rel1_slot))?;
        self.write_pod(&rel1)?;
        self.out.seek(SeekFrom::Start(rel2_slot))?;
        self.write_pod(&rel2)?;
        self.out.seek(SeekFrom::Start(heap_end))?;

        Ok(rep_heap(Type::TimeSamples, off, false))
    }

    // -----------------------------------------------------------------
    // LZ4 wrapper
    // -----------------------------------------------------------------

    fn write_lz4_compressed(&mut self, input: &[u8]) -> Result<()> {
        let compressed = lz4_compress_single_chunk(input);
        self.write_count(compressed.len() as u64)?;
        self.write_bytes(&compressed)?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Free helpers
// ---------------------------------------------------------------------------

struct Interner<T: Clone + Eq + std::hash::Hash> {
    items: Vec<T>,
    index: HashMap<T, u32>,
}

impl<T: Clone + Eq + std::hash::Hash> Interner<T> {
    fn new() -> Self {
        Self {
            items: Vec::new(),
            index: HashMap::new(),
        }
    }

    fn intern(&mut self, v: T) -> u32 {
        if let Some(&i) = self.index.get(&v) {
            return i;
        }
        let i = self.items.len() as u32;
        self.index.insert(v.clone(), i);
        self.items.push(v);
        i
    }
}

fn rep_inline(ty: Type, payload: u64) -> ValueRep {
    let ty_bits = ((ty as u64) & 0xFF) << 48;
    let inlined = 1_u64 << 62;
    ValueRep(ty_bits | inlined | (payload & ((1 << 48) - 1)))
}

fn rep_heap(ty: Type, offset: u64, is_array: bool) -> ValueRep {
    let ty_bits = ((ty as u64) & 0xFF) << 48;
    let array_bit = if is_array { 1_u64 << 63 } else { 0 };
    ValueRep(ty_bits | array_bit | (offset & ((1 << 48) - 1)))
}

/// Heap array value with the compressed bit set. Used for integer arrays
/// large enough to hit [`MIN_COMPRESSED_ARRAY_SIZE`].
fn rep_heap_compressed(ty: Type, offset: u64) -> ValueRep {
    let ty_bits = ((ty as u64) & 0xFF) << 48;
    let array_bit = 1_u64 << 63;
    let compressed_bit = 1_u64 << 61;
    ValueRep(ty_bits | array_bit | compressed_bit | (offset & ((1 << 48) - 1)))
}

/// Minimum element count at which an integer array is compressed. Matches
/// `CrateFile::MIN_COMPRESSED_ARRAY_SIZE` on the reader side — below this, the
/// reader forces the uncompressed path regardless of the compressed bit.
const MIN_COMPRESSED_ARRAY_SIZE: usize = 4;

fn compute_jump(has_child: bool, has_sibling: bool, sibling_offset: i32) -> i32 {
    match (has_child, has_sibling) {
        (true, true) => sibling_offset,
        (true, false) => -1,
        (false, true) => 0,
        (false, false) => -2,
    }
}

fn kid_had_child(existing: &i32) -> bool {
    // A slot that was left with default (0) or jump==-2 had no children;
    // anything else indicates a child was recorded.
    *existing == -1 || *existing > 0
}

fn parent_of(path: &Path) -> Option<Path> {
    let s = path.as_str();
    if s.is_empty() || s == "/" {
        return None;
    }

    // Variant segment parent: /Prim{set=sel} → /Prim
    if s.ends_with('}') {
        if let Some(pos) = s.rfind('{') {
            return Path::new(&s[..pos]).ok();
        }
    }

    // Property path: /Prim.x → /Prim (prim path).
    if path.is_property_path() {
        return Some(path.prim_path());
    }

    // Regular prim path.
    match s.rsplit_once('/') {
        Some(("", _)) => Some(Path::abs_root()),
        Some((before, _)) => Path::new(before).ok(),
        None => None,
    }
}

/// Returns `(segment, is_property)` where `segment` is the last element of the
/// path and `is_property` is true if the element was attached via `.`.
fn last_segment(path: &Path) -> (&str, bool) {
    let s = path.as_str();

    if s.ends_with('}') {
        if let Some(pos) = s.rfind('{') {
            return (&s[pos..], false);
        }
    }

    if path.is_property_path() {
        if let Some(pos) = s.rfind('.') {
            return (&s[pos + 1..], true);
        }
    }

    if let Some(pos) = s.rfind('/') {
        return (&s[pos + 1..], false);
    }

    (s, false)
}

fn lz4_compress_single_chunk(input: &[u8]) -> Vec<u8> {
    // Single-chunk framing: leading byte = 0 chunk count, then raw LZ4.
    let mut out = Vec::with_capacity(1 + input.len());
    out.push(0_u8);
    out.extend_from_slice(&lz4_flex::compress(input));
    out
}
