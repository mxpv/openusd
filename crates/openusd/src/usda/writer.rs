//! Text format (`usda`) writer.
//!
//! Walks an [`AbstractData`] layer and emits a `usda` representation. The
//! output aims for semantic round-trip: parsing the emitted text with
//! [`usda::parse`](super::parse) must reproduce the original specs
//! opinion-for-opinion.

// TODO: byte-for-byte parity with C++ `Sdf_WriteLayer` (`fileIO_Common`), so
// a layer can be compared with a C++ baseline as text. Known divergences: C++
// orders layer and prim metadata in its own field order, writes a dictionary
// across lines, separates sibling prims with a blank line, sorts a variant
// set's variants by name, and omits an attribute's declaration line when it
// has connections, samples, or a spline but no default, metadata, or `custom`.

use std::hash::Hash;
use std::path::Path as FsPath;
use std::{
    collections::HashMap,
    fmt::Write as FmtWrite,
    io::{self, Write},
    iter,
    ops::{Deref, DerefMut},
};

use crate::gf;
use crate::sdf::{
    self, AbstractData, AssetPath, ChildrenKey, FieldKey, FormatError, LayerOffset, ListOp, Path, Payload, Reference,
    SpecType, Specifier, Value, Variability,
};
use crate::tf::{self, Token};

/// Emits `usda` text from an [`AbstractData`].
pub struct TextWriter;

impl TextWriter {
    /// Write the layer to a newly allocated `String`.
    pub fn write_to_string(data: &dyn AbstractData) -> Result<String, FormatError> {
        let mut buf = Vec::new();
        emit(data, &mut buf)?;
        Ok(String::from_utf8(buf).expect("the usda writer emits UTF-8 text"))
    }

    /// Write the layer to a file on disk, which it replaces only once the
    /// whole layer is written.
    pub fn write_to_file(data: &dyn AbstractData, path: impl AsRef<FsPath>) -> Result<(), FormatError> {
        let mut file = tf::SafeOutputFile::create(path.as_ref())?;
        Self::write(data, file.file())?;
        file.persist()?;
        Ok(())
    }

    /// One value as `usda` writes it, e.g. `(1, 1, 1)` for a `double3`.
    ///
    /// The same rendering a layer's own text uses, for a caller that has a value
    /// rather than a layer — showing a schema's fallback in documentation, say.
    pub fn value_to_string(value: &sdf::Value) -> Result<String, FormatError> {
        let mut text = String::new();
        format_value(&mut ValueText::of(&mut text), value, 0)?;
        Ok(text)
    }

    /// Write the layer to any `io::Write` sink, through a buffer of its own,
    /// so `out` takes the text in large writes.
    pub fn write<W: Write>(data: &dyn AbstractData, out: &mut W) -> Result<(), FormatError> {
        let mut out = io::BufWriter::new(out);
        emit(data, &mut out)?;
        out.flush()?;
        Ok(())
    }
}

/// Writes the layer to `out` as it comes, for a sink that buffers already.
fn emit(data: &dyn AbstractData, out: &mut dyn Write) -> Result<(), FormatError> {
    Emitter {
        out,
        indent: 0,
        scratch: String::new(),
    }
    .emit_layer(data)
}

struct Emitter<'w> {
    out: &'w mut dyn Write,
    indent: usize,
    /// The text of the value or item being written, kept from one to the
    /// next so its storage is allocated once.
    scratch: String,
}

impl Emitter<'_> {
    // ---------- layout helpers ----------

    fn write_indent(&mut self) -> io::Result<()> {
        for _ in 0..self.indent {
            self.out.write_all(b"    ")?;
        }
        Ok(())
    }

    /// `line` at the current indent, ended by a newline.
    fn write_line(&mut self, line: &str) -> Result<(), FormatError> {
        self.write_indent()?;
        self.out.write_all(line.as_bytes())?;
        self.out.write_all(b"\n")?;
        Ok(())
    }

    /// The scratch text at the current indent, ended by a newline.
    fn write_scratch_line(&mut self) -> Result<(), FormatError> {
        self.write_indent()?;
        self.out.write_all(self.scratch.as_bytes())?;
        self.out.write_all(b"\n")?;
        Ok(())
    }

    /// The parenthesized metadata block after a declaration, one field per
    /// line one level in, and nothing when `fields` is empty.
    fn emit_metadata_block(
        &mut self,
        data: &dyn AbstractData,
        path: &Path,
        fields: &[String],
    ) -> Result<(), FormatError> {
        if fields.is_empty() {
            return Ok(());
        }
        writeln!(self.out, " (")?;
        self.indent += 1;
        for name in fields {
            let value = data.field(path, name)?;
            self.emit_metadata_entry(path, name, &value)?;
        }
        self.indent -= 1;
        self.write_indent()?;
        self.out.write_all(b")")?;
        Ok(())
    }

    // ---------- top-level walk ----------

    fn emit_layer(&mut self, data: &dyn AbstractData) -> Result<(), FormatError> {
        writeln!(self.out, "#usda 1.0")?;

        let root = Path::abs_root();
        let has_root = data.has_spec(&root);

        // Layer metadata, as C++ `SdfUsdaFileFormat` writes the header: every
        // field but primChildren, with subLayerOffsets merged into subLayers;
        // the comment first, the fields in byte order, then the relocates. An
        // empty comment or `doc` and a false `hasOwnedSubLayers` are not
        // written.
        let written = |name: &String| {
            if is_prim_structural_field(name) || name == FieldKey::SubLayerOffsets.as_str() {
                false
            } else if name == FieldKey::HasOwnedSubLayers.as_str() {
                matches!(data.field(&root, name).as_deref(), Ok(Value::Bool(true)))
            } else if name == FieldKey::Comment.as_str() || name == FieldKey::Documentation.as_str() {
                !is_empty_string(data, &root, name)
            } else {
                true
            }
        };
        let mut meta_fields: Vec<String> = if has_root {
            data.list_fields(&root)
                .unwrap_or_default()
                .into_iter()
                .filter(written)
                .collect()
        } else {
            Vec::new()
        };
        let place = |name: &String| {
            (
                name != FieldKey::Comment.as_str(),
                name == FieldKey::LayerRelocates.as_str(),
            )
        };
        meta_fields.sort_by(|a, b| place(a).cmp(&place(b)).then_with(|| a.cmp(b)));
        if !meta_fields.is_empty() {
            writeln!(self.out, "(")?;
            self.indent += 1;
            for name in &meta_fields {
                if name == FieldKey::SubLayers.as_str() {
                    self.emit_sub_layers(data, &root)?;
                    continue;
                }
                let value = data.field(&root, name)?;
                self.emit_metadata_entry(&root, name, &value)?;
            }
            self.indent -= 1;
            writeln!(self.out, ")")?;
        }

        // Layer-level `reorder rootPrims`, stored as `primOrder` on the
        // pseudo-root. Emitted between the metadata block and the root prims.
        if has_root
            && let Some(Value::TokenVec(v)) = get_value(data, &root, FieldKey::PrimOrder.as_str())
            && v.len() > 1
        {
            writeln!(self.out)?;
            self.emit_reorder("rootPrims", &v)?;
        }

        // Root prims
        let children = if has_root {
            children(data, &root, ChildrenKey::PrimChildren)
        } else {
            Vec::new()
        };
        for name in &children {
            writeln!(self.out)?;
            let child_path = root.append_path(name.as_str())?;
            self.emit_prim(data, &child_path, name)?;
        }
        writeln!(self.out)?;

        Ok(())
    }

    // ---------- prim ----------

    fn emit_prim(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<(), FormatError> {
        // Header: [specifier] [typeName] "name"
        self.write_indent()?;
        let specifier = get_value(data, path, FieldKey::Specifier.as_str())
            .and_then(|v| match v {
                Value::Specifier(s) => Some(s),
                _ => None,
            })
            .unwrap_or(Specifier::Def);
        self.out.write_all(specifier_keyword(specifier).as_bytes())?;

        // The type that stands for any type is written as no type (C++
        // `Sdf_WritePrimPreamble`).
        if let Some(Value::Token(type_name)) = get_value(data, path, FieldKey::TypeName.as_str())
            && !type_name.is_empty()
            && type_name.as_str() != sdf::ANY_TYPE
        {
            write!(self.out, " {type_name}")?;
        }

        let mut quoted = String::new();
        write_quoted(&mut quoted, name)?;
        write!(self.out, " {quoted}")?;

        let meta_fields = metadata_fields(data, path, is_prim_structural_field);
        self.emit_metadata_block(data, path, &meta_fields)?;

        writeln!(self.out)?;
        self.write_line("{")?;
        self.indent += 1;
        self.emit_prim_body(data, path)?;
        self.indent -= 1;
        self.write_line("}")
    }

    /// A prim's or variant's body, laid out as C++ `Sdf_WritePrimBody` lays
    /// it out: reorder statements, the properties sorted by name and then
    /// type, a blank line before the child prims and between them, then the
    /// variant sets.
    fn emit_prim_body(&mut self, data: &dyn AbstractData, path: &Path) -> Result<(), FormatError> {
        self.emit_body_reorders(data, path)?;

        let mut props = children(data, path, ChildrenKey::PropertyChildren)
            .into_iter()
            .map(|name| Ok((path.append_property(&name)?, name)))
            .collect::<Result<Vec<_>, FormatError>>()?;
        props.sort_by(|(a_path, a), (b_path, b)| {
            tf::dictionary_cmp(a.as_str(), b.as_str()).then_with(|| {
                let kind = |p: &Path| data.spec_type(p).map(|t| t as u32);
                kind(a_path).cmp(&kind(b_path))
            })
        });
        for (prop_path, name) in &props {
            self.emit_property(data, prop_path, name)?;
        }

        let children = children(data, path, ChildrenKey::PrimChildren);
        if !props.is_empty() && !children.is_empty() {
            writeln!(self.out)?;
        }
        for (i, name) in children.iter().enumerate() {
            if i > 0 {
                writeln!(self.out)?;
            }
            let child_path = path.append_path(name.as_str())?;
            self.emit_prim(data, &child_path, name)?;
        }

        if let Some(Value::TokenVec(vset_names)) = get_value(data, path, ChildrenKey::VariantSetChildren.as_str()) {
            for vset in &vset_names {
                let vset_path = path.append_variant_selection(vset, "")?;
                self.emit_variant_set(data, &vset_path, vset.as_str())?;
            }
        }
        Ok(())
    }

    /// Emit `reorder nameChildren / properties` statements (if authored) at
    /// the top of a prim or variant body. The grammar only accepts these
    /// inside `{...}`, not in the metadata block.
    ///
    /// As C++ `Sdf_WritePrimNamespaceReorders` writes them: properties first,
    /// each only when it orders more than one name.
    fn emit_body_reorders(&mut self, data: &dyn AbstractData, path: &Path) -> Result<(), FormatError> {
        if let Some(Value::TokenVec(v)) = get_value(data, path, FieldKey::PropertyOrder.as_str())
            && v.len() > 1
        {
            self.emit_reorder("properties", &v)?;
        }
        if let Some(Value::TokenVec(v)) = get_value(data, path, FieldKey::PrimOrder.as_str())
            && v.len() > 1
        {
            self.emit_reorder("nameChildren", &v)?;
        }
        Ok(())
    }

    // ---------- property (attribute or relationship) ----------

    fn emit_property(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<(), FormatError> {
        match data.spec_type(path) {
            Some(SpecType::Attribute) => self.emit_attribute(data, path, name),
            Some(SpecType::Relationship) => self.emit_relationship(data, path, name),
            Some(other) => Err(FormatError::Encode {
                reason: format!("unsupported property spec type {other:?} at {path}").into(),
            }),
            None => Err(FormatError::Encode {
                reason: format!("property path {path} has no spec").into(),
            }),
        }
    }

    fn emit_attribute(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<(), FormatError> {
        let custom = matches!(
            get_value(data, path, FieldKey::Custom.as_str()),
            Some(Value::Bool(true))
        );
        let variability = match get_value(data, path, FieldKey::Variability.as_str()) {
            Some(Value::Variability(Variability::Uniform)) => "uniform ",
            _ => "",
        };

        // The declared spelling is written back as its standard spelling (C++
        // `GetSerializationName`): `Color` in, `color3d` out; an unregistered
        // spelling stays as authored.
        let type_name = match get_value(data, path, FieldKey::TypeName.as_str()) {
            Some(Value::Token(t)) => sdf::ValueTypeName::from(t).serialization_name(),
            _ => {
                return Err(FormatError::Encode {
                    reason: format!("attribute {path} missing typeName").into(),
                });
            }
        };

        let default = get_value(data, path, FieldKey::Default.as_str());
        let time_samples = get_value(data, path, FieldKey::TimeSamples.as_str());
        let spline = get_value(data, path, FieldKey::Spline.as_str());
        let connections = get_value(data, path, FieldKey::ConnectionPaths.as_str());
        // Only a list op with an effect writes a connection statement.
        let connections_written = matches!(&connections, Some(Value::PathListOp(op)) if !op.is_empty());
        let meta_fields = metadata_fields(data, path, is_attribute_structural_field);

        // The declaration, which C++ `Sdf_WriteAttribute` writes only when it
        // carries something or no other statement would declare the attribute.
        // Every statement carries the variability, so a uniform attribute
        // stays uniform whichever of them declares it.
        if !meta_fields.is_empty()
            || default.is_some()
            || custom
            || (time_samples.is_none() && spline.is_none() && !connections_written)
        {
            self.write_indent()?;
            if custom {
                self.out.write_all(b"custom ")?;
            }
            write!(self.out, "{variability}{type_name} {name}")?;

            if let Some(v) = default {
                self.out.write_all(b" = ")?;
                self.write_value(&v)?;
            }

            self.emit_metadata_block(data, path, &meta_fields)?;
            writeln!(self.out)?;
        }

        if let Some(Value::TimeSamples(samples)) = time_samples {
            self.write_indent()?;
            write!(self.out, "{variability}{type_name} {name}.timeSamples = ")?;
            self.write_time_samples(&samples)?;
            writeln!(self.out)?;
        }

        if let Some(Value::Dictionary(dict)) = spline {
            self.write_indent()?;
            write!(self.out, "{variability}{type_name} {name}.spline = ")?;
            self.write_spline(&dict)?;
            writeln!(self.out)?;
        }

        if let Some(Value::PathListOp(op)) = connections {
            self.emit_targets_statement(&format!("{variability}{type_name} {name}.connect"), &op)?;
        }

        Ok(())
    }

    /// Emit a spline dictionary in the native spline grammar, laid out as C++
    /// `Sdf_FileIOUtility::WriteSpline` lays it out. Inverse of
    /// `parser::parse_spline`. The input `dict` has the keys produced there:
    /// `curveType`, `pre/postExtrapolation`, `loopParameters`, `knots`,
    /// `knotCustomData`.
    //
    // TODO: the spline dictionary is the AOUSD Python reference's model. It
    // names a tangent pair `(slope, width)` where C++ reads `(width, slope)`,
    // has no tangent algorithm (`autoEase`), and stores a `preValue` of 0 for
    // a single-valued knot. A C++ `TsSpline`-faithful model needs the two
    // references reconciled. The text keeps each tangent pair in the order it
    // was read, which C++ reads back unchanged.
    fn write_spline(&mut self, dict: &HashMap<String, Value>) -> Result<(), FormatError> {
        self.out.write_all(b"{\n")?;
        self.indent += 1;

        // In time order, as C++ keeps a spline's knots.
        let mut knots: Vec<&sdf::Dictionary> = match dict.get("knots") {
            Some(Value::ValueVec(knots)) => knots.iter().filter_map(|knot| knot.try_as_dictionary_ref()).collect(),
            _ => Vec::new(),
        };
        let by_time =
            |a: &&sdf::Dictionary, b: &&sdf::Dictionary| get_double(a, "time").total_cmp(&get_double(b, "time"));
        if !knots.is_sorted_by(|a, b| by_time(a, b).is_le()) {
            knots.sort_by(by_time);
        }
        let curve_type = match dict.get("curveType") {
            Some(Value::Token(t)) => t.as_str(),
            _ => "bezier",
        };
        let hermite = curve_type == "hermite";
        // A curve segment runs from a knot whose next interpolation is curve
        // to the knot after it (C++ `TsKnotMap::HasCurveSegments`).
        let curved = knots
            .split_last()
            .is_some_and(|(_, segments)| segments.iter().any(|knot| interpolation(knot) == "curve"));
        if hermite || curved {
            self.scratch.clear();
            self.scratch.push_str(curve_type);
            self.scratch.push(',');
            self.write_scratch_line()?;
        }

        for (dir, key) in [("pre", "preExtrapolation"), ("post", "postExtrapolation")] {
            if let Some(Value::Dictionary(extrapolation)) = dict.get(key) {
                self.write_extrapolation(dir, extrapolation)?;
            }
        }

        let loop_keys = ["protoStart", "protoEnd", "numPreLoops", "numPostLoops", "valueOffset"];
        if let Some(Value::Dictionary(loop_dict)) = dict.get("loopParameters")
            && loop_keys.iter().any(|key| get_double(loop_dict, key) != 0.0)
        {
            self.write_loop(loop_dict)?;
        }

        let knot_custom = match dict.get("knotCustomData") {
            Some(Value::Dictionary(m)) => Some(m),
            _ => None,
        };
        // The first knot has no segment before it, but writes a pre-tangent
        // as though one were curved.
        let mut incoming = "curve";
        for knot in knots {
            self.write_knot(knot, incoming, hermite, knot_custom)?;
            incoming = interpolation(knot);
        }

        self.indent -= 1;
        self.write_indent()?;
        self.out.write_all(b"}")?;
        Ok(())
    }

    /// An extrapolation that is not the `held` C++ falls back to, `sloped`
    /// with its slope in parentheses (C++ `_WriteSplineExtrapolation`).
    fn write_extrapolation(&mut self, dir: &str, extrapolation: &HashMap<String, Value>) -> Result<(), FormatError> {
        let mode = match extrapolation.get("mode") {
            Some(Value::Token(t)) => t.as_str(),
            _ => "held",
        };
        if mode == "held" {
            return Ok(());
        }
        let s = &mut self.scratch;
        s.clear();
        s.push_str(dir);
        s.push_str(": ");
        // A looping mode is held as one word (`looprepeat`) and written as
        // two (`loop repeat`).
        match mode.strip_prefix("loop") {
            Some(kind) => {
                s.push_str("loop ");
                s.push_str(kind);
            }
            None => s.push_str(mode),
        }
        if mode == "sloped" {
            s.push('(');
            tf::stringify_float(s, get_double(extrapolation, "slope"));
            s.push(')');
        }
        s.push(',');
        self.write_scratch_line()
    }

    /// The inner loop's prototype span, its pre- and post-loop counts, and
    /// its value offset, as the `loop:` line of C++
    /// `Sdf_FileIOUtility::WriteSpline` writes them.
    fn write_loop(&mut self, params: &HashMap<String, Value>) -> Result<(), FormatError> {
        let s = &mut self.scratch;
        s.clear();
        s.push_str("loop: (");
        tf::stringify_float(s, get_double(params, "protoStart"));
        s.push_str(", ");
        tf::stringify_float(s, get_double(params, "protoEnd"));
        // The loop counts are integers, written as C++ `%d` writes them.
        write!(
            s,
            ", {}, {}, ",
            get_double(params, "numPreLoops") as i64,
            get_double(params, "numPostLoops") as i64
        )?;
        tf::stringify_float(s, get_double(params, "valueOffset"));
        s.push_str("),");
        self.write_scratch_line()
    }

    /// One knot, as C++ `_SplineKnotWriter` writes it: its time and values,
    /// its pre-tangent when the segment into it is a curve (`incoming`), its
    /// post-tangent or next interpolation, and its custom data.
    fn write_knot(
        &mut self,
        knot: &HashMap<String, Value>,
        incoming: &str,
        hermite: bool,
        knot_custom: Option<&sdf::Dictionary>,
    ) -> Result<(), FormatError> {
        let time = get_double(knot, "time");
        let pre_value = get_double(knot, "preValue");
        // A side's two numbers, the second written where C++ writes one: on a
        // Bezier spline, and on a Hermite spline only where the layer gave a
        // non-zero second number (C++ `_WriteTangent` writes a Hermite
        // tangent's slope alone). A tangent read with one number has none.
        let side = |slope: &str, width: &str| {
            let width = match knot.get(width) {
                Some(Value::Double(width)) if !hermite || *width != 0.0 => Some(*width),
                _ => None,
            };
            (get_double(knot, slope), width)
        };
        let (pre_slope, pre_width) = side("preTangentSlope", "preTangentWidth");
        let (post_slope, post_width) = side("postTangentSlope", "postTangentWidth");
        let authored = |slope: f64, width: Option<f64>| slope != 0.0 || width.is_some_and(|width| width != 0.0);
        let tangent = |s: &mut String, slope: f64, width: Option<f64>| match width {
            Some(width) => format_tuple_float(s, &[slope, width]),
            None => format_tuple_float(s, &[slope]),
        };

        let s = &mut self.scratch;
        s.clear();
        tf::stringify_float(s, time);
        s.push(':');
        if pre_value != 0.0 {
            s.push(' ');
            tf::stringify_float(s, pre_value);
            s.push_str(" &");
        }
        s.push(' ');
        tf::stringify_float(s, get_double(knot, "value"));
        // C++ writes a tangent beside a curve segment. One authored beside
        // another kind of segment is written too, and C++ reads it back. C++'s
        // own output never holds such a tangent.
        if incoming == "curve" || authored(pre_slope, pre_width) {
            s.push_str("; pre ");
            tangent(s, pre_slope, pre_width)?;
        }
        let next = interpolation(knot);
        s.push_str("; post ");
        s.push_str(next);
        if next == "curve" || authored(post_slope, post_width) {
            s.push(' ');
            tangent(s, post_slope, post_width)?;
        }

        if let Some(knot_custom) = knot_custom
            && let Some(Value::Dictionary(custom)) = knot_custom.get(&time.to_string())
            && !custom.is_empty()
        {
            s.push_str("; ");
            format_inline_dictionary(s, custom)?;
        }

        s.push(',');
        self.write_scratch_line()
    }

    fn emit_relationship(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<(), FormatError> {
        let custom = matches!(
            get_value(data, path, FieldKey::Custom.as_str()),
            Some(Value::Bool(true))
        );
        let targets = get_value(data, path, FieldKey::TargetPaths.as_str());
        let meta_fields = metadata_fields(data, path, is_relationship_structural_field);
        let list_ops = matches!(&targets, Some(Value::PathListOp(op)) if !op.is_empty() && !op.is_explicit());

        // The declaration, which C++ `Sdf_WriteRelationship` writes only when
        // it carries metadata or explicit targets, or nothing else declares
        // the relationship.
        // A relationship is uniform unless it says otherwise, the reverse of
        // an attribute, so `varying` is the keyword the text form spells out,
        // on every statement as C++ `Sdf_WriteRelationship` writes it.
        let varying = if matches!(
            get_value(data, path, FieldKey::Variability.as_str()),
            Some(Value::Variability(Variability::Uniform))
        ) {
            ""
        } else {
            "varying "
        };
        if !meta_fields.is_empty() || custom || !list_ops {
            self.write_indent()?;
            if custom {
                self.out.write_all(b"custom ")?;
            }
            write!(self.out, "{varying}rel {name}")?;
            if let Some(Value::PathListOp(op)) = &targets
                && op.is_explicit()
            {
                self.out.write_all(b" = ")?;
                self.write_listop_items(op.explicit_items(), &mut write_path, Items::Terminated)?;
            }
            self.emit_metadata_block(data, path, &meta_fields)?;
            writeln!(self.out)?;
        }

        // The `delete`, `add`, `prepend`, `append` and `reorder` target
        // statements.
        if let Some(Value::PathListOp(op)) = &targets
            && !op.is_explicit()
        {
            self.emit_targets_statement(&format!("{varying}rel {name}"), op)?;
        }
        Ok(())
    }

    // ---------- variant set / variant ----------

    /// A variant set, its variants in byte order of their names, as C++
    /// `Sdf_WriteVariantSet` sorts them; a set with no variants is not
    /// written.
    fn emit_variant_set(&mut self, data: &dyn AbstractData, vset_path: &Path, name: &str) -> Result<(), FormatError> {
        let mut variant_names = children(data, vset_path, ChildrenKey::VariantChildren);
        if variant_names.is_empty() {
            return Ok(());
        }
        variant_names.sort();

        self.write_indent()?;
        let mut quoted = String::new();
        write_quoted(&mut quoted, name)?;
        writeln!(self.out, "variantSet {quoted} = {{")?;
        self.indent += 1;

        let prim = vset_path.prim_path();
        for v_name in &variant_names {
            let v_path = prim.append_variant_selection(name, v_name)?;
            self.emit_variant(data, &v_path, v_name.as_str())?;
        }

        self.indent -= 1;
        self.write_indent()?;
        writeln!(self.out, "}}")?;
        Ok(())
    }

    fn emit_variant(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<(), FormatError> {
        self.write_indent()?;
        let mut quoted = String::new();
        write_quoted(&mut quoted, name)?;
        self.out.write_all(quoted.as_bytes())?;

        let meta_fields = metadata_fields(data, path, is_prim_structural_field);
        self.emit_metadata_block(data, path, &meta_fields)?;

        writeln!(self.out, " {{")?;
        self.indent += 1;
        self.emit_prim_body(data, path)?;
        self.indent -= 1;
        // C++ `Sdf_WriteVariant` closes a variant after a blank line.
        writeln!(self.out)?;
        self.write_indent()?;
        writeln!(self.out, "}}")?;
        Ok(())
    }

    /// A layer's or prim's relocates, one pair per line, as C++
    /// `_WriteRelocates` writes them in a metadata block (`, ` ends every pair
    /// but the last).
    fn emit_relocates(&mut self, keyword: &str, relocates: &[(Path, Path)]) -> Result<(), FormatError> {
        self.write_indent()?;
        writeln!(self.out, "{keyword} = {{")?;
        self.indent += 1;
        for (i, (source, target)) in relocates.iter().enumerate() {
            let separator = if i + 1 < relocates.len() { ", " } else { "" };
            self.write_indent()?;
            writeln!(self.out, "<{}>: <{}>{separator}", source.as_str(), target.as_str())?;
        }
        self.indent -= 1;
        self.write_line("}")
    }

    /// Combine `subLayers` (asset paths) with `subLayerOffsets` at emit time —
    /// the text grammar wants them fused into `subLayers = [@path@ (offset=X; scale=Y), ...]`.
    fn emit_sub_layers(&mut self, data: &dyn AbstractData, root: &Path) -> Result<(), FormatError> {
        let sublayers = match get_value(data, root, FieldKey::SubLayers.as_str()) {
            Some(Value::StringVec(v)) => v,
            _ => return Ok(()),
        };
        let offsets = match get_value(data, root, FieldKey::SubLayerOffsets.as_str()) {
            Some(Value::LayerOffsetVec(v)) => v,
            _ => Vec::new(),
        };

        // One per line, as C++ `SdfUsdaFileFormat` writes them.
        self.write_indent()?;
        writeln!(self.out, "subLayers = [")?;
        self.indent += 1;
        for (i, path) in sublayers.iter().enumerate() {
            self.scratch.clear();
            write_asset_path(&mut self.scratch, path)?;
            if let Some(offset) = offsets.get(i) {
                write_layer_offset(&mut self.scratch, offset, None);
            }
            if i + 1 < sublayers.len() {
                self.scratch.push(',');
            }
            self.write_scratch_line()?;
        }
        self.indent -= 1;
        self.write_line("]")?;
        Ok(())
    }

    // ---------- metadata entry ----------

    /// One metadata field of the spec at `path`.
    fn emit_metadata_entry(&mut self, path: &Path, name: &str, value: &Value) -> Result<(), FormatError> {
        // "comment" is authored as a bare string in the metadata block, with
        // no keyword. Parser recognises a lone string as the Sdf comment field.
        if name == FieldKey::Comment.as_str()
            && let Value::String(text) = value
        {
            self.write_indent()?;
            let mut buf = String::new();
            write_quoted(&mut buf, text)?;
            self.out.write_all(buf.as_bytes())?;
            writeln!(self.out)?;
            return Ok(());
        }

        // Several fields are stored under internal names that differ from the
        // USD text grammar keywords. Map them back before emitting.
        let keyword = if name == FieldKey::LayerRelocates.as_str() {
            "relocates"
        } else if name == FieldKey::InheritPaths.as_str() {
            "inherits"
        } else if name == FieldKey::Documentation.as_str() {
            "doc"
        } else if name == FieldKey::VariantSetNames.as_str() {
            "variantSets"
        } else if name == FieldKey::VariantSelection.as_str() {
            "variants"
        } else {
            name
        };

        // A prim's relocates are relative to the prim and sorted, as C++
        // `Sdf_WritePrimMetadata` keeps them in an `SdfRelocatesMap`; a
        // layer's are absolute and in their stored order.
        if let Value::Relocates(relocates) = value {
            if name != FieldKey::Relocates.as_str() {
                return self.emit_relocates(keyword, relocates);
            }
            let mut relative: Vec<_> = relocates
                .iter()
                .map(|(source, target)| (source.make_relative(path), target.make_relative(path)))
                .collect();
            // Sorted by source, each source once with its first target.
            relative.sort_by(|(a, _), (b, _)| a.cmp(b));
            relative.dedup_by(|(a, _), (b, _)| a == b);
            return self.emit_relocates(keyword, &relative);
        }

        // Variant-set names write as a name vector, which brackets only a list
        // of more than one. C++ gives the field its own emitter for this
        // rather than sending it through the generic list-op path.
        if keyword == "variantSets"
            && let Value::StringListOp(op) = value
        {
            let names = op.clone().convert(|_, name| Some(Name(name)));
            self.emit_listop_statement(keyword, &names, |s, name| write_quoted(s, &name.0))?;
            return Ok(());
        }

        // ListOps in metadata blocks render as multi-line prepend/append/... entries.
        if let Some(emitted) = self.try_emit_listop_metadata(keyword, value)?
            && emitted
        {
            return Ok(());
        }

        self.write_indent()?;
        write!(self.out, "{keyword} = ")?;

        // A display unit is written as the bare name of the unit, which is
        // what the grammar accepts back. Storing it as a token rather than as
        // C++'s enum is what makes this the field's business and not the
        // value's: nothing about the token says it is a unit.
        //
        // `%` and `default` are not identifiers, so a layer authoring either
        // cannot be read back — by us or by USD, which emits the same text and
        // rejects it on import (verified against usd-core 26.8). Emitting what
        // upstream emits keeps a layer exactly as portable as one it wrote.
        if keyword == FieldKey::DisplayUnit.as_str()
            && let Value::Token(unit) = value
        {
            write!(self.out, "{}", unit.as_str())?;
            writeln!(self.out)?;
            return Ok(());
        }

        // A symmetry function is a bare identifier, empty when none is named
        // (C++ `Sdf_WritePrimMetadata`, `Sdf_WriteAttribute`,
        // `Sdf_WriteRelationship`).
        if keyword == FieldKey::SymmetryFunction.as_str()
            && let Value::Token(function) = value
        {
            writeln!(self.out, "{}", function.as_str())?;
            return Ok(());
        }

        // A bool field (`active`, `hidden`, `instanceable`) is written as a
        // word; a bool value elsewhere streams as an int.
        if let Value::Bool(b) = value {
            writeln!(self.out, "{b}")?;
            return Ok(());
        }

        self.write_value(value)?;
        writeln!(self.out)?;
        Ok(())
    }

    fn emit_reorder(&mut self, target: &str, names: &[Token]) -> Result<(), FormatError> {
        self.write_indent()?;
        write!(self.out, "reorder {target} = [")?;
        for (i, n) in names.iter().enumerate() {
            if i > 0 {
                self.out.write_all(b", ")?;
            }
            let mut buf = String::new();
            write_quoted(&mut buf, n.as_str())?;
            self.out.write_all(buf.as_bytes())?;
        }
        writeln!(self.out, "]")?;
        Ok(())
    }

    /// Returns `Ok(Some(true))` if this value was a `ListOp` and was fully emitted;
    /// `Ok(Some(false))` / `Ok(None)` if caller should emit as a normal field.
    fn try_emit_listop_metadata(&mut self, name: &str, value: &Value) -> Result<Option<bool>, FormatError> {
        match value {
            Value::TokenListOp(op) => {
                self.emit_listop_statement(name, op, |s, t| write_quoted(s, t.as_str()))?;
                Ok(Some(true))
            }
            Value::StringListOp(op) => {
                self.emit_listop_statement(name, op, |s, t| write_quoted(s, t))?;
                Ok(Some(true))
            }
            Value::PathListOp(op) => {
                self.emit_listop_statement(name, op, |s, p| {
                    write!(s, "<{}>", p.as_str())?;
                    Ok(())
                })?;
                Ok(Some(true))
            }
            Value::ReferenceListOp(op) => {
                // A reference with custom data spans lines, one level in
                // from the statement, as it is always one item of a list.
                let indent = self.indent + 1;
                self.emit_listop_statement(name, op, |s, r| write_reference(s, r, indent))?;
                Ok(Some(true))
            }
            Value::PayloadListOp(op) => {
                self.emit_listop_statement(name, op, write_payload)?;
                Ok(Some(true))
            }
            Value::IntListOp(op) => {
                self.emit_listop_statement(name, op, |s, v| write!(s, "{v}").map_err(Into::into))?;
                Ok(Some(true))
            }
            Value::Int64ListOp(op) => {
                self.emit_listop_statement(name, op, |s, v| write!(s, "{v}").map_err(Into::into))?;
                Ok(Some(true))
            }
            Value::UIntListOp(op) => {
                self.emit_listop_statement(name, op, |s, v| write!(s, "{v}").map_err(Into::into))?;
                Ok(Some(true))
            }
            Value::UInt64ListOp(op) => {
                self.emit_listop_statement(name, op, |s, v| write!(s, "{v}").map_err(Into::into))?;
                Ok(Some(true))
            }
            Value::UnregisteredValueListOp(op) => {
                self.emit_listop_statement(name, op, |s, body: &String| {
                    s.push_str(body);
                    Ok(())
                })?;
                Ok(Some(true))
            }
            _ => Ok(None),
        }
    }

    fn emit_listop_statement<T, F>(&mut self, prefix: &str, op: &ListOp<T>, fmt_item: F) -> Result<(), FormatError>
    where
        T: Bracketed,
        F: FnMut(&mut String, &T) -> Result<(), FormatError>,
    {
        self.emit_list_statements(prefix, op, fmt_item, Items::Separated)
    }

    /// A relationship's targets or an attribute's connections, whose items
    /// each end with a comma when they go one per line (C++
    /// `Sdf_WriteRelationshipTargetList`, `Sdf_WriteConnectionStatement`).
    fn emit_targets_statement(&mut self, prefix: &str, op: &ListOp<sdf::Path>) -> Result<(), FormatError> {
        self.emit_list_statements(prefix, op, write_path, Items::Terminated)
    }

    fn emit_list_statements<T, F>(
        &mut self,
        prefix: &str,
        op: &ListOp<T>,
        mut fmt_item: F,
        items_end: Items,
    ) -> Result<(), FormatError>
    where
        T: Bracketed,
        F: FnMut(&mut String, &T) -> Result<(), FormatError>,
    {
        if op.is_explicit() {
            self.write_indent()?;
            write!(self.out, "{prefix} = ")?;
            self.write_listop_items(op.explicit_items(), &mut fmt_item, items_end)?;
            writeln!(self.out)?;
            return Ok(());
        }

        for (kw, items) in [
            ("delete", op.deleted_items()),
            ("add", op.added_items()),
            ("prepend", op.prepended_items()),
            ("append", op.appended_items()),
            ("reorder", op.ordered_items()),
        ] {
            if !items.is_empty() {
                self.write_indent()?;
                write!(self.out, "{kw} {prefix} = ")?;
                self.write_listop_items(items, &mut fmt_item, items_end)?;
                writeln!(self.out)?;
            }
        }
        Ok(())
    }

    /// The body of one list-op statement: the items bracketed, `None` for an
    /// empty list, and a lone item bare where its type allows it
    /// (C++ `_WriteListOpList`).
    fn write_listop_items<T, F>(&mut self, items: &[T], fmt_item: &mut F, items_end: Items) -> Result<(), FormatError>
    where
        T: Bracketed,
        F: FnMut(&mut String, &T) -> Result<(), FormatError>,
    {
        if items.is_empty() {
            self.out.write_all(b"None")?;
        } else if items.len() == 1 && !items[0].needs_brackets() {
            self.scratch.clear();
            fmt_item(&mut self.scratch, &items[0])?;
            self.out.write_all(self.scratch.as_bytes())?;
        } else if T::PER_LINE {
            writeln!(self.out, "[")?;
            self.indent += 1;
            for (i, item) in items.iter().enumerate() {
                self.scratch.clear();
                fmt_item(&mut self.scratch, item)?;
                if items_end == Items::Terminated || i + 1 < items.len() {
                    self.scratch.push(',');
                }
                self.write_scratch_line()?;
            }
            self.indent -= 1;
            self.write_indent()?;
            self.out.write_all(b"]")?;
        } else {
            self.out.write_all(b"[")?;
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    self.out.write_all(b", ")?;
                }
                self.scratch.clear();
                fmt_item(&mut self.scratch, item)?;
                self.out.write_all(self.scratch.as_bytes())?;
            }
            self.out.write_all(b"]")?;
        }
        Ok(())
    }

    // ---------- value formatting ----------

    fn write_value(&mut self, value: &Value) -> Result<(), FormatError> {
        self.scratch.clear();
        let mut text = ValueText {
            text: &mut self.scratch,
            spill: Some(&mut *self.out),
        };
        format_value(&mut text, value, self.indent)?;
        text.finish()?;
        Ok(())
    }

    fn write_time_samples(&mut self, samples: &[(f64, Value)]) -> Result<(), FormatError> {
        self.out.write_all(b"{")?;
        writeln!(self.out)?;
        self.indent += 1;
        for (time, value) in samples {
            self.write_indent()?;
            self.scratch.clear();
            tf::stringify_float(&mut self.scratch, *time);
            self.scratch.push_str(": ");
            self.out.write_all(self.scratch.as_bytes())?;
            self.write_value(value)?;
            writeln!(self.out, ",")?;
        }
        self.indent -= 1;
        self.write_indent()?;
        self.out.write_all(b"}")?;
        Ok(())
    }
}

/// The text of a value as it is formatted. An array hands what it holds to
/// `spill` between its elements once that reaches [`SPILL`] bytes, so a large
/// array's text is never held whole; without `spill` the whole value stays
/// in `text`.
struct ValueText<'o> {
    text: &'o mut String,
    spill: Option<&'o mut dyn Write>,
}

/// How much of an array's text [`ValueText`] holds before handing it on.
const SPILL: usize = 1 << 16;

impl<'o> ValueText<'o> {
    /// Text that keeps the whole value in `text`.
    fn of(text: &'o mut String) -> Self {
        Self { text, spill: None }
    }

    /// Hands what is left to `spill`, the end of a value written to one.
    fn finish(mut self) -> io::Result<()> {
        if let Some(out) = self.spill.as_mut() {
            out.write_all(self.text.as_bytes())?;
            self.text.clear();
        }
        Ok(())
    }

    /// Hands the text to `spill` where it has reached [`SPILL`] bytes.
    fn spill(&mut self) -> io::Result<()> {
        if self.text.len() >= SPILL
            && let Some(out) = self.spill.as_mut()
        {
            out.write_all(self.text.as_bytes())?;
            self.text.clear();
        }
        Ok(())
    }
}

impl Deref for ValueText<'_> {
    type Target = String;

    fn deref(&self) -> &String {
        self.text
    }
}

impl DerefMut for ValueText<'_> {
    fn deref_mut(&mut self) -> &mut String {
        self.text
    }
}

// ---------- value formatter (string-producing) ----------

// One arm per variant, grouped by value type family so a new variant has an
// obvious home. Folding together the distinct variants that happen to share
// a formatter would scatter that grouping.
/// A value whose line is indented `indent` levels: a dictionary in it spans
/// several lines, its entries one level in and its `}` at `indent`.
#[allow(clippy::match_same_arms)]
fn format_value(s: &mut ValueText<'_>, v: &Value, indent: usize) -> Result<(), FormatError> {
    match v {
        // The USDA parser reads the `None` token as `Value::ValueBlock`. Emitting
        // either `Value::None` (absent-opinion marker) or `Value::Value` (expression
        // placeholder) as `None` would silently re-parse as `Value::ValueBlock` and
        // drop the original variant.
        Value::None => {
            return Err(FormatError::Encode {
                reason: "Value::None cannot be serialized to USDA".into(),
            });
        }
        Value::Value => {
            return Err(FormatError::Encode {
                reason: "Value::Value cannot be serialized to USDA".into(),
            });
        }
        Value::ValueBlock => s.push_str("None"),

        // C++ streams a bool as an int (`VtStreamOut(bool const &)`).
        Value::Bool(b) => s.push_str(if *b { "1" } else { "0" }),
        Value::BoolVec(v) => format_vec(s, v, |s, b| {
            s.push(if *b { '1' } else { '0' });
            Ok(())
        })?,

        Value::Uchar(n) => write!(s, "{n}")?,
        Value::UcharVec(v) => format_vec(s, v, |s, n| write!(s, "{n}").map_err(Into::into))?,
        Value::Int(n) => write!(s, "{n}")?,
        Value::IntVec(v) => format_vec(s, v, |s, n| write!(s, "{n}").map_err(Into::into))?,
        Value::Uint(n) => write!(s, "{n}")?,
        Value::UintVec(v) => format_vec(s, v, |s, n| write!(s, "{n}").map_err(Into::into))?,
        Value::Int64(n) => write!(s, "{n}")?,
        Value::Int64Vec(v) => format_vec(s, v, |s, n| write!(s, "{n}").map_err(Into::into))?,
        Value::Uint64(n) => write!(s, "{n}")?,
        Value::Uint64Vec(v) => format_vec(s, v, |s, n| write!(s, "{n}").map_err(Into::into))?,

        Value::Half(h) => gf::stringify_half(s, *h),
        Value::HalfVec(v) => format_vec(s, v, |s, h| {
            gf::stringify_half(s, *h);
            Ok(())
        })?,
        Value::Float(f) => tf::stringify_float(s, *f),
        Value::FloatVec(v) => format_vec(s, v, |s, f| {
            tf::stringify_float(s, *f);
            Ok(())
        })?,
        Value::Double(d) => tf::stringify_float(s, *d),
        Value::DoubleVec(v) => format_vec(s, v, |s, d| {
            tf::stringify_float(s, *d);
            Ok(())
        })?,

        Value::String(v) => write_quoted(s, v)?,
        Value::StringVec(v) => format_vec(s, v, |s, t: &String| write_quoted(s, t))?,
        Value::Token(v) => write_quoted(s, v)?,
        Value::TokenVec(v) => format_vec(s, v, |s, t: &Token| write_quoted(s, t))?,

        Value::AssetPath(v) => write_asset_path(s, v)?,
        Value::AssetPathVec(v) => format_vec(s, v, |s, p: &AssetPath| write_asset_path(s, p))?,

        Value::Vec2h(a) => format_tuple_half(s, &[a.x, a.y])?,
        Value::Vec3h(a) => format_tuple_half(s, &[a.x, a.y, a.z])?,
        Value::Vec4h(a) => format_tuple_half(s, &[a.x, a.y, a.z, a.w])?,
        Value::Quath(a) => format_tuple_half(s, &[a.w, a.x, a.y, a.z])?,
        Value::Vec2hVec(v) => format_vec(s, v, |s, a| format_tuple_half(s, &[a.x, a.y]))?,
        Value::Vec3hVec(v) => format_vec(s, v, |s, a| format_tuple_half(s, &[a.x, a.y, a.z]))?,
        Value::Vec4hVec(v) => format_vec(s, v, |s, a| format_tuple_half(s, &[a.x, a.y, a.z, a.w]))?,
        Value::QuathVec(v) => format_vec(s, v, |s, a| format_tuple_half(s, &[a.w, a.x, a.y, a.z]))?,

        Value::Vec2f(a) => format_tuple_float(s, &[a.x, a.y])?,
        Value::Vec3f(a) => format_tuple_float(s, &[a.x, a.y, a.z])?,
        Value::Vec4f(a) => format_tuple_float(s, &[a.x, a.y, a.z, a.w])?,
        Value::Quatf(a) => format_tuple_float(s, &[a.w, a.x, a.y, a.z])?,
        Value::Vec2fVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.x, a.y]))?,
        Value::Vec3fVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.x, a.y, a.z]))?,
        Value::Vec4fVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.x, a.y, a.z, a.w]))?,
        Value::QuatfVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.w, a.x, a.y, a.z]))?,

        Value::Vec2d(a) => format_tuple_float(s, &[a.x, a.y])?,
        Value::Vec3d(a) => format_tuple_float(s, &[a.x, a.y, a.z])?,
        Value::Vec4d(a) => format_tuple_float(s, &[a.x, a.y, a.z, a.w])?,
        Value::Quatd(a) => format_tuple_float(s, &[a.w, a.x, a.y, a.z])?,
        Value::Vec2dVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.x, a.y]))?,
        Value::Vec3dVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.x, a.y, a.z]))?,
        Value::Vec4dVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.x, a.y, a.z, a.w]))?,
        Value::QuatdVec(v) => format_vec(s, v, |s, a| format_tuple_float(s, &[a.w, a.x, a.y, a.z]))?,

        Value::Vec2i(a) => format_tuple_int(s, &[a.x, a.y])?,
        Value::Vec3i(a) => format_tuple_int(s, &[a.x, a.y, a.z])?,
        Value::Vec4i(a) => format_tuple_int(s, &[a.x, a.y, a.z, a.w])?,
        Value::Vec2iVec(v) => format_vec(s, v, |s, a| format_tuple_int(s, &[a.x, a.y]))?,
        Value::Vec3iVec(v) => format_vec(s, v, |s, a| format_tuple_int(s, &[a.x, a.y, a.z]))?,
        Value::Vec4iVec(v) => format_vec(s, v, |s, a| format_tuple_int(s, &[a.x, a.y, a.z, a.w]))?,

        Value::Matrix2d(m) => format_matrix(s, &m.0, 2)?,
        Value::Matrix3d(m) => format_matrix(s, &m.0, 3)?,
        Value::Matrix4d(m) => format_matrix(s, &m.0, 4)?,
        Value::Matrix2dVec(v) => format_vec(s, v, |s, m| format_matrix(s, &m.0, 2))?,
        Value::Matrix3dVec(v) => format_vec(s, v, |s, m| format_matrix(s, &m.0, 3))?,
        Value::Matrix4dVec(v) => format_vec(s, v, |s, m| format_matrix(s, &m.0, 4))?,

        Value::Specifier(sp) => s.push_str(specifier_keyword(*sp)),
        Value::Permission(p) => s.push_str(match p {
            sdf::Permission::Public => "public",
            sdf::Permission::Private => "private",
        }),
        Value::Variability(vr) => s.push_str(match vr {
            Variability::Varying => "varying",
            Variability::Uniform => "uniform",
        }),

        Value::Dictionary(dict) | Value::UnregisteredDictionary(dict) => {
            format_dictionary(s, dict, indent)?;
        }

        Value::TokenListOp(op) => format_inline_listop(s, op, |s, t: &Token| write_quoted(s, t.as_str()))?,
        Value::StringListOp(op) => format_inline_listop(s, op, |s, t: &String| write_quoted(s, t))?,
        Value::PathListOp(op) => format_inline_listop(s, op, |s, p| {
            write!(s, "<{}>", p.as_str())?;
            Ok(())
        })?,
        Value::ReferenceListOp(op) => format_inline_listop(s, op, |s, r| write_reference(s, r, indent))?,
        Value::PayloadListOp(op) => format_inline_listop(s, op, |s, p| write_payload(s, p))?,
        Value::IntListOp(op) => format_inline_listop(s, op, |s, v| write!(s, "{v}").map_err(Into::into))?,
        Value::Int64ListOp(op) => format_inline_listop(s, op, |s, v| write!(s, "{v}").map_err(Into::into))?,
        Value::UIntListOp(op) => format_inline_listop(s, op, |s, v| write!(s, "{v}").map_err(Into::into))?,
        Value::UInt64ListOp(op) => format_inline_listop(s, op, |s, v| write!(s, "{v}").map_err(Into::into))?,

        Value::Payload(p) => write_payload(s, p)?,
        Value::PathVec(v) => format_vec(s, v, |s, p| {
            write!(s, "<{}>", p.as_str())?;
            Ok(())
        })?,
        Value::Relocates(v) => {
            s.push_str("{ ");
            for (i, (src, tgt)) in v.iter().enumerate() {
                if i > 0 {
                    s.push_str(", ");
                }
                write!(s, "<{}>: <{}>", src.as_str(), tgt.as_str())?;
            }
            s.push_str(" }");
        }
        // C++ `Sdf_WritePrimMetadata` writes the selections as a dictionary
        // of strings.
        Value::VariantSelectionMap(m) => {
            let selections = m
                .iter()
                .map(|(set, variant)| (set.clone(), Value::String(variant.clone())))
                .collect();
            format_dictionary(s, &selections, indent)?;
        }

        Value::TimeSamples(_) => {
            return Err(FormatError::Encode {
                reason: "Value::TimeSamples must be handled by caller".into(),
            });
        }

        Value::Opaque => {
            return Err(FormatError::Encode {
                reason: "an opaque value is never serialized".into(),
            });
        }

        Value::LayerOffsetVec(offsets) => {
            format_vec(s, offsets, |s, o| format_tuple_float(s, &[o.offset, o.scale]))?;
        }

        Value::ValueVec(v) => format_vec(s, v, |s, v| format_value(s, v, indent))?,
        // An unregistered value is the literal a layer was written with,
        // recorded because nothing could type it. Quoting it would make it a
        // string; it is copied out as it came in.
        Value::UnregisteredValue(v) => s.push_str(v),
        Value::UnregisteredValueListOp(op) => format_inline_listop(s, op, |s, body: &String| {
            s.push_str(body);
            Ok(())
        })?,

        Value::TimeCode(t) => tf::stringify_float(s, t.0),
        Value::TimeCodeVec(v) => format_vec(s, v, |s, t| {
            tf::stringify_float(s, t.0);
            Ok(())
        })?,

        Value::PathExpression(expr) => write_quoted(s, &expr.to_string())?,
        Value::PathExpressionVec(v) => format_vec(s, v, |s, expr| {
            write_quoted(s, &expr.to_string())?;
            Ok(())
        })?,
    }
    Ok(())
}

fn format_vec<'o, T, F>(s: &mut ValueText<'o>, items: &[T], mut fmt: F) -> Result<(), FormatError>
where
    F: FnMut(&mut ValueText<'o>, &T) -> Result<(), FormatError>,
{
    s.push('[');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        fmt(s, item)?;
        s.spill()?;
    }
    s.push(']');
    Ok(())
}

/// An item of a list op, which knows whether it can be written without the
/// brackets around it when it is the only one.
///
/// C++ answers this per element type too
/// (`_ListOpWriter<T>::SingleItemRequiresBrackets`), and for the same reason:
/// `prepend apiSchemas = "X"` does not read as a list, while
/// `prepend references = @a.usd@` does.
trait Bracketed: Clone + PartialEq + Hash {
    fn needs_brackets(&self) -> bool;

    /// Whether a list of several is written one item per line, as C++ writes
    /// paths, references and payloads (`_ListOpWriter<T>::ItemPerLine`).
    const PER_LINE: bool = false;
}

/// A lone name or number keeps its brackets: nothing else marks it as a list.
macro_rules! bracketed_items {
    ($($ty:ty),* $(,)?) => {
        $(impl Bracketed for $ty {
            fn needs_brackets(&self) -> bool {
                true
            }
        })*
    };
}

bracketed_items!(Token, String, i32, u32, i64, u64);

/// A name, which writes bare even when alone: the grammar takes a single
/// name without brackets (C++ `Sdf_FileIOUtility::WriteNameVector`).
#[derive(Default, Clone, PartialEq, Hash)]
struct Name(String);

impl Bracketed for Name {
    fn needs_brackets(&self) -> bool {
        false
    }
}

/// A lone path is already delimited by its angle brackets.
impl Bracketed for sdf::Path {
    fn needs_brackets(&self) -> bool {
        false
    }

    const PER_LINE: bool = true;
}

/// A lone payload is already delimited by its asset path.
impl Bracketed for sdf::Payload {
    fn needs_brackets(&self) -> bool {
        false
    }

    const PER_LINE: bool = true;
}

/// A reference writes bare like a payload, until custom data gives it a
/// parenthesised block that would swallow a following item.
impl Bracketed for sdf::Reference {
    fn needs_brackets(&self) -> bool {
        !self.custom_data.is_empty()
    }

    const PER_LINE: bool = true;
}

/// How the items of a list written one per line end.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Items {
    /// A comma between items (a list-op field).
    Separated,
    /// A comma after every item (relationship targets and connections).
    Terminated,
}

fn write_path(s: &mut String, path: &sdf::Path) -> Result<(), FormatError> {
    write!(s, "<{}>", path.as_str())?;
    Ok(())
}

fn format_inline_listop<'o, T, F>(s: &mut ValueText<'o>, op: &ListOp<T>, fmt_item: F) -> Result<(), FormatError>
where
    T: Clone + PartialEq + Hash,
    F: FnMut(&mut ValueText<'o>, &T) -> Result<(), FormatError>,
{
    // Only explicit list ops render inline; non-explicit must be broken out by caller.
    if !op.is_explicit() {
        // Best-effort: flatten for inline contexts.
        let items = op.flatten();
        return format_vec(s, &items, fmt_item);
    }
    format_vec(s, op.explicit_items(), fmt_item)
}

fn format_tuple_half<const N: usize>(s: &mut String, a: &[crate::gf::f16; N]) -> Result<(), FormatError> {
    s.push('(');
    for (i, v) in a.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        gf::stringify_half(s, *v);
    }
    s.push(')');
    Ok(())
}

/// `values` as a parenthesized, comma-separated tuple: `(1, 0.5, 2)`.
fn format_tuple_float<F: zmij::Float + Into<f64>>(s: &mut String, values: &[F]) -> Result<(), FormatError> {
    s.push('(');
    for (i, v) in values.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        tf::stringify_float(s, *v);
    }
    s.push(')');
    Ok(())
}

fn format_tuple_int<const N: usize>(s: &mut String, a: &[i32; N]) -> Result<(), FormatError> {
    s.push('(');
    for (i, v) in a.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        write!(s, "{v}")?;
    }
    s.push(')');
    Ok(())
}

/// A matrix as C++ streams one (`operator<<(std::ostream&, GfMatrix4d)`):
/// `( (a, b), (c, d) )`.
fn format_matrix(s: &mut String, m: &[f64], dim: usize) -> Result<(), FormatError> {
    s.push_str("( ");
    for row in 0..dim {
        if row > 0 {
            s.push_str(", ");
        }
        format_tuple_float(s, &m[row * dim..][..dim])?;
    }
    s.push_str(" )");
    Ok(())
}

/// Looks up `key` in `dict` and returns its `Double` value, defaulting to `0.0`
/// when the key is missing or holds a non-double.
fn get_double(dict: &HashMap<String, Value>, key: &str) -> f64 {
    match dict.get(key) {
        Some(Value::Double(v)) => *v,
        _ => 0.0,
    }
}

/// A dictionary, an entry per line one level in from the line that opens it,
/// which is indented `indent` levels, and the `}` at that level (C++
/// `Sdf_FileIOUtility::_WriteDictionary`).
fn format_dictionary(s: &mut ValueText<'_>, dict: &HashMap<String, Value>, indent: usize) -> Result<(), FormatError> {
    let mut keys: Vec<&String> = dict.keys().collect();
    keys.sort();
    s.push_str("{\n");
    for k in &keys {
        let value = &dict[k.as_str()];
        push_indent(s, indent + 1);
        push_entry_head(s, k, value)?;
        format_value(s, value, indent + 1)?;
        s.push('\n');
    }
    push_indent(s, indent);
    s.push('}');
    Ok(())
}

/// The head of a dictionary entry, `type key = `.
fn push_entry_head(s: &mut String, key: &str, value: &Value) -> Result<(), FormatError> {
    // A nested dictionary is introduced by the `dictionary` keyword; any other
    // entry carries the role-blind name of its value's kind, as C++ emits it.
    let type_name = match value {
        // A dictionary under an unregistered field is still spelled as one;
        // only the field around it was unregistered.
        Value::Dictionary(_) | Value::UnregisteredDictionary(_) => Some(Token::new("dictionary")),
        other => sdf::ValueKind::from(other).type_name().map(|ty| ty.as_token()),
    };
    if let Some(ty) = type_name {
        s.push_str(ty.as_str());
        s.push(' ');
    }
    // A key is bare only when it is an identifier (C++ `TfIsValidIdentifier`);
    // C++ refuses a bare namespaced key (`int a:b = 3`) in a dictionary.
    if tf::is_valid_identifier(key) {
        s.push_str(key);
    } else {
        write_quoted(s, key)?;
    }
    s.push_str(" = ");
    Ok(())
}

/// A dictionary on one line, its entries in key order and separated by
/// semicolons, as C++ `Sdf_FileIOUtility::WriteDictionary` writes one with
/// `multiLine` off: a spline knot's custom data.
fn format_inline_dictionary(s: &mut String, dict: &HashMap<String, Value>) -> Result<(), FormatError> {
    let mut entries: Vec<_> = dict.iter().collect();
    entries.sort_by_key(|(key, _)| *key);
    s.push_str("{ ");
    for (i, (key, value)) in entries.into_iter().enumerate() {
        if i > 0 {
            s.push_str("; ");
        }
        push_entry_head(s, key, value)?;
        match value {
            Value::Dictionary(nested) | Value::UnregisteredDictionary(nested) => format_inline_dictionary(s, nested)?,
            value => format_value(&mut ValueText::of(s), value, 0)?,
        }
    }
    s.push_str(" }");
    Ok(())
}

/// A spline knot's next interpolation, `held` when it records none.
fn interpolation(knot: &HashMap<String, Value>) -> &str {
    match knot.get("nextInterpolationMode") {
        Some(Value::Token(t)) => t.as_str(),
        _ => "held",
    }
}

fn push_indent(s: &mut String, levels: usize) {
    s.extend(iter::repeat_n("    ", levels));
}

/// Writes `text` as a USDA string, quoted as C++ `Sdf_FileIOUtility::Quote`
/// quotes it: in double quotes, or single quotes when it holds a double quote
/// and no single one; in triple quotes, with its newlines as they are, when it
/// holds a newline; with the quote, a backslash, `\r` and `\t` escaped, and
/// any other ASCII character outside the printable range as `\xNN`.
///
/// The reader expands escapes (C++ `TfEscapeStringReplaceChar`), so a backslash
/// must be doubled or it would read back as whatever it precedes — a Windows
/// path would return with `\t` as a tab. Escaping also means one delimiter
/// always suffices, so no string is unquotable.
fn write_quoted(s: &mut String, text: &str) -> Result<(), FormatError> {
    let quote = if text.contains('"') && !text.contains('\'') {
        '\''
    } else {
        '"'
    };
    let triple = text.contains('\n');
    let quotes = if triple { 3 } else { 1 };
    s.extend(iter::repeat_n(quote, quotes));
    for c in text.chars() {
        match c {
            '\n' if triple => s.push('\n'),
            '\n' => s.push_str("\\n"),
            '\r' => s.push_str("\\r"),
            '\t' => s.push_str("\\t"),
            '\\' => s.push_str("\\\\"),
            c if c == quote => {
                s.push('\\');
                s.push(c);
            }
            c if c.is_ascii() && !(' '..='~').contains(&c) => write!(s, "\\x{:02x}", c as u8)?,
            other => s.push(other),
        }
    }
    s.extend(iter::repeat_n(quote, quotes));
    Ok(())
}

fn write_asset_path(s: &mut String, path: &str) -> Result<(), FormatError> {
    if path.contains('@') {
        s.push_str("@@@");
        s.push_str(path);
        s.push_str("@@@");
    } else {
        s.push('@');
        s.push_str(path);
        s.push('@');
    }
    Ok(())
}

/// A reference on a line indented `indent` levels, as C++
/// `_ListOpWriter<SdfReference>` writes one: custom data puts its layer
/// offset and the data on lines of their own, in parentheses.
fn write_reference(s: &mut String, r: &Reference, indent: usize) -> Result<(), FormatError> {
    write_arc_target(s, &r.asset_path, &r.prim_path)?;
    if r.custom_data.is_empty() {
        write_layer_offset(s, &r.layer_offset, None);
        return Ok(());
    }
    s.push_str(" (\n");
    write_layer_offset(s, &r.layer_offset, Some(indent + 1));
    push_indent(s, indent + 1);
    s.push_str("customData = ");
    format_dictionary(&mut ValueText::of(s), &r.custom_data, indent + 1)?;
    s.push('\n');
    push_indent(s, indent);
    s.push(')');
    Ok(())
}

fn write_payload(s: &mut String, p: &Payload) -> Result<(), FormatError> {
    write_arc_target(s, &p.asset_path, &p.prim_path)?;
    write_layer_offset(s, &p.layer_offset, None);
    Ok(())
}

/// An arc's asset and prim path. An internal arc always writes its prim
/// path, `<>` when empty, since that is what targets the default prim.
fn write_arc_target(s: &mut String, asset_path: &str, prim_path: &Path) -> Result<(), FormatError> {
    if !asset_path.is_empty() {
        write_asset_path(s, asset_path)?;
        if prim_path.is_empty() {
            return Ok(());
        }
    }
    write!(s, "<{}>", prim_path.as_str())?;
    Ok(())
}

/// A sublayer's, reference's or payload's layer offset, as C++
/// `WriteLayerOffset` writes it: nothing where it equals the identity as
/// `SdfLayerOffset` compares them, within 1e-6, and otherwise each part that
/// is not exactly the identity's. With `multi_line`, the indent to write each
/// part on a line of its own at; without, the parts go in parentheses after
/// the asset.
fn write_layer_offset(s: &mut String, offset: &LayerOffset, multi_line: Option<usize>) {
    if offset.is_close(&LayerOffset::IDENTITY) {
        return;
    }
    let parts = [("offset", offset.offset, 0.0), ("scale", offset.scale, 1.0)];
    let parts = parts.into_iter().filter(|&(_, value, identity)| value != identity);
    if multi_line.is_none() {
        s.push_str(" (");
    }
    for (i, (name, value, _)) in parts.enumerate() {
        match multi_line {
            Some(indent) => push_indent(s, indent),
            None if i > 0 => s.push_str("; "),
            None => {}
        }
        s.push_str(name);
        s.push_str(" = ");
        tf::stringify_float(s, value);
        if multi_line.is_some() {
            s.push('\n');
        }
    }
    if multi_line.is_none() {
        s.push(')');
    }
}

fn specifier_keyword(s: Specifier) -> &'static str {
    match s {
        Specifier::Def => "def",
        Specifier::Over => "over",
        Specifier::Class => "class",
    }
}

fn get_value(data: &dyn AbstractData, path: &Path, field: &str) -> Option<Value> {
    data.field(path, field).ok().map(|v| v.into_owned())
}

/// Composed `primChildren` / `propertyChildren` name list (`key` selects which),
/// empty when unset.
fn children(data: &dyn AbstractData, path: &Path, key: ChildrenKey) -> Vec<Token> {
    match get_value(data, path, key.as_str()) {
        Some(Value::TokenVec(v)) => v,
        _ => Vec::new(),
    }
}

// Field classifiers. Match C++ `Sdf_Is{Prim,Attribute,Relationship}MetadataField`.

const PRIM_STRUCTURAL_FIELDS: &[&str] = &[
    FieldKey::Specifier.as_str(),
    FieldKey::TypeName.as_str(),
    FieldKey::PrimOrder.as_str(),
    FieldKey::PropertyOrder.as_str(),
    ChildrenKey::PrimChildren.as_str(),
    ChildrenKey::PropertyChildren.as_str(),
    ChildrenKey::VariantChildren.as_str(),
    ChildrenKey::VariantSetChildren.as_str(),
];

const ATTRIBUTE_STRUCTURAL_FIELDS: &[&str] = &[
    FieldKey::TypeName.as_str(),
    FieldKey::Default.as_str(),
    FieldKey::Custom.as_str(),
    FieldKey::Variability.as_str(),
    FieldKey::TimeSamples.as_str(),
    FieldKey::ConnectionPaths.as_str(),
    ChildrenKey::ConnectionChildren.as_str(),
    FieldKey::Spline.as_str(),
];

const RELATIONSHIP_STRUCTURAL_FIELDS: &[&str] = &[
    FieldKey::Custom.as_str(),
    FieldKey::Variability.as_str(),
    FieldKey::TargetPaths.as_str(),
    ChildrenKey::RelationshipTargetChildren.as_str(),
];

/// A spec's metadata fields in the order C++ writes them
/// (`Sdf_WritePrimMetadata`, `Sdf_WriteAttribute`, `Sdf_WriteRelationship`):
/// the comment first, then the rest sorted by field name with
/// `TfDictionaryLessThan`.
fn metadata_fields(data: &dyn AbstractData, path: &Path, structural: fn(&str) -> bool) -> Vec<String> {
    let mut fields: Vec<String> = data
        .list_fields(path)
        .unwrap_or_default()
        .into_iter()
        .filter(|n| !structural(n))
        // C++ writes a comment only when it is not empty.
        .filter(|n| n != FieldKey::Comment.as_str() || !is_empty_string(data, path, n))
        .collect();
    fields.sort_by(|a, b| {
        let comment = |n: &str| n != FieldKey::Comment.as_str();
        comment(a).cmp(&comment(b)).then_with(|| tf::dictionary_cmp(a, b))
    });
    fields
}

/// Whether the field `name` at `path` holds the empty string.
fn is_empty_string(data: &dyn AbstractData, path: &Path, name: &str) -> bool {
    matches!(data.field(path, name).as_deref(), Ok(Value::String(text)) if text.is_empty())
}

fn is_prim_structural_field(name: &str) -> bool {
    PRIM_STRUCTURAL_FIELDS.contains(&name)
}

fn is_attribute_structural_field(name: &str) -> bool {
    ATTRIBUTE_STRUCTURAL_FIELDS.contains(&name)
}

fn is_relationship_structural_field(name: &str) -> bool {
    RELATIONSHIP_STRUCTURAL_FIELDS.contains(&name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{Data, path};
    use crate::{sdf, usda};

    /// An unregistered value is the literal a layer was written with, so it
    /// is copied out, not quoted. Quoting `(1, 2, 3)` would turn a tuple into
    /// a string the next reader could not tell apart from one.
    #[test]
    fn unregistered_value_is_copied() {
        for literal in ["7", "(1, 2, 3)", "[a, b]", "\"already quoted\""] {
            let mut out = String::new();
            format_value(
                &mut ValueText::of(&mut out),
                &Value::UnregisteredValue(literal.to_owned()),
                0,
            )
            .expect("writes");
            assert_eq!(out, literal);
        }
    }

    /// Each item of an unregistered list op is the recorded text of a whole
    /// body, so the brackets stay even for one item — `[1, 2]`, never `1, 2`.
    #[test]
    fn unregistered_listop_keeps_brackets() {
        let op = sdf::ListOp::<String>::explicit(["1, 2".to_owned()]);

        let mut out = String::new();
        format_value(&mut ValueText::of(&mut out), &Value::UnregisteredValueListOp(op), 0).expect("writes");
        assert_eq!(out, "[1, 2]");
    }

    /// An operation with nothing in it still writes a body.
    #[test]
    fn unregistered_listop_empty() {
        let op = sdf::ListOp::<String>::explicit([]);

        let mut out = String::new();
        format_value(&mut ValueText::of(&mut out), &Value::UnregisteredValueListOp(op), 0).expect("writes");
        assert_eq!(out, "[]");
    }

    /// An unregistered field's operations come back out as statements, each
    /// body inside the brackets it was authored with - the shared list-op
    /// helper would write a lone item bare and turn `[1, 2]` into `1, 2`.
    #[test]
    fn unregistered_metadata_statements() {
        let source = r#"#usda 1.0

def "Mesh" (
    prepend madeUpList = [1, 2]
    delete madeUpList = 3
    madeUpField = 1.50
)
{
}
"#;
        let data = usda::parse(source).expect("parses");
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");

        assert!(text.contains("prepend madeUpList = [1, 2]"), "{text}");
        assert!(text.contains("delete madeUpList = [3]"), "{text}");
        assert!(text.contains("madeUpField = 1.50"), "{text}");

        // The writer sorts metadata as C++ does, so compare the fields as a set.
        let reparsed = usda::parse(&text).expect("re-parses");
        let path = sdf::Path::new("/Mesh").unwrap();
        let sorted = |data: &sdf::Data| {
            let mut fields = data.spec(&path).expect("spec").fields.clone();
            fields.sort_by(|a, b| a.0.as_str().cmp(b.0.as_str()));
            fields
        };
        assert_eq!(sorted(&data), sorted(&reparsed));
    }

    /// A field stored under a name of its own is written by its keyword:
    /// `inheritPaths` as `inherits`, `documentation` as `doc`, on a prim and
    /// on a property.
    #[test]
    fn field_keywords() {
        let source = "#usda 1.0\n\ndef \"A\" (\n    doc = \"a prim\"\n    inherits = </C>\n)\n{\n    double x = 1 (\n        doc = \"a property\"\n    )\n}\n";
        let data = usda::parse(source).expect("parses");
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
        for line in ["inherits = </C>", "doc = \"a prim\"", "doc = \"a property\""] {
            assert!(text.contains(line), "{line}\n{text}");
        }
        assert!(
            !text.contains("inheritPaths") && !text.contains("documentation"),
            "{text}"
        );
    }

    /// A class arc authored under a variant anchors in the namespace
    /// composition maps it in, which the written form re-reads.
    #[test]
    fn variant_arc_roundtrip() {
        let source = "#usda 1.0\n\ndef \"A\" (\n    variants = {\n        string v = \"x\"\n    }\n    prepend variantSets = \"v\"\n)\n{\n    variantSet \"v\" = {\n        \"x\" {\n            def \"B\" (\n                inherits = <../D>\n                specializes = <C>\n            )\n            {\n            }\n        }\n    }\n}\n";
        let data = usda::parse(source).expect("parses");
        let prim = sdf::Path::new("/A{v=x}B").unwrap();
        let arcs = |key: FieldKey| {
            data.spec(&prim)
                .expect("spec")
                .get(key.as_str())
                .expect("authored")
                .to_owned()
                .try_as_path_list_op()
                .unwrap()
        };
        assert_eq!(arcs(FieldKey::InheritPaths).explicit_items(), [path("/A/D").unwrap()]);
        assert_eq!(arcs(FieldKey::Specializes).explicit_items(), [path("/A/B/C").unwrap()]);

        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
        let reparsed = usda::parse(&text).expect("re-parses");
        assert_eq!(
            data.spec(&prim).expect("spec").fields,
            reparsed.spec(&prim).expect("spec").fields
        );
    }

    /// Every unit whose name is an identifier survives emit → re-parse.
    ///
    /// `%` and `default` are left out because the grammar has no term for
    /// them; upstream writes the same unreadable text for those two.
    #[test]
    fn display_units_roundtrip() {
        for unit in ["mm", "cm", "dm", "m", "km", "in", "ft", "yd", "mi", "deg", "rad"] {
            let source = format!(
                "#usda 1.0\n\ndef \"Mesh\"\n{{\n    custom double a = 1 (\n        displayUnit = {unit}\n    )\n}}\n"
            );
            let data = usda::parse(&source).expect("parses");
            let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
            let reparsed = usda::parse(&text).unwrap_or_else(|e| panic!("{unit} re-parses: {e:#}"));
            let path = sdf::Path::new("/Mesh.a").unwrap();
            assert_eq!(
                reparsed.spec(&path).expect("spec").get(FieldKey::DisplayUnit.as_str()),
                Some(&Value::token(unit)),
                "{unit}"
            );
        }
    }

    /// A reference's custom data survives a write and re-read, with and
    /// without a layer offset, and an identity offset is left out as C++ does.
    /// The source is what C++ 25.05 writes for these references.
    #[test]
    fn reference_custom_data_roundtrip() {
        let source = r#"#usda 1.0

over "R" (
    prepend references = [
        @./a.usda@ (
            customData = {
                string note = "only data"
            }
        ),
        @./b.usda@ (offset = 5; scale = 2),
        @./c.usda@</P> (
            offset = 5
            scale = 2
            customData = {
                int n = 1
            }
        )
    ]
)
{
}
"#;
        let data = usda::parse(source).expect("parses");
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
        assert!(!text.contains("offset = 0"), "identity offset written: {text}");
        let reparsed = usda::parse(&text).unwrap_or_else(|e| panic!("re-parses: {e:#}\n{text}"));
        let references = |data: &Data| match data.spec(&path("/R").unwrap()).expect("spec").get("references") {
            Some(Value::ReferenceListOp(op)) => op.prepended_items().to_vec(),
            other => panic!("references: {other:?}"),
        };
        let written = references(&reparsed);
        assert_eq!(written, references(&data));
        assert_eq!(
            written[0].custom_data.get("note"),
            Some(&Value::String("only data".into()))
        );
        assert_eq!(written[1].layer_offset, LayerOffset::new(5.0, 2.0));
        assert_eq!(written[2].custom_data.get("n"), Some(&Value::Int(1)));
    }

    /// Variant-set names write as a name vector: one name bare, several
    /// bracketed. The generic list-op rule would bracket the lone name too.
    #[test]
    fn variant_sets_name_vector() {
        for (authored, expected) in [
            ("\"v\"", "prepend variantSets = \"v\""),
            ("[\"a\", \"b\"]", "prepend variantSets = [\"a\", \"b\"]"),
        ] {
            let source = format!(
                "#usda 1.0

def \"P\" (
    prepend variantSets = {authored}
)
{{
}}
"
            );
            let data = usda::parse(&source).expect("parses");
            let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
            assert!(text.contains(expected), "{authored} -> {text}");
            usda::parse(&text).unwrap_or_else(|e| panic!("{authored} re-parses: {e:#}"));
        }
    }

    /// A display unit is written as the bare name the grammar reads back, not
    /// as the quoted string every other token becomes.
    #[test]
    fn display_unit_roundtrip() {
        let source = "#usda 1.0\n\ndef \"Mesh\"\n{\n    custom double a = 1 (\n        displayUnit = mm\n    )\n}\n";
        let data = usda::parse(source).expect("parses");
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");

        assert!(text.contains("displayUnit = mm"), "{text}");
        let reparsed = usda::parse(&text).expect("re-parses");
        let path = sdf::Path::new("/Mesh.a").unwrap();
        assert_eq!(
            reparsed.spec(&path).expect("spec").get(FieldKey::DisplayUnit.as_str()),
            Some(&Value::token("mm"))
        );
    }

    /// A dictionary under an unregistered field is spelled `dictionary` like
    /// any other, so a dictionary holding one still re-parses.
    #[test]
    fn nested_unregistered_dictionary() {
        let mut data = Data::new();
        let root = sdf::Path::abs_root();
        data.create_spec(root.clone(), sdf::SpecType::PseudoRoot);
        let inner = sdf::Dictionary::from([("k".to_owned(), Value::Int(1))]);
        let outer = sdf::Dictionary::from([("nested".to_owned(), Value::UnregisteredDictionary(inner))]);
        data.set_field(&root, FieldKey::CustomLayerData.as_str(), Value::Dictionary(outer));

        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
        assert!(text.contains("dictionary nested"), "{text}");
        usda::parse(&text).expect("re-parses");
    }

    /// An unregistered type's value survives load → save → load as the text
    /// it was authored with, which is the whole point of recording it.
    #[test]
    fn unregistered_value_roundtrip() {
        let source = r#"#usda 1.0

def "Mesh"
{
    custom myType tuple = (1, 2, 3)
    custom myType asset = @a/b.usd@
    custom myType target = </Mesh>
    custom myType quoted = "a]b"
}
"#;
        let data = usda::parse(source).expect("parses");
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
        let reparsed = usda::parse(&text).expect("re-parses");

        for (name, literal) in [
            ("tuple", "(1, 2, 3)"),
            ("asset", "@a/b.usd@"),
            ("target", "</Mesh>"),
            ("quoted", "\"a]b\""),
        ] {
            let path = sdf::Path::new(&format!("/Mesh.{name}")).unwrap();
            assert_eq!(
                reparsed.spec(&path).expect("spec").get("default"),
                Some(&Value::UnregisteredValue(literal.to_owned())),
                "{name}"
            );
        }
    }

    /// A relationship keeps its variability through emit → re-parse. The text
    /// form spells only the `varying` case, so the uniform default has to
    /// survive as the absence of a keyword.
    #[test]
    fn relationship_variability_roundtrip() {
        let source = r#"#usda 1.0

def "Mesh"
{
    rel plain
    varying rel moving
    custom rel owned
}
"#;
        let data = crate::usda::parse(source).expect("parses");
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");

        assert!(text.contains("rel plain"), "{text}");
        assert!(!text.contains("uniform rel"), "uniform is never spelled: {text}");
        assert!(text.contains("varying rel moving"), "{text}");
        assert!(text.contains("custom rel owned"), "{text}");

        let reparsed = crate::usda::parse(&text).expect("re-parses");
        for name in ["plain", "moving", "owned"] {
            let path = crate::sdf::Path::new(&format!("/Mesh.{name}")).unwrap();
            assert_eq!(
                data.spec(&path).expect("spec").fields,
                reparsed.spec(&path).expect("spec").fields,
                "{name} round-trips"
            );
        }
    }

    /// Forms a layer may author that C++ reads into other data, written back
    /// as C++ writes them (its `testSdfParsing` inputs 139, 176, 184 and 220):
    /// a layer's relative relocates anchored at the root, an empty sublayer
    /// list left out, the any-type prim untyped, and a spline's Hermite
    /// tangents and looping extrapolation.
    #[test]
    fn cpp_input_forms() {
        for (source, expected) in [
            (
                "#usda 1.0\n(\n    relocates = {\n        <a/b>: <c/d>\n    }\n)\n",
                "#usda 1.0\n(\n    relocates = {\n        </a/b>: </c/d>\n    }\n)\n\n",
            ),
            ("#usda 1.0\n(\n    subLayers = [\n    ]\n)\n", "#usda 1.0\n\n"),
            (
                "#usda 1.0\ndef __AnyType__ \"P\"\n{\n}\n",
                "#usda 1.0\n\ndef \"P\"\n{\n}\n\n",
            ),
            (
                "#usda 1.0\ndef \"P\"\n{\n    float s.spline = {\n        hermite,\n        post: loop repeat,\n        \
                 1: 8; pre (0); post curve (4),\n        6: 20; pre (2); post curve (2),\n    }\n}\n",
                "#usda 1.0\n\ndef \"P\"\n{\n    float s.spline = {\n        hermite,\n        post: loop repeat,\n        \
                 1: 8; pre (0); post curve (4),\n        6: 20; pre (2); post curve (2),\n    }\n}\n\n",
            ),
        ] {
            let data = usda::parse(source).unwrap_or_else(|e| panic!("{source}: {e:#}"));
            let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
            assert_eq!(text, expected, "{source}");
        }
    }

    /// A Bezier spline keeps what it authors: an explicit `none`
    /// extrapolation, a tangent whose second number is 0, a tangent on a
    /// linear segment, and its knots, which come out in time order as C++
    /// keeps them.
    #[test]
    fn spline_kept() {
        let source = "#usda 1.0\ndef \"P\"\n{\n    double s.spline = {\n        pre: none,\n        \
                      6: 20; post linear (2, 3),\n        1: 8; pre (1, 0); post curve (4, 5),\n    }\n}\n";
        let expected = "#usda 1.0\n\ndef \"P\"\n{\n    double s.spline = {\n        bezier,\n        pre: none,\n        \
                        1: 8; pre (1, 0); post curve (4, 5),\n        6: 20; pre (0, 0); post linear (2, 3),\n    }\n}\n\n";
        let data = usda::parse(source).expect("parses");
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).expect("writes");
        assert_eq!(text, expected);
    }

    #[test]
    fn writes_empty_layer() {
        let data = Data::new();
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).unwrap();
        assert_eq!(text, "#usda 1.0\n\n");
    }

    #[test]
    fn writes_single_def() {
        let mut data = Data::new();
        let root = Path::abs_root();
        let root_spec = data.create_spec(root.clone(), SpecType::PseudoRoot);
        root_spec.add(ChildrenKey::PrimChildren, Value::TokenVec(vec!["Foo".into()]));

        let foo = path("/Foo").unwrap();
        let foo_spec = data.create_spec(foo, SpecType::Prim);
        foo_spec.add(FieldKey::Specifier, Value::Specifier(Specifier::Def));
        foo_spec.add(FieldKey::TypeName, Value::Token("Xform".into()));

        let text = TextWriter::write_to_string(&data as &dyn AbstractData).unwrap();
        assert!(text.contains("def Xform \"Foo\""));
    }

    /// An `asset[]` attribute keeps its type through parse → emit → re-parse,
    /// emitting `@...@` elements rather than `string[]` quoted strings.
    #[test]
    fn asset_array_roundtrip() {
        use crate::usda::parser::Parser;

        let src = concat!(
            "#usda 1.0\n",
            "def Material \"M\"\n{\n",
            "    asset[] inputs:files = [@./tex_a.png@, @./tex_b.png@]\n",
            "}\n",
        );

        let parsed = Parser::new(src).parse().expect("parse asset[] source");
        let files = parsed
            .get(&path("/M.inputs:files").unwrap())
            .and_then(|s| s.get(FieldKey::Default.as_str()))
            .expect("inputs:files default");
        assert!(
            matches!(files, Value::AssetPathVec(v) if v == &["./tex_a.png", "./tex_b.png"]),
            "parsed as {files:?}, expected AssetPathVec"
        );

        let reader = Data::from_specs(parsed);
        let emitted = TextWriter::write_to_string(&reader as &dyn AbstractData).unwrap();
        assert!(emitted.contains("asset[] inputs:files"), "emitted: {emitted}");
        assert!(emitted.contains("@./tex_a.png@"), "emitted: {emitted}");
        assert!(!emitted.contains("string[]"), "emitted: {emitted}");

        let reparsed = Parser::new(&emitted).parse().expect("re-parse emitted");
        let files = reparsed
            .get(&path("/M.inputs:files").unwrap())
            .and_then(|s| s.get(FieldKey::Default.as_str()));
        assert!(matches!(files, Some(Value::AssetPathVec(_))), "re-parsed as {files:?}");
    }

    /// A legacy spelling is read and written back as its standard twin (C++
    /// `GetSerializationName`).
    #[test]
    fn legacy_name_canonicalized() {
        use crate::usda::parser::Parser;

        let src = "#usda 1.0\ndef \"P\"\n{\n    Color c = (1, 2, 3)\n    Vec3f[] v = [(1, 2, 3)]\n}\n";
        let parsed = Parser::new(src).parse().expect("parse legacy spellings");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert!(emitted.contains("color3d c = "), "emitted: {emitted}");
        assert!(emitted.contains("float3[] v = "), "emitted: {emitted}");

        let reparsed = Parser::new(&emitted).parse().expect("re-parse emitted");
        let type_name = |attr: &str| {
            reparsed
                .get(&path(attr).unwrap())
                .and_then(|s| s.get(FieldKey::TypeName.as_str()))
                .cloned()
        };
        assert_eq!(type_name("/P.c"), Some(Value::token("color3d")));
        assert_eq!(type_name("/P.v"), Some(Value::token("float3[]")));
    }

    /// An unregistered spelling is written back as authored.
    #[test]
    fn unknown_name_verbatim() {
        use crate::usda::parser::Parser;

        let src = "#usda 1.0\ndef \"P\"\n{\n    custom double3d[] baz\n}\n";
        let parsed = Parser::new(src).parse().expect("parse unregistered declaration");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert!(emitted.contains("custom double3d[] baz"), "emitted: {emitted}");

        let reparsed = Parser::new(&emitted).parse().expect("re-parse emitted");
        let type_name = reparsed
            .get(&path("/P.baz").unwrap())
            .and_then(|s| s.get(FieldKey::TypeName.as_str()))
            .cloned();
        assert_eq!(type_name, Some(Value::token("double3d[]")));
    }

    /// Dictionary entries carry the role-blind name of their value's kind, and
    /// a nested dictionary the `dictionary` keyword.
    #[test]
    fn dict_entry_type_names() {
        let mut data = Data::new();
        data.create_spec(Path::abs_root(), SpecType::PseudoRoot)
            .add(ChildrenKey::PrimChildren, Value::TokenVec(vec!["P".into()]));
        let prim = data.create_spec(path("/P").unwrap(), SpecType::Prim);
        prim.add(FieldKey::Specifier, Value::Specifier(Specifier::Def));
        let mut sub = HashMap::new();
        sub.insert("n".to_owned(), Value::Int(1));
        let mut custom = HashMap::new();
        custom.insert("v".to_owned(), Value::vec3f(1.0, 2.0, 3.0));
        custom.insert("sub".to_owned(), Value::Dictionary(sub.into()));
        prim.add(FieldKey::CustomData, Value::Dictionary(custom.into()));

        let emitted = TextWriter::write_to_string(&data as &dyn AbstractData).unwrap();
        assert!(emitted.contains("float3 v = "), "emitted: {emitted}");
        assert!(emitted.contains("dictionary sub = {"), "emitted: {emitted}");
        assert!(emitted.contains("int n = "), "emitted: {emitted}");
    }

    /// Time samples of every shape keep their declared kind through parse →
    /// emit → re-parse.
    #[test]
    fn typed_samples_round_trip() {
        use crate::usda::parser::Parser;

        let src = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures/typed_timesamples.usda"))
            .expect("fixture readable");
        let parsed = Parser::new(&src).parse().expect("parse fixture");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        let reparsed = Parser::new(&emitted).parse().expect("re-parse emitted");
        let samples = |attr: &str| {
            reparsed
                .get(&path(attr).unwrap())
                .and_then(|s| s.get(FieldKey::TimeSamples.as_str()))
                .cloned()
                .expect("samples")
                .try_as_time_samples()
                .expect("a sample map")
        };
        assert_eq!(
            samples("/Anim.weight"),
            vec![
                (0.0, Value::Float(4.0)),
                (1.0, Value::Float(0.5)),
                (2.0, Value::ValueBlock)
            ]
        );
        assert_eq!(
            samples("/Anim.mode"),
            vec![(0.0, Value::token("on")), (1.0, Value::token("off"))]
        );
        assert_eq!(
            samples("/Anim.indices"),
            vec![(0.0, Value::IntVec(vec![1, 2, 3])), (1.0, Value::IntVec(Vec::new()))]
        );
        assert_eq!(
            samples("/Anim.velocity"),
            vec![(0.0, Value::vec3f(1.0, 0.0, 0.0)), (1.0, Value::vec3f(0.0, 1.0, 0.0))]
        );
        assert_eq!(
            samples("/Anim.cue"),
            vec![
                (0.0, Value::TimeCode(sdf::TimeCode(24.0))),
                (1.0, Value::TimeCode(sdf::TimeCode(48.5)))
            ]
        );
    }

    /// Emit `text` via `write_quoted` then re-tokenize the output and return
    /// what the lexer recovered.
    fn write_quoted_and_reparse(text: &str) -> String {
        use crate::usda::token::Token;
        use logos::Logos;

        let mut out = String::new();
        write_quoted(&mut out, text).unwrap();

        let mut lexer = Token::lexer(&out);
        let first = lexer.next().expect("lexer produced no token").expect("lexer error");
        assert!(
            lexer.next().is_none(),
            "expected a single token, got trailing input: {out:?}"
        );
        match first {
            Token::String(s) => s.into_owned(),
            other => panic!("expected Token::String, got {other:?} for output {out:?}"),
        }
    }

    #[test]
    fn write_quoted_roundtrips_tricky_strings() {
        // Plain text.
        assert_eq!(write_quoted_and_reparse("hello"), "hello");
        // Contains only double quotes — must be wrapped in single quotes.
        assert_eq!(write_quoted_and_reparse(r#"has "quotes""#), r#"has "quotes""#);
        // Contains only single quotes — must be wrapped in double quotes.
        assert_eq!(write_quoted_and_reparse("has 'apostrophes'"), "has 'apostrophes'");
        // Contains both kinds of quotes on one line — no single-char delimiter works,
        // so the emitter must fall back to triple quotes.
        assert_eq!(write_quoted_and_reparse(r#"mix "dq" and 'sq'"#), r#"mix "dq" and 'sq'"#);
        // Contains a newline — must use triple quotes.
        assert_eq!(write_quoted_and_reparse("line1\nline2"), "line1\nline2");
        // Contains a newline and `"""` — must switch to triple single-quote.
        assert_eq!(write_quoted_and_reparse("pre\n\"\"\"post"), "pre\n\"\"\"post");
        // Contains a newline and `'''` — must use triple double-quote.
        assert_eq!(write_quoted_and_reparse("pre\n'''post"), "pre\n'''post");
        // Escaping leaves no unquotable string: the case that used to have no
        // valid delimiter round-trips like any other.
        assert_eq!(
            write_quoted_and_reparse("line\n\"\"\"and'''both"),
            "line\n\"\"\"and'''both"
        );
        // A backslash survives, which delimiter choice alone could not manage —
        // a Windows path would otherwise come back with `\t` as a tab.
        assert_eq!(write_quoted_and_reparse(r"C:\temp\new"), r"C:\temp\new");
    }

    #[test]
    fn dictionary_key_with_space_roundtrips() {
        // The USDA parser accepts quoted strings, bare identifiers, and
        // namespaced identifiers (with `:`) as dictionary keys. Keys that are
        // none of those (spaces, hyphens, digit-leading, ...) must be emitted
        // quoted or they will tokenize into multiple lexemes and fail to parse.
        use crate::usda::parser::Parser;

        let mut data = Data::new();
        let root = Path::abs_root();
        let root_spec = data.create_spec(root.clone(), SpecType::PseudoRoot);

        let mut dict = HashMap::new();
        dict.insert("simple".to_string(), Value::Int(1));
        dict.insert("ns:colon:key".to_string(), Value::Int(2));
        dict.insert("key with space".to_string(), Value::Int(3));
        dict.insert("1leading-digit".to_string(), Value::Int(4));
        root_spec.add(FieldKey::CustomLayerData, Value::Dictionary(dict.into()));

        let text = TextWriter::write_to_string(&data as &dyn AbstractData).unwrap();
        let parsed = Parser::new(&text)
            .parse()
            .unwrap_or_else(|e| panic!("re-parse failed:\n---emitted---\n{text}\n---end---\n{e:#}"));

        let spec = parsed.get(&root).expect("pseudo-root spec should round-trip");
        let got = spec.get(FieldKey::CustomLayerData.as_str()).expect("customLayerData");
        let Value::Dictionary(got) = got else {
            panic!("expected Dictionary, got {got:?}");
        };
        for k in ["simple", "ns:colon:key", "key with space", "1leading-digit"] {
            assert!(
                got.contains_key(k),
                "lost key {k:?}; roundtripped keys: {:?}",
                got.keys().collect::<Vec<_>>()
            );
        }
    }

    /// An attribute declared only by its `.connect`, `.timeSamples` or
    /// `.spline` statement is written without a bare declaration, and the
    /// statement keeps its variability, as OpenUSD 26.11 writes this layer
    /// back. The spline's body is left out of the check: it is written in the
    /// dictionary form.
    #[test]
    fn declared_by_statement() {
        use crate::usda::parser::Parser;

        let text = r#"#usda 1.0
def Shader "Mapping"
{
    float3 inputs:in1.connect = </Material/Coords.outputs:out>
    uniform double u.timeSamples = { 1: 2 }
    float s.spline = { 1: 2, }
}
"#;
        let parsed = Parser::new(text).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert!(
            emitted.contains("    float3 inputs:in1.connect = </Material/Coords.outputs:out>\n"),
            "{emitted}"
        );
        assert!(emitted.contains("    uniform double u.timeSamples = {\n"), "{emitted}");
        assert!(!emitted.contains("float3 inputs:in1\n"), "{emitted}");
        assert!(!emitted.contains("double u\n"), "{emitted}");
        assert!(emitted.contains("    float s.spline = {\n"), "{emitted}");
        assert!(!emitted.contains("float s\n"), "{emitted}");
    }

    /// A hand-written layer is written as OpenUSD 26.11 writes it
    /// (`Sdf.Layer.OpenAsAnonymous(source).ExportToString()`), byte for byte:
    /// layer metadata sorted, one sublayer per line, properties sorted by name,
    /// a reorder statement only when it orders more than one name, blank lines
    /// around child prims, a variant closed after a blank line, strings quoted
    /// as C++ quotes them, and a blank line at the end.
    #[test]
    fn layout_as_cpp() {
        use crate::usda::parser::Parser;

        let source = r#"#usda 1.0
(
    upAxis = "Y"
    subLayers = [@a.usda@, @b.usda@ (offset = 2)]
    defaultPrim = "Root"
)

def "Root" (
    prepend variantSets = "look"
)
{
    string quoted = "say \"hi\""
    string lines = "one\ntwo"
    string tab = "a\tb\x01"
    int b = 2
    int a = 1
    reorder properties = ["b", "a"]

    def "First"
    {
    }

    def "Second"
    {
        int x = 1
        reorder properties = ["x"]
        reorder nameChildren = ["Only"]

        def "Only"
        {
        }
    }

    variantSet "look" = {
        "red" {
            int c = 3
        }
    }
}
"#;
        let written = r#"#usda 1.0
(
    defaultPrim = "Root"
    subLayers = [
        @a.usda@,
        @b.usda@ (offset = 2)
    ]
    upAxis = "Y"
)

def "Root" (
    prepend variantSets = "look"
)
{
    reorder properties = ["b", "a"]
    int a = 1
    int b = 2
    string lines = """one
two"""
    string quoted = 'say "hi"'
    string tab = "a\tb\x01"

    def "First"
    {
    }

    def "Second"
    {
        int x = 1

        def "Only"
        {
        }
    }
    variantSet "look" = {
        "red" {
            int c = 3

        }
    }
}

"#;
        let parsed = Parser::new(source).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, written);
    }

    /// A hand-written layer is written as OpenUSD 26.11 writes it
    /// (`Sdf.Layer.OpenAsAnonymous(source).ExportToString()`), byte for byte:
    /// a list of more than one path or reference one item per line, and
    /// properties in `TfDictionaryLessThan` order (`abc2` before `abc10`,
    /// `xformOp:transform` before `xformOpOrder`).
    #[test]
    fn lists_as_cpp() {
        use crate::usda::parser::Parser;

        let source = r#"#usda 1.0

def Xform "P" (
    prepend references = [@a.usda@</A>, </B>]
)
{
    uniform token[] xformOpOrder = ["xformOp:transform"]
    matrix4d xformOp:transform = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
    rel many = [</A>, </B>]
    rel one = </A>
    float in.connect = [</A.x>, </B.y>]
    int abc10 = 1
    int abc2 = 2
}
"#;
        let written = r#"#usda 1.0

def Xform "P" (
    prepend references = [
        @a.usda@</A>,
        </B>
    ]
)
{
    int abc2 = 2
    int abc10 = 1
    float in.connect = [
        </A.x>,
        </B.y>,
    ]
    rel many = [
        </A>,
        </B>,
    ]
    rel one = </A>
    matrix4d xformOp:transform = ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) )
    uniform token[] xformOpOrder = ["xformOp:transform"]
}

"#;
        let parsed = Parser::new(source).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, written);
    }

    /// A hand-written layer is written as OpenUSD 26.11 writes it
    /// (`Sdf.Layer.OpenAsAnonymous(source).ExportToString()`), byte for byte:
    /// metadata comment first and then sorted, nested dictionaries indented, a
    /// reference's custom data on lines of its own, `<>` for an internal arc to
    /// the default prim, variants sorted and selections as a dictionary, a
    /// relationship's bare declaration left out unless it is custom, and the
    /// layer header with its relocates last and no empty `doc` or false
    /// `hasOwnedSubLayers`.
    #[test]
    fn metadata_as_cpp() {
        use crate::usda::parser::Parser;

        let source = r#"#usda 1.0
(
    relocates = {
        </A/B>: </A/C>,
        </A/D>: </A/E>
    }
    "layer comment"
    doc = ""
    upAxis = "Z"
    hasOwnedSubLayers = false
)

def "P" (
    kind = "component"
    customData = {
        int b = 1
        dictionary nested = {
            string s = "x"
        }
    }
    "prim comment"
    variants = {
        string look = "red"
        string size = "big"
    }
    prepend variantSets = ["size", "look"]
    references = @r.usda@</R> (offset = 2; customData = {int n = 1})
    hidden = true
)
{
    custom rel r (doc = "d")
    rel q
    prepend rel q = </X>
    custom rel c
    add rel c = </Y>

    variantSet "size" = {
        "small" {
        }
        "big" {
        }
    }
    variantSet "look" = {
        "red" {
        }
    }
}

def "Q" (
    references = <>
    payload = <>
)
{
}
"#;
        let written = r#"#usda 1.0
(
    "layer comment"
    upAxis = "Z"
    relocates = {
        </A/B>: </A/C>, 
        </A/D>: </A/E>
    }
)

def "P" (
    "prim comment"
    customData = {
        int b = 1
        dictionary nested = {
            string s = "x"
        }
    }
    hidden = true
    kind = "component"
    references = [
        @r.usda@</R> (
            offset = 2
            customData = {
                int n = 1
            }
        )
    ]
    variants = {
        string look = "red"
        string size = "big"
    }
    prepend variantSets = ["size", "look"]
)
{
    custom rel c
    add rel c = </Y>
    prepend rel q = </X>
    custom rel r (
        doc = "d"
    )
    variantSet "size" = {
        "big" {

        }
        "small" {

        }
    }
    variantSet "look" = {
        "red" {

        }
    }
}

def "Q" (
    payload = <>
    references = <>
)
{
}

"#;
        let parsed = Parser::new(source).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, written);
    }

    /// A true `hasOwnedSubLayers` and a `doc` with text are written, as
    /// OpenUSD 26.11 writes this header back.
    #[test]
    fn header_kept() {
        let text = "#usda 1.0\n(\n    doc = \"kept\"\n    hasOwnedSubLayers = true\n)\n\n";
        let parsed = usda::parser::Parser::new(text).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, text);
    }

    /// A variant set with no variants is not written, though the prim still
    /// names it, as OpenUSD 26.11 writes a layer built with
    /// `Sdf.VariantSetSpec(prim, "empty")` and a set `v` with the variants `b`
    /// and `a`. The text grammar has no empty variant set, so the layer is
    /// built in memory.
    #[test]
    fn empty_variant_set() {
        use crate::usda::parser::Parser;

        let source = r#"#usda 1.0
def "Q" (
    prepend variantSets = ["empty", "v"]
)
{
    variantSet "v" = {
        "b" {
        }
        "a" {
        }
    }
}
"#;
        let written = r#"#usda 1.0

def "Q" (
    prepend variantSets = ["empty", "v"]
)
{
    variantSet "v" = {
        "a" {

        }
        "b" {

        }
    }
}

"#;
        let mut parsed = Parser::new(source).parse().expect("parse");
        let prim = path("/Q").unwrap();
        parsed.insert(
            prim.append_variant_selection("empty", "").unwrap(),
            sdf::SpecData::new(SpecType::VariantSet),
        );
        parsed
            .get_mut(&prim)
            .unwrap()
            .add(ChildrenKey::VariantSetChildren, Value::token_vec(["empty", "v"]));
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, written);
    }

    /// `permission` and `symmetryFunction` are bare identifiers on prims and
    /// properties alike, and a symmetry function may be namespaced or left
    /// out, ending at the line, as OpenUSD 26.11 writes this layer back
    /// (`Sdf.Layer.OpenAsAnonymous(source).ExportToString()`).
    #[test]
    fn identifier_metadata() {
        use crate::usda::parser::Parser;

        let source = r#"#usda 1.0
def "P" (
    permission = private
    symmetryFunction = mirror
)
{
    int a = 1 (
        permission = public
        symmetryFunction = flip
    )
    int b = 2 (
        symmetryFunction =
        doc = "next"
    )
    int c = 3 (
        symmetryFunction = Foo::bar
    )
    rel r (
        permission = private
        symmetryFunction = s
    )
}
"#;
        let written = r#"#usda 1.0

def "P" (
    permission = private
    symmetryFunction = mirror
)
{
    int a = 1 (
        permission = public
        symmetryFunction = flip
    )
    int b = 2 (
        doc = "next"
        symmetryFunction = 
    )
    int c = 3 (
        symmetryFunction = Foo::bar
    )
    rel r (
        permission = private
        symmetryFunction = s
    )
}

"#;
        let parsed = Parser::new(source).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, written);
    }

    /// Numbers, bools and matrices as OpenUSD 26.11 writes them: the layer
    /// below is its output for these values, made with `Sdf.AttributeSpec`
    /// and `Layer.ExportToString`.
    #[test]
    fn numbers_as_cpp() {
        use crate::usda::parser::Parser;

        let written = r#"#usda 1.0

def "P" (
    active = false
)
{
    bool b = 1
    double big = 1e15
    bool[] bs = [1, 0]
    double d = 24
    float f = 0.65
    half h = 0.0999756
    half3 h3 = (0.0999756, 1000.5, 3)
    matrix2d m = ( (1, 0.5), (0, 1) )
    double s.timeSamples = {
        1: 2.5,
        2.5: 3,
    }
    double tiny = 2.220446049250313e-16
}
"#;
        let parsed = Parser::new(written).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        for line in written.lines().skip(3) {
            assert!(emitted.contains(line), "{line:?} missing from:\n{emitted}");
        }
    }

    /// A whole-number frame reads back as the double C++ registers the field
    /// as, though it is written without a fraction.
    #[test]
    fn whole_frame_stays_double() {
        use crate::usda::parser::Parser;

        let src = "#usda 1.0
(
    startFrame = 1.0
    endFrame = 24.0
)
";
        let parsed = Parser::new(src).parse().unwrap();
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert!(
            emitted.contains(
                "startFrame = 1
"
            ),
            "{emitted}"
        );
        let reparsed = Parser::new(&emitted).parse().unwrap();
        let root = reparsed.get(&Path::abs_root()).unwrap();
        assert_eq!(root.get("startFrame"), Some(&Value::Double(1.0)));
        assert_eq!(root.get("endFrame"), Some(&Value::Double(24.0)));
    }

    /// Layer offsets, relocates, comments, relationship list ops and strings
    /// as OpenUSD 26.8 writes them, byte for byte: an offset within 1e-6 of
    /// the identity left out, a prim's relocates relative and sorted, an empty
    /// comment left out, `varying` on a list-op statement, and a triple-quoted
    /// string that ends in an escaped quote.
    #[test]
    fn edge_cases_as_cpp() {
        use crate::usda::parser::Parser;

        let source = r#"#usda 1.0
(
    ""
    subLayers = [
        @./s.usda@ (offset = 0.0000001),
        @./t.usda@ (offset = 2; scale = 1.0000001)
    ]
)

def "A" (
    ""
    relocates = {
        <Z>: <Y>,
        </A/B>: </A/C>
    }
    prepend references = @./r.usda@ (offset = 0.0000001)
    prepend payload = @./y.usda@ (scale = 1.0000001)
)
{
    prepend varying rel r = </A/B>
    string s = """it's
end\""""
    float f (
        ""
        doc = "d"
    )
}
"#;
        // C++ ends every relocates pair but the last with `, `, a space
        // included, which is added here so no line of the literal ends in
        // whitespace.
        let written = r#"#usda 1.0
(
    subLayers = [
        @./s.usda@,
        @./t.usda@ (offset = 2; scale = 1.0000001)
    ]
)

def "A" (
    prepend payload = @./y.usda@
    prepend references = @./r.usda@
    relocates = {
        <B>: <C>,
        <Z>: <Y>
    }
)
{
    float f (
        doc = "d"
    )
    prepend varying rel r = </A/B>
    string s = """it's
end\""""
}

"#
        .replace("<B>: <C>,\n", "<B>: <C>, \n");
        let parsed = Parser::new(source).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, written);
        let reparsed = Parser::new(&emitted).parse().expect("the written layer reads back");
        let s = reparsed
            .get(&path("/A.s").unwrap())
            .unwrap()
            .get(FieldKey::Default.as_str())
            .unwrap();
        assert_eq!(s, &Value::String("it's\nend\"".to_owned()));
    }

    /// An attribute whose connection list edits nothing keeps its
    /// declaration, since no connection statement declares it.
    #[test]
    fn empty_connection_declared() {
        use crate::usda::parser::Parser;

        let mut parsed = Parser::new("#usda 1.0\ndef \"P\" {\n    float c\n}\n")
            .parse()
            .expect("parse");
        let spec = parsed.get_mut(&path("/P.c").unwrap()).unwrap();
        spec.add(FieldKey::ConnectionPaths, Value::PathListOp(ListOp::default()));
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert!(emitted.contains("    float c\n"), "{emitted}");
        let reparsed = Parser::new(&emitted).parse().expect("the written layer reads back");
        let attr = reparsed.get(&path("/P.c").unwrap()).expect("the attribute survives");
        assert_eq!(attr.get(FieldKey::TypeName.as_str()), Some(&Value::token("float")));
    }

    /// Every mix of both quote characters, LF and CRLF line breaks, and a
    /// trailing quote or backslash comes back as it was written, through the
    /// string delimiters alone and through a whole layer.
    #[test]
    fn string_delimiters_roundtrip() {
        use crate::usda::parser::Parser;

        let mut texts = Vec::new();
        for quotes in ["", "'", "\"", "'\"", "\"\"\"", "'''"] {
            for line_break in ["", "\n", "\r\n"] {
                for end in ["", "\"", "'", "\\", "\\\"", "\\\n", "\n\""] {
                    texts.push(format!("a{quotes}b{line_break}c{end}"));
                    texts.push(format!("{end}{quotes}{line_break}"));
                }
            }
        }
        for text in &texts {
            assert_eq!(&write_quoted_and_reparse(text), text, "{text:?}");
        }

        let mut parsed = Parser::new("#usda 1.0\ndef \"P\" {\n}\n").parse().expect("parse");
        let mut names = Vec::new();
        for (i, text) in texts.iter().enumerate() {
            let name = format!("s{i}");
            let mut spec = sdf::SpecData::new(SpecType::Attribute);
            spec.add(FieldKey::TypeName, Value::token("string"));
            spec.add(FieldKey::Default, Value::String(text.clone()));
            parsed.insert(path(format!("/P.{name}")).unwrap(), spec);
            names.push(name);
        }
        let prim = parsed.get_mut(&path("/P").unwrap()).unwrap();
        prim.add(ChildrenKey::PropertyChildren, Value::token_vec(names));
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        let reparsed = Parser::new(&emitted).parse().expect("the written layer reads back");
        for (i, text) in texts.iter().enumerate() {
            let attr = reparsed.get(&path(format!("/P.s{i}")).unwrap()).unwrap();
            assert_eq!(
                attr.get(FieldKey::Default.as_str()),
                Some(&Value::String(text.clone())),
                "{text:?}"
            );
        }
    }

    /// A relocated source is written once, with the first target authored
    /// for it, as OpenUSD 26.8 writes a prim's relocates; a `varying`
    /// statement after a plain one leaves the relationship varying.
    #[test]
    fn relocates_and_variability_as_cpp() {
        use crate::usda::parser::Parser;

        let source = r#"#usda 1.0

def "A" (
    relocates = {
        </A/B>: </A/C>,
        </A/B>: </A/D>
    }
)
{
    rel r (
        doc = "x"
    )
    prepend varying rel r = </A>
}
"#;
        let written = r#"#usda 1.0

def "A" (
    relocates = {
        <B>: <C>
    }
)
{
    varying rel r (
        doc = "x"
    )
    prepend varying rel r = </A>
}

"#;
        let parsed = Parser::new(source).parse().expect("parse");
        let emitted = TextWriter::write_to_string(&Data::from_specs(parsed) as &dyn AbstractData).unwrap();
        assert_eq!(emitted, written);
    }

    /// A layer with CRLF line endings reads as one with LF, but for a CRLF
    /// inside a triple-quoted string, which stays in the string as OpenUSD
    /// 26.8 reads it.
    #[test]
    fn crlf_layer_reads() {
        use crate::usda::parser::Parser;

        let source =
            "#usda 1.0\r\ndef \"P\"\r\n{\r\n    string s = \"\"\"a\r\nb\"\"\"\r\n    string t = \"c\"\r\n}\r\n";
        let parsed = Parser::new(source).parse().expect("parse");
        let default = |name: &str| {
            let spec = parsed.get(&path(name).unwrap()).unwrap();
            spec.get(FieldKey::Default.as_str()).cloned()
        };
        assert_eq!(default("/P.s"), Some(Value::String("a\r\nb".to_owned())));
        assert_eq!(default("/P.t"), Some(Value::String("c".to_owned())));
    }
}
