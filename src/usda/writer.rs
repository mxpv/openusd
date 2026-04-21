//! Text format (`usda`) writer.
//!
//! Walks an [`AbstractData`] layer and emits a `usda` representation. The
//! output aims for semantic round-trip: parsing the emitted text with
//! [`TextReader`](super::TextReader) must reproduce the original specs
//! opinion-for-opinion.

use std::{
    collections::HashMap,
    fmt::Write as FmtWrite,
    io::{self, Write},
};

use anyhow::{bail, Context, Result};

use crate::sdf::{
    self, AbstractData, ChildrenKey, FieldKey, LayerOffset, ListOp, Path, Payload, Reference, SpecType, Specifier,
    Value, Variability,
};

/// Emits `usda` text from an [`AbstractData`].
pub struct TextWriter;

impl TextWriter {
    /// Write the layer to a newly allocated `String`.
    pub fn write_to_string(data: &dyn AbstractData) -> Result<String> {
        let mut buf = Vec::new();
        Self::write(data, &mut buf)?;
        String::from_utf8(buf).context("writer produced non-UTF-8 output")
    }

    /// Write the layer to a file on disk.
    pub fn write_to_file(data: &dyn AbstractData, path: impl AsRef<std::path::Path>) -> Result<()> {
        let text = Self::write_to_string(data)?;
        std::fs::write(path, text).context("failed to write usda file")?;
        Ok(())
    }

    /// Write the layer to any `io::Write` sink.
    pub fn write<W: Write>(data: &dyn AbstractData, out: &mut W) -> Result<()> {
        let mut emitter = Emitter { out, indent: 0 };
        emitter.emit_layer(data)
    }
}

struct Emitter<'w, W: Write> {
    out: &'w mut W,
    indent: usize,
}

impl<W: Write> Emitter<'_, W> {
    // ---------- layout helpers ----------

    fn write_indent(&mut self) -> io::Result<()> {
        for _ in 0..self.indent {
            self.out.write_all(b"    ")?;
        }
        Ok(())
    }

    // ---------- top-level walk ----------

    fn emit_layer(&mut self, data: &dyn AbstractData) -> Result<()> {
        writeln!(self.out, "#usda 1.0")?;

        let root = Path::abs_root();
        let has_root = data.has_spec(&root);

        // Layer metadata: every field except primChildren is metadata.
        // subLayerOffsets is merged into subLayers at emit time.
        let meta_fields: Vec<String> = if has_root {
            data.list(&root)
                .unwrap_or_default()
                .into_iter()
                .filter(|n| !is_prim_structural_field(n) && n != FieldKey::SubLayerOffsets.as_str())
                .collect()
        } else {
            Vec::new()
        };

        if !meta_fields.is_empty() {
            writeln!(self.out, "(")?;
            self.indent += 1;
            for name in &meta_fields {
                if name == FieldKey::SubLayers.as_str() {
                    self.emit_sub_layers(data, &root)?;
                    continue;
                }
                let value = data.get(&root, name)?;
                self.emit_metadata_entry(name, &value)?;
            }
            self.indent -= 1;
            writeln!(self.out, ")")?;
        }

        // Root prims
        let children = if has_root {
            prim_children(data, &root)
        } else {
            Vec::new()
        };
        for name in &children {
            writeln!(self.out)?;
            let child_path = root.append_path(name.as_str())?;
            self.emit_prim(data, &child_path, name)?;
        }

        Ok(())
    }

    // ---------- prim ----------

    fn emit_prim(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<()> {
        // Header: [specifier] [typeName] "name"
        self.write_indent()?;
        let specifier = get_value(data, path, FieldKey::Specifier.as_str())
            .and_then(|v| match v {
                Value::Specifier(s) => Some(s),
                _ => None,
            })
            .unwrap_or(Specifier::Def);
        self.out.write_all(specifier_keyword(specifier).as_bytes())?;

        if let Some(Value::Token(type_name)) = get_value(data, path, FieldKey::TypeName.as_str()) {
            if !type_name.is_empty() {
                write!(self.out, " {type_name}")?;
            }
        }

        let mut quoted = String::new();
        write_quoted(&mut quoted, name)?;
        write!(self.out, " {quoted}")?;

        let meta_fields: Vec<String> = data
            .list(path)
            .unwrap_or_default()
            .into_iter()
            .filter(|n| !is_prim_structural_field(n))
            .collect();

        if !meta_fields.is_empty() {
            writeln!(self.out, " (")?;
            self.indent += 1;
            for name in &meta_fields {
                let value = data.get(path, name)?;
                self.emit_metadata_entry(name, &value)?;
            }
            self.indent -= 1;
            self.write_indent()?;
            self.out.write_all(b")")?;
        }

        writeln!(self.out)?;
        self.write_indent()?;
        writeln!(self.out, "{{")?;
        self.indent += 1;

        // Properties
        let props = property_children(data, path);
        for name in &props {
            let prop_path = path.append_property(name)?;
            self.emit_property(data, &prop_path, name)?;
        }

        // Variant sets
        if let Some(Value::TokenVec(vset_names)) = get_value(data, path, ChildrenKey::VariantSetChildren.as_str()) {
            for vset in &vset_names {
                let vset_path = path.append_variant_selection(vset, "");
                self.emit_variant_set(data, &vset_path, vset)?;
            }
        }

        // Child prims
        let children = prim_children(data, path);
        for name in &children {
            let child_path = path.append_path(name.as_str())?;
            self.emit_prim(data, &child_path, name)?;
        }

        self.indent -= 1;
        self.write_indent()?;
        writeln!(self.out, "}}")?;

        Ok(())
    }

    // ---------- property (attribute or relationship) ----------

    fn emit_property(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<()> {
        match data.spec_type(path) {
            Some(SpecType::Attribute) => self.emit_attribute(data, path, name),
            Some(SpecType::Relationship) => self.emit_relationship(data, path, name),
            Some(other) => anyhow::bail!("unsupported property spec type {other:?} at {path}"),
            None => anyhow::bail!("property path {path} has no spec"),
        }
    }

    fn emit_attribute(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<()> {
        self.write_indent()?;

        if matches!(
            get_value(data, path, FieldKey::Custom.as_str()),
            Some(Value::Bool(true))
        ) {
            self.out.write_all(b"custom ")?;
        }
        if matches!(
            get_value(data, path, FieldKey::Variability.as_str()),
            Some(Value::Variability(Variability::Uniform))
        ) {
            self.out.write_all(b"uniform ")?;
        }

        let type_name = match get_value(data, path, FieldKey::TypeName.as_str()) {
            Some(Value::Token(t)) => t,
            _ => anyhow::bail!("attribute {path} missing typeName"),
        };
        write!(self.out, "{type_name} {name}")?;

        let default = get_value(data, path, FieldKey::Default.as_str());
        let time_samples = get_value(data, path, FieldKey::TimeSamples.as_str());
        let spline = get_value(data, path, SPLINE_FIELD);

        if let Some(v) = default {
            self.out.write_all(b" = ")?;
            self.write_value(&v)?;
        }

        let meta_fields: Vec<String> = data
            .list(path)
            .unwrap_or_default()
            .into_iter()
            .filter(|n| !is_attribute_structural_field(n))
            .collect();

        if !meta_fields.is_empty() {
            self.out.write_all(b" (")?;
            writeln!(self.out)?;
            self.indent += 1;
            for name in &meta_fields {
                let value = data.get(path, name)?;
                self.emit_metadata_entry(name, &value)?;
            }
            self.indent -= 1;
            self.write_indent()?;
            self.out.write_all(b")")?;
        }

        writeln!(self.out)?;

        // Time samples (separate statement if present)
        if let Some(Value::TimeSamples(samples)) = time_samples {
            self.write_indent()?;
            write!(self.out, "{type_name} {name}.timeSamples = ")?;
            self.write_time_samples(&samples)?;
            writeln!(self.out)?;
        }

        // Connections (separate statement if present)
        if let Some(Value::PathListOp(op)) = get_value(data, path, FieldKey::ConnectionPaths.as_str()) {
            self.emit_connection(name, &op, &type_name)?;
        }

        // Splines (separate statement if present)
        if let Some(Value::Dictionary(dict)) = spline {
            self.write_indent()?;
            write!(self.out, "{type_name} {name}.spline = ")?;
            self.write_spline(&dict)?;
            writeln!(self.out)?;
        }

        Ok(())
    }

    /// Emit a spline dictionary in the native spline grammar. Inverse of
    /// `parser::parse_spline`. The input `dict` has the keys produced there:
    /// `curveType`, `pre/postExtrapolation`, `loopParameters`, `knots`,
    /// `knotCustomData`.
    fn write_spline(&mut self, dict: &HashMap<String, Value>) -> Result<()> {
        self.out.write_all(b"{")?;
        writeln!(self.out)?;
        self.indent += 1;

        let curve_type = match dict.get("curveType") {
            Some(Value::Token(t)) => t.as_str(),
            _ => "bezier",
        };
        self.write_indent()?;
        writeln!(self.out, "{curve_type},")?;

        // Extrapolation
        if let Some(value) = dict.get("preExtrapolation") {
            self.write_extrapolation("pre", value)?;
        }
        if let Some(value) = dict.get("postExtrapolation") {
            self.write_extrapolation("post", value)?;
        }

        // Loop parameters
        if let Some(Value::Dictionary(loop_dict)) = dict.get("loopParameters") {
            self.write_loop(loop_dict)?;
        }

        // Knots
        let knot_custom = match dict.get("knotCustomData") {
            Some(Value::Dictionary(m)) => Some(m),
            _ => None,
        };
        if let Some(Value::ValueVec(knots)) = dict.get("knots") {
            for knot in knots {
                if let Value::Dictionary(knot) = knot {
                    self.write_knot(knot, knot_custom)?;
                }
            }
        }

        self.indent -= 1;
        self.write_indent()?;
        self.out.write_all(b"}")?;
        Ok(())
    }

    fn write_extrapolation(&mut self, dir: &str, value: &Value) -> Result<()> {
        self.write_indent()?;
        match value {
            Value::ValueBlock | Value::None => {
                writeln!(self.out, "{dir}: none,")?;
            }
            Value::Dictionary(d) => {
                let mode = match d.get("mode") {
                    Some(Value::Token(t)) => t.as_str(),
                    _ => "none",
                };
                let slope = match d.get("slope") {
                    Some(Value::Double(s)) => *s,
                    _ => 0.0,
                };
                if slope != 0.0 {
                    let mut buf = String::new();
                    format_double(&mut buf, slope);
                    writeln!(self.out, "{dir}: {mode} ({buf}),")?;
                } else {
                    writeln!(self.out, "{dir}: {mode},")?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn write_loop(&mut self, d: &HashMap<String, Value>) -> Result<()> {
        let f = |k: &str| -> f64 {
            match d.get(k) {
                Some(Value::Double(v)) => *v,
                _ => 0.0,
            }
        };
        let a = f("protoStart");
        let b = f("protoEnd");
        let c = f("numPreLoops");
        let e = f("numPostLoops");
        let g = f("valueOffset");
        self.write_indent()?;
        let mut buf = String::new();
        buf.push_str("loop: (");
        format_double(&mut buf, a);
        buf.push_str(", ");
        format_double(&mut buf, b);
        buf.push_str(", ");
        format_double(&mut buf, c);
        buf.push_str(", ");
        format_double(&mut buf, e);
        buf.push_str(", ");
        format_double(&mut buf, g);
        buf.push(')');
        writeln!(self.out, "{buf},")?;
        Ok(())
    }

    fn write_knot(
        &mut self,
        knot: &HashMap<String, Value>,
        knot_custom: Option<&HashMap<String, Value>>,
    ) -> Result<()> {
        let d = |k: &str| -> f64 {
            match knot.get(k) {
                Some(Value::Double(v)) => *v,
                _ => 0.0,
            }
        };
        let time = d("time");
        let value = d("value");
        let pre_value = d("preValue");
        let pre_slope = d("preTangentSlope");
        let pre_width = d("preTangentWidth");
        let post_slope = d("postTangentSlope");
        let post_width = d("postTangentWidth");
        let interp = match knot.get("nextInterpolationMode") {
            Some(Value::Token(t)) => t.as_str(),
            _ => "held",
        };

        self.write_indent()?;
        let mut buf = String::new();
        format_double(&mut buf, time);
        buf.push_str(": ");
        if pre_value != 0.0 {
            let mut pv = String::new();
            format_double(&mut pv, pre_value);
            buf.push_str(&pv);
            buf.push_str(" & ");
        }
        format_double(&mut buf, value);

        if pre_slope != 0.0 || pre_width != 0.0 {
            buf.push_str("; pre (");
            format_double(&mut buf, pre_slope);
            buf.push_str(", ");
            format_double(&mut buf, pre_width);
            buf.push(')');
        }

        if interp != "held" || post_slope != 0.0 || post_width != 0.0 {
            buf.push_str("; post ");
            buf.push_str(interp);
            if post_slope != 0.0 || post_width != 0.0 {
                buf.push_str(" (");
                format_double(&mut buf, post_slope);
                buf.push_str(", ");
                format_double(&mut buf, post_width);
                buf.push(')');
            }
        }

        let time_key = if time.fract() == 0.0 && time.is_finite() {
            format!("{}", time as i64)
        } else {
            format!("{time}")
        };
        if let Some(Value::Dictionary(custom)) = knot_custom.and_then(|m| m.get(&time_key)) {
            buf.push_str("; ");
            let mut dict_str = String::new();
            format_dictionary(&mut dict_str, custom)?;
            buf.push_str(&dict_str);
        }

        buf.push(',');
        writeln!(self.out, "{buf}")?;
        Ok(())
    }

    fn emit_connection(&mut self, attr_name: &str, op: &ListOp<Path>, type_name: &str) -> Result<()> {
        // Emit as `typeName attr.connect = paths` or list-op form.
        self.emit_listop_statement(&format!("{type_name} {attr_name}.connect"), op, |s, p| {
            write!(s, "<{}>", p.as_str())?;
            Ok(())
        })
    }

    fn emit_relationship(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<()> {
        self.write_indent()?;

        if matches!(
            get_value(data, path, FieldKey::Custom.as_str()),
            Some(Value::Bool(true))
        ) {
            self.out.write_all(b"custom ")?;
        }
        if matches!(
            get_value(data, path, FieldKey::Variability.as_str()),
            Some(Value::Variability(Variability::Uniform))
        ) {
            self.out.write_all(b"uniform ")?;
        }

        write!(self.out, "rel {name}")?;

        let targets = get_value(data, path, FieldKey::TargetPaths.as_str());
        let meta_fields: Vec<String> = data
            .list(path)
            .unwrap_or_default()
            .into_iter()
            .filter(|n| !is_relationship_structural_field(n))
            .collect();

        if let Some(Value::PathListOp(op)) = &targets {
            if op.explicit {
                match op.explicit_items.len() {
                    0 => {
                        self.out.write_all(b" = None")?;
                    }
                    1 => {
                        write!(self.out, " = <{}>", op.explicit_items[0].as_str())?;
                    }
                    _ => {
                        self.out.write_all(b" = [")?;
                        for (i, p) in op.explicit_items.iter().enumerate() {
                            if i > 0 {
                                self.out.write_all(b", ")?;
                            }
                            write!(self.out, "<{}>", p.as_str())?;
                        }
                        self.out.write_all(b"]")?;
                    }
                }
            }
            // Non-explicit list ops for rel targets: emit on a separate line below.
        }

        if !meta_fields.is_empty() {
            writeln!(self.out, " (")?;
            self.indent += 1;
            for name in &meta_fields {
                let value = data.get(path, name)?;
                self.emit_metadata_entry(name, &value)?;
            }
            self.indent -= 1;
            self.write_indent()?;
            self.out.write_all(b")")?;
        }

        writeln!(self.out)?;

        // Non-explicit list op target paths
        if let Some(Value::PathListOp(op)) = &targets {
            if !op.explicit {
                self.emit_listop_statement(&format!("rel {name}"), op, |s, p| {
                    write!(s, "<{}>", p.as_str())?;
                    Ok(())
                })?;
            }
        }

        Ok(())
    }

    // ---------- variant set / variant ----------

    fn emit_variant_set(&mut self, data: &dyn AbstractData, vset_path: &Path, name: &str) -> Result<()> {
        self.write_indent()?;
        let mut quoted = String::new();
        write_quoted(&mut quoted, name)?;
        writeln!(self.out, "variantSet {quoted} = {{")?;
        self.indent += 1;

        if let Some(Value::TokenVec(variant_names)) = get_value(data, vset_path, ChildrenKey::VariantChildren.as_str())
        {
            let prim = vset_path.prim_path();
            for v_name in &variant_names {
                let v_path = prim.append_variant_selection(name, v_name);
                self.emit_variant(data, &v_path, v_name)?;
            }
        }

        self.indent -= 1;
        self.write_indent()?;
        writeln!(self.out, "}}")?;
        Ok(())
    }

    fn emit_variant(&mut self, data: &dyn AbstractData, path: &Path, name: &str) -> Result<()> {
        self.write_indent()?;
        let mut quoted = String::new();
        write_quoted(&mut quoted, name)?;
        self.out.write_all(quoted.as_bytes())?;

        let meta_fields: Vec<String> = data
            .list(path)
            .unwrap_or_default()
            .into_iter()
            .filter(|n| !is_prim_structural_field(n))
            .collect();

        if !meta_fields.is_empty() {
            writeln!(self.out, " (")?;
            self.indent += 1;
            for name in &meta_fields {
                let value = data.get(path, name)?;
                self.emit_metadata_entry(name, &value)?;
            }
            self.indent -= 1;
            self.write_indent()?;
            self.out.write_all(b")")?;
        }

        writeln!(self.out, " {{")?;
        self.indent += 1;

        let props = property_children(data, path);
        for prop in &props {
            let prop_path = path.append_property(prop)?;
            self.emit_property(data, &prop_path, prop)?;
        }

        let children = prim_children(data, path);
        for child in &children {
            let child_path = path.append_path(child.as_str())?;
            self.emit_prim(data, &child_path, child)?;
        }

        self.indent -= 1;
        self.write_indent()?;
        writeln!(self.out, "}}")?;
        Ok(())
    }

    /// Combine `subLayers` (asset paths) with `subLayerOffsets` at emit time —
    /// the text grammar wants them fused into `subLayers = [@path@ (offset=X; scale=Y), ...]`.
    fn emit_sub_layers(&mut self, data: &dyn AbstractData, root: &Path) -> Result<()> {
        let sublayers = match get_value(data, root, FieldKey::SubLayers.as_str()) {
            Some(Value::StringVec(v)) => v,
            _ => return Ok(()),
        };
        let offsets = match get_value(data, root, FieldKey::SubLayerOffsets.as_str()) {
            Some(Value::LayerOffsetVec(v)) => v,
            _ => Vec::new(),
        };

        self.write_indent()?;
        self.out.write_all(b"subLayers = [")?;
        for (i, path) in sublayers.iter().enumerate() {
            if i > 0 {
                self.out.write_all(b", ")?;
            }
            let mut buf = String::new();
            write_asset_path(&mut buf, path)?;
            self.out.write_all(buf.as_bytes())?;

            if let Some(offset) = offsets.get(i) {
                if *offset != LayerOffset::default() {
                    let mut buf = String::new();
                    buf.push_str(" (offset = ");
                    format_double(&mut buf, offset.offset);
                    buf.push_str("; scale = ");
                    format_double(&mut buf, offset.scale);
                    buf.push(')');
                    self.out.write_all(buf.as_bytes())?;
                }
            }
        }
        self.out.write_all(b"]")?;
        writeln!(self.out)?;
        Ok(())
    }

    // ---------- metadata entry ----------

    fn emit_metadata_entry(&mut self, name: &str, value: &Value) -> Result<()> {
        // "comment" is authored as a bare string in the metadata block, with
        // no keyword. Parser recognises a lone string as the Sdf comment field.
        if name == FieldKey::Comment.as_str() {
            if let Value::String(text) = value {
                self.write_indent()?;
                let mut buf = String::new();
                write_quoted(&mut buf, text)?;
                self.out.write_all(buf.as_bytes())?;
                writeln!(self.out)?;
                return Ok(());
            }
        }

        // `primOrder` / `propertyOrder` are stored under those field names but
        // the text grammar expresses them as `reorder nameChildren/properties`.
        if name == FieldKey::PrimOrder.as_str() {
            if let Value::TokenVec(v) = value {
                return self.emit_reorder("nameChildren", v);
            }
        }
        if name == FieldKey::PropertyOrder.as_str() {
            if let Value::TokenVec(v) = value {
                return self.emit_reorder("properties", v);
            }
        }

        // `layerRelocates` is stored with that name but the text keyword is
        // plain `relocates` at layer scope.
        let keyword = if name == FieldKey::LayerRelocates.as_str() {
            "relocates"
        } else {
            name
        };

        // ListOps in metadata blocks render as multi-line prepend/append/... entries.
        if let Some(emitted) = self.try_emit_listop_metadata(keyword, value)? {
            if emitted {
                return Ok(());
            }
        }

        self.write_indent()?;
        write!(self.out, "{keyword} = ")?;
        self.write_value(value)?;
        writeln!(self.out)?;
        Ok(())
    }

    fn emit_reorder(&mut self, target: &str, names: &[String]) -> Result<()> {
        self.write_indent()?;
        write!(self.out, "reorder {target} = [")?;
        for (i, n) in names.iter().enumerate() {
            if i > 0 {
                self.out.write_all(b", ")?;
            }
            let mut buf = String::new();
            write_quoted(&mut buf, n)?;
            self.out.write_all(buf.as_bytes())?;
        }
        writeln!(self.out, "]")?;
        Ok(())
    }

    /// Returns `Ok(Some(true))` if this value was a ListOp and was fully emitted;
    /// `Ok(Some(false))` / `Ok(None)` if caller should emit as a normal field.
    fn try_emit_listop_metadata(&mut self, name: &str, value: &Value) -> Result<Option<bool>> {
        match value {
            Value::TokenListOp(op) | Value::StringListOp(op) => {
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
                self.emit_listop_statement(name, op, write_reference)?;
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
            _ => Ok(None),
        }
    }

    fn emit_listop_statement<T, F>(&mut self, prefix: &str, op: &ListOp<T>, mut fmt_item: F) -> Result<()>
    where
        T: Default + Clone + PartialEq,
        F: FnMut(&mut String, &T) -> Result<()>,
    {
        if op.explicit {
            self.write_indent()?;
            write!(self.out, "{prefix} = ")?;
            self.write_listop_items(&op.explicit_items, &mut fmt_item)?;
            writeln!(self.out)?;
            return Ok(());
        }

        for (kw, items) in [
            ("delete", &op.deleted_items),
            ("add", &op.added_items),
            ("prepend", &op.prepended_items),
            ("append", &op.appended_items),
            ("reorder", &op.ordered_items),
        ] {
            if !items.is_empty() {
                self.write_indent()?;
                write!(self.out, "{kw} {prefix} = ")?;
                self.write_listop_items(items, &mut fmt_item)?;
                writeln!(self.out)?;
            }
        }
        Ok(())
    }

    fn write_listop_items<T, F>(&mut self, items: &[T], fmt_item: &mut F) -> Result<()>
    where
        F: FnMut(&mut String, &T) -> Result<()>,
    {
        if items.len() == 1 {
            let mut buf = String::new();
            fmt_item(&mut buf, &items[0])?;
            self.out.write_all(buf.as_bytes())?;
        } else {
            self.out.write_all(b"[")?;
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    self.out.write_all(b", ")?;
                }
                let mut buf = String::new();
                fmt_item(&mut buf, item)?;
                self.out.write_all(buf.as_bytes())?;
            }
            self.out.write_all(b"]")?;
        }
        Ok(())
    }

    // ---------- value formatting ----------

    fn write_value(&mut self, value: &Value) -> Result<()> {
        let mut buf = String::new();
        format_value(&mut buf, value)?;
        self.out.write_all(buf.as_bytes())?;
        Ok(())
    }

    fn write_time_samples(&mut self, samples: &[(f64, Value)]) -> Result<()> {
        self.out.write_all(b"{")?;
        writeln!(self.out)?;
        self.indent += 1;
        for (time, value) in samples {
            self.write_indent()?;
            let mut t = String::new();
            format_double(&mut t, *time);
            write!(self.out, "{t}: ")?;
            self.write_value(value)?;
            writeln!(self.out, ",")?;
        }
        self.indent -= 1;
        self.write_indent()?;
        self.out.write_all(b"}")?;
        Ok(())
    }
}

// ---------- value formatter (string-producing) ----------

fn format_value(s: &mut String, v: &Value) -> Result<()> {
    match v {
        // The USDA parser reads the `None` token as `Value::ValueBlock`. Emitting
        // either `Value::None` (absent-opinion marker) or `Value::Value` (expression
        // placeholder) as `None` would silently re-parse as `Value::ValueBlock` and
        // drop the original variant.
        Value::None => bail!("Value::None cannot be serialized to USDA"),
        Value::Value => bail!("Value::Value cannot be serialized to USDA"),
        Value::ValueBlock => s.push_str("None"),

        Value::Bool(b) => s.push_str(if *b { "true" } else { "false" }),
        Value::BoolVec(v) => format_vec(s, v, |s, b| {
            s.push_str(if *b { "true" } else { "false" });
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

        Value::Half(h) => format_double(s, h.to_f64()),
        Value::HalfVec(v) => format_vec(s, v, |s, h| {
            format_double(s, h.to_f64());
            Ok(())
        })?,
        Value::Float(f) => format_double(s, f64::from(*f)),
        Value::FloatVec(v) => format_vec(s, v, |s, f| {
            format_double(s, f64::from(*f));
            Ok(())
        })?,
        Value::Double(d) => format_double(s, *d),
        Value::DoubleVec(v) => format_vec(s, v, |s, d| {
            format_double(s, *d);
            Ok(())
        })?,

        Value::String(v) => write_quoted(s, v)?,
        Value::StringVec(v) => format_vec(s, v, |s, t: &String| write_quoted(s, t))?,
        Value::Token(v) => write_quoted(s, v)?,
        Value::TokenVec(v) => format_vec(s, v, |s, t: &String| write_quoted(s, t))?,

        Value::AssetPath(v) => write_asset_path(s, v)?,

        Value::Vec2h(a) => format_tuple_half(s, a)?,
        Value::Vec3h(a) => format_tuple_half(s, a)?,
        Value::Vec4h(a) => format_tuple_half(s, a)?,
        Value::Quath(a) => format_tuple_half(s, a)?,
        Value::Vec2hVec(v) => format_vec(s, v, format_tuple_half)?,
        Value::Vec3hVec(v) => format_vec(s, v, format_tuple_half)?,
        Value::Vec4hVec(v) => format_vec(s, v, format_tuple_half)?,
        Value::QuathVec(v) => format_vec(s, v, format_tuple_half)?,

        Value::Vec2f(a) => format_tuple_f32(s, a)?,
        Value::Vec3f(a) => format_tuple_f32(s, a)?,
        Value::Vec4f(a) => format_tuple_f32(s, a)?,
        Value::Quatf(a) => format_tuple_f32(s, a)?,
        Value::Vec2fVec(v) => format_vec(s, v, format_tuple_f32)?,
        Value::Vec3fVec(v) => format_vec(s, v, format_tuple_f32)?,
        Value::Vec4fVec(v) => format_vec(s, v, format_tuple_f32)?,
        Value::QuatfVec(v) => format_vec(s, v, format_tuple_f32)?,

        Value::Vec2d(a) => format_tuple_f64(s, a)?,
        Value::Vec3d(a) => format_tuple_f64(s, a)?,
        Value::Vec4d(a) => format_tuple_f64(s, a)?,
        Value::Quatd(a) => format_tuple_f64(s, a)?,
        Value::Vec2dVec(v) => format_vec(s, v, format_tuple_f64)?,
        Value::Vec3dVec(v) => format_vec(s, v, format_tuple_f64)?,
        Value::Vec4dVec(v) => format_vec(s, v, format_tuple_f64)?,
        Value::QuatdVec(v) => format_vec(s, v, format_tuple_f64)?,

        Value::Vec2i(a) => format_tuple_int(s, a)?,
        Value::Vec3i(a) => format_tuple_int(s, a)?,
        Value::Vec4i(a) => format_tuple_int(s, a)?,
        Value::Vec2iVec(v) => format_vec(s, v, format_tuple_int)?,
        Value::Vec3iVec(v) => format_vec(s, v, format_tuple_int)?,
        Value::Vec4iVec(v) => format_vec(s, v, format_tuple_int)?,

        Value::Matrix2d(m) => format_matrix(s, m, 2)?,
        Value::Matrix3d(m) => format_matrix(s, m, 3)?,
        Value::Matrix4d(m) => format_matrix(s, m, 4)?,
        Value::Matrix2dVec(v) => format_vec(s, v, |s, m| format_matrix(s, m, 2))?,
        Value::Matrix3dVec(v) => format_vec(s, v, |s, m| format_matrix(s, m, 3))?,
        Value::Matrix4dVec(v) => format_vec(s, v, |s, m| format_matrix(s, m, 4))?,

        Value::Specifier(sp) => s.push_str(specifier_keyword(*sp)),
        Value::Permission(p) => s.push_str(match p {
            sdf::Permission::Public => "public",
            sdf::Permission::Private => "private",
        }),
        Value::Variability(vr) => s.push_str(match vr {
            Variability::Varying => "varying",
            Variability::Uniform => "uniform",
        }),

        Value::Dictionary(dict) => format_dictionary(s, dict)?,

        Value::TokenListOp(op) | Value::StringListOp(op) => {
            format_inline_listop(s, op, |s, t: &String| write_quoted(s, t))?
        }
        Value::PathListOp(op) => format_inline_listop(s, op, |s, p| {
            write!(s, "<{}>", p.as_str())?;
            Ok(())
        })?,
        Value::ReferenceListOp(op) => format_inline_listop(s, op, write_reference)?,
        Value::PayloadListOp(op) => format_inline_listop(s, op, write_payload)?,
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
        Value::VariantSelectionMap(m) => {
            let mut keys: Vec<&String> = m.keys().collect();
            keys.sort();
            s.push_str("{ ");
            for (i, k) in keys.iter().enumerate() {
                if i > 0 {
                    s.push_str("; ");
                }
                s.push_str("string ");
                write_quoted(s, k)?;
                s.push_str(" = ");
                write_quoted(s, &m[*k])?;
            }
            s.push_str(" }");
        }

        Value::TimeSamples(_) => anyhow::bail!("Value::TimeSamples must be handled by caller"),

        Value::LayerOffsetVec(offsets) => {
            format_vec(s, offsets, |s, o| {
                format_layer_offset(s, o);
                Ok(())
            })?;
        }

        Value::ValueVec(v) => format_vec(s, v, format_value)?,
        Value::UnregisteredValue(v) => write_quoted(s, v)?,
        Value::UnregisteredValueListOp(op) => format_inline_listop(s, op, |s, t: &String| write_quoted(s, t))?,

        Value::TimeCode(t) => format_double(s, *t),
        Value::TimeCodeVec(v) => format_vec(s, v, |s, t| {
            format_double(s, *t);
            Ok(())
        })?,

        Value::PathExpression(expr) => write_quoted(s, expr)?,
    }
    Ok(())
}

fn format_vec<T, F>(s: &mut String, items: &[T], mut fmt: F) -> Result<()>
where
    F: FnMut(&mut String, &T) -> Result<()>,
{
    s.push('[');
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        fmt(s, item)?;
    }
    s.push(']');
    Ok(())
}

fn format_inline_listop<T, F>(s: &mut String, op: &ListOp<T>, fmt_item: F) -> Result<()>
where
    T: Default + Clone + PartialEq,
    F: FnMut(&mut String, &T) -> Result<()>,
{
    // Only explicit list ops render inline; non-explicit must be broken out by caller.
    if !op.explicit {
        // Best-effort: flatten for inline contexts.
        let items = op.flatten();
        return format_vec(s, &items, fmt_item);
    }
    format_vec(s, &op.explicit_items, fmt_item)
}

fn format_tuple_half<const N: usize>(s: &mut String, a: &[half::f16; N]) -> Result<()> {
    s.push('(');
    for (i, v) in a.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        format_double(s, v.to_f64());
    }
    s.push(')');
    Ok(())
}

fn format_tuple_f32<const N: usize>(s: &mut String, a: &[f32; N]) -> Result<()> {
    s.push('(');
    for (i, v) in a.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        format_double(s, f64::from(*v));
    }
    s.push(')');
    Ok(())
}

fn format_tuple_f64<const N: usize>(s: &mut String, a: &[f64; N]) -> Result<()> {
    s.push('(');
    for (i, v) in a.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        format_double(s, *v);
    }
    s.push(')');
    Ok(())
}

fn format_tuple_int<const N: usize>(s: &mut String, a: &[i32; N]) -> Result<()> {
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

fn format_matrix(s: &mut String, m: &[f64], dim: usize) -> Result<()> {
    s.push('(');
    for row in 0..dim {
        if row > 0 {
            s.push_str(", ");
        }
        s.push('(');
        for col in 0..dim {
            if col > 0 {
                s.push_str(", ");
            }
            format_double(s, m[row * dim + col]);
        }
        s.push(')');
    }
    s.push(')');
    Ok(())
}

fn format_double(s: &mut String, v: f64) {
    if v.is_nan() {
        s.push_str("nan");
    } else if v.is_infinite() {
        s.push_str(if v > 0.0 { "inf" } else { "-inf" });
    } else if v.fract() == 0.0 && v.is_finite() && v.abs() < 1e16 {
        // Integer-valued floats need an explicit `.0` to re-parse as a float
        // rather than an int in type-free contexts (time samples, dict entries).
        let as_int = v as i64;
        write!(s, "{as_int}.0").unwrap();
    } else {
        // Ryu-backed shortest round-trip.
        write!(s, "{v}").unwrap();
    }
}

fn format_dictionary(s: &mut String, dict: &HashMap<String, Value>) -> Result<()> {
    let mut keys: Vec<&String> = dict.keys().collect();
    keys.sort();
    s.push('{');
    s.push('\n');
    for k in &keys {
        let value = &dict[k.as_str()];
        let type_name = dict_value_type_name(value);
        s.push_str("    ");
        if let Some(ty) = type_name {
            s.push_str(ty);
            s.push(' ');
        }
        if is_bare_dict_key(k) {
            s.push_str(k);
        } else {
            write_quoted(s, k)?;
        }
        s.push_str(" = ");
        format_value(s, value)?;
        s.push('\n');
    }
    s.push('}');
    Ok(())
}

/// A dictionary key can be emitted unquoted only when it tokenizes as a USDA
/// `Identifier` or `NamespacedIdentifier`: starts with a letter/underscore and
/// continues with alphanumerics, underscores, or colons.
fn is_bare_dict_key(k: &str) -> bool {
    let mut chars = k.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == ':')
}

fn format_layer_offset(s: &mut String, o: &LayerOffset) {
    s.push('(');
    format_double(s, o.offset);
    s.push_str(", ");
    format_double(s, o.scale);
    s.push(')');
}

fn write_quoted(s: &mut String, text: &str) -> Result<()> {
    // The USDA lexer does not unescape string contents; it preserves the raw
    // bytes between the delimiters. So we must NOT emit backslash-escapes for
    // literal backslashes — we pick a delimiter the content can't close.
    let has_newline = text.contains('\n');
    let has_dq = text.contains('"');
    let has_sq = text.contains('\'');
    let has_triple_dq = text.contains("\"\"\"");
    let has_triple_sq = text.contains("'''");

    // A single-character delimiter works only if the text contains no newline
    // and does not include that delimiter. Otherwise we need triple quotes.
    if has_newline || (has_dq && has_sq) {
        if !has_triple_dq {
            s.push_str("\"\"\"");
            s.push_str(text);
            s.push_str("\"\"\"");
            return Ok(());
        }
        if !has_triple_sq {
            s.push_str("'''");
            s.push_str(text);
            s.push_str("'''");
            return Ok(());
        }
        bail!("cannot emit USDA string containing both \"\"\" and '''");
    }

    // Single-line text with at most one kind of quote present: use the
    // opposite single-character delimiter.
    if has_dq {
        s.push('\'');
        s.push_str(text);
        s.push('\'');
    } else {
        s.push('"');
        s.push_str(text);
        s.push('"');
    }
    Ok(())
}

fn write_asset_path(s: &mut String, path: &str) -> Result<()> {
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

fn write_reference(s: &mut String, r: &Reference) -> Result<()> {
    if !r.asset_path.is_empty() {
        write_asset_path(s, &r.asset_path)?;
    }
    if !r.prim_path.is_empty() {
        write!(s, "<{}>", r.prim_path.as_str())?;
    }
    if r.layer_offset != LayerOffset::default() {
        s.push_str(" (offset = ");
        format_double(s, r.layer_offset.offset);
        s.push_str("; scale = ");
        format_double(s, r.layer_offset.scale);
        s.push(')');
    }
    Ok(())
}

fn write_payload(s: &mut String, p: &Payload) -> Result<()> {
    if !p.asset_path.is_empty() {
        write_asset_path(s, &p.asset_path)?;
    }
    if !p.prim_path.is_empty() {
        write!(s, "<{}>", p.prim_path.as_str())?;
    }
    if let Some(offset) = &p.layer_offset {
        if *offset != LayerOffset::default() {
            s.push_str(" (offset = ");
            format_double(s, offset.offset);
            s.push_str("; scale = ");
            format_double(s, offset.scale);
            s.push(')');
        }
    }
    Ok(())
}

fn specifier_keyword(s: Specifier) -> &'static str {
    match s {
        Specifier::Def => "def",
        Specifier::Over => "over",
        Specifier::Class => "class",
    }
}

/// Name of the USD type that describes this value variant, for dict entries.
/// Returns `None` for types that don't have a plain typed form (e.g. list ops).
fn dict_value_type_name(v: &Value) -> Option<&'static str> {
    Some(match v {
        Value::Bool(_) => "bool",
        Value::BoolVec(_) => "bool[]",
        Value::Uchar(_) => "uchar",
        Value::UcharVec(_) => "uchar[]",
        Value::Int(_) => "int",
        Value::IntVec(_) => "int[]",
        Value::Uint(_) => "uint",
        Value::UintVec(_) => "uint[]",
        Value::Int64(_) => "int64",
        Value::Int64Vec(_) => "int64[]",
        Value::Uint64(_) => "uint64",
        Value::Uint64Vec(_) => "uint64[]",
        Value::Half(_) => "half",
        Value::HalfVec(_) => "half[]",
        Value::Float(_) => "float",
        Value::FloatVec(_) => "float[]",
        Value::Double(_) => "double",
        Value::DoubleVec(_) => "double[]",
        Value::String(_) => "string",
        Value::StringVec(_) => "string[]",
        Value::Token(_) => "token",
        Value::TokenVec(_) => "token[]",
        Value::AssetPath(_) => "asset",
        Value::Vec2h(_) => "half2",
        Value::Vec3h(_) => "half3",
        Value::Vec4h(_) => "half4",
        Value::Vec2hVec(_) => "half2[]",
        Value::Vec3hVec(_) => "half3[]",
        Value::Vec4hVec(_) => "half4[]",
        Value::Vec2f(_) => "float2",
        Value::Vec3f(_) => "float3",
        Value::Vec4f(_) => "float4",
        Value::Vec2fVec(_) => "float2[]",
        Value::Vec3fVec(_) => "float3[]",
        Value::Vec4fVec(_) => "float4[]",
        Value::Vec2d(_) => "double2",
        Value::Vec3d(_) => "double3",
        Value::Vec4d(_) => "double4",
        Value::Vec2dVec(_) => "double2[]",
        Value::Vec3dVec(_) => "double3[]",
        Value::Vec4dVec(_) => "double4[]",
        Value::Vec2i(_) => "int2",
        Value::Vec3i(_) => "int3",
        Value::Vec4i(_) => "int4",
        Value::Vec2iVec(_) => "int2[]",
        Value::Vec3iVec(_) => "int3[]",
        Value::Vec4iVec(_) => "int4[]",
        Value::Quath(_) => "quath",
        Value::Quatf(_) => "quatf",
        Value::Quatd(_) => "quatd",
        Value::QuathVec(_) => "quath[]",
        Value::QuatfVec(_) => "quatf[]",
        Value::QuatdVec(_) => "quatd[]",
        Value::Matrix2d(_) => "matrix2d",
        Value::Matrix3d(_) => "matrix3d",
        Value::Matrix4d(_) => "matrix4d",
        Value::Matrix2dVec(_) => "matrix2d[]",
        Value::Matrix3dVec(_) => "matrix3d[]",
        Value::Matrix4dVec(_) => "matrix4d[]",
        Value::TimeCode(_) => "timecode",
        Value::TimeCodeVec(_) => "timecode[]",
        Value::Dictionary(_) => "dictionary",
        _ => return None,
    })
}

fn get_value(data: &dyn AbstractData, path: &Path, field: &str) -> Option<Value> {
    data.get(path, field).ok().map(|v| v.into_owned())
}

fn prim_children(data: &dyn AbstractData, path: &Path) -> Vec<String> {
    match get_value(data, path, ChildrenKey::PrimChildren.as_str()) {
        Some(Value::TokenVec(v)) => v,
        _ => Vec::new(),
    }
}

fn property_children(data: &dyn AbstractData, path: &Path) -> Vec<String> {
    match get_value(data, path, ChildrenKey::PropertyChildren.as_str()) {
        Some(Value::TokenVec(v)) => v,
        _ => Vec::new(),
    }
}

// Field classifiers. Match C++ `Sdf_Is{Prim,Attribute,Relationship}MetadataField`.

/// `spline` names the in-memory spline dictionary slot but isn't yet defined
/// in [`FieldKey`]. Keep it local until promoted into the schema.
const SPLINE_FIELD: &str = "spline";

const PRIM_STRUCTURAL_FIELDS: &[&str] = &[
    FieldKey::Specifier.as_str(),
    FieldKey::TypeName.as_str(),
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
    SPLINE_FIELD,
];

const RELATIONSHIP_STRUCTURAL_FIELDS: &[&str] = &[
    FieldKey::Custom.as_str(),
    FieldKey::Variability.as_str(),
    FieldKey::TargetPaths.as_str(),
    ChildrenKey::RelationshipTargetChildren.as_str(),
];

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
    use crate::sdf::{path, Data};

    #[test]
    fn writes_empty_layer() {
        let data = Data::new();
        let text = TextWriter::write_to_string(&data as &dyn AbstractData).unwrap();
        assert_eq!(text, "#usda 1.0\n");
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
            Token::String(s) => s.to_owned(),
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
        // Worst case: newline plus both `"""` and `'''`. No USDA delimiter can wrap
        // this losslessly; the writer must report an error rather than emit output
        // the lexer will reject.
        let worst = "line\n\"\"\"and'''both";
        let mut out = String::new();
        assert!(
            write_quoted(&mut out, worst).is_err(),
            "expected error for un-quotable string, got output {out:?}"
        );
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
        root_spec.add(FieldKey::CustomLayerData, Value::Dictionary(dict));

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
}
