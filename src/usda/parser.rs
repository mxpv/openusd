use anyhow::{anyhow, bail, ensure, Context, Result};
use logos::{Lexer, Logos};
use std::mem::MaybeUninit;
use std::ops::Range;
use std::{any::type_name, collections::HashMap, fmt::Debug, str::FromStr};

use crate::sdf::{
    self,
    schema::{ChildrenKey, FieldKey},
};

use super::token::Token;

type LexResult<'source> = std::result::Result<Token<'source>, ()>;

/// Parser translates a list of tokens into structured data.
pub struct Parser<'a> {
    lexer: Lexer<'a, Token<'a>>,
    lookahead: Option<(LexResult<'a>, Range<usize>)>,
    source: &'a str,
    line_offsets: Vec<usize>,
    last_span: Option<Range<usize>>,
}

/// Captures the line context for the most recent token consumed by the parser.
#[derive(Debug, Clone)]
pub struct ErrorHighlight {
    pub line: usize,
    pub column: usize,
    pub line_text: String,
    pub pointer_line: String,
}

impl ErrorHighlight {
    /// Renders a human-readable representation of the highlighted line.
    pub fn render(&self) -> String {
        format!(
            "line {} column {}\n{}\n{}",
            self.line, self.column, self.line_text, self.pointer_line
        )
    }
}

impl<'a> Parser<'a> {
    pub fn new(data: &'a str) -> Self {
        Self {
            lexer: Token::lexer(data),
            lookahead: None,
            source: data,
            line_offsets: Self::compute_line_offsets(data),
            last_span: None,
        }
    }

    /// Returns a highlight for the most recent token span processed by the parser.
    pub fn last_error_highlight(&self) -> Option<ErrorHighlight> {
        self.last_span
            .clone()
            .and_then(|span| self.highlight_for_span(span))
    }

    fn highlight_for_span(&self, span: Range<usize>) -> Option<ErrorHighlight> {
        if self.source.is_empty() {
            return None;
        }
        let mut offset = span.start.min(self.source.len());
        if offset == self.source.len() && offset > 0 {
            offset -= 1;
        }
        let line_index = self.line_index_for_offset(offset);
        let line_start = *self.line_offsets.get(line_index)?;
        let line_end = self
            .line_offsets
            .get(line_index + 1)
            .copied()
            .unwrap_or(self.source.len());
        let bounded_end = line_end.min(self.source.len());
        let raw_line = &self.source[line_start..bounded_end];
        let line_text = raw_line.trim_end_matches(['\r', '\n']).to_string();

        let mut column_chars = 0usize;
        for ch in self.source[line_start..offset].chars() {
            if ch == '\n' || ch == '\r' {
                break;
            }
            column_chars += 1;
        }
        let column = column_chars + 1;

        let mut pointer_line = String::new();
        for ch in self.source[line_start..offset].chars() {
            if ch == '\n' || ch == '\r' {
                break;
            }
            pointer_line.push(if ch == '\t' { '\t' } else { ' ' });
        }
        pointer_line.push('^');

        Some(ErrorHighlight {
            line: line_index + 1,
            column,
            line_text,
            pointer_line,
        })
    }

    fn line_index_for_offset(&self, offset: usize) -> usize {
        match self.line_offsets.binary_search(&offset) {
            Ok(idx) => idx,
            Err(idx) => idx.saturating_sub(1),
        }
    }

    #[inline]
    fn fetch_next(&mut self) -> Result<Token<'a>> {
        let (token, span) = if let Some((token, span)) = self.lookahead.take() {
            (token, span)
        } else {
            let token = self
                .lexer
                .next()
                .context("Unexpected end of tokens")?;
            let span = self.lexer.span();
            (token, span)
        };
        self.last_span = Some(span.clone());
        token.map_err(|e| anyhow!("Logos error: {e:?}"))
    }

    #[inline]
    fn peek_next(&mut self) -> Option<&LexResult<'a>> {
        if self.lookahead.is_none() {
            let next = self.lexer.next()?;
            let span = self.lexer.span();
            self.lookahead = Some((next, span));
        }
        self.lookahead.as_ref().map(|(token, _)| token)
    }

    fn ensure_next(&mut self, expected_token: Token) -> Result<()> {
        let token = self.fetch_next()?;
        ensure!(
            token == expected_token,
            "Unexpected token (want: {expected_token:?}, got {token:?})"
        );
        Ok(())
    }

    #[inline]
    fn ensure_pun(&mut self, value: char) -> Result<()> {
        self.ensure_next(Token::Punctuation(value))
            .context("Punctuation token expected")
    }

    fn fetch_str(&mut self) -> Result<&str> {
        let token = self.fetch_next()?;
        token
            .clone()
            .try_as_string()
            .ok_or_else(|| anyhow!("Unexpected token {token:?} (want String)"))
    }

    /// Parse tokens to specs.
    /// Walks the entire token stream, seeding the pseudo root and recursing through every prim.
    pub fn parse(&mut self) -> Result<HashMap<sdf::Path, sdf::Spec>> {
        let mut data = HashMap::new();
        let current_path = sdf::Path::abs_root();

        // Read pseudo root.
        let mut pseudo_root_spec = self.read_pseudo_root().context("Unable to parse pseudo root")?;
        let mut root_children = Vec::new();

        // Read root defs.
        while self.peek_next().is_some() {
            self.read_prim(&current_path, &mut root_children, &mut data)?;
        }

        pseudo_root_spec.add(ChildrenKey::PrimChildren, sdf::Value::TokenVec(root_children));
        data.insert(current_path.clone(), pseudo_root_spec);
        Ok(data)
    }

    /// Parse the file header/pseudo-root to populate layer-level metadata before prim traversal.
    fn read_pseudo_root(&mut self) -> Result<sdf::Spec> {
        // Make sure text file starts with #usda...
        let version = self
            .fetch_next()?
            .try_as_magic()
            .ok_or_else(|| anyhow!("Text file must start with magic token, got {:?}", self.peek_next()))?;
        ensure!(version == "1.0", "File must start with '#usda 1.0', got: {version:?}");

        let mut root = sdf::Spec::new(sdf::SpecType::PseudoRoot);

        if self.peek_next().map(|r| r.as_ref().ok()) != Some(Some(&Token::Punctuation('('))) {
            return Ok(root);
        }

        // Eat (
        self.ensure_pun('(')?;

        const KNOWN_PROPS: &[(&str, Type)] = &[
            (FieldKey::DefaultPrim.as_str(), Type::Token),
            (FieldKey::StartTimeCode.as_str(), Type::Uint64),
            (FieldKey::HasOwnedSubLayers.as_str(), Type::StringVec),
            ("doc", Type::String),
            ("endTimeCode", Type::Uint64),
            ("framesPerSecond", Type::Uint64),
            ("metersPerUnit", Type::Double),
            ("timeCodesPerSecond", Type::Uint64),
            ("upAxis", Type::Token),
        ];

        // Read pseudo root properties
        loop {
            let next = self.fetch_next().context("Unable to fetch next pseudo root property")?;

            match next {
                Token::Punctuation(')') => break,
                Token::String(str) => {
                    root.add(FieldKey::Documentation, str);
                }
                Token::Doc => {
                    self.ensure_pun('=')?;
                    let value = self.fetch_str()?;
                    root.add("doc", value);
                }
                Token::SubLayers => {
                    self.ensure_pun('=')?;
                    let (sublayers, sublayer_offsets) = self.parse_sublayers().context("Unable to parse subLayers")?;
                    root.add(FieldKey::SubLayers, sublayers);
                    root.add(FieldKey::SubLayerOffsets, sublayer_offsets);
                }
                Token::Identifier(name) => {
                    if let Some((name, ty)) = KNOWN_PROPS.iter().copied().find(|(n, _)| *n == name) {
                        self.ensure_pun('=')?;
                        let value = self
                            .parse_value(ty)
                            .with_context(|| format!("Unable to parse value for {name}"))?;
                        root.add(name, value);
                    }
                }
                _ => bail!("Unexpected token {next:?}"),
            }
        }

        Ok(root)
    }

    /// Parse a prim declaration, capture its metadata, and recursively traverse nested prims/props.
    fn read_prim(
        &mut self,
        current_path: &sdf::Path,
        parent_children: &mut Vec<String>,
        data: &mut HashMap<sdf::Path, sdf::Spec>,
    ) -> Result<()> {
        let mut spec = sdf::Spec::new(sdf::SpecType::Prim);

        let specifier = {
            let specifier_token = self.fetch_next().context("Unable to read prim specifier")?;
            match specifier_token {
                Token::Def => sdf::Specifier::Def,
                Token::Over => sdf::Specifier::Over,
                Token::Class => sdf::Specifier::Class,
                _ => bail!("Unexpected prim specifier: {specifier_token:?}"),
            }
        };

        let mut name_token = self.fetch_next()?;
        if specifier == sdf::Specifier::Def || specifier == sdf::Specifier::Class {
            if let Some(prim_type) = name_token.clone().try_as_identifier() {
                spec.add(FieldKey::TypeName, sdf::Value::Token(prim_type.to_string()));
                name_token = self.fetch_next()?;
            }
        }

        let name = name_token
            .clone()
            .try_as_string()
            .ok_or_else(|| anyhow!("Unexpected token {name_token:?} (want String)"))?;
        parent_children.push(name.to_string());
        let prim_path = current_path.append_path(name)?;

        let mut properties = Vec::new();
        let mut brace_consumed = false;

        let brace = self.fetch_next()?;
        match brace {
            Token::Punctuation('(') => {
                self.read_prim_metadata(&mut spec, None)
                    .context("Unable to parse prim metadata")?;
                self.ensure_pun(')').context("Prim metadata must end with )")?;
            }
            Token::Punctuation('{') => {
                brace_consumed = true;
            }
            other => {
                // Support metadata without wrapping parentheses.
                self.read_prim_metadata(&mut spec, Some(other))
                    .context("Unable to parse prim metadata")?;
                brace_consumed = false;
            }
        };

        if !brace_consumed {
            self.ensure_pun('{')?;
        }

        let mut children = Vec::new();
        loop {
            let next = self
                .peek_next()
                .context("Unexpected end of prim body")?
                .as_ref()
                .map_err(|e| anyhow!("{e:?}"))?;
            match next {
                Token::Punctuation('}') => {
                    self.fetch_next()?;
                    break;
                }
                Token::Def | Token::Over | Token::Class => {
                    self.read_prim(&prim_path, &mut children, data)
                        .context("Unable to read nested primitive")?;
                }
                Token::Rel => {
                    self.fetch_next()?;
                    self.skip_relationship()?;
                }
                _ => {
                    self.read_attribute(&prim_path, &mut properties, data)
                        .context("Unable to read attribute")?;
                }
            }
        }
        spec.add(ChildrenKey::PrimChildren, sdf::Value::TokenVec(children));

        spec.add(FieldKey::Specifier, sdf::Value::Specifier(specifier));
        spec.add(ChildrenKey::PropertyChildren, sdf::Value::TokenVec(properties));
        data.insert(prim_path, spec);

        Ok(())
    }

    /// Parse an attribute/property declaration, including variability, metadata, and default value.
    fn read_attribute(
        &mut self,
        current_path: &sdf::Path,
        properties: &mut Vec<String>,
        data: &mut HashMap<sdf::Path, sdf::Spec>,
    ) -> Result<()> {
        let mut spec = sdf::Spec::new(sdf::SpecType::Attribute);
        let mut custom = false;
        let mut variability = sdf::Variability::Varying;

        if let Some(Ok(Token::Custom)) = self.peek_next() {
            custom = true;
            self.fetch_next()?;
        }

        if let Some(Ok(Token::Varying)) = self.peek_next() {
            self.fetch_next()?;
        } else if let Some(Ok(Token::Uniform)) = self.peek_next() {
            variability = sdf::Variability::Uniform;
            self.fetch_next()?;
        }

        let type_token = self.fetch_next()?;
        let type_name = match type_token {
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => s,
            other => bail!("Unexpected token type for attribute type, expected Identifier, got {other:?}"),
        };
        let data_type = Self::parse_data_type(type_name)?;

        let name_token = self.fetch_next()?;
        let name = match name_token {
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => s,
            _ => bail!("Unexpected token type for attribute name: {name_token:?}"),
        };

        if name.contains(".connect") {
            if matches!(self.peek_next(), Some(Ok(Token::Punctuation('=')))) {
                self.fetch_next()?;
                self.skip_connection_value()?;
            }
            return Ok(());
        }

        if !matches!(self.peek_next(), Some(Ok(Token::Punctuation('=')))) {
            return Ok(());
        }

        self.ensure_pun('=')?;
        let value = self.parse_value(data_type)?;
        let path = current_path.append_property(name)?;

        if matches!(self.peek_next(), Some(Ok(Token::Punctuation('(')))) {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse attribute metadata")?;
        }

        properties.push(name.to_string());

        spec.add(FieldKey::Custom, sdf::Value::Bool(custom));
        spec.add(FieldKey::Variability, sdf::Value::Variability(variability));
        spec.add(FieldKey::TypeName, sdf::Value::Token(type_name.to_string()));
        spec.add(FieldKey::Default, value);
        data.insert(path, spec);

        Ok(())
    }

    /// Skip over a relationship/connection value without interpreting its contents.
    fn skip_connection_value(&mut self) -> Result<()> {
        let token = self.fetch_next()?;
        if let Token::Punctuation('[') = token {
            let mut depth = 1i32;
            while depth > 0 {
                let next = self.fetch_next()?;
                match next {
                    Token::Punctuation('[') => depth += 1,
                    Token::Punctuation(']') => depth -= 1,
                    _ => {}
                }
            }
        }
        Ok(())
    }

    /// Parse the metadata block attached to an attribute and stash entries on the spec.
    fn parse_property_metadata(&mut self, spec: &mut sdf::Spec) -> Result<()> {
        self.ensure_pun('(')?;

        loop {
            if matches!(self.peek_next(), Some(Ok(Token::Punctuation(')')))) {
                self.fetch_next()?;
                break;
            }

            let name_token = self.fetch_next()?;
            let name = match name_token {
                Token::Identifier(s) | Token::NamespacedIdentifier(s) => s,
                other => bail!("Unexpected attribute metadata name token: {other:?}"),
            };

            self.ensure_pun('=')?;
            let value = self
                .parse_property_metadata_value()
                .with_context(|| format!("Unable to parse attribute metadata value for {name}"))?;
            spec.fields.insert(name.to_owned(), value);

            if matches!(self.peek_next(), Some(Ok(Token::Punctuation(',')))) {
                self.fetch_next()?;
            }
        }

        Ok(())
    }

    /// Parse a single attribute metadata value (scalar or array) from within a metadata block.
    fn parse_property_metadata_value(&mut self) -> Result<sdf::Value> {
        let token = self.fetch_next()?;
        match token {
            Token::String(value) => Ok(sdf::Value::String(value.to_owned())),
            Token::Identifier(value) | Token::NamespacedIdentifier(value) => Ok(sdf::Value::Token(value.to_owned())),
            Token::Number(raw) => {
                if let Ok(int) = raw.parse::<i64>() {
                    Ok(sdf::Value::Int64(int))
                } else if let Ok(float) = raw.parse::<f64>() {
                    Ok(sdf::Value::Double(float))
                } else {
                    bail!("Unable to parse numeric metadata value: {raw}");
                }
            }
            Token::Punctuation('[') => {
                let mut values = Vec::new();
                loop {
                    if matches!(self.peek_next(), Some(Ok(Token::Punctuation(']')))) {
                        self.fetch_next()?;
                        break;
                    }

                    let entry = self.fetch_next()?;
                    let value = match entry {
                        Token::String(v) => v.to_owned(),
                        Token::Identifier(v) | Token::NamespacedIdentifier(v) | Token::Number(v) => v.to_owned(),
                        other => bail!("Unsupported metadata array element: {other:?}"),
                    };
                    values.push(value);

                    match self.fetch_next()? {
                        Token::Punctuation(',') => continue,
                        Token::Punctuation(']') => break,
                        other => bail!("Unexpected token in metadata array: {other:?}"),
                    }
                }
                Ok(sdf::Value::StringVec(values))
            }
            other => bail!("Unsupported property metadata value token: {other:?}"),
        }
    }

    /// Skip an entire relationship declaration so it does not register as a property.
    fn skip_relationship(&mut self) -> Result<()> {
        let target = self.fetch_next()?;
        match target {
            Token::Identifier(_) | Token::NamespacedIdentifier(_) => {}
            other => bail!("Unexpected token in relationship declaration: {other:?}"),
        }
        if matches!(self.peek_next(), Some(Ok(Token::Punctuation('=')))) {
            self.fetch_next()?;
            self.skip_connection_value()?;
        }
        Ok(())
    }

    /// Parse prim metadata contained either within parentheses or directly after the prim
    /// declaration (until `{` is encountered).
    fn read_prim_metadata(&mut self, spec: &mut sdf::Spec, first: Option<Token<'a>>) -> Result<()> {
        let mut current = first;

        loop {
            if matches!(self.peek_next(), Some(Ok(Token::Punctuation(')'))))
                || matches!(self.peek_next(), Some(Ok(Token::Punctuation('{'))))
            {
                break;
            }

            let token = match current.take() {
                Some(token) => token,
                None => self.fetch_next()?,
            };

            self.read_prim_metadata_entry(token, spec)
                .context("Unable to parse prim metadata entry")?;
        }

        Ok(())
    }

    /// Parse a single prim metadata assignment, honoring list ops for supported fields.
    fn read_prim_metadata_entry(&mut self, token: Token<'a>, spec: &mut sdf::Spec) -> Result<()> {
        let (list_op, name_token) = match token {
            Token::Add | Token::Append | Token::Delete | Token::Prepend | Token::Reorder => {
                let name = self.fetch_next()?;
                (Some(token), name)
            }
            _ => (None, token),
        };

        let name = match name_token {
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => s,
            Token::Kind => FieldKey::Kind.as_str(),
            Token::References => FieldKey::References.as_str(),
            Token::Payload => FieldKey::Payload.as_str(),
            Token::Inherits => FieldKey::InheritPaths.as_str(),
            other => bail!("Unexpected metadata name token: {other:?}"),
        };

        self.ensure_pun('=')?;

        match name {
            n if n == FieldKey::Active.as_str() => {
                let value = self.parse_token::<bool>().context("Unable to parse active flag")?;
                spec.add(FieldKey::Active, sdf::Value::Bool(value));
            }
            "apiSchemas" => {
                let values = self.parse_token_list().context("Unable to parse apiSchemas list")?;
                let list_op = self
                    .apply_list_op(list_op, values)
                    .context("Unable to build apiSchemas listOp")?;
                spec.add("apiSchemas", sdf::Value::TokenListOp(list_op));
            }
            n if n == FieldKey::References.as_str() => {
                let references = self.parse_reference_list().context("Unable to parse references")?;
                let list_op = self
                    .apply_list_op(list_op, references)
                    .context("Unable to build references listOp")?;
                spec.add(FieldKey::References, sdf::Value::ReferenceListOp(list_op));
            }
            n if n == FieldKey::InheritPaths.as_str() => {
                let paths = if matches!(self.peek_next(), Some(Ok(Token::Punctuation('[')))) {
                    let mut collected = Vec::new();
                    self.parse_array_fn(|this| {
                        collected.push(this.parse_inherit_path()?);
                        Ok(())
                    })?;
                    collected
                } else {
                    vec![self.parse_inherit_path()?]
                };
                let list_op = self
                    .apply_list_op(list_op, paths)
                    .context("Unable to build inherits listOp")?;
                spec.add(FieldKey::InheritPaths, sdf::Value::PathListOp(list_op));
            }
            n if n == FieldKey::Kind.as_str() => {
                ensure!(list_op.is_none(), "kind metadata does not support list ops");
                let value = self.parse_token::<String>().context("Unable to parse kind metadata")?;
                spec.add(FieldKey::Kind, sdf::Value::Token(value));
            }
            other => bail!("Unsupported prim metadata: {other}"),
        }

        Ok(())
    }

    /// Parse one reference entry, including optional target prim path and layer offset.
    fn parse_reference(&mut self) -> Result<sdf::Reference> {
        let asset_path = self
            .fetch_next()?
            .try_as_asset_ref()
            .ok_or_else(|| anyhow!("Asset reference expected"))?;

        let mut reference = sdf::Reference {
            asset_path: asset_path.to_string(),
            prim_path: sdf::Path::default(),
            layer_offset: sdf::LayerOffset::default(),
            custom_data: HashMap::new(),
        };

        if matches!(self.peek_next(), Some(Ok(Token::PathRef(_)))) {
            let path = self
                .fetch_next()?
                .try_as_path_ref()
                .ok_or_else(|| anyhow!("Path reference expected"))?;
            reference.prim_path = sdf::Path::new(path)?;
        }

        if let Some(Ok(Token::Punctuation('('))) = self.peek_next() {
            self.parse_reference_layer_offset(&mut reference.layer_offset)
                .context("Unable to parse reference layer offset")?;
        }

        Ok(reference)
    }

    /// Parse `(offset = ...; scale = ...)` blocks attached to references or sublayers.
    fn parse_reference_layer_offset(&mut self, layer_offset: &mut sdf::LayerOffset) -> Result<()> {
        self.ensure_pun('(')?;

        self.parse_seq_fn(';', |this, _index| {
            let token = this.fetch_next()?;
            this.ensure_pun('=')?;
            let value = this.parse_value(Type::Double)?;

            match token {
                Token::Offset => {
                    layer_offset.offset = value.try_as_double().context("Expected double for offset")?;
                }
                Token::Scale => {
                    layer_offset.scale = value.try_as_double().context("Expected double for scale")?;
                }
                unexpected => bail!("Unexpected token in layer offset: {unexpected:?}"),
            }

            Ok(())
        })?;

        Ok(())
    }

    /// Parse a list-op friendly sequence of references.
    fn parse_reference_list(&mut self) -> Result<Vec<sdf::Reference>> {
        if matches!(self.peek_next(), Some(Ok(Token::Punctuation('[')))) {
            let mut out = Vec::new();
            self.parse_array_fn(|this| {
                out.push(this.parse_reference()?);
                Ok(())
            })?;
            Ok(out)
        } else {
            Ok(vec![self.parse_reference()?])
        }
    }

    fn parse_inherit_path(&mut self) -> Result<sdf::Path> {
        let token = self.fetch_next()?;
        let path_str = token
            .try_as_path_ref()
            .ok_or_else(|| anyhow!("Path reference expected for inherits metadata"))?;
        sdf::Path::new(path_str)
    }

    fn parse_token_list(&mut self) -> Result<Vec<String>> {
        if matches!(self.peek_next(), Some(Ok(Token::Punctuation('[')))) {
            self.parse_array()
        } else {
            let value = self.parse_token::<String>()?;
            Ok(vec![value])
        }
    }

    fn apply_list_op<T: Default + Clone>(&mut self, op: Option<Token<'a>>, items: Vec<T>) -> Result<sdf::ListOp<T>> {
        let mut list = sdf::ListOp::default();

        match op {
            None => {
                list.explicit = true;
                list.explicit_items = items;
            }
            Some(Token::Prepend) => list.prepended_items = items,
            Some(Token::Append) => list.appended_items = items,
            Some(Token::Add) => list.added_items = items,
            Some(Token::Delete) => list.deleted_items = items,
            Some(Token::Reorder) => list.ordered_items = items,
            other => bail!("Unsupported list op: {other:?}"),
        }

        Ok(list)
    }

    /// Decode a typed value based on USD's scalar/array/role type tables.
    fn parse_value(&mut self, ty: Type) -> Result<sdf::Value> {
        let value = match ty {
            // Bool
            Type::Bool => sdf::Value::Bool(self.parse_bool()?),
            Type::BoolVec => sdf::Value::BoolVec(self.parse_bool_array()?),

            // Asset paths
            Type::Asset => sdf::Value::AssetPath(self.parse_asset_path()?),
            Type::AssetVec => sdf::Value::StringVec(self.parse_asset_path_array()?),

            // Ints
            Type::Uchar => sdf::Value::Uchar(self.parse_token()?),
            Type::UcharVec => sdf::Value::UcharVec(self.parse_array()?),

            Type::Int => sdf::Value::Int(self.parse_token()?),
            Type::Int2 => sdf::Value::Vec2i(self.parse_tuple::<_, 2>()?.into()),
            Type::Int3 => sdf::Value::Vec3i(self.parse_tuple::<_, 3>()?.into()),
            Type::Int4 => sdf::Value::Vec4i(self.parse_tuple::<_, 4>()?.into()),
            Type::IntVec => sdf::Value::IntVec(self.parse_array()?),
            Type::Int2Vec => sdf::Value::Vec2i(self.parse_array_of_tuples::<_, 2>()?),
            Type::Int3Vec => sdf::Value::Vec3i(self.parse_array_of_tuples::<_, 3>()?),
            Type::Int4Vec => sdf::Value::Vec4i(self.parse_array_of_tuples::<_, 4>()?),
            Type::Uint => sdf::Value::Uint(self.parse_token()?),
            Type::Int64 => sdf::Value::Int64(self.parse_token()?),
            Type::Uint64 => sdf::Value::Uint64(self.parse_token()?),

            // Half
            Type::Half => sdf::Value::Half(self.parse_token()?),
            Type::Half2 => sdf::Value::HalfVec(self.parse_tuple::<_, 2>()?.into()),
            Type::Half3 => sdf::Value::Vec3h(self.parse_tuple::<_, 3>()?.into()),
            Type::Half4 => sdf::Value::Vec4h(self.parse_tuple::<_, 4>()?.into()),

            Type::HalfVec => sdf::Value::HalfVec(self.parse_array()?),
            Type::Half2Vec => sdf::Value::Vec2h(self.parse_array_of_tuples::<_, 2>()?),
            Type::Half3Vec => sdf::Value::Vec3h(self.parse_array_of_tuples::<_, 3>()?),
            Type::Half4Vec => sdf::Value::Vec4h(self.parse_array_of_tuples::<_, 4>()?),

            // Float
            Type::Float => sdf::Value::Float(self.parse_token()?),
            Type::Float2 => sdf::Value::Vec2f(self.parse_tuple::<_, 2>()?.into()),
            Type::Float3 => sdf::Value::Vec3f(self.parse_tuple::<_, 3>()?.into()),
            Type::Float4 => sdf::Value::Vec4f(self.parse_tuple::<_, 4>()?.into()),
            Type::FloatVec => sdf::Value::FloatVec(self.parse_array()?),
            Type::Float2Vec => sdf::Value::Vec2f(self.parse_array_of_tuples::<_, 2>()?),
            Type::Float3Vec => sdf::Value::Vec3f(self.parse_array_of_tuples::<_, 3>()?),
            Type::Float4Vec => sdf::Value::Vec4f(self.parse_array_of_tuples::<_, 4>()?),

            // Double
            Type::Double => sdf::Value::Double(self.parse_token()?),
            Type::Double2 => sdf::Value::Vec2d(self.parse_tuple::<_, 2>()?.into()),
            Type::Double3 => sdf::Value::Vec3d(self.parse_tuple::<_, 3>()?.into()),
            Type::Double4 => sdf::Value::Vec4d(self.parse_tuple::<_, 4>()?.into()),
            Type::DoubleVec => sdf::Value::DoubleVec(self.parse_array()?),
            Type::Double2Vec => sdf::Value::Vec2d(self.parse_array_of_tuples::<_, 2>()?),
            Type::Double3Vec => sdf::Value::Vec3d(self.parse_array_of_tuples::<_, 3>()?),
            Type::Double4Vec => sdf::Value::Vec4d(self.parse_array_of_tuples::<_, 4>()?),

            // Quats
            Type::Quath => sdf::Value::Quath(self.parse_tuple::<_, 4>()?.into()),
            Type::Quatf => sdf::Value::Quatf(self.parse_tuple::<_, 4>()?.into()),
            Type::Quatd => sdf::Value::Quatd(self.parse_tuple::<_, 4>()?.into()),

            // String and tokens
            Type::String => sdf::Value::String(self.fetch_str()?.to_owned()),
            Type::Token => sdf::Value::Token(self.fetch_str()?.to_owned()),

            Type::StringVec => sdf::Value::StringVec(self.parse_array()?),
            Type::TokenVec => sdf::Value::TokenVec(self.parse_array()?),

            _ => bail!("Unimplemented data type: {ty:?}"),
        };

        Ok(value)
    }

    /// Parse basic types and roles.
    /// See
    /// - <https://openusd.org/dev/api/_usd__page__datatypes.html#Usd_Basic_Datatypes>
    /// - <https://openusd.org/dev/api/_usd__page__datatypes.html#Usd_Roles>
    fn parse_data_type(ty: &str) -> Result<Type> {
        let data_type = match ty {
            // Bool
            "bool" => Type::Bool,
            "bool[]" => Type::BoolVec,

            // Ints
            "uchar" => Type::Uchar,
            "uchar[]" => Type::UcharVec,
            "int" => Type::Int,
            "int2" => Type::Int2,
            "int3" => Type::Int3,
            "int4" => Type::Int4,
            "int[]" => Type::IntVec,
            "int2[]" => Type::Int2Vec,
            "int3[]" => Type::Int3Vec,
            "int4[]" => Type::Int4Vec,
            "uint" => Type::Uint,
            "int64" => Type::Int64,
            "uint64" => Type::Uint64,

            // Half
            "half" => Type::Half,
            "half2" | "texCoord2h" => Type::Half2,
            "half3" | "point3h" | "normal3h" | "vector3h" | "color3h" | "texCoord3h" => Type::Half3,
            "half4" | "color4h" => Type::Half4,
            "half[]" => Type::HalfVec,
            "half2[]" | "texCoord2h[]" => Type::Half2Vec,
            "half3[]" | "point3h[]" | "normal3h[]" | "vector3h[]" | "color3h[]" | "texCoord3h[]" => Type::Half3Vec,
            "half4[]" | "color4h[]" => Type::Half4Vec,

            // Float
            "float" => Type::Float,
            "float2" | "texCoord2f" => Type::Float2,
            "float3" | "point3f" | "normal3f" | "vector3f" | "color3f" | "texCoord3f" => Type::Float3,
            "float4" | "color4f" => Type::Float4,
            "float[]" => Type::FloatVec,
            "float2[]" | "texCoord2f[]" => Type::Float2Vec,
            "float3[]" | "point3f[]" | "normal3f[]" | "vector3f[]" | "color3f[]" | "texCoord3f[]" => Type::Float3Vec,
            "float4[]" | "color4f[]" => Type::Float4Vec,

            // Double
            "double" => Type::Double,
            "double2" | "texCoord2d" => Type::Double2,
            "double3" | "point3d" | "normal3d" | "vector3d" | "color3d" | "texCoord3d" => Type::Double3,
            "double4" | "color4d" => Type::Double4,
            "double[]" => Type::DoubleVec,
            "double2[]" | "texCoord2d[]" => Type::Double2Vec,
            "double3[]" | "point3d[]" | "normal3d[]" | "vector3d[]" | "color3d[]" | "texCoord3d[]" => Type::Double3Vec,
            "double4[]" => Type::Double4Vec,

            // Matrices
            "matrix2d" => Type::Matrix2d,
            "matrix3d" => Type::Matrix3d,
            "matrix4d" | "frame4d" => Type::Matrix4d,

            // Quats
            "quatd" => Type::Quatd,
            "quatf" => Type::Quatf,
            "quath" => Type::Quath,

            // String, tokens
            "string" | "token" => Type::String,
            "string[]" | "token[]" => Type::TokenVec,
            "asset" => Type::Asset,
            "asset[]" => Type::AssetVec,

            _ => bail!("Unsupported data type: {ty}"),
        };

        Ok(data_type)
    }

    /// Parse single token as `T` which can be deserialized from string (such as `int`, `float`, etc).
    fn parse_token<T: FromStr>(&mut self) -> Result<T>
    where
        <T as FromStr>::Err: std::fmt::Debug,
    {
        let token = self.fetch_next()?;
        let value_str = match token {
            Token::Number(s) | Token::Identifier(s) | Token::String(s) | Token::NamespacedIdentifier(s) => s,
            _ => bail!("Expected a number, identifier, or string, got {token:?}"),
        };
        let value = T::from_str(value_str)
            .map_err(|err| anyhow!("Failed to parse {} from '{}': {:?}", type_name::<T>(), value_str, err))?;

        Ok(value)
    }

    /// Parse USD's flexible boolean literal forms (identifiers, numeric, or string).
    fn parse_bool(&mut self) -> Result<bool> {
        let token = self.fetch_next()?;
        match token {
            Token::Identifier(value) | Token::NamespacedIdentifier(value) => match value {
                "true" => Ok(true),
                "false" => Ok(false),
                other => bail!("Unexpected identifier for bool literal: {other}"),
            },
            Token::Number(value) => {
                let parsed = value.parse::<f64>().context("Unable to parse numeric bool")?;
                if parsed == 0.0 {
                    Ok(false)
                } else if parsed == 1.0 {
                    Ok(true)
                } else {
                    bail!("Numeric bool literals must be 0 or 1, got {value}");
                }
            }
            Token::String(value) => match value {
                "true" => Ok(true),
                "false" => Ok(false),
                other => bail!("Unexpected string for bool literal: {other}"),
            },
            other => bail!("Unexpected token for bool literal: {other:?}"),
        }
    }

    /// Parse an array of booleans, reusing the permissive literal parsing rules.
    fn parse_bool_array(&mut self) -> Result<Vec<bool>> {
        let mut out = Vec::new();
        self.parse_array_fn(|this| {
            out.push(this.parse_bool()?);
            Ok(())
        })?;
        Ok(out)
    }

    fn parse_asset_path(&mut self) -> Result<String> {
        let token = self.fetch_next()?;
        token
            .try_as_asset_ref()
            .map(|value| value.to_owned())
            .ok_or_else(|| anyhow!("Asset reference expected"))
    }

    fn parse_asset_path_array(&mut self) -> Result<Vec<String>> {
        let mut result = Vec::new();
        self.parse_array_fn(|this| {
            result.push(this.parse_asset_path()?);
            Ok(())
        })?;
        Ok(result)
    }

    /// Parse `subLayers` entries along with their optional `(offset/scale)` metadata.
    fn parse_sublayers(&mut self) -> Result<(sdf::Value, sdf::Value)> {
        let mut sublayers = Vec::new();
        let mut sublayer_offsets = Vec::new();

        self.parse_array_fn(|this| {
            let asset_path = this
                .fetch_next()?
                .try_as_asset_ref()
                .ok_or_else(|| anyhow!("Asset ref expected, got {:?}", this.peek_next()))?;
            sublayers.push(asset_path.to_string());

            let mut layer_offset = sdf::LayerOffset::default();
            if let Some(Ok(Token::Punctuation('('))) = this.peek_next() {
                let mut offset = None;
                let mut scale = None;

                this.parse_seq_fn(';', |this, _| {
                    let token = this.fetch_next()?;
                    this.ensure_pun('=')?;
                    let value = this.parse_value(Type::Double)?;
                    match token {
                        Token::Offset => {
                            ensure!(offset.is_none(), "offset specified twice");
                            offset = Some(value);
                        }
                        Token::Scale => {
                            ensure!(scale.is_none(), "scale specified twice");
                            scale = Some(value);
                        }
                        _ => bail!("Unexpected token type: {token:?}"),
                    }
                    Ok(())
                })?;

                if let Some(offset) = offset {
                    layer_offset.offset = offset.try_as_double().context("Unexpected offset type, want double")?;
                }
                if let Some(scale) = scale {
                    layer_offset.scale = scale.try_as_double().context("")?;
                }
            }
            sublayer_offsets.push(layer_offset);
            Ok(())
        })?;

        debug_assert_eq!(sublayers.len(), sublayer_offsets.len());

        Ok((
            sdf::Value::StringVec(sublayers),
            sdf::Value::LayerOffsetVec(sublayer_offsets),
        ))
    }

    /// Generic array parser that delegates element parsing while handling delimiters.
    fn parse_array_fn(&mut self, mut read_elements: impl FnMut(&mut Self) -> Result<()>) -> Result<()> {
        self.ensure_pun('[').context("Array must start with [")?;

        let mut index = 0;
        loop {
            if self.peek_next().map(|r| r.as_ref().ok()) == Some(Some(&Token::Punctuation(']'))) {
                self.fetch_next()?;
                break;
            }

            read_elements(self).with_context(|| format!("Unable to read array element {index}"))?;
            index += 1;

            match self.fetch_next()? {
                Token::Punctuation(',') => continue,
                Token::Punctuation(']') => break,
                t => bail!("Either comma or closing bracket expected after value, got: {t:?}"),
            }
        }
        Ok(())
    }

    /// Parse delimiter-separated sequences like `(a, b)` or `(offset = ...; scale = ...)`.
    fn parse_seq_fn(
        &mut self,
        delim: char,
        mut read_element: impl FnMut(&mut Self, usize) -> Result<()>,
    ) -> Result<()> {
        self.ensure_pun('(').context("Open brace expected")?;

        let mut index = 0;
        loop {
            if self.peek_next().map(|r| r.as_ref().ok()) == Some(Some(&Token::Punctuation(')'))) {
                self.fetch_next()?;
                break;
            }

            read_element(self, index).with_context(|| format!("Unable to read element {index}"))?;
            index += 1;

            match self.fetch_next()? {
                Token::Punctuation(')') => break,
                Token::Punctuation(d) if d == delim => continue,
                t => bail!("Unexpected token between (): {t:?}"),
            }
        }
        Ok(())
    }

    /// Parse fixed-size tuples, preserving order and surfacing contextual errors.
    fn parse_tuple<T, const N: usize>(&mut self) -> Result<[T; N]>
    where
        T: FromStr,
        <T as FromStr>::Err: Debug,
    {
        let mut result: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
        self.parse_seq_fn(',', |this, i| {
            result[i] = MaybeUninit::new(this.parse_token::<T>()?);
            Ok(())
        })?;
        let result = unsafe { std::mem::transmute_copy::<_, [T; N]>(&result) };
        Ok(result)
    }

    /// Parse array or array of tuples.
    fn parse_array<T>(&mut self) -> Result<Vec<T>>
    where
        T: FromStr + Default,
        <T as FromStr>::Err: Debug,
    {
        let mut out = Vec::new();
        self.parse_array_fn(|this| {
            out.push(this.parse_token::<T>()?);
            Ok(())
        })?;
        Ok(out)
    }

    /// Parse array of tuples.
    fn parse_array_of_tuples<T, const N: usize>(&mut self) -> Result<Vec<T>>
    where
        T: FromStr,
        <T as FromStr>::Err: Debug,
    {
        let mut out = Vec::new();
        self.parse_array_fn(|this| {
            out.extend(this.parse_tuple::<T, N>()?);
            Ok(())
        })?;
        Ok(out)
    }

    fn compute_line_offsets(source: &str) -> Vec<usize> {
        let mut offsets = Vec::new();
        offsets.push(0);
        for (idx, ch) in source.char_indices() {
            if ch == '\n' {
                offsets.push(idx + ch.len_utf8());
            }
        }
        if offsets.last().copied().unwrap_or_default() != source.len() {
            offsets.push(source.len());
        }
        offsets
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Type {
    Bool,
    BoolVec,
    Uchar,
    UcharVec,
    Int,
    Int2,
    Int3,
    Int4,
    IntVec,
    Int2Vec,
    Int3Vec,
    Int4Vec,
    Uint,
    Int64,
    Uint64,
    Half,
    Half2,
    Half3,
    Half4,
    HalfVec,
    Half2Vec,
    Half3Vec,
    Half4Vec,
    Float,
    Float2,
    Float3,
    Float4,
    FloatVec,
    Float2Vec,
    Float3Vec,
    Float4Vec,
    Double,
    Double2,
    Double3,
    Double4,
    DoubleVec,
    Double2Vec,
    Double3Vec,
    Double4Vec,
    Quath,
    Quatf,
    Quatd,
    String,
    Token,
    Asset,
    StringVec,
    TokenVec,
    AssetVec,
    Matrix2d,
    Matrix3d,
    Matrix4d,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;

    #[test]
    fn parse_empty_array() {
        let mut parser = Parser::new("[]");
        let array = parser.parse_array::<u32>().unwrap();
        assert!(array.is_empty());
    }

    #[test]
    fn parse_tuple() {
        let mut parser = Parser::new("(1, 2, 3)");
        let result = parser.parse_tuple::<u32, 3>().unwrap();
        assert_eq!(result, [1_u32, 2, 3]);
    }

    #[test]
    fn parse_array() {
        let mut parser = Parser::new("[1, 2, 3]");
        let result = parser.parse_array::<u32>().unwrap();
        assert_eq!(result, vec![1_u32, 2, 3]);
    }

    #[test]
    fn parse_array_of_tuples() {
        let mut parser = Parser::new("[(1, 2), (3, 4)]");
        let result = parser.parse_array_of_tuples::<u32, 2>().unwrap();
        assert_eq!(result, vec![1_u32, 2, 3, 4]);
    }

    #[test]
    // Verifies pseudo-root parsing captures doc strings and layer metadata from the header.
    fn parse_pseudo_root() {
        let mut parser = Parser::new(
            r#"
            #usda 1.0
            (
                doc = """test string"""

                upAxis = "Y"
                metersPerUnit = 0.01

                defaultPrim = "World"
            )
            "#,
        );

        let pseudo_root = parser.read_pseudo_root().unwrap();

        assert!(pseudo_root
            .fields
            .get("doc")
            .and_then(|v| v.try_as_string_ref())
            .unwrap()
            .eq("test string"));

        assert!(pseudo_root
            .fields
            .get("upAxis")
            .and_then(|v| v.try_as_token_ref())
            .unwrap()
            .eq("Y"));
    }

    #[test]
    // Confirms nested prim traversal builds the expected child hierarchy.
    fn parse_nested_prims() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Xform "Forest_set"
{
    def Xform "Outskirts"
    {
        # More deeply nested groups, bottoming out at references to other assemblies and components
    }

    def Xform "Glade"
    {
        # More deeply nested groups, bottoming out at references to other assemblies and components
    }
}
            "#,
        );

        let data = parser.parse().unwrap();

        assert!(data.contains_key(&sdf::Path::abs_root()));

        let pseudo_root = data.get(&sdf::path("/").unwrap()).unwrap();
        assert_eq!(pseudo_root.ty, sdf::SpecType::PseudoRoot);
        let prim_children = pseudo_root.fields.get("primChildren").unwrap().to_owned();
        assert_eq!(
            prim_children.try_as_token_vec().unwrap(),
            vec![String::from("Forest_set")]
        );

        let forest_set_prim = data.get(&sdf::path("/Forest_set").unwrap()).unwrap();
        let prim_children = forest_set_prim.fields.get("primChildren").unwrap().to_owned();
        assert_eq!(
            prim_children.try_as_token_vec().unwrap(),
            vec![String::from("Outskirts"), String::from("Glade")]
        );

        assert!(data.contains_key(&sdf::path("/Forest_set/Outskirts").unwrap()));
        assert!(data.contains_key(&sdf::path("/Forest_set/Glade").unwrap()));
    }

    #[test]
    // Ensures attribute metadata blocks are captured on the owning spec.
    fn parse_attribute_metadata_interpolation() {
        let mut parser = Parser::new(
            r#"
#usda 1.0


def Mesh "M"
{
    normal3f[] normals = [(0, 0, 1)] (
        interpolation = "faceVarying"
    )
}
            "#,
        );

        let data = parser.parse().unwrap();
        let normals = data.get(&sdf::path("/M.normals").unwrap()).unwrap();

        let interpolation = normals
            .fields
            .get("interpolation")
            .expect("missing interpolation metadata")
            .try_as_string_ref()
            .expect("interpolation metadata must be a string");

        assert_eq!(interpolation, "faceVarying");
    }

    #[test]
    // Verifies the parser tolerates custom/asset/connect syntax and filters unsanitized props.
    fn parse_unsanitized_attributes() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Shader "Image_Texture"
{
    custom token info:id = "UsdUVTexture"
    uniform bool doubleSided = 1
    asset inputs:file = @./texture.png@
    token outputs:surface.connect = </Image_Texture.outputs:surface>
    token outputs:surface
}
            "#,
        );

        let data = parser.parse().unwrap();
        let shader = data.get(&sdf::path("/Image_Texture").unwrap()).unwrap();

        let double_sided = data.get(&sdf::path("/Image_Texture.doubleSided").unwrap()).unwrap();
        assert!(matches!(
            double_sided.fields.get(sdf::schema::FieldKey::Default.as_str()),
            Some(sdf::Value::Bool(true))
        ));

        let info_spec = data.get(&sdf::path("/Image_Texture.info:id").unwrap()).unwrap();
        assert!(matches!(
            info_spec.fields.get(sdf::schema::FieldKey::Custom.as_str()),
            Some(sdf::Value::Bool(true))
        ));

        let file_spec = data.get(&sdf::path("/Image_Texture.inputs:file").unwrap()).unwrap();
        assert!(matches!(
            file_spec
                .fields
                .get(sdf::schema::FieldKey::Default.as_str()),
            Some(sdf::Value::AssetPath(path)) if path == "./texture.png"
        ));

        assert!(!data.contains_key(&sdf::path("/Image_Texture.outputs:surface.connect").unwrap()));
        assert!(!data.contains_key(&sdf::path("/Image_Texture.outputs:surface").unwrap()));

        let props = shader
            .fields
            .get(sdf::schema::ChildrenKey::PropertyChildren.as_str())
            .and_then(|value| match value {
                sdf::Value::TokenVec(tokens) => Some(tokens.clone()),
                _ => None,
            })
            .unwrap_or_default();
        assert!(props.contains(&"info:id".to_string()));
        assert!(props.contains(&"doubleSided".to_string()));
        assert!(props.contains(&"inputs:file".to_string()));
    }

    #[test]
    fn parse_reports_error_span_for_invalid_pseudo_root() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let fixture_path = manifest_dir.join("fixtures/invalid_pseudo_root.usda");
        let data =
            fs::read_to_string(&fixture_path).expect("read invalid pseudo-root fixture content");

        let mut parser = Parser::new(&data);
        let err = parser.parse().expect_err("parser should fail for malformed pseudo-root");
        let highlight = parser
            .last_error_highlight()
            .expect("parser should record error highlight");

        let message = format!("{err:#}");
        assert!(
            message.contains("Unable to parse pseudo root"),
            "error should mention pseudo-root parse failure, got: {message}"
        );
        assert_eq!(highlight.line, 4, "unexpected error line");
        assert_eq!(highlight.column, 5, "unexpected error column");
        assert!(
            highlight.line_text.trim_start().starts_with('='),
            "line text should contain '=' token, got: {:?}",
            highlight.line_text
        );
        assert_eq!(
            highlight.pointer_line, "    ^",
            "caret should align with offending token"
        );
    }

    #[test]
    // Exercises a wide set of attribute types to validate scalar/array decoding.
    fn parse_attributes() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Xform "World"
{
    bool flipNormals = true
    bool[] boolArray = [true, true, false, false, true, false]

    uchar singleChar = 128
    uchar[] chars = [128, 129, 130, 131, 132, 133, 134, 135, 136, 137]

    float2 clippingRange = (1, 10000000)
    float3 diffuseColor = (0.18, 0.18, 0.18)
    float4[] clippingPlanes = []

    int[] faceVertexCounts = [1, 2, 3, 4, 5, 6]
    point3f[] points = [(1.0, -2.0, 3.0), (3.0, 5.0, 6.0)]

    normal3f[] normals = [(0, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 0), (0, 0, 1), (1, 0, 0)]

    double3 xformOp:rotateXYZ = (0, 0, 0)
	double3 xformOp:scale = (1, 1, 1)
    double3 xformOp:translate = (0, 1, 0)

    uniform token[] xformOpOrder = ["xformOp:translate", "xformOp:rotateXYZ"]
}
            "#,
        );

        let data = parser.parse().unwrap();

        let world = data.get(&sdf::path("/World").unwrap()).unwrap();

        let props = world
            .fields
            .get("properties")
            .unwrap()
            .to_owned()
            .try_as_token_vec()
            .unwrap();

        assert_eq!(
            props,
            [
                "flipNormals",
                "boolArray",
                "singleChar",
                "chars",
                "clippingRange",
                "diffuseColor",
                "clippingPlanes",
                "faceVertexCounts",
                "points",
                "normals",
                "xformOp:rotateXYZ",
                "xformOp:scale",
                "xformOp:translate",
                "xformOpOrder"
            ]
            .into_iter()
            .map(String::from)
            .collect::<Vec<_>>()
        );

        let normals = data.get(&sdf::path("/World.normals").unwrap()).unwrap();
        let value = normals.fields.get("default").unwrap();

        assert_eq!(
            &[
                0_f32, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 1.0, 0.0,
                0.0
            ],
            value.try_as_vec_3f_ref().unwrap().as_slice()
        );

        let order = data.get(&sdf::path("/World.xformOpOrder").unwrap()).unwrap();

        assert_eq!(
            order
                .fields
                .get("default")
                .unwrap()
                .to_owned()
                .try_as_token_vec()
                .unwrap(),
            vec![String::from("xformOp:translate"), String::from("xformOp:rotateXYZ")]
        )
    }

    #[test]
    // Validates sublayer parsing captures offsets, scales, and defaults when missing.
    fn test_parse_layer_offsets() {
        let mut parser = Parser::new(
            r#"
[
    @./someAnimation.usd@ (offset = 10; scale = 0.5),
    @./another.usd@
]
            "#,
        );

        let (sublayers, offsets) = parser.parse_sublayers().unwrap();

        let sublayers = sublayers.try_as_string_vec().unwrap();
        assert_eq!(
            sublayers,
            vec!["./someAnimation.usd".to_string(), "./another.usd".to_string()]
        );

        let offsets = offsets.try_as_layer_offset_vec().unwrap();

        assert_eq!(offsets[0].offset, 10.0);
        assert_eq!(offsets[0].scale, 0.5);

        // Default one
        assert_eq!(offsets[1].offset, 0.0);
        assert_eq!(offsets[1].scale, 1.0);
    }

    #[test]
    // Ensures pseudo-root parsing records sublayer paths and their offsets.
    fn test_parse_sublayers_in_pseudo_root() {
        let mut parser = Parser::new(
            r#"
#usda 1.0
(
    subLayers = [
        @./someAnimation.usd@ (offset = 10; scale = 0.5),
        @./another.usd@
    ]
)
            "#,
        );

        let data = parser.parse().unwrap();
        let pseudo_root = data.get(&sdf::Path::abs_root()).unwrap();

        let sublayers = pseudo_root
            .fields
            .get(FieldKey::SubLayers.as_str())
            .unwrap()
            .clone()
            .try_as_string_vec()
            .unwrap();
        assert_eq!(
            sublayers,
            vec!["./someAnimation.usd".to_string(), "./another.usd".to_string()]
        );

        let offsets = pseudo_root
            .fields
            .get(FieldKey::SubLayerOffsets.as_str())
            .unwrap()
            .clone()
            .try_as_layer_offset_vec()
            .unwrap();

        assert_eq!(offsets[0].offset, 10.0);
        assert_eq!(offsets[0].scale, 0.5);

        // Default one
        assert_eq!(offsets[1].offset, 0.0);
        assert_eq!(offsets[1].scale, 1.0);
    }

    #[test]
    // Checks prim metadata list ops for apiSchemas and the active flag.
    fn parse_prim_metadata_api_schemas() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Mesh "Mesh_001" (
    active = true
    prepend apiSchemas = ["MaterialBindingAPI"]
)
{
}
            "#,
        );

        let data = parser.parse().unwrap();
        let mesh = data.get(&sdf::path("/Mesh_001").unwrap()).unwrap();

        assert!(mesh
            .fields
            .get(FieldKey::Active.as_str())
            .unwrap()
            .to_owned()
            .try_as_bool()
            .unwrap());

        let api = mesh
            .fields
            .get("apiSchemas")
            .unwrap()
            .to_owned()
            .try_as_token_list_op()
            .unwrap();

        assert!(api.explicit_items.is_empty());
        assert_eq!(api.prepended_items, vec![String::from("MaterialBindingAPI")]);
    }

    #[test]
    // Ensures prim reference metadata is parsed with asset/prim path and default offsets.
    fn parse_prim_metadata_references() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Mesh "visual" (
    references = @./visual.usd@</visual>
)
{
}
            "#,
        );

        let data = parser.parse().unwrap();
        let mesh = data.get(&sdf::path("/visual").unwrap()).unwrap();

        let references = mesh
            .fields
            .get(FieldKey::References.as_str())
            .unwrap()
            .to_owned()
            .try_as_reference_list_op()
            .unwrap();

        assert!(references.explicit);
        assert_eq!(references.explicit_items.len(), 1);

        let reference = &references.explicit_items[0];
        assert_eq!(reference.asset_path, "./visual.usd");
        assert_eq!(reference.prim_path.as_str(), "/visual");
        assert_eq!(reference.layer_offset.offset, 0.0);
        assert_eq!(reference.layer_offset.scale, 1.0);
    }
}
