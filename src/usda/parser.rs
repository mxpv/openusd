use anyhow::{anyhow, bail, ensure, Context, Result};
use logos::Logos;
use std::iter::Peekable;
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
    iter: Peekable<logos::SpannedIter<'a, Token<'a>>>,
    source: &'a str,
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
            iter: Token::lexer(data).spanned().peekable(),
            source: data,
            last_span: None,
        }
    }

    /// Returns a highlight for the most recent token span processed by the parser.
    pub fn last_error_highlight(&self) -> Option<ErrorHighlight> {
        self.last_span.clone().and_then(|span| self.highlight_for_span(span))
    }

    fn highlight_for_span(&self, span: Range<usize>) -> Option<ErrorHighlight> {
        if self.source.is_empty() {
            return None;
        }
        let source = self.source;

        let mut offset = span.start.min(source.len());
        if offset == source.len() && offset > 0 {
            offset -= 1;
        }

        // Calculate line and column by counting newlines up to the offset
        let mut line = 1;
        let mut line_start = 0;

        for (idx, ch) in source[..offset].char_indices() {
            if ch == '\n' {
                line += 1;
                line_start = idx + ch.len_utf8();
            }
        }

        // Find the end of the current line
        let line_end = source[line_start..]
            .find('\n')
            .map(|pos| line_start + pos)
            .unwrap_or(source.len());

        let line_text = source[line_start..line_end].trim_end_matches(['\r', '\n']).to_string();

        // Calculate column (character count from line start to offset)
        let mut column = 1;
        for ch in source[line_start..offset].chars() {
            if ch == '\n' || ch == '\r' {
                break;
            }
            column += 1;
        }

        // Build pointer line
        let mut pointer_line = String::new();
        for ch in source[line_start..offset].chars() {
            if ch == '\n' || ch == '\r' {
                break;
            }
            pointer_line.push(if ch == '\t' { '\t' } else { ' ' });
        }
        pointer_line.push('^');

        Some(ErrorHighlight {
            line,
            column,
            line_text,
            pointer_line,
        })
    }

    #[inline]
    fn fetch_next(&mut self) -> Result<Token<'a>> {
        let (token, span) = self.iter.next().context("Unexpected end of tokens")?;
        self.last_span = Some(span);
        token.map_err(|e| anyhow!("Logos error: {e:?}"))
    }

    #[inline]
    fn peek_next(&mut self) -> Option<&LexResult<'a>> {
        self.iter.peek().map(|(token, _)| token)
    }

    #[inline]
    fn is_next(&mut self, expected: Token) -> bool {
        matches!(self.peek_next(), Some(Ok(t)) if *t == expected)
    }

    /// Consume the next token if it matches, returning whether it was consumed.
    #[inline]
    fn try_consume(&mut self, expected: Token) -> bool {
        if self.is_next(expected) {
            let _ = self.fetch_next();
            true
        } else {
            false
        }
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

    fn fetch_str(&mut self) -> Result<&'a str> {
        match self.fetch_next()? {
            Token::String(s) => Ok(s),
            other => bail!("Unexpected token {other:?} (want String)"),
        }
    }

    /// Consumes and returns a path reference (`<...>`) token, or errors.
    fn fetch_path_ref(&mut self) -> Result<&'a str> {
        match self.fetch_next()? {
            Token::PathRef(s) => Ok(s),
            other => bail!("Path reference expected, got {other:?}"),
        }
    }

    /// Consumes and returns an identifier token, or errors.
    fn expect_identifier(&mut self) -> Result<&'a str> {
        match self.fetch_next()? {
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => Ok(s),
            other => bail!("expected identifier, got {other:?}"),
        }
    }

    /// Consumes and returns an identifier or keyword-as-name token.
    ///
    /// Unlike `expect_identifier`, this also accepts keyword tokens (e.g. `rel`, `kind`)
    /// via `keyword_lexeme`, allowing them to be used as property or relationship names.
    fn expect_name(&mut self) -> Result<&'a str> {
        let token = self.fetch_next()?;
        match token {
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => Ok(s),
            other => other
                .keyword_lexeme()
                .ok_or_else(|| anyhow!("expected name, got {other:?}")),
        }
    }

    /// Tries to consume a list-op keyword (`add`, `append`, `prepend`, `delete`, `reorder`).
    fn try_list_op(&mut self) -> Option<Token<'a>> {
        match self.peek_next() {
            Some(Ok(Token::Add | Token::Append | Token::Prepend | Token::Delete | Token::Reorder)) => {
                self.fetch_next().ok()
            }
            _ => None,
        }
    }

    /// Parses a single item or a bracketed array of items.
    fn one_or_list<T>(&mut self, mut parse: impl FnMut(&mut Self) -> Result<T>) -> Result<Vec<T>> {
        if self.try_consume(Token::None) {
            return Ok(Vec::new());
        }
        if self.is_next(Token::Punctuation('[')) {
            let mut out = Vec::new();
            self.parse_block('[', ']', |this| {
                out.push(parse(this)?);
                Ok(())
            })?;
            Ok(out)
        } else {
            Ok(vec![parse(self)?])
        }
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

        if !root_children.is_empty() {
            pseudo_root_spec.add(ChildrenKey::PrimChildren, sdf::Value::TokenVec(root_children));
        }
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
        ensure!(version.starts_with("1.0"), "Unsupported USDA version: {version:?}");

        let mut root = sdf::Spec::new(sdf::SpecType::PseudoRoot);

        if !self.is_next(Token::Punctuation('(')) {
            return Ok(root);
        }

        const KNOWN_PROPS: &[(&str, TypeInfo)] = &[
            (FieldKey::DefaultPrim.as_str(), TypeInfo::scalar(Type::Token)),
            (FieldKey::StartTimeCode.as_str(), TypeInfo::scalar(Type::Double)),
            (FieldKey::HasOwnedSubLayers.as_str(), TypeInfo::scalar(Type::Bool)),
            ("doc", TypeInfo::scalar(Type::String)),
            ("endTimeCode", TypeInfo::scalar(Type::Double)),
            ("framesPerSecond", TypeInfo::scalar(Type::Double)),
            ("metersPerUnit", TypeInfo::scalar(Type::Double)),
            ("timeCodesPerSecond", TypeInfo::scalar(Type::Double)),
            ("upAxis", TypeInfo::scalar(Type::Token)),
        ];

        self.parse_block('(', ')', |this| {
            let next = this.fetch_next().context("Unable to fetch next pseudo root property")?;

            match next {
                Token::String(str) => {
                    root.add(FieldKey::Comment, str);
                }
                Token::Doc => {
                    this.ensure_pun('=')?;
                    let value = this.fetch_str()?;
                    root.add(FieldKey::Documentation, value);
                }
                Token::SubLayers => {
                    this.ensure_pun('=')?;
                    let (sublayers, sublayer_offsets) = this.parse_sublayers().context("Unable to parse subLayers")?;
                    root.add(FieldKey::SubLayers, sublayers);
                    root.add(FieldKey::SubLayerOffsets, sublayer_offsets);
                }
                Token::Relocates => {
                    this.ensure_pun('=')?;
                    let pairs = this.parse_relocates_dict().context("Unable to parse relocates")?;
                    root.add(FieldKey::LayerRelocates, sdf::Value::Relocates(pairs));
                }
                Token::Identifier(name) => {
                    this.ensure_pun('=')?;
                    if let Some(&(known_name, info)) = KNOWN_PROPS.iter().find(|(n, _)| *n == name) {
                        let value = this
                            .parse_value(info)
                            .with_context(|| format!("Unable to parse value for {known_name}"))?;
                        root.add(known_name, value);
                    } else {
                        let value = this
                            .parse_property_metadata_value()
                            .with_context(|| format!("Unable to parse pseudo root metadata value for {name}"))?;
                        root.add(name, value);
                    }
                }
                _ => bail!("Unexpected token {next:?}"),
            }
            Ok(())
        })?;

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
        if let Token::Identifier(prim_type) = name_token {
            spec.add(FieldKey::TypeName, sdf::Value::Token(prim_type.to_string()));
            name_token = self.fetch_next()?;
        }

        let Token::String(name) = name_token else {
            bail!("Expected prim name string, got {name_token:?}");
        };
        parent_children.push(name.to_string());
        let prim_path = current_path.append_path(name)?;

        let mut properties = Vec::new();

        // Optional metadata block.
        if self.is_next(Token::Punctuation('(')) {
            self.parse_block('(', ')', |this| {
                this.read_prim_metadata_entry(&mut spec)
                    .context("Unable to parse prim metadata entry")
            })?;
        }

        let (children, props, variant_sets) = self.read_prim_body(&prim_path, data)?;
        if !children.is_empty() {
            spec.add(ChildrenKey::PrimChildren, sdf::Value::TokenVec(children));
        }
        properties.extend(props);

        spec.add(FieldKey::Specifier, sdf::Value::Specifier(specifier));
        if !properties.is_empty() {
            spec.add(ChildrenKey::PropertyChildren, sdf::Value::TokenVec(properties));
        }
        if !variant_sets.is_empty() {
            spec.add(ChildrenKey::VariantSetChildren, sdf::Value::TokenVec(variant_sets));
        }
        data.insert(prim_path, spec);

        Ok(())
    }

    /// Parse the body of a prim or variant (`{ ... }`).
    ///
    /// Returns the child prim names and property names found in the body.
    fn read_prim_body(
        &mut self,
        path: &sdf::Path,
        data: &mut HashMap<sdf::Path, sdf::Spec>,
    ) -> Result<(Vec<String>, Vec<String>, Vec<String>)> {
        let mut children = Vec::new();
        let mut properties = Vec::new();
        let mut suffixed_properties = Vec::<String>::new();
        let mut variant_sets = Vec::new();

        self.parse_block('{', '}', |this| {
            match this
                .peek_next()
                .context("Unexpected end of prim body")?
                .as_ref()
                .map_err(|e| anyhow!("{e:?}"))?
            {
                Token::Def | Token::Over | Token::Class => {
                    this.read_prim(path, &mut children, data)?;
                }
                Token::VariantSet => {
                    let name = this.read_variant_set(path, data)?;
                    variant_sets.push(name);
                }
                Token::Rel => {
                    this.fetch_next()?;
                    this.read_relationship(path, false, &mut properties, data, None)?;
                }
                Token::Reorder => {
                    this.read_reorder(path, data)?;
                }
                _ => {
                    this.read_attribute(path, &mut properties, &mut suffixed_properties, data)?;
                }
            }
            Ok(())
        })?;

        // Append properties that were only declared via suffixed forms
        // (e.g. `.connect`, `.timeSamples`) and never had a bare declaration.
        for name in suffixed_properties {
            push_unique(&mut properties, &name);
        }

        Ok((children, properties, variant_sets))
    }

    /// Parse `reorder nameChildren = [...]` or `reorder properties = [...]`.
    ///
    /// These statements set the `primOrder` or `propertyOrder` fields on the
    /// owning prim spec, controlling child/property display order.
    fn read_reorder(&mut self, path: &sdf::Path, data: &mut HashMap<sdf::Path, sdf::Spec>) -> Result<()> {
        self.fetch_next()?; // consume `reorder`

        let token = self
            .fetch_next()
            .context("Expected 'nameChildren' or 'properties' after 'reorder'")?;
        let field_key = match token {
            Token::NameChildren => FieldKey::PrimOrder,
            Token::Properties => FieldKey::PropertyOrder,
            other => bail!("Unsupported reorder target: {other:?}"),
        };

        self.ensure_pun('=')?;

        let names = self.one_or_list(|this| Ok(this.fetch_str()?.to_owned()))?;
        if let Some(spec) = data.get_mut(path) {
            spec.add(field_key, sdf::Value::TokenVec(names));
        } else {
            let mut spec = sdf::Spec::new(sdf::SpecType::Prim);
            spec.add(field_key, sdf::Value::TokenVec(names));
            data.insert(path.clone(), spec);
        }

        Ok(())
    }

    /// Parse a `variantSet "name" = { "variant1" (...) { ... } ... }` block.
    ///
    /// Each variant inside the set is represented as a child prim under a variant set
    /// spec in the scene hierarchy: `/{prim}{vset=name}{variant}`.
    fn read_variant_set(&mut self, prim_path: &sdf::Path, data: &mut HashMap<sdf::Path, sdf::Spec>) -> Result<String> {
        self.fetch_next()?; // consume `variantSet`

        let name = self.fetch_str().context("Expected variant set name")?.to_string();
        self.ensure_pun('=')?;

        // Create the variant set spec.
        let vset_path = sdf::Path::new(&format!("{}{{{name}=}}", prim_path))?;
        let mut vset_spec = sdf::Spec::new(sdf::SpecType::VariantSet);
        let mut variant_children = Vec::new();

        // Parse each variant: "VariantName" (...) { ... }
        self.parse_block('{', '}', |this| {
            let variant_name = this.fetch_str().context("Expected variant name")?.to_string();

            variant_children.push(variant_name.clone());

            let variant_path = sdf::Path::new(&format!("{}{{{name}={variant_name}}}", prim_path))?;
            let mut variant_spec = sdf::Spec::new(sdf::SpecType::Variant);

            // Optional metadata block.
            if this.is_next(Token::Punctuation('(')) {
                this.parse_block('(', ')', |this| {
                    this.read_prim_metadata_entry(&mut variant_spec)
                        .context("Unable to parse variant metadata entry")
                })?;
            }

            // Variant body.
            let (children, properties, variant_sets) = this.read_prim_body(&variant_path, data)?;
            if !children.is_empty() {
                variant_spec.add(ChildrenKey::PrimChildren, sdf::Value::TokenVec(children));
            }
            if !properties.is_empty() {
                variant_spec.add(ChildrenKey::PropertyChildren, sdf::Value::TokenVec(properties));
            }
            if !variant_sets.is_empty() {
                variant_spec.add(ChildrenKey::VariantSetChildren, sdf::Value::TokenVec(variant_sets));
            }
            data.insert(variant_path, variant_spec);
            Ok(())
        })?;

        vset_spec.add(ChildrenKey::VariantChildren, sdf::Value::TokenVec(variant_children));
        data.insert(vset_path, vset_spec);

        Ok(name)
    }

    /// Merge a spec's fields into an existing spec at the given path, or insert it.
    fn merge_spec(data: &mut HashMap<sdf::Path, sdf::Spec>, path: sdf::Path, spec: sdf::Spec) {
        use std::collections::hash_map::Entry;
        match data.entry(path) {
            Entry::Occupied(mut e) => e.get_mut().extend_from(spec),
            Entry::Vacant(e) => {
                e.insert(spec);
            }
        }
    }

    /// Create an attribute spec with the standard type/custom/variability fields.
    fn make_attribute_spec(type_info: &TypeInfo, custom: bool, variability: sdf::Variability) -> sdf::Spec {
        let mut spec = sdf::Spec::new(sdf::SpecType::Attribute);
        spec.add(FieldKey::TypeName, sdf::Value::Token(type_info.to_string()));
        if custom {
            spec.add(FieldKey::Custom, sdf::Value::Bool(true));
        }
        if variability != sdf::Variability::default() {
            spec.add(FieldKey::Variability, sdf::Value::Variability(variability));
        }
        spec
    }

    /// Parse an attribute/property declaration, including variability, metadata, and default value.
    fn read_attribute(
        &mut self,
        current_path: &sdf::Path,
        properties: &mut Vec<String>,
        suffixed_properties: &mut Vec<String>,
        data: &mut HashMap<sdf::Path, sdf::Spec>,
    ) -> Result<()> {
        let mut custom = false;
        let list_op = self.try_list_op();

        if self.try_consume(Token::Custom) {
            if self.try_consume(Token::Rel) {
                return self.read_relationship(current_path, true, properties, data, list_op);
            }
            custom = true;
        }

        if self.try_consume(Token::Rel) {
            return self.read_relationship(current_path, false, properties, data, list_op);
        }

        let mut spec = sdf::Spec::new(sdf::SpecType::Attribute);
        let mut variability = sdf::Variability::Varying;
        if self.try_consume(Token::Varying) {
            // default
        } else if self.try_consume(Token::Uniform) {
            variability = sdf::Variability::Uniform;
        }

        let type_info = self.try_parse_type()?.context("attribute type expected")?;

        let name = self.expect_name().context("attribute name expected")?;

        // Read optional `.suffix` (e.g. `.connect`, `.timeSamples`, `.spline`).
        let suffix = if self.try_consume(Token::Punctuation('.')) {
            Some(self.fetch_next()?)
        } else {
            None
        };

        // Check for metadata before checking for assignment
        if self.is_next(Token::Punctuation('(')) {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse attribute metadata")?;
        }

        if matches!(suffix, Some(Token::Connect)) {
            push_unique(suffixed_properties, name);
            if self.try_consume(Token::Punctuation('=')) {
                let list_op = list_op.or(self.try_list_op());
                let targets = self
                    .parse_connection_targets()
                    .context("Unable to parse connection targets")?;
                let path = current_path.append_property(name)?;

                let spec = data
                    .entry(path)
                    .or_insert_with(|| Self::make_attribute_spec(&type_info, custom, variability));

                let list_op = self
                    .apply_list_op(list_op, targets)
                    .context("Unable to build connection listOp")?;
                spec.add(FieldKey::ConnectionPaths, sdf::Value::PathListOp(list_op));
            }
            return Ok(());
        }

        if matches!(suffix, Some(Token::TimeSamples)) {
            push_unique(suffixed_properties, name);
            self.ensure_pun('=')?;
            let samples = self.parse_time_samples(type_info)?;
            let path = current_path.append_property(name)?;

            let spec = data
                .entry(path)
                .or_insert_with(|| Self::make_attribute_spec(&type_info, custom, variability));
            spec.add(FieldKey::TimeSamples, sdf::Value::TimeSamples(samples));
            return Ok(());
        }

        if matches!(suffix, Some(Token::Spline)) {
            push_unique(suffixed_properties, name);
            self.ensure_pun('=')?;
            let spline = self.parse_spline()?;
            let path = current_path.append_property(name)?;

            let spec = data
                .entry(path)
                .or_insert_with(|| Self::make_attribute_spec(&type_info, custom, variability));
            spec.add("spline", spline);
            return Ok(());
        }

        if let Some(tok) = suffix {
            bail!("Unsupported attribute suffix: {tok:?}");
        }

        // Check if there's an assignment
        if !self.is_next(Token::Punctuation('=')) {
            let path = current_path.append_property(name)?;
            if !properties.contains(&name.to_string()) {
                properties.push(name.to_string());
            }

            let mut base = Self::make_attribute_spec(&type_info, custom, variability);
            base.extend_from(spec);
            Self::merge_spec(data, path, base);
            return Ok(());
        }

        self.ensure_pun('=')?;
        let value = self.parse_value(type_info)?;
        let path = current_path.append_property(name)?;

        if self.is_next(Token::Punctuation('(')) {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse attribute metadata")?;
        }

        push_unique(properties, name);

        let mut base = Self::make_attribute_spec(&type_info, custom, variability);
        base.extend_from(spec);
        base.add(FieldKey::Default, value);
        Self::merge_spec(data, path, base);

        Ok(())
    }
    /// Parses a connection target list into USD paths.
    fn parse_connection_targets(&mut self) -> Result<Vec<sdf::Path>> {
        self.one_or_list(|this| this.parse_path_reference().context("Connection path expected"))
    }

    /// Parses a single `<...>` path reference token into an `sdf::Path`.
    fn parse_path_reference(&mut self) -> Result<sdf::Path> {
        sdf::Path::new(self.fetch_path_ref()?)
    }

    /// Parses a relocates dictionary: `{ <source>: <target>, ... }`.
    fn parse_relocates_dict(&mut self) -> Result<Vec<(sdf::Path, sdf::Path)>> {
        let mut pairs = Vec::new();
        self.parse_block('{', '}', |this| {
            let src = this.fetch_path_ref().context("Expected relocate source path")?;
            this.ensure_pun(':')
                .context("Expected ':' between relocate source and target")?;
            let tgt = this.fetch_path_ref().context("Expected relocate target path")?;
            let src_path = sdf::Path::new(src)?;
            let tgt_path = sdf::Path::from(tgt);
            pairs.push((src_path, tgt_path));
            Ok(())
        })?;
        Ok(pairs)
    }

    /// Parse the metadata block attached to a property and stash entries on the spec.
    fn parse_property_metadata(&mut self, spec: &mut sdf::Spec) -> Result<()> {
        self.parse_block('(', ')', |this| {
            let list_op = this.try_list_op();

            let name_token = this.fetch_next()?;
            let name = match name_token {
                // Bare string in property metadata is a comment.
                Token::String(s) => {
                    spec.add(FieldKey::Comment, sdf::Value::String(s.to_owned()));
                    return Ok(());
                }
                Token::Identifier(s) | Token::NamespacedIdentifier(s) => s.to_owned(),
                Token::CustomData => "customData".to_owned(),
                Token::Doc => FieldKey::Documentation.as_str().to_owned(),
                other => other
                    .keyword_lexeme()
                    .map(str::to_owned)
                    .ok_or_else(|| anyhow!("Unexpected attribute metadata name token: {other:?}"))?,
            };

            this.ensure_pun('=')?;
            let value = this
                .parse_property_metadata_value()
                .with_context(|| format!("Unable to parse attribute metadata value for {name}"))?;

            // Wrap in a dictionary keyed by the list op name to match the baseline format.
            let value = match list_op {
                Some(ref tok @ (Token::Prepend | Token::Append | Token::Delete | Token::Add)) => {
                    let key = tok.keyword_lexeme().unwrap().to_owned();
                    sdf::Value::Dictionary(HashMap::from([(key, value)]))
                }
                _ => value,
            };

            spec.add(name, value);
            Ok(())
        })?;

        Ok(())
    }

    /// Parse a single attribute metadata value (scalar or array) from within a metadata block.
    fn parse_property_metadata_value(&mut self) -> Result<sdf::Value> {
        // Handle array case: parse each element as a typed scalar, then collect
        // into the most specific Vec variant that fits all elements.
        if self.is_next(Token::Punctuation('[')) {
            let mut values = Vec::new();
            self.parse_block('[', ']', |this| {
                values.push(this.parse_property_metadata_value()?);
                Ok(())
            })?;

            // Infer the array type from the first element.
            return Ok(match values.first() {
                Some(sdf::Value::Double(_)) => sdf::Value::DoubleVec(
                    values
                        .into_iter()
                        .map(|v| v.try_as_double().unwrap_or_default())
                        .collect(),
                ),
                Some(sdf::Value::Int64(_)) => sdf::Value::Int64Vec(
                    values
                        .into_iter()
                        .map(|v| v.try_as_int_64().unwrap_or_default())
                        .collect(),
                ),
                _ => sdf::Value::StringVec(
                    values
                        .into_iter()
                        .map(|v| match v {
                            sdf::Value::String(s) | sdf::Value::Token(s) => s,
                            other => format!("{other:?}"),
                        })
                        .collect(),
                ),
            });
        }

        // Handle dictionary case by peeking, so parse_dictionary can consume the '{'
        if self.is_next(Token::Punctuation('{')) {
            return self.parse_dictionary();
        }

        let token = self.fetch_next()?;
        match token {
            Token::None => Ok(sdf::Value::ValueBlock),
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
            other => bail!("Unsupported property metadata value token: {other:?}"),
        }
    }

    /// Parse a dictionary value from `{` to `}`.
    fn parse_dictionary(&mut self) -> Result<sdf::Value> {
        let mut dict = HashMap::new();

        self.parse_block('{', '}', |this| {
            // Try optional type hint, then read the key.
            let type_hint = this.try_parse_type()?;

            let key_token = this.fetch_next()?;
            let key = match key_token {
                Token::Identifier(s) | Token::NamespacedIdentifier(s) | Token::String(s) => s.to_owned(),
                other => other
                    .keyword_lexeme()
                    .map(str::to_owned)
                    .ok_or_else(|| anyhow!("Expected identifier as dictionary key, got: {other:?}"))?,
            };

            this.ensure_pun('=')?;

            let value = if let Some(info) = type_hint {
                this.parse_value(info)?
            } else {
                this.parse_property_metadata_value()?
            };
            dict.insert(key, value);
            Ok(())
        })?;

        Ok(sdf::Value::Dictionary(dict))
    }

    fn read_relationship(
        &mut self,
        current_path: &sdf::Path,
        custom: bool,
        properties: &mut Vec<String>,
        data: &mut HashMap<sdf::Path, sdf::Spec>,
        outer_list_op: Option<Token<'a>>,
    ) -> Result<()> {
        let name = self.expect_name().context("relationship name expected")?;

        let mut spec = sdf::Spec::new(sdf::SpecType::Relationship);
        if custom {
            spec.add(FieldKey::Custom, sdf::Value::Bool(true));
        }

        // Check for metadata before or instead of assignment
        if self.is_next(Token::Punctuation('(')) {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse relationship metadata")?;
        }

        let path = current_path.append_property(name)?;
        push_unique(properties, name);

        // Check if there's an assignment
        if !self.is_next(Token::Punctuation('=')) {
            Self::merge_spec(data, path, spec);
            return Ok(());
        }

        self.ensure_pun('=')?;
        let list_op = outer_list_op.or(self.try_list_op());
        let targets: Vec<sdf::Path> = self
            .one_or_list(Self::parse_path_reference)
            .context("Unable to parse relationship targets")?
            .into_iter()
            .filter(|p| !p.is_empty())
            .map(|p| path.make_absolute(&p))
            .collect();

        let list_op = self
            .apply_list_op(list_op, targets)
            .context("Unable to build relationship targets listOp")?;
        spec.add(FieldKey::TargetPaths, sdf::Value::PathListOp(list_op));

        if self.is_next(Token::Punctuation('(')) {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse relationship metadata")?;
        }

        Self::merge_spec(data, path, spec);
        Ok(())
    }

    /// Parse prim metadata contained either within parentheses or directly after the prim
    /// declaration (until `{` is encountered).
    /// Parse a single prim metadata assignment, honoring list ops for supported fields.
    fn read_prim_metadata_entry(&mut self, spec: &mut sdf::Spec) -> Result<()> {
        let list_op = self.try_list_op();
        let name_token = self.fetch_next()?;

        let name = match name_token {
            // Bare string in metadata is a comment.
            Token::String(s) => {
                spec.add(FieldKey::Comment, sdf::Value::String(s.to_owned()));
                return Ok(());
            }
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => s,
            Token::Kind => FieldKey::Kind.as_str(),
            Token::References => FieldKey::References.as_str(),
            Token::Payload => FieldKey::Payload.as_str(),
            Token::Inherits => FieldKey::InheritPaths.as_str(),
            Token::Specializes => FieldKey::Specializes.as_str(),
            Token::Variants => FieldKey::VariantSelection.as_str(),
            Token::VariantSets => FieldKey::VariantSetNames.as_str(),
            Token::Relocates => FieldKey::Relocates.as_str(),
            Token::CustomData => "customData",
            Token::Doc => FieldKey::Documentation.as_str(),
            Token::Permission => FieldKey::Permission.as_str(),
            other => bail!("Unexpected metadata name token: {other:?}"),
        };

        self.ensure_pun('=')?;

        match name {
            n if n == FieldKey::Active.as_str() => {
                let value = self.parse_token::<bool>().context("Unable to parse active flag")?;
                spec.add(FieldKey::Active, sdf::Value::Bool(value));
            }
            "apiSchemas" => {
                let values = self
                    .one_or_list(|this| this.parse_token::<String>())
                    .context("Unable to parse apiSchemas list")?;
                let list_op = self
                    .apply_list_op(list_op, values)
                    .context("Unable to build apiSchemas listOp")?;
                spec.add("apiSchemas", sdf::Value::TokenListOp(list_op));
            }
            n if n == FieldKey::References.as_str() => {
                let references = self
                    .one_or_list(Self::parse_reference)
                    .context("Unable to parse references")?;
                let list_op = self
                    .apply_list_op(list_op, references)
                    .context("Unable to build references listOp")?;
                spec.add(FieldKey::References, sdf::Value::ReferenceListOp(list_op));
            }
            n if n == FieldKey::Payload.as_str() => {
                let payloads = self
                    .one_or_list(Self::parse_payload)
                    .context("Unable to parse payloads")?;
                let list_op = self
                    .apply_list_op(list_op, payloads)
                    .context("Unable to build payload listOp")?;
                spec.add(FieldKey::Payload, sdf::Value::PayloadListOp(list_op));
            }
            n if n == FieldKey::InheritPaths.as_str() => {
                let paths = self.one_or_list(Self::parse_path_reference)?;
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
            "customData" => {
                ensure!(list_op.is_none(), "customData metadata does not support list ops");
                let value = self
                    .parse_property_metadata_value()
                    .context("Unable to parse customData dictionary")?;
                spec.add("customData", value);
            }
            n if n == FieldKey::Documentation.as_str() => {
                ensure!(list_op.is_none(), "doc metadata does not support list ops");
                let value = self.parse_token::<String>().context("Unable to parse doc metadata")?;
                spec.add(FieldKey::Documentation, sdf::Value::String(value));
            }
            n if n == FieldKey::AssetInfo.as_str() => {
                ensure!(list_op.is_none(), "assetInfo does not support list ops");
                let value = self.parse_dictionary().context("Unable to parse assetInfo")?;
                spec.add(FieldKey::AssetInfo, value);
            }
            n if n == FieldKey::VariantSelection.as_str() => {
                ensure!(list_op.is_none(), "variants does not support list ops");
                let dict = self.parse_dictionary().context("Unable to parse variants")?;
                if let sdf::Value::Dictionary(map) = dict {
                    let selections: HashMap<String, String> = map
                        .into_iter()
                        .filter_map(|(k, v)| v.try_as_string().map(|s| (k, s.to_owned())))
                        .collect();
                    spec.add(FieldKey::VariantSelection, sdf::Value::VariantSelectionMap(selections));
                }
            }
            n if n == FieldKey::VariantSetNames.as_str() => {
                let values = self
                    .one_or_list(|this| this.parse_token::<String>())
                    .context("Unable to parse variantSets")?;
                let list_op = self
                    .apply_list_op(list_op, values)
                    .context("Unable to build variantSets listOp")?;
                spec.add(FieldKey::VariantSetNames, sdf::Value::TokenListOp(list_op));
            }
            n if n == FieldKey::Specializes.as_str() => {
                let paths = self.one_or_list(Self::parse_path_reference)?;
                let list_op = self
                    .apply_list_op(list_op, paths)
                    .context("Unable to build specializes listOp")?;
                spec.add(FieldKey::Specializes, sdf::Value::PathListOp(list_op));
            }
            n if n == FieldKey::Instanceable.as_str() => {
                ensure!(list_op.is_none(), "instanceable metadata does not support list ops");
                let value = self.parse_bool().context("Unable to parse instanceable flag")?;
                spec.add(FieldKey::Instanceable, sdf::Value::Bool(value));
            }
            n if n == FieldKey::Relocates.as_str() => {
                ensure!(list_op.is_none(), "relocates does not support list ops");
                let pairs = self.parse_relocates_dict().context("Unable to parse relocates")?;
                spec.add(FieldKey::Relocates, sdf::Value::Relocates(pairs));
            }
            "displayName" => {
                ensure!(list_op.is_none(), "displayName does not support list ops");
                let value = self.fetch_str().context("Unable to parse displayName")?;
                spec.add("displayName", sdf::Value::String(value.to_owned()));
            }
            n if n == FieldKey::Permission.as_str() => {
                ensure!(list_op.is_none(), "permission does not support list ops");
                let value = self.expect_identifier().context("Unable to parse permission")?;
                let perm = match value {
                    "public" => sdf::Permission::Public,
                    "private" => sdf::Permission::Private,
                    other => bail!("Invalid permission value: {other}"),
                };
                spec.add(FieldKey::Permission, sdf::Value::Permission(perm));
            }
            n if n == FieldKey::Prefix.as_str() => {
                ensure!(list_op.is_none(), "prefix does not support list ops");
                let value = self.fetch_str().context("Unable to parse prefix")?;
                spec.add(FieldKey::Prefix, sdf::Value::String(value.to_owned()));
            }
            other => bail!("Unsupported prim metadata: {other}"),
        }

        Ok(())
    }

    /// Parse an extrapolation mode: `mode [(slope)]`.
    fn parse_extrapolation(&mut self) -> Result<sdf::Value> {
        let mode = self.expect_identifier()?;
        if mode == "none" {
            return Ok(sdf::Value::ValueBlock);
        }
        let slope = if self.is_next(Token::Punctuation('(')) {
            self.ensure_pun('(')?;
            let v = self.parse_token::<f64>()?;
            self.ensure_pun(')')?;
            v
        } else {
            0.0
        };
        Ok(sdf::Value::Dictionary(HashMap::from([
            ("mode".to_owned(), sdf::Value::Token(mode.to_owned())),
            ("slope".to_owned(), sdf::Value::Double(slope)),
        ])))
    }

    /// Parse a spline value: `{ curveType, knots... }`.
    ///
    /// The result is stored as a `Dictionary` matching the baseline JSON structure:
    /// `{ curveType, preExtrapolation, postExtrapolation, loopParameters, knots, knotCustomData }`.
    fn parse_spline(&mut self) -> Result<sdf::Value> {
        let mut curve_type: Option<String> = None;
        let mut pre_extrapolation = sdf::Value::ValueBlock;
        let mut post_extrapolation = sdf::Value::ValueBlock;
        let mut loop_params = sdf::Value::ValueBlock;
        let mut knots = Vec::new();
        let mut knot_custom_data: HashMap<String, sdf::Value> = HashMap::new();

        self.parse_block('{', '}', |this| {
            let token = this.fetch_next()?;
            match token {
                // Curve type: `bezier`, `hermite`, etc.
                Token::Identifier(name)
                    if !matches!(name, "pre" | "post" | "loop") && !this.is_next(Token::Punctuation(':')) =>
                {
                    curve_type = Some(name.to_owned());
                }
                // Extrapolation: `pre : mode` or `post: mode [(slope)]`
                // With no space, the tokenizer produces `NamespacedIdentifier("pre:")`.
                Token::Identifier(dir @ ("pre" | "post")) if this.try_consume(Token::Punctuation(':')) => {
                    let extrap = this.parse_extrapolation()?;
                    if dir == "pre" {
                        pre_extrapolation = extrap;
                    } else {
                        post_extrapolation = extrap;
                    }
                }
                Token::NamespacedIdentifier("pre:") => {
                    pre_extrapolation = this.parse_extrapolation()?;
                }
                Token::NamespacedIdentifier("post:") => {
                    post_extrapolation = this.parse_extrapolation()?;
                }
                // Loop parameters
                Token::Identifier("loop") | Token::NamespacedIdentifier("loop:") => {
                    if matches!(token, Token::Identifier(_)) {
                        this.ensure_pun(':')?;
                    }
                    let vals = this.parse_tuple::<f64, 5>()?;
                    loop_params = sdf::Value::Dictionary(HashMap::from([
                        ("protoStart".to_owned(), sdf::Value::Double(vals[0])),
                        ("protoEnd".to_owned(), sdf::Value::Double(vals[1])),
                        ("numPreLoops".to_owned(), sdf::Value::Double(vals[2])),
                        ("numPostLoops".to_owned(), sdf::Value::Double(vals[3])),
                        ("valueOffset".to_owned(), sdf::Value::Double(vals[4])),
                    ]));
                }
                // Knot: `time : value [& preValue] [; pre (...)] [; post mode [...]] [; { customData }]`
                Token::Number(time_str) => {
                    let time: f64 = time_str.parse()?;
                    this.ensure_pun(':')?;
                    let first: f64 = this.parse_token()?;

                    let mut pre_slope = 0.0;
                    let mut pre_width = 0.0;
                    let mut post_slope = 0.0;
                    let mut post_width = 0.0;
                    let mut interp_mode = "held".to_owned();

                    // `time : value` or `time : preValue & value`
                    let (pre_value, value) = if this.try_consume(Token::Punctuation('&')) {
                        let actual: f64 = this.parse_token()?;
                        (first, actual)
                    } else {
                        (0.0, first)
                    };

                    // Optional semicolon-separated knot attributes
                    while this.try_consume(Token::Punctuation(';')) {
                        if this.is_next(Token::Punctuation('{')) {
                            // Per-knot custom data
                            let sdf::Value::Dictionary(dict) = this.parse_dictionary()? else {
                                unreachable!();
                            };
                            let time_key = if time.fract() == 0.0 && time.is_finite() {
                                format!("{}", time as i64)
                            } else {
                                format!("{time}")
                            };
                            knot_custom_data.insert(time_key, sdf::Value::Dictionary(dict));
                            continue;
                        }

                        let dir = this.expect_identifier()?;
                        match dir {
                            "pre" => {
                                let vals = this.parse_tuple::<f64, 2>()?;
                                pre_slope = vals[0];
                                pre_width = vals[1];
                            }
                            "post" => {
                                // `post mode` or `post mode (slope, width)`
                                let mode = this.expect_identifier()?;
                                interp_mode = mode.to_owned();
                                if this.is_next(Token::Punctuation('(')) {
                                    let vals = this.parse_tuple::<f64, 2>()?;
                                    post_slope = vals[0];
                                    post_width = vals[1];
                                }
                            }
                            other => bail!("Unexpected knot attribute: {other}"),
                        }
                    }

                    knots.push(sdf::Value::Dictionary(HashMap::from([
                        ("time".to_owned(), sdf::Value::Double(time)),
                        ("value".to_owned(), sdf::Value::Double(value)),
                        ("preValue".to_owned(), sdf::Value::Double(pre_value)),
                        ("preTangentSlope".to_owned(), sdf::Value::Double(pre_slope)),
                        ("preTangentWidth".to_owned(), sdf::Value::Double(pre_width)),
                        ("postTangentSlope".to_owned(), sdf::Value::Double(post_slope)),
                        ("postTangentWidth".to_owned(), sdf::Value::Double(post_width)),
                        ("nextInterpolationMode".to_owned(), sdf::Value::Token(interp_mode)),
                    ])));
                }
                other => bail!("Unexpected spline token: {other:?}"),
            }
            Ok(())
        })?;

        Ok(sdf::Value::Dictionary(HashMap::from([
            (
                "curveType".to_owned(),
                sdf::Value::Token(curve_type.unwrap_or_else(|| "bezier".to_owned())),
            ),
            ("preExtrapolation".to_owned(), pre_extrapolation),
            ("postExtrapolation".to_owned(), post_extrapolation),
            ("loopParameters".to_owned(), loop_params),
            ("knots".to_owned(), sdf::Value::ValueVec(knots)),
            ("knotCustomData".to_owned(), sdf::Value::Dictionary(knot_custom_data)),
        ])))
    }

    /// Parse a time sample map: `{ time : value, time : value, ... }`.
    ///
    /// Per-time values are dispatched two ways:
    ///
    /// - When the property's declared type and the next token agree
    ///   on shape (a tuple type opening with `(` or `[`, or any
    ///   array type opening with `[`), route through [`parse_value`]
    ///   so the value lands in the matching typed variant
    ///   (`Vec3f` / `QuatfVec` / `Matrix4d` / `IntVec` / `FloatVec` /
    ///   `TokenVec` / …).
    ///
    /// - Otherwise fall through to [`parse_property_metadata_value`]
    ///   so malformed-but-historically-accepted samples still load
    ///   — the spec corpus's `attributes.usda` deliberately authors
    ///   bare scalars (`5.67`, `-7`) and `None` against typed
    ///   `vector3f` properties to verify the parser's tolerance.
    fn parse_time_samples(&mut self, info: TypeInfo<'_>) -> Result<sdf::TimeSampleMap> {
        let mut samples = Vec::new();
        self.parse_block('{', '}', |this| {
            let time_str = this.fetch_next()?;
            let time: f64 = match time_str {
                Token::Number(s) => s.parse()?,
                other => bail!("Expected time value, got {other:?}"),
            };
            this.ensure_pun(':')?;
            let value = if this.next_is_typed_value(info) {
                this.parse_value(info)?
            } else {
                this.parse_property_metadata_value()?
            };
            samples.push((time, value));
            Ok(())
        })?;
        Ok(samples)
    }

    /// Heuristic: should the next token be parsed under [`parse_value`]
    /// for `info`, or is the type-blind metadata-value path safer?
    ///
    /// Returns `true` when the next token opens a literal whose shape
    /// matches the declared type:
    ///
    /// - `(` for a tuple type (vector / quat / matrix row / matrix).
    /// - `[` for any array type (scalar arrays like `int[]`,
    ///   `float[]`, `token[]`, as well as arrays of tuples like
    ///   `quatf[]` or `matrix4d[]`).
    ///
    /// Anything else (scalar literal, `None`, identifier) flows
    /// through the type-blind path so the spec corpus's lenient
    /// `vector3f`-with-bare-scalar samples keep parsing.
    fn next_is_typed_value(&mut self, info: TypeInfo<'_>) -> bool {
        let is_tuple_type = matches!(
            info.ty,
            Type::Int2
                | Type::Int3
                | Type::Int4
                | Type::Half2
                | Type::Half3
                | Type::Half4
                | Type::Float2
                | Type::Float3
                | Type::Float4
                | Type::Double2
                | Type::Double3
                | Type::Double4
                | Type::Quath
                | Type::Quatf
                | Type::Quatd
                | Type::Matrix2d
                | Type::Matrix3d
                | Type::Matrix4d
        );
        match self.peek_next() {
            Some(Ok(Token::Punctuation('('))) => is_tuple_type,
            Some(Ok(Token::Punctuation('['))) => is_tuple_type || info.is_array,
            _ => false,
        }
    }

    /// Parse one reference entry, including optional target prim path and layer offset.
    fn parse_reference(&mut self) -> Result<sdf::Reference> {
        let mut reference = sdf::Reference::default();

        match self.fetch_next()? {
            Token::AssetRef(asset_path) => {
                reference.asset_path = asset_path.to_string();
                if let Some(Ok(Token::PathRef(path))) = self.peek_next() {
                    reference.prim_path = sdf::Path::new(path)?;
                    self.fetch_next()?;
                }
            }
            Token::PathRef(path) => {
                reference.prim_path = sdf::Path::new(path)?;
            }
            token => {
                bail!("Expected asset reference (@...@) or path reference (<...>), got {token:?}");
            }
        }

        if self.is_next(Token::Punctuation('(')) {
            let (offset, custom_data) = self
                .parse_reference_layer_offset()
                .context("Unable to parse reference layer offset")?;
            reference.layer_offset = offset;
            reference.custom_data = custom_data;
        }

        Ok(reference)
    }

    /// Parse `(offset = ...; scale = ...; customData = {...})` blocks attached to
    /// references or sublayers.
    fn parse_reference_layer_offset(&mut self) -> Result<(sdf::LayerOffset, HashMap<String, sdf::Value>)> {
        let mut layer_offset = sdf::LayerOffset::default();
        let mut custom_data = HashMap::new();

        self.parse_block('(', ')', |this| {
            let token = this.fetch_next()?;
            this.ensure_pun('=')?;

            match token {
                Token::Offset => {
                    let value = this.parse_value(TypeInfo::scalar(Type::Double))?;
                    layer_offset.offset = value.try_as_double().context("Expected double for offset")?;
                }
                Token::Scale => {
                    let value = this.parse_value(TypeInfo::scalar(Type::Double))?;
                    layer_offset.scale = value.try_as_double().context("Expected double for scale")?;
                }
                Token::CustomData => {
                    let sdf::Value::Dictionary(dict) = this.parse_dictionary()? else {
                        unreachable!("parse_dictionary always returns Dictionary");
                    };
                    custom_data = dict;
                }
                unexpected => bail!("Unexpected token in layer offset: {unexpected:?}"),
            }

            Ok(())
        })?;

        Ok((layer_offset, custom_data))
    }

    /// Parse one payload entry, including optional target prim path and layer offset.
    fn parse_payload(&mut self) -> Result<sdf::Payload> {
        let mut payload = sdf::Payload::default();

        match self.fetch_next()? {
            Token::AssetRef(asset_path) => {
                payload.asset_path = asset_path.to_string();
                if let Some(Ok(Token::PathRef(path))) = self.peek_next() {
                    payload.prim_path = sdf::Path::new(path)?;
                    self.fetch_next()?;
                }
            }
            Token::PathRef(path) => {
                payload.prim_path = sdf::Path::new(path)?;
            }
            token => {
                bail!("Expected asset reference (@...@) or path reference (<...>), got {token:?}");
            }
        }

        if self.is_next(Token::Punctuation('(')) {
            let (offset, _custom_data) = self
                .parse_reference_layer_offset()
                .context("Unable to parse payload layer offset")?;
            payload.layer_offset = Some(offset);
        }

        Ok(payload)
    }

    fn apply_list_op<T: Default + Clone + PartialEq>(
        &mut self,
        op: Option<Token<'a>>,
        items: Vec<T>,
    ) -> Result<sdf::ListOp<T>> {
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
    fn parse_value(&mut self, info: TypeInfo) -> Result<sdf::Value> {
        // None means "value block" (explicitly unset) regardless of type.
        if self.try_consume(Token::None) {
            return Ok(sdf::Value::ValueBlock);
        }

        let value = match (info.ty, info.is_array) {
            (Type::Bool, false) => sdf::Value::Bool(self.parse_bool()?),
            (Type::Bool, true) => sdf::Value::BoolVec(self.parse_bool_array()?),

            (Type::Asset, false) => sdf::Value::AssetPath(self.parse_asset_path()?),
            (Type::Asset, true) => sdf::Value::StringVec(self.parse_asset_path_array()?),

            (Type::Uchar, false) => sdf::Value::Uchar(self.parse_token()?),
            (Type::Uchar, true) => sdf::Value::UcharVec(self.parse_array()?),

            (Type::Int, false) => sdf::Value::Int(self.parse_token()?),
            (Type::Int, true) => sdf::Value::IntVec(self.parse_array()?),
            (Type::Int2, false) => sdf::Value::Vec2i(self.parse_tuple::<_, 2>()?),
            (Type::Int2, true) => sdf::Value::Vec2iVec(self.parse_array_of_tuples::<_, 2>()?),
            (Type::Int3, false) => sdf::Value::Vec3i(self.parse_tuple::<_, 3>()?),
            (Type::Int3, true) => sdf::Value::Vec3iVec(self.parse_array_of_tuples::<_, 3>()?),
            (Type::Int4, false) => sdf::Value::Vec4i(self.parse_tuple::<_, 4>()?),
            (Type::Int4, true) => sdf::Value::Vec4iVec(self.parse_array_of_tuples::<_, 4>()?),
            (Type::Uint, false) => sdf::Value::Uint(self.parse_token()?),
            (Type::Int64, false) => sdf::Value::Int64(self.parse_token()?),
            (Type::Int64, true) => sdf::Value::Int64Vec(self.parse_array()?),
            (Type::Uint64, false) => sdf::Value::Uint64(self.parse_token()?),

            (Type::Half, false) => sdf::Value::Half(self.parse_token()?),
            (Type::Half, true) => sdf::Value::HalfVec(self.parse_array()?),
            (Type::Half2, false) => sdf::Value::Vec2h(self.parse_tuple::<_, 2>()?),
            (Type::Half2, true) => sdf::Value::Vec2hVec(self.parse_array_of_tuples::<_, 2>()?),
            (Type::Half3, false) => sdf::Value::Vec3h(self.parse_tuple::<_, 3>()?),
            (Type::Half3, true) => sdf::Value::Vec3hVec(self.parse_array_of_tuples::<_, 3>()?),
            (Type::Half4, false) => sdf::Value::Vec4h(self.parse_tuple::<_, 4>()?),
            (Type::Half4, true) => sdf::Value::Vec4hVec(self.parse_array_of_tuples::<_, 4>()?),

            (Type::Float, false) => sdf::Value::Float(self.parse_token()?),
            (Type::Float, true) => sdf::Value::FloatVec(self.parse_array()?),
            (Type::Float2, false) => sdf::Value::Vec2f(self.parse_tuple::<_, 2>()?),
            (Type::Float2, true) => sdf::Value::Vec2fVec(self.parse_array_of_tuples::<_, 2>()?),
            (Type::Float3, false) => sdf::Value::Vec3f(self.parse_tuple::<_, 3>()?),
            (Type::Float3, true) => sdf::Value::Vec3fVec(self.parse_array_of_tuples::<_, 3>()?),
            (Type::Float4, false) => sdf::Value::Vec4f(self.parse_tuple::<_, 4>()?),
            (Type::Float4, true) => sdf::Value::Vec4fVec(self.parse_array_of_tuples::<_, 4>()?),

            (Type::Double, false) => sdf::Value::Double(self.parse_token()?),
            (Type::Double, true) => sdf::Value::DoubleVec(self.parse_array()?),
            (Type::Double2, false) => sdf::Value::Vec2d(self.parse_tuple::<_, 2>()?),
            (Type::Double2, true) => sdf::Value::Vec2dVec(self.parse_array_of_tuples::<_, 2>()?),
            (Type::Double3, false) => sdf::Value::Vec3d(self.parse_tuple::<_, 3>()?),
            (Type::Double3, true) => sdf::Value::Vec3dVec(self.parse_array_of_tuples::<_, 3>()?),
            (Type::Double4, false) => sdf::Value::Vec4d(self.parse_tuple::<_, 4>()?),
            (Type::Double4, true) => sdf::Value::Vec4dVec(self.parse_array_of_tuples::<_, 4>()?),

            (Type::Quath, false) => sdf::Value::Quath(self.parse_tuple::<_, 4>()?),
            (Type::Quatf, false) => sdf::Value::Quatf(self.parse_tuple::<_, 4>()?),
            (Type::Quatd, false) => sdf::Value::Quatd(self.parse_tuple::<_, 4>()?),
            (Type::Quath, true) => sdf::Value::QuathVec(self.parse_array_of_tuples::<_, 4>()?),
            (Type::Quatf, true) => sdf::Value::QuatfVec(self.parse_array_of_tuples::<_, 4>()?),
            (Type::Quatd, true) => sdf::Value::QuatdVec(self.parse_array_of_tuples::<_, 4>()?),

            (Type::String, false) => sdf::Value::String(self.fetch_str()?.to_owned()),
            (Type::Token, false) => sdf::Value::Token(self.fetch_str()?.to_owned()),
            (Type::String | Type::Token, true) => sdf::Value::TokenVec(self.parse_array()?),

            (Type::Matrix2d, false) => sdf::Value::Matrix2d(self.parse_matrix::<2, 4>()?),
            (Type::Matrix3d, false) => sdf::Value::Matrix3d(self.parse_matrix::<3, 9>()?),
            (Type::Matrix4d, false) => sdf::Value::Matrix4d(self.parse_matrix::<4, 16>()?),
            (Type::Matrix2d, true) => sdf::Value::Matrix2dVec(self.parse_matrix_array::<2, 4>()?),
            (Type::Matrix3d, true) => sdf::Value::Matrix3dVec(self.parse_matrix_array::<3, 9>()?),
            (Type::Matrix4d, true) => sdf::Value::Matrix4dVec(self.parse_matrix_array::<4, 16>()?),

            (Type::Dictionary, _) => self.parse_dictionary()?,

            (Type::Custom, _) => bail!("Cannot parse value for unrecognized type: {}", info.type_name),

            (ty, true) => bail!("Array of {ty:?} is not supported"),
        };

        Ok(value)
    }

    /// Parses a scalar type name into a `Type`. Does not handle arrays.
    ///
    /// See
    /// - <https://openusd.org/dev/api/_usd__page__datatypes.html#Usd_Basic_Datatypes>
    /// - <https://openusd.org/dev/api/_usd__page__datatypes.html#Usd_Roles>
    fn parse_base_type(name: &str) -> Result<Type> {
        let ty = match name {
            "bool" => Type::Bool,
            "uchar" => Type::Uchar,
            "int" => Type::Int,
            "int2" => Type::Int2,
            "int3" => Type::Int3,
            "int4" => Type::Int4,
            "uint" => Type::Uint,
            "int64" => Type::Int64,
            "uint64" => Type::Uint64,
            "half" => Type::Half,
            "half2" | "texCoord2h" => Type::Half2,
            "half3" | "point3h" | "normal3h" | "vector3h" | "color3h" | "texCoord3h" => Type::Half3,
            "half4" | "color4h" => Type::Half4,
            "float" => Type::Float,
            "float2" | "texCoord2f" => Type::Float2,
            "float3" | "point3f" | "normal3f" | "vector3f" | "color3f" | "texCoord3f" => Type::Float3,
            "float4" | "color4f" => Type::Float4,
            "double" => Type::Double,
            "double2" | "texCoord2d" => Type::Double2,
            "double3" | "point3d" | "normal3d" | "vector3d" | "color3d" | "texCoord3d" => Type::Double3,
            "double4" | "color4d" => Type::Double4,
            "matrix2d" => Type::Matrix2d,
            "matrix3d" => Type::Matrix3d,
            "matrix4d" | "frame4d" => Type::Matrix4d,
            "quatd" => Type::Quatd,
            "quatf" => Type::Quatf,
            "quath" => Type::Quath,
            "string" | "token" => Type::String,
            "asset" => Type::Asset,
            "dictionary" => Type::Dictionary,
            _ => bail!("Unsupported type: {name}"),
        };
        Ok(ty)
    }

    /// Tries to parse a type declaration: a recognized type name optionally followed by `[]`.
    ///
    /// Returns `Ok(None)` if the next token is not a known type (without consuming it).
    fn try_parse_type(&mut self) -> Result<Option<TypeInfo<'a>>> {
        let base = match self.peek_next() {
            Some(Ok(Token::Identifier(name))) => *name,
            Some(Ok(Token::Dictionary)) => "dictionary",
            _ => return Ok(None),
        };

        let ty = Self::parse_base_type(base).unwrap_or(Type::Custom);
        self.fetch_next()?;

        let mut is_array = false;
        if self.is_next(Token::Punctuation('[')) {
            self.fetch_next()?;
            self.ensure_pun(']')?;
            is_array = true;
        }

        Ok(Some(TypeInfo {
            ty,
            type_name: base,
            is_array,
        }))
    }

    /// Parse single token as `T` which can be deserialized from string (such as `int`, `float`, etc).
    fn parse_token<T: FromStr>(&mut self) -> Result<T>
    where
        <T as FromStr>::Err: std::fmt::Debug,
    {
        let token = self.fetch_next()?;
        let value_str = match token {
            Token::Number(s) | Token::Identifier(s) | Token::String(s) | Token::NamespacedIdentifier(s) => s,
            Token::Inf => "inf",
            Token::Punctuation('-') => {
                // Handle negative inf
                let next = self.fetch_next()?;
                if matches!(next, Token::Inf) {
                    "-inf"
                } else {
                    bail!("Expected number after '-', got {next:?}")
                }
            }
            Token::Punctuation('+') => {
                // Handle positive inf
                let next = self.fetch_next()?;
                if matches!(next, Token::Inf) {
                    "inf"
                } else {
                    bail!("Expected number after '+', got {next:?}")
                }
            }
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
            Token::Identifier(value) | Token::NamespacedIdentifier(value) | Token::String(value) => {
                if value.eq_ignore_ascii_case("true") {
                    Ok(true)
                } else if value.eq_ignore_ascii_case("false") {
                    Ok(false)
                } else {
                    bail!("Unexpected value for bool literal: {value}")
                }
            }
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
            other => bail!("Unexpected token for bool literal: {other:?}"),
        }
    }

    /// Parse an array of booleans, reusing the permissive literal parsing rules.
    fn parse_bool_array(&mut self) -> Result<Vec<bool>> {
        let mut out = Vec::new();
        self.parse_block('[', ']', |this| {
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
        self.parse_block('[', ']', |this| {
            result.push(this.parse_asset_path()?);
            Ok(())
        })?;
        Ok(result)
    }

    /// Parse `subLayers` entries along with their optional `(offset/scale)` metadata.
    fn parse_sublayers(&mut self) -> Result<(sdf::Value, sdf::Value)> {
        let mut sublayers = Vec::new();
        let mut sublayer_offsets = Vec::new();

        self.parse_block('[', ']', |this| {
            let asset_path = this
                .fetch_next()?
                .try_as_asset_ref()
                .ok_or_else(|| anyhow!("Asset ref expected, got {:?}", this.peek_next()))?;
            sublayers.push(asset_path.to_string());

            let mut layer_offset = sdf::LayerOffset::default();
            if this.is_next(Token::Punctuation('(')) {
                let mut offset = None;
                let mut scale = None;

                this.parse_block('(', ')', |this| {
                    let token = this.fetch_next()?;
                    this.ensure_pun('=')?;
                    let value = this.parse_value(TypeInfo::scalar(Type::Double))?;
                    match token {
                        Token::Offset => {
                            offset = Some(value);
                        }
                        Token::Scale => {
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
    /// Parses a delimited block: `open` ... entries ... `close`.
    ///
    /// Calls `entry` for each item. Commas between entries are consumed automatically.
    /// Handles empty blocks and trailing commas.
    fn parse_block(&mut self, open: char, close: char, mut entry: impl FnMut(&mut Self) -> Result<()>) -> Result<()> {
        self.ensure_pun(open)?;
        loop {
            if self.try_consume(Token::Punctuation(close)) {
                break;
            }
            entry(self)?;
            while self.try_consume(Token::Punctuation(',')) || self.try_consume(Token::Punctuation(';')) {}
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
        let mut i = 0;
        self.parse_block('(', ')', |this| {
            ensure!(i < N, "tuple has too many elements (expected {N})");
            result[i] = MaybeUninit::new(this.parse_token::<T>()?);
            i += 1;
            Ok(())
        })?;
        let result = unsafe { std::mem::transmute_copy::<_, [T; N]>(&result) };
        Ok(result)
    }

    /// Parse a `[...]` array, using `parse_element` for each item.
    fn parse_array_with<T>(&mut self, mut parse_element: impl FnMut(&mut Self) -> Result<T>) -> Result<Vec<T>> {
        let mut out = Vec::new();
        self.parse_block('[', ']', |this| {
            out.push(parse_element(this)?);
            Ok(())
        })?;
        Ok(out)
    }

    /// Parse a `[scalar, ...]` array of `FromStr` values.
    fn parse_array<T>(&mut self) -> Result<Vec<T>>
    where
        T: FromStr + Default,
        <T as FromStr>::Err: Debug,
    {
        self.parse_array_with(Self::parse_token)
    }

    /// Parse a `[(tuple), ...]` array of fixed-size tuples.
    fn parse_array_of_tuples<T, const N: usize>(&mut self) -> Result<Vec<[T; N]>>
    where
        T: FromStr,
        <T as FromStr>::Err: Debug,
    {
        self.parse_array_with(Self::parse_tuple)
    }

    /// Parse a single matrix literal, flattening rows in row-major order.
    ///
    /// Handles both bare `(row), (row), ...` and bracket-wrapped `[ (row), ... ]` forms.
    fn parse_matrix<const N: usize, const M: usize>(&mut self) -> Result<[f64; M]> {
        if self.is_next(Token::Punctuation('[')) {
            let mut arr = self.parse_matrix_array::<N, M>()?;
            ensure!(arr.len() == 1, "expected a single matrix value");
            return Ok(arr.remove(0));
        }

        let mut values = [0_f64; M];
        let mut idx = 0;
        self.parse_block('(', ')', |this| {
            let row = this.parse_tuple::<f64, N>()?;
            for v in row {
                ensure!(idx < M, "matrix{N}d literal has too many elements");
                values[idx] = v;
                idx += 1;
            }
            Ok(())
        })?;
        ensure!(idx == M, "matrix{N}d literal must contain {N} rows");
        Ok(values)
    }

    /// Parse `[ matrix, matrix, ... ]`.
    fn parse_matrix_array<const N: usize, const M: usize>(&mut self) -> Result<Vec<[f64; M]>> {
        self.parse_array_with(Self::parse_matrix::<N, M>)
    }
}

/// Push a string into a Vec if it's not already present.
fn push_unique(vec: &mut Vec<String>, name: &str) {
    if !vec.iter().any(|s| s == name) {
        vec.push(name.to_owned());
    }
}

/// Result of parsing a type declaration, holding the parsed base type,
/// the original token text, and whether `[]` was present.
#[derive(Debug, Clone, Copy)]
struct TypeInfo<'a> {
    ty: Type,
    type_name: &'a str,
    is_array: bool,
}

impl<'a> TypeInfo<'a> {
    const fn scalar(ty: Type) -> TypeInfo<'a> {
        TypeInfo {
            ty,
            type_name: "",
            is_array: false,
        }
    }
}

impl std::fmt::Display for TypeInfo<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_array {
            write!(f, "{}[]", self.type_name)
        } else {
            write!(f, "{}", self.type_name)
        }
    }
}

/// Base data type without array semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Type {
    Bool,
    Uchar,
    Int,
    Int2,
    Int3,
    Int4,
    Uint,
    Int64,
    Uint64,
    Half,
    Half2,
    Half3,
    Half4,
    Float,
    Float2,
    Float3,
    Float4,
    Double,
    Double2,
    Double3,
    Double4,
    Quath,
    Quatf,
    Quatd,
    String,
    Token,
    Asset,
    Matrix2d,
    Matrix3d,
    Matrix4d,
    Dictionary,
    /// Unrecognized type name; the raw name is preserved in `TypeInfo::type_name`.
    Custom,
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
        assert_eq!(result, vec![[1_u32, 2], [3, 4]]);
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
            .get(FieldKey::Documentation.as_str())
            .and_then(|v| v.try_as_string_ref())
            .unwrap()
            .eq("test string"));

        assert!(pseudo_root
            .get("upAxis")
            .and_then(|v| v.try_as_token_ref())
            .unwrap()
            .eq("Y"));
    }

    #[test]
    // Accepts quoted dictionary keys that include namespace separators.
    fn parse_dictionary_with_quoted_namespace_keys() {
        let mut parser = Parser::new(
            r#"
#usda 1.0
(
    customLayerData = {
        dictionary renderSettings = {
            bool "rtx:raytracing:fractionalCutoutOpacity" = 1
            token "rtx:rendermode" = "PathTracing"
        }
    }
)
"#,
        );

        let pseudo_root = parser.read_pseudo_root().unwrap();
        let custom_layer_data = pseudo_root
            .get("customLayerData")
            .expect("customLayerData metadata present");
        let dict = match custom_layer_data {
            sdf::Value::Dictionary(dict) => dict,
            other => panic!("customLayerData parsed as unexpected value: {other:?}"),
        };

        let render_settings = match dict.get("renderSettings") {
            Some(sdf::Value::Dictionary(d)) => d,
            other => panic!("renderSettings parsed as unexpected value: {other:?}"),
        };

        assert!(render_settings.contains_key("rtx:raytracing:fractionalCutoutOpacity"));
        assert!(render_settings.contains_key("rtx:rendermode"));
    }

    #[test]
    // Ensures pseudo-root parsing preserves dictionary-valued metadata entries.
    fn parse_pseudo_root_dictionary_metadata() {
        let mut parser = Parser::new(
            r#"
#usda 1.0
(
    customLayerData = {
        dictionary cameraSettings = {
            dictionary Front = {
                double3 position = (5, 0, 0)
                double radius = 5
            }
        }
        string boundCamera = "/OmniverseKit_Persp"
    }
)
"#,
        );

        let pseudo_root = parser.read_pseudo_root().unwrap();

        let custom_layer_data = pseudo_root
            .get("customLayerData")
            .expect("customLayerData metadata present");

        let dict = match custom_layer_data {
            sdf::Value::Dictionary(dict) => dict,
            other => panic!("customLayerData parsed as unexpected value: {other:?}"),
        };

        let camera_settings = dict.get("cameraSettings").expect("cameraSettings dictionary entry");
        let camera_dict = match camera_settings {
            sdf::Value::Dictionary(dict) => dict,
            other => panic!("cameraSettings parsed as unexpected value: {other:?}"),
        };

        let front = camera_dict.get("Front").expect("Front entry");
        let front_dict = match front {
            sdf::Value::Dictionary(dict) => dict,
            other => panic!("Front stored as unexpected value: {other:?}"),
        };

        let position = front_dict.get("position").expect("Front.position entry");
        match position {
            sdf::Value::Vec3d(values) => assert_eq!(values, &[5.0, 0.0, 0.0]),
            other => panic!("Front.position stored as unexpected value: {other:?}"),
        }

        let radius = front_dict.get("radius").expect("Front.radius entry");
        match radius {
            sdf::Value::Double(value) => assert_eq!(*value, 5.0),
            other => panic!("Front.radius stored as unexpected value: {other:?}"),
        }

        let bound_camera = dict.get("boundCamera").expect("boundCamera entry");
        match bound_camera {
            sdf::Value::String(value) => assert_eq!(value, "/OmniverseKit_Persp"),
            sdf::Value::Token(value) => assert_eq!(value, "/OmniverseKit_Persp"),
            other => panic!("boundCamera stored as unexpected value: {other:?}"),
        }
    }

    #[test]
    // Verifies parsing of expressionVariables metadata field with typed values.
    fn parse_expression_variables() {
        let mut parser = Parser::new(
            r#"
#usda 1.0
(
    expressionVariables = {
        string ASSET_PATH = "/models/characters"
        bool USE_HIGH_RES = true
        int64 LOD_LEVEL = 2
    }
)
"#,
        );

        let pseudo_root = parser.read_pseudo_root().unwrap();

        let expr_vars = pseudo_root
            .get("expressionVariables")
            .expect("expressionVariables metadata present");

        let dict = match expr_vars {
            sdf::Value::Dictionary(dict) => dict,
            other => panic!("expressionVariables parsed as unexpected value: {other:?}"),
        };

        let asset_path = dict.get("ASSET_PATH").expect("ASSET_PATH entry");
        match asset_path {
            sdf::Value::String(value) => assert_eq!(value, "/models/characters"),
            other => panic!("ASSET_PATH stored as unexpected value: {other:?}"),
        }

        let use_high_res = dict.get("USE_HIGH_RES").expect("USE_HIGH_RES entry");
        match use_high_res {
            sdf::Value::Bool(value) => assert!(*value),
            other => panic!("USE_HIGH_RES stored as unexpected value: {other:?}"),
        }

        let lod_level = dict.get("LOD_LEVEL").expect("LOD_LEVEL entry");
        match lod_level {
            sdf::Value::Int64(value) => assert_eq!(*value, 2),
            other => panic!("LOD_LEVEL stored as unexpected value: {other:?}"),
        }
    }

    #[test]
    // Verifies parsing of expressionVariables with array types.
    fn parse_expression_variables_arrays() {
        let mut parser = Parser::new(
            r#"
#usda 1.0
(
    expressionVariables = {
        string[] RENDER_PASSES = ["beauty", "shadow", "reflection"]
        int64[] FRAME_RANGE = [1, 100]
        bool[] FLAGS = [true, false, true]
    }
)
"#,
        );

        let pseudo_root = parser.read_pseudo_root().unwrap();

        let expr_vars = pseudo_root
            .get("expressionVariables")
            .expect("expressionVariables metadata present");

        let dict = match expr_vars {
            sdf::Value::Dictionary(dict) => dict,
            other => panic!("expressionVariables parsed as unexpected value: {other:?}"),
        };

        let render_passes = dict.get("RENDER_PASSES").expect("RENDER_PASSES entry");
        match render_passes {
            sdf::Value::TokenVec(values) | sdf::Value::StringVec(values) => {
                assert_eq!(values, &["beauty", "shadow", "reflection"]);
            }
            other => panic!("RENDER_PASSES stored as unexpected value: {other:?}"),
        }

        let frame_range = dict.get("FRAME_RANGE").expect("FRAME_RANGE entry");
        match frame_range {
            sdf::Value::Int64Vec(values) => assert_eq!(values, &[1, 100]),
            other => panic!("FRAME_RANGE stored as unexpected value: {other:?}"),
        }

        let flags = dict.get("FLAGS").expect("FLAGS entry");
        match flags {
            sdf::Value::BoolVec(values) => assert_eq!(values, &[true, false, true]),
            other => panic!("FLAGS stored as unexpected value: {other:?}"),
        }
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
        let prim_children = pseudo_root.get("primChildren").unwrap().to_owned();
        assert_eq!(
            prim_children.try_as_token_vec().unwrap(),
            vec![String::from("Forest_set")]
        );

        let forest_set_prim = data.get(&sdf::path("/Forest_set").unwrap()).unwrap();
        let prim_children = forest_set_prim.get("primChildren").unwrap().to_owned();
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
            .get("interpolation")
            .expect("missing interpolation metadata")
            .try_as_string_ref()
            .expect("interpolation metadata must be a string");

        assert_eq!(interpolation, "faceVarying");
    }

    #[test]
    // Verifies the parser tolerates custom/asset/connect syntax and records connection props.
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
            double_sided.get(FieldKey::Default.as_str()),
            Some(sdf::Value::Bool(true))
        ));

        let info_spec = data.get(&sdf::path("/Image_Texture.info:id").unwrap()).unwrap();
        assert!(matches!(
            info_spec.get(FieldKey::Custom.as_str()),
            Some(sdf::Value::Bool(true))
        ));

        let file_spec = data.get(&sdf::path("/Image_Texture.inputs:file").unwrap()).unwrap();
        assert!(matches!(
            file_spec
                .get(FieldKey::Default.as_str()),
            Some(sdf::Value::AssetPath(path)) if path == "./texture.png"
        ));

        let output_spec = data
            .get(&sdf::path("/Image_Texture.outputs:surface").unwrap())
            .expect("missing outputs:surface spec");
        assert!(matches!(
            output_spec
                .get(FieldKey::TypeName.as_str()),
            Some(sdf::Value::Token(t)) if t == "token"
        ));

        // Connection paths are stored on the same spec (not a separate `.connect` spec).
        assert!(matches!(
            output_spec
                .get(FieldKey::ConnectionPaths.as_str()),
            Some(sdf::Value::PathListOp(op)) if op.explicit_items.len() == 1
        ));

        let props = shader
            .get(sdf::schema::ChildrenKey::PropertyChildren.as_str())
            .and_then(|value| match value {
                sdf::Value::TokenVec(tokens) => Some(tokens.clone()),
                _ => None,
            })
            .unwrap_or_default();
        assert!(props.contains(&"info:id".to_string()));
        assert!(props.contains(&"doubleSided".to_string()));
        assert!(props.contains(&"inputs:file".to_string()));
        assert!(props.contains(&"outputs:surface".to_string()));
    }

    #[test]
    // Ensures matrix4d scalar attributes parse into row-major data.
    fn parse_matrix4d_attribute() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Xform "X" {
    matrix4d xformOp:transform = ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) )
}
            "#,
        );

        let data = parser.parse().unwrap();
        let transform = data
            .get(&sdf::path("/X.xformOp:transform").unwrap())
            .expect("transform spec missing");
        let matrix = transform
            .get(FieldKey::Default.as_str())
            .expect("matrix default missing");

        match matrix {
            sdf::Value::Matrix4d(values) => {
                assert_eq!(values.len(), 16);
                assert_eq!(values[0], 1.0);
                assert_eq!(values[5], 1.0);
                assert_eq!(values[10], 1.0);
                assert_eq!(values[15], 1.0);
            }
            other => panic!("expected Matrix4d, got {other:?}"),
        }
    }

    #[test]
    // Ensures matrix4d array attributes parse into contiguous row-major data.
    fn parse_matrix4d_array_attribute() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Scope "Root" {
    matrix4d[] transforms = [
        ( (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1) ),
        ( (2, 0, 0, 0), (0, 2, 0, 0), (0, 0, 2, 0), (0, 0, 0, 2) )
    ]
}
            "#,
        );

        let data = parser.parse().unwrap();
        let transforms = data
            .get(&sdf::path("/Root.transforms").unwrap())
            .expect("transforms spec missing");
        let matrix = transforms
            .get(FieldKey::Default.as_str())
            .expect("matrix default missing");

        match matrix {
            sdf::Value::Matrix4dVec(values) => {
                assert_eq!(values.len(), 2);
                assert_eq!(values[0][0], 1.0);
                assert_eq!(values[0][15], 1.0);
                assert_eq!(values[1][0], 2.0);
                assert_eq!(values[1][15], 2.0);
            }
            other => panic!("expected Matrix4dVec, got {other:?}"),
        }
    }

    #[test]
    // Validates output declarations and connection attributes produce specs with connection paths.
    fn parse_material_output_connections() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Material "Mat"
{
    token outputs:surface.connect = </Mat/Preview.outputs:surface>
    token outputs:surface

    def Shader "Preview"
    {
        uniform token info:id = "UsdPreviewSurface"
        token outputs:surface
    }
}
            "#,
        );

        let data = parser.parse().unwrap();
        let mat = data.get(&sdf::path("/Mat").unwrap()).unwrap();

        let props = mat
            .get(sdf::schema::ChildrenKey::PropertyChildren.as_str())
            // Clone because try_as_token_vec consumes the Value.
            .and_then(|value| value.clone().try_as_token_vec())
            .unwrap_or_default();
        assert!(props.contains(&"outputs:surface".to_string()));

        let output = data
            .get(&sdf::path("/Mat.outputs:surface").unwrap())
            .expect("missing outputs:surface spec");
        assert!(matches!(
            output.get(FieldKey::TypeName.as_str()),
            Some(sdf::Value::Token(t)) if t == "token"
        ));

        // Connection paths are stored on the same spec (not a separate `.connect` spec).
        match output.get(FieldKey::ConnectionPaths.as_str()) {
            Some(sdf::Value::PathListOp(op)) => {
                assert_eq!(op.explicit_items.len(), 1);
                assert_eq!(op.explicit_items[0].as_str(), "/Mat/Preview.outputs:surface");
            }
            other => panic!("unexpected connection paths value: {other:?}"),
        }
    }

    #[test]
    // Verifies relationships are parsed with targets in the raw spec map.
    fn parse_relationship_specs() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Scope "Root"
{
    rel material:binding = </Mat>
}
            "#,
        );

        let data = parser.parse().unwrap();
        let rel_spec = data
            .get(&sdf::path("/Root.material:binding").unwrap())
            .expect("missing relationship spec");
        let targets = rel_spec
            .get(FieldKey::TargetPaths.as_str())
            .and_then(|v| v.try_as_path_list_op_ref())
            .expect("missing targets on relationship");
        assert_eq!(targets.explicit_items.len(), 1);
        assert_eq!(targets.explicit_items[0].as_str(), "/Mat");
    }

    #[test]
    fn parse_reports_error_span_for_invalid_pseudo_root() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let fixture_path = manifest_dir.join("fixtures/invalid_pseudo_root.usda");
        let data = fs::read_to_string(&fixture_path).expect("read invalid pseudo-root fixture content");

        let mut parser = Parser::new(&data);
        let err = parser
            .parse()
            .expect_err("parser should fail for malformed pseudo-root");
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
    fn parse_crlf_line_endings() {
        // Simulate Windows line endings (\r\n) throughout the file.
        let input = "#usda 1.0\r\n(\r\n    defaultPrim = \"World\"\r\n)\r\n\r\ndef Scope \"World\"\r\n{\r\n}\r\n";
        let mut parser = Parser::new(input);
        let data = parser.parse().unwrap();

        let root = data.get(&sdf::Path::abs_root()).unwrap();
        assert_eq!(root.ty, sdf::SpecType::PseudoRoot);
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
            .get(ChildrenKey::PropertyChildren.as_str())
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
        let value = normals.get("default").unwrap();

        assert_eq!(
            value.try_as_vec_3f_vec_ref().unwrap(),
            &[
                [0_f32, 1.0, 0.0],
                [1.0, 0.0, 0.0],
                [0.0, 1.0, 0.0],
                [0.0, 0.0, 1.0],
                [0.0, 1.0, 0.0],
                [0.0, 0.0, 1.0],
                [1.0, 0.0, 0.0],
            ]
        );

        let order = data.get(&sdf::path("/World.xformOpOrder").unwrap()).unwrap();

        assert_eq!(
            order.get("default").unwrap().to_owned().try_as_token_vec().unwrap(),
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
            .get(FieldKey::Active.as_str())
            .unwrap()
            .to_owned()
            .try_as_bool()
            .unwrap());

        let api = mesh
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

    #[test]
    fn test_inf_value() {
        let data = r#"#usda 1.0

def "Test" {
    float value = -inf
}
"#;
        let mut parser = Parser::new(data);
        let result = parser.parse();
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
    }

    #[test]
    fn test_customdata_parsing() {
        let data = r#"#usda 1.0

over "GLOBAL" (
    customData = {
        string libraryName = "test"
    }
)
{
}
"#;
        let mut parser = Parser::new(data);
        let result = parser.parse();
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
        let data = result.unwrap();
        assert_ne!(data.len(), 0);
    }

    #[test]
    fn parse_schema_issue14() {
        let data = std::fs::read_to_string("fixtures/usdPhysics_schema.usda").unwrap();
        let mut parser = Parser::new(&data);

        let specs = parser.parse().unwrap();

        // Basic sanity checks
        assert_ne!(specs.len(), 0, "Should have parsed some specs");

        // Check that GLOBAL prim exists and has customData
        let global_path = sdf::Path::from_str("/GLOBAL").unwrap();
        assert!(specs.contains_key(&global_path), "Should have /GLOBAL prim");

        let global_spec = &specs[&global_path];
        assert!(global_spec.contains("customData"), "GLOBAL should have customData");

        // Check that PhysicsScene class exists
        let physics_scene_path = sdf::Path::from_str("/PhysicsScene").unwrap();
        assert!(
            specs.contains_key(&physics_scene_path),
            "Should have /PhysicsScene class"
        );

        let physics_scene_spec = &specs[&physics_scene_path];
        assert!(
            physics_scene_spec.contains("customData"),
            "PhysicsScene should have customData"
        );

        // Check that attributes were parsed (e.g., physics:gravityDirection)
        let gravity_attr_path = sdf::Path::from_str("/PhysicsScene.physics:gravityDirection").unwrap();
        assert!(
            specs.contains_key(&gravity_attr_path),
            "Should have physics:gravityDirection attribute"
        );

        // Check that the attribute has customData in its metadata
        let gravity_spec = &specs[&gravity_attr_path];
        assert!(
            gravity_spec.contains("customData"),
            "gravity attribute should have customData"
        );

        println!("Successfully parsed {} specs", specs.len());
    }

    #[test]
    // Ensures relationship metadata is parsed correctly.
    fn parse_relationship_metadata() {
        let mut parser = Parser::new(
            r#"
#usda 1.0
def Xform "root" {
    def Mesh "mesh" (
        prepend apiSchemas = ["MaterialBindingAPI"]
    )
    {
        rel material:binding:physics = </root/Physics/PhysicsMaterial> (
            bindMaterialAs = "weakerThanDescendants"
        )
    }
}
"#,
        );

        let specs = parser.parse().expect("stage parsed");

        let relationship_path = sdf::Path::new("/root/mesh.material:binding:physics").expect("relationship path valid");
        let relationship_spec = specs.get(&relationship_path).expect("relationship spec present");

        let bind_material_as = relationship_spec
            .get("bindMaterialAs")
            .expect("bindMaterialAs metadata present");
        assert_eq!(
            bind_material_as
                .try_as_string_ref()
                .expect("bindMaterialAs stored as string"),
            "weakerThanDescendants"
        );

        let targets = relationship_spec
            .get(FieldKey::TargetPaths.as_str())
            .expect("relationship targets present");
        let list_op = targets
            .try_as_path_list_op_ref()
            .expect("relationship targets stored as path listOp");
        assert_eq!(
            list_op
                .explicit_items
                .first()
                .expect("relationship target present")
                .as_str(),
            "/root/Physics/PhysicsMaterial"
        );
    }

    /// Regression: per-time values inside `.timeSamples = { ... }` must be
    /// parsed under the property's declared type so typed-tuple forms
    /// (`(w, x, y, z)` for `quatf[]`, `(r, g, b)` for `float3[]`,
    /// matrix rows for `matrix4d`) round-trip into the matching
    /// `Value::QuatfVec` / `Vec3fVec` / `Matrix4d` variants. Pixar's
    /// `UsdSkelExamples/HumanFemale.walk.usd` is the canonical example
    /// — its rotation samples are arrays of quaternion tuples and
    /// failed with `Unsupported property metadata value token: Punctuation('(')`
    /// before the type-aware dispatch landed.
    #[test]
    fn parse_typed_tuple_time_samples() {
        let mut parser = Parser::new(
            r#"#usda 1.0
def Xform "Anim"
{
    quatf[] rotations.timeSamples = {
        0: [(1, 0, 0, 0), (0.7071, 0, 0.7071, 0)],
        1: [(0.7071, 0, 0.7071, 0), (0, 0, 1, 0)],
    }
    float3[] translations.timeSamples = {
        0: [(0, 0, 0), (1, 2, 3)],
    }
    matrix4d xformOp:transform.timeSamples = {
        0: ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)),
    }
}
"#,
        );
        let specs = parser.parse().expect("typed timeSamples parsed");

        let rotations = specs
            .get(&sdf::Path::new("/Anim.rotations").unwrap())
            .and_then(|s| s.get(FieldKey::TimeSamples.as_str()))
            .expect("rotations.timeSamples present");
        let samples = match rotations {
            sdf::Value::TimeSamples(s) => s,
            other => panic!("expected TimeSamples, got {other:?}"),
        };
        assert_eq!(samples.len(), 2);
        match &samples[0].1 {
            sdf::Value::QuatfVec(v) => {
                assert_eq!(v.len(), 2);
                assert_eq!(v[0], [1.0, 0.0, 0.0, 0.0]);
            }
            other => panic!("expected QuatfVec for quatf[] sample, got {other:?}"),
        }

        let translations = specs
            .get(&sdf::Path::new("/Anim.translations").unwrap())
            .and_then(|s| s.get(FieldKey::TimeSamples.as_str()))
            .expect("translations.timeSamples present");
        let samples = match translations {
            sdf::Value::TimeSamples(s) => s,
            other => panic!("expected TimeSamples, got {other:?}"),
        };
        match &samples[0].1 {
            sdf::Value::Vec3fVec(v) => {
                assert_eq!(v.len(), 2);
                assert_eq!(v[1], [1.0, 2.0, 3.0]);
            }
            other => panic!("expected Vec3fVec for float3[] sample, got {other:?}"),
        }

        let xform = specs
            .get(&sdf::Path::new("/Anim.xformOp:transform").unwrap())
            .and_then(|s| s.get(FieldKey::TimeSamples.as_str()))
            .expect("xformOp:transform.timeSamples present");
        let samples = match xform {
            sdf::Value::TimeSamples(s) => s,
            other => panic!("expected TimeSamples, got {other:?}"),
        };
        match &samples[0].1 {
            sdf::Value::Matrix4d(m) => {
                assert_eq!(m[0], 1.0);
                assert_eq!(m[5], 1.0);
                assert_eq!(m[10], 1.0);
                assert_eq!(m[15], 1.0);
            }
            other => panic!("expected Matrix4d for matrix4d sample, got {other:?}"),
        }
    }

    /// Regression: per-time values authored as scalar arrays against a
    /// typed `T[]` property must land in the precise typed `Vec`
    /// variant, not the type-blind `Int64Vec` / `DoubleVec` /
    /// `StringVec` fallbacks that `parse_property_metadata_value`
    /// produces.
    #[test]
    fn parse_typed_scalar_array_time_samples() {
        let mut parser = Parser::new(
            r#"#usda 1.0
def Xform "Anim"
{
    int[] indices.timeSamples = {
        0: [1, 2, 3],
    }
    float[] weights.timeSamples = {
        0: [0.25, 0.5, 0.25],
    }
    token[] joints.timeSamples = {
        0: ["Root", "Hip", "Knee"],
    }
    bool[] flags.timeSamples = {
        0: [true, false, true],
    }
}
"#,
        );
        let specs = parser.parse().expect("typed scalar-array timeSamples parsed");

        let take = |path: &str| {
            let value = specs
                .get(&sdf::Path::new(path).unwrap())
                .and_then(|s| s.get(FieldKey::TimeSamples.as_str()))
                .unwrap_or_else(|| panic!("{path}.timeSamples present"));
            match value {
                sdf::Value::TimeSamples(s) => s.clone(),
                other => panic!("expected TimeSamples for {path}, got {other:?}"),
            }
        };

        match &take("/Anim.indices")[0].1 {
            sdf::Value::IntVec(v) => assert_eq!(v, &[1, 2, 3]),
            other => panic!("expected IntVec for int[] sample, got {other:?}"),
        }
        match &take("/Anim.weights")[0].1 {
            sdf::Value::FloatVec(v) => assert_eq!(v, &[0.25, 0.5, 0.25]),
            other => panic!("expected FloatVec for float[] sample, got {other:?}"),
        }
        match &take("/Anim.joints")[0].1 {
            sdf::Value::TokenVec(v) => assert_eq!(v, &["Root", "Hip", "Knee"]),
            other => panic!("expected TokenVec for token[] sample, got {other:?}"),
        }
        match &take("/Anim.flags")[0].1 {
            sdf::Value::BoolVec(v) => assert_eq!(v, &[true, false, true]),
            other => panic!("expected BoolVec for bool[] sample, got {other:?}"),
        }
    }

    /// Regression: bare scalars and `None` authored against a typed
    /// vector property's `.timeSamples` must still parse — the spec
    /// corpus's `attributes.usda` tests parser tolerance with
    /// `vector3f my:attribute.timeSamples = { 3 : 5.67, 6.78 : None, ... }`,
    /// and we don't want the type-aware tuple dispatch to regress
    /// that.
    #[test]
    fn parse_lenient_time_samples_keep_scalar_and_none() {
        let mut parser = Parser::new(
            r#"#usda 1.0
def Xform "X"
{
    custom uniform vector3f my:attribute.timeSamples = {
        3 : 5.67,
        6.78 : None,
        3567.234: -7,
    }
}
"#,
        );
        let specs = parser.parse().expect("lenient timeSamples parsed");
        let value = specs
            .get(&sdf::Path::new("/X.my:attribute").unwrap())
            .and_then(|s| s.get(FieldKey::TimeSamples.as_str()))
            .expect("timeSamples present");
        let samples = match value {
            sdf::Value::TimeSamples(s) => s,
            other => panic!("expected TimeSamples, got {other:?}"),
        };
        assert_eq!(samples.len(), 3);
        assert!(matches!(samples[1].1, sdf::Value::ValueBlock));
    }

    #[test]
    fn parse_reference_asset_only() {
        let mut parser = Parser::new("@./model.usda@");
        let reference = parser.parse_reference().unwrap();
        assert_eq!(reference.asset_path, "./model.usda");
        assert_eq!(reference.prim_path, sdf::Path::default());
    }

    #[test]
    fn parse_reference_asset_with_prim_path() {
        let mut parser = Parser::new("@./model.usda@</Root>");
        let reference = parser.parse_reference().unwrap();
        assert_eq!(reference.asset_path, "./model.usda");
        assert_eq!(reference.prim_path.as_str(), "/Root");
    }

    #[test]
    fn parse_reference_path_only() {
        let mut parser = Parser::new("</Foo>");
        let reference = parser.parse_reference().unwrap();
        assert!(reference.asset_path.is_empty());
        assert_eq!(reference.prim_path.as_str(), "/Foo");
    }

    #[test]
    fn parse_reference_invalid_token() {
        let mut parser = Parser::new("123");
        assert!(parser.parse_reference().is_err());
    }

    #[test]
    fn try_parse_type_scalar() {
        let mut parser = Parser::new("float x");
        let info = parser.try_parse_type().unwrap().unwrap();
        assert_eq!(info.ty, Type::Float);
        assert_eq!(info.type_name, "float");
        assert!(!info.is_array);
        assert_eq!(info.to_string(), "float");
    }

    #[test]
    fn try_parse_type_array_no_space() {
        // After tokenizer change, `float[]` is three tokens: float [ ]
        let mut parser = Parser::new("float[] x");
        let info = parser.try_parse_type().unwrap().unwrap();
        assert_eq!(info.ty, Type::Float);
        assert_eq!(info.type_name, "float");
        assert!(info.is_array);
        assert_eq!(info.to_string(), "float[]");
    }

    #[test]
    fn try_parse_type_array_with_space() {
        let mut parser = Parser::new("int [] x");
        let info = parser.try_parse_type().unwrap().unwrap();
        assert_eq!(info.ty, Type::Int);
        assert!(info.is_array);
        assert_eq!(info.to_string(), "int[]");
    }

    #[test]
    fn try_parse_type_alias() {
        let mut parser = Parser::new("point3f x");
        let info = parser.try_parse_type().unwrap().unwrap();
        assert_eq!(info.ty, Type::Float3);
        assert_eq!(info.type_name, "point3f");
        assert_eq!(info.to_string(), "point3f");
    }

    #[test]
    fn try_parse_type_dictionary() {
        let mut parser = Parser::new("dictionary x");
        let info = parser.try_parse_type().unwrap().unwrap();
        assert_eq!(info.ty, Type::Dictionary);
        assert!(!info.is_array);
    }

    #[test]
    fn try_parse_type_not_a_type() {
        let mut parser = Parser::new("foobar x");
        let info = parser.try_parse_type().unwrap().unwrap();
        assert_eq!(info.ty, Type::Custom);
        assert_eq!(info.type_name, "foobar");
    }

    #[test]
    fn try_parse_type_matrix_array() {
        let mut parser = Parser::new("matrix4d[] x");
        let info = parser.try_parse_type().unwrap().unwrap();
        assert_eq!(info.ty, Type::Matrix4d);
        assert!(info.is_array);
        assert_eq!(info.to_string(), "matrix4d[]");
    }

    /// Array type with space between type name and `[]` parses correctly in a full attribute.
    #[test]
    fn parse_attribute_array_type_with_space() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Scope "Root" {
    int [] myList = [5, 6, 7]
}
"#,
        );
        let data = parser.parse().unwrap();
        let path = sdf::path("/Root").unwrap().append_property("myList").unwrap();
        let spec = data.get(&path).expect("myList spec not found");
        assert_eq!(
            spec.get(FieldKey::TypeName.as_str()),
            Some(&sdf::Value::Token("int[]".into()))
        );
        assert_eq!(spec.get("default"), Some(&sdf::Value::IntVec(vec![5, 6, 7])));
    }

    /// `over` with a type name should parse the type and prim name.
    #[test]
    fn parse_over_with_type_name() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

over MfScope "TestOver"
{
}
"#,
        );
        let data = parser.parse().unwrap();
        let path = sdf::path("/TestOver").unwrap();
        let spec = data.get(&path).expect("TestOver not found");
        assert_eq!(
            spec.get(FieldKey::Specifier.as_str()),
            Some(&sdf::Value::Specifier(sdf::Specifier::Over))
        );
        assert_eq!(
            spec.get(FieldKey::TypeName.as_str()),
            Some(&sdf::Value::Token("MfScope".into()))
        );
    }

    /// Prim metadata `displayName` should be parsed as a string.
    #[test]
    fn parse_prim_display_name() {
        let mut parser = Parser::new(
            r#"
#usda 1.0

def Scope "Root" (
    displayName = "My Root"
)
{
}
"#,
        );
        let data = parser.parse().unwrap();
        let path = sdf::path("/Root").unwrap();
        let spec = data.get(&path).unwrap();
        assert_eq!(spec.get("displayName"), Some(&sdf::Value::String("My Root".into())));
    }

    #[test]
    fn parse_prim_display_name_utf8() {
        let input = "#usda 1.0\ndef Scope \"R\" (\n    displayName = \"\u{1F680}\"\n)\n{\n}\n";
        let mut parser = Parser::new(input);
        let data = parser.parse().unwrap();
        let spec = data.get(&sdf::path("/R").unwrap()).unwrap();
        assert_eq!(spec.get("displayName"), Some(&sdf::Value::String("\u{1F680}".into())));
    }

    #[test]
    fn parse_spline_empty() {
        let mut parser = Parser::new(
            r#"#usda 1.0
def "p" { double x.spline = {} }
"#,
        );
        let data = parser.parse().unwrap();
        let d = data
            .get(&sdf::path("/p.x").unwrap())
            .unwrap()
            .get("spline")
            .unwrap()
            .try_as_dictionary_ref()
            .unwrap();
        assert_eq!(d.get("curveType"), Some(&sdf::Value::Token("bezier".into())));
        assert_eq!(d.get("preExtrapolation"), Some(&sdf::Value::ValueBlock));
        assert!(d.get("knots").unwrap().try_as_value_vec_ref().unwrap().is_empty());
    }

    #[test]
    fn parse_spline_knot_with_tangents() {
        let mut parser = Parser::new(
            r#"#usda 1.0
def "p" {
    float x.spline = {
        hermite,
        10 : 5.0 ; pre (1.0, 2.0) ; post curve (3.0, 4.0)
    }
}
"#,
        );
        let data = parser.parse().unwrap();
        let d = data
            .get(&sdf::path("/p.x").unwrap())
            .unwrap()
            .get("spline")
            .unwrap()
            .try_as_dictionary_ref()
            .unwrap();
        assert_eq!(d.get("curveType"), Some(&sdf::Value::Token("hermite".into())));

        let knots = d.get("knots").unwrap().try_as_value_vec_ref().unwrap();
        assert_eq!(knots.len(), 1);

        let knot = knots[0].try_as_dictionary_ref().unwrap();
        assert_eq!(knot.get("time"), Some(&sdf::Value::Double(10.0)));
        assert_eq!(knot.get("value"), Some(&sdf::Value::Double(5.0)));
        assert_eq!(knot.get("preTangentSlope"), Some(&sdf::Value::Double(1.0)));
        assert_eq!(knot.get("preTangentWidth"), Some(&sdf::Value::Double(2.0)));
        assert_eq!(knot.get("postTangentSlope"), Some(&sdf::Value::Double(3.0)));
        assert_eq!(knot.get("postTangentWidth"), Some(&sdf::Value::Double(4.0)));
        assert_eq!(
            knot.get("nextInterpolationMode"),
            Some(&sdf::Value::Token("curve".into()))
        );
    }

    #[test]
    fn parse_spline_extrapolation_and_loop() {
        let mut parser = Parser::new(
            r#"#usda 1.0
def "p" {
    double x.spline = {
        pre: sloped (2.5),
        post: clamp,
        loop: (1.0, 10.0, 0, 3, 0.5),
        5 : 1.0 & 9.0
    }
}
"#,
        );
        let data = parser.parse().unwrap();
        let d = data
            .get(&sdf::path("/p.x").unwrap())
            .unwrap()
            .get("spline")
            .unwrap()
            .try_as_dictionary_ref()
            .unwrap();

        let pre = d.get("preExtrapolation").unwrap().try_as_dictionary_ref().unwrap();
        assert_eq!(pre.get("mode"), Some(&sdf::Value::Token("sloped".into())));
        assert_eq!(pre.get("slope"), Some(&sdf::Value::Double(2.5)));

        let post = d.get("postExtrapolation").unwrap().try_as_dictionary_ref().unwrap();
        assert_eq!(post.get("mode"), Some(&sdf::Value::Token("clamp".into())));
        assert_eq!(post.get("slope"), Some(&sdf::Value::Double(0.0)));

        let lp = d.get("loopParameters").unwrap().try_as_dictionary_ref().unwrap();
        assert_eq!(lp.get("protoStart"), Some(&sdf::Value::Double(1.0)));
        assert_eq!(lp.get("numPostLoops"), Some(&sdf::Value::Double(3.0)));
        assert_eq!(lp.get("valueOffset"), Some(&sdf::Value::Double(0.5)));

        // `5 : 1.0 & 9.0` — preValue is 1.0, value is 9.0.
        let knot = d.get("knots").unwrap().try_as_value_vec_ref().unwrap()[0]
            .try_as_dictionary_ref()
            .unwrap();
        assert_eq!(knot.get("preValue"), Some(&sdf::Value::Double(1.0)));
        assert_eq!(knot.get("value"), Some(&sdf::Value::Double(9.0)));
    }
}
