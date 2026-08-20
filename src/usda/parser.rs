use super::error::{Ctx, RawError, bail, ensure};
use std::collections::HashMap;

use crate::sdf::{
    self,
    schema::{ChildrenKey, FieldKey},
};
use crate::tf;

use super::cursor::Cursor;
use super::error::ParseError;
use super::token::Token;
use super::types::{self, Type, TypeInfo};

/// Parser translates a list of tokens into structured data.
pub struct Parser<'a> {
    cursor: Cursor<'a>,
}

/// The names a prim or variant body declares: child prims, properties, and
/// variant sets, in authored order.
type PrimBodyNames = (Vec<String>, Vec<String>, Vec<String>);

impl<'a> Parser<'a> {
    pub fn new(data: &'a str) -> Self {
        Self {
            cursor: Cursor::new(data),
        }
    }

    /// Consumes and returns an identifier or keyword-as-name token.
    ///
    /// Keyword tokens (e.g. `rel`, `kind`) are accepted through
    /// `keyword_lexeme`, so they may be used as property or relationship names.
    fn expect_name(&mut self) -> Result<&'a str, RawError> {
        let token = self.cursor.bump()?;
        match token {
            Token::Identifier(s) | Token::NamespacedIdentifier(s) => Ok(s),
            other => other
                .keyword_lexeme()
                .ok_or_else(|| RawError::new(format!("expected name, got {other:?}"))),
        }
    }

    /// Tries to consume a list-op keyword (`add`, `append`, `prepend`, `delete`, `reorder`).
    fn try_list_op(&mut self) -> Result<Option<Token<'a>>, RawError> {
        if matches!(
            self.cursor.peek()?,
            Some(Token::Add | Token::Append | Token::Prepend | Token::Delete | Token::Reorder)
        ) {
            return Ok(Some(self.cursor.bump()?));
        }
        Ok(None)
    }

    /// Parses a single item or a bracketed array of items.
    fn parse_one_or_list<T>(
        &mut self,
        mut parse: impl FnMut(&mut Cursor<'a>) -> Result<T, RawError>,
    ) -> Result<Vec<T>, RawError> {
        if self.cursor.eat(&Token::None)? {
            return Ok(Vec::new());
        }
        if self.cursor.at_punctuation('[')? {
            return types::parse_array_with(&mut self.cursor, parse);
        }
        Ok(vec![parse(&mut self.cursor)?])
    }

    /// Runs `entry` over each item of a delimited block, tolerating `,` and `;`
    /// separators between items.
    fn parse_block(
        &mut self,
        open: char,
        close: char,
        mut entry: impl FnMut(&mut Self) -> Result<(), RawError>,
    ) -> Result<(), RawError> {
        self.cursor.expect_punctuation(open)?;
        loop {
            if self.cursor.eat_punctuation(close)? {
                break;
            }
            entry(self)?;
            while self.cursor.eat_punctuation(',')? || self.cursor.eat_punctuation(';')? {}
        }
        Ok(())
    }

    /// Parse tokens to specs, locating any failure in the source text.
    pub fn parse(mut self) -> Result<HashMap<sdf::Path, sdf::SpecData>, ParseError> {
        self.parse_impl()
            .map_err(|cause| ParseError::new(cause, self.cursor.source(), self.cursor.diagnostic_span()))
    }

    /// Walks the entire token stream, seeding the pseudo root and recursing through every prim.
    fn parse_impl(&mut self) -> Result<HashMap<sdf::Path, sdf::SpecData>, RawError> {
        let mut data = HashMap::new();
        let current_path = sdf::Path::abs_root();

        // Read pseudo root.
        let mut pseudo_root_spec = self.read_pseudo_root().context("Unable to parse pseudo root")?;
        let mut root_children = Vec::new();

        // Read root defs and any layer-level `reorder rootPrims` statements.
        while let Some(token) = self.cursor.peek()? {
            if matches!(token, Token::Reorder) {
                self.read_reorder(&mut pseudo_root_spec)?;
            } else {
                self.read_prim(&current_path, &mut root_children, &mut data)?;
            }
        }

        if !root_children.is_empty() {
            pseudo_root_spec.add(ChildrenKey::PrimChildren, sdf::Value::token_vec(root_children));
        }
        data.insert(current_path.clone(), pseudo_root_spec);
        Ok(data)
    }

    /// Parse the file header/pseudo-root to populate layer-level metadata before prim traversal.
    fn read_pseudo_root(&mut self) -> Result<sdf::SpecData, RawError> {
        // Make sure text file starts with #usda...
        let version = match self.cursor.bump()? {
            Token::Magic(version) => version,
            other => bail!("Text file must start with magic token, got {other:?}"),
        };
        ensure!(version.starts_with("1.0"), "Unsupported USDA version: {version:?}");

        let mut root = sdf::SpecData::new(sdf::SpecType::PseudoRoot);

        if !self.cursor.at_punctuation('(')? {
            return Ok(root);
        }

        const KNOWN_PROPS: &[(&str, TypeInfo<'_>)] = &[
            (FieldKey::DefaultPrim.as_str(), TypeInfo::scalar(Type::Token)),
            (FieldKey::StartTimeCode.as_str(), TypeInfo::scalar(Type::Double)),
            (FieldKey::HasOwnedSubLayers.as_str(), TypeInfo::scalar(Type::Bool)),
            ("doc", TypeInfo::scalar(Type::String)),
            ("endTimeCode", TypeInfo::scalar(Type::Double)),
            ("framePrecision", TypeInfo::scalar(Type::Int)),
            ("framesPerSecond", TypeInfo::scalar(Type::Double)),
            ("metersPerUnit", TypeInfo::scalar(Type::Double)),
            ("timeCodesPerSecond", TypeInfo::scalar(Type::Double)),
            ("upAxis", TypeInfo::scalar(Type::Token)),
        ];

        self.parse_block('(', ')', |this| {
            let next = this
                .cursor
                .bump()
                .context("Unable to fetch next pseudo root property")?;

            match next {
                Token::String(str) => {
                    root.add(FieldKey::Comment, sdf::Value::String(str.into_owned()));
                }
                Token::Doc => {
                    this.cursor.expect_punctuation('=')?;
                    let value = this.cursor.expect_string()?;
                    root.add(FieldKey::Documentation, sdf::Value::String(value.into_owned()));
                }
                Token::SubLayers => {
                    this.cursor.expect_punctuation('=')?;
                    let (sublayers, offsets) =
                        types::parse_sublayers(&mut this.cursor).context("Unable to parse subLayers")?;
                    root.add(FieldKey::SubLayers, sdf::Value::StringVec(sublayers));
                    root.add(FieldKey::SubLayerOffsets, sdf::Value::LayerOffsetVec(offsets));
                }
                Token::Relocates => {
                    this.cursor.expect_punctuation('=')?;
                    let pairs = types::parse_relocates(&mut this.cursor).context("Unable to parse relocates")?;
                    root.add(FieldKey::LayerRelocates, sdf::Value::Relocates(pairs));
                }
                Token::Identifier(name) => {
                    this.cursor.expect_punctuation('=')?;
                    if let Some(&(known_name, info)) = KNOWN_PROPS.iter().find(|(n, _)| *n == name) {
                        let value = types::parse_value(&mut this.cursor, info)
                            .with_context(|| format!("Unable to parse value for {known_name}"))?;
                        root.add(known_name, value);
                    } else {
                        let value = types::parse_untyped_value(&mut this.cursor)
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
        data: &mut HashMap<sdf::Path, sdf::SpecData>,
    ) -> Result<(), RawError> {
        let mut spec = sdf::SpecData::new(sdf::SpecType::Prim);

        let specifier = {
            let specifier_token = self.cursor.bump().context("Unable to read prim specifier")?;
            match specifier_token {
                Token::Def => sdf::Specifier::Def,
                Token::Over => sdf::Specifier::Over,
                Token::Class => sdf::Specifier::Class,
                _ => bail!("Unexpected prim specifier: {specifier_token:?}"),
            }
        };

        let mut name_token = self.cursor.bump()?;
        if let Token::Identifier(prim_type) = name_token {
            spec.add(FieldKey::TypeName, sdf::Value::token(prim_type));
            name_token = self.cursor.bump()?;
        }

        let Token::String(name) = name_token else {
            bail!("Expected prim name string, got {name_token:?}");
        };
        parent_children.push(name.to_string());
        let prim_path = current_path.append_path(name.as_ref())?;

        let mut properties = Vec::new();

        // Optional metadata block.
        if self.cursor.at_punctuation('(')? {
            self.parse_block('(', ')', |this| {
                this.read_prim_metadata_entry(&mut spec)
                    .context("Unable to parse prim metadata entry")
            })?;
        }

        let (children, props, variant_sets) = self.read_prim_body(&prim_path, &mut spec, data)?;
        if !children.is_empty() {
            spec.add(ChildrenKey::PrimChildren, sdf::Value::token_vec(children));
        }
        properties.extend(props);

        spec.add(FieldKey::Specifier, sdf::Value::Specifier(specifier));
        if !properties.is_empty() {
            spec.add(ChildrenKey::PropertyChildren, sdf::Value::token_vec(properties));
        }
        if !variant_sets.is_empty() {
            spec.add(ChildrenKey::VariantSetChildren, sdf::Value::token_vec(variant_sets));
        }
        data.insert(prim_path, spec);

        Ok(())
    }

    /// Parse the body of a prim or variant (`{ ... }`).
    ///
    /// Returns the child prim names, property names, and variant-set names
    /// found in the body ([`PrimBodyNames`]). `owner_spec` is the in-progress
    /// prim/variant spec that owns this body; `reorder` statements write
    /// `primOrder`/`propertyOrder` directly into it.
    fn read_prim_body(
        &mut self,
        path: &sdf::Path,
        owner_spec: &mut sdf::SpecData,
        data: &mut HashMap<sdf::Path, sdf::SpecData>,
    ) -> Result<PrimBodyNames, RawError> {
        let mut children = Vec::new();
        let mut properties = Vec::new();
        let mut suffixed_properties = Vec::<String>::new();
        let mut variant_sets = Vec::new();

        self.parse_block('{', '}', |this| {
            match this.cursor.peek()?.context("Unexpected end of prim body")? {
                Token::Def | Token::Over | Token::Class => {
                    this.read_prim(path, &mut children, data)?;
                }
                Token::VariantSet => {
                    let name = this.read_variant_set(path, data)?;
                    variant_sets.push(name);
                }
                Token::Rel => {
                    this.cursor.bump()?;
                    this.read_relationship(path, false, sdf::Variability::Uniform, &mut properties, data, None)?;
                }
                Token::Reorder => {
                    this.read_reorder(owner_spec)?;
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

    /// Parse `reorder nameChildren = [...]`, `reorder properties = [...]`, or
    /// the layer-level `reorder rootPrims = [...]`.
    ///
    /// These statements set the `primOrder` or `propertyOrder` fields on the
    /// owning prim/variant spec, controlling child/property display order;
    /// `rootPrims` sets `primOrder` on the pseudo-root.
    fn read_reorder(&mut self, owner_spec: &mut sdf::SpecData) -> Result<(), RawError> {
        self.cursor.bump()?; // consume `reorder`

        let token = self
            .cursor
            .bump()
            .context("Expected 'nameChildren' or 'properties' after 'reorder'")?;
        let field_key = match token {
            Token::NameChildren | Token::RootPrims => FieldKey::PrimOrder,
            Token::Properties => FieldKey::PropertyOrder,
            other => bail!("Unsupported reorder target: {other:?}"),
        };

        self.cursor.expect_punctuation('=')?;

        let names = self.parse_one_or_list(|c| Ok(c.expect_string()?.into_owned()))?;
        owner_spec.add(field_key, sdf::Value::token_vec(names));

        Ok(())
    }

    /// Parse a `variantSet "name" = { "variant1" (...) { ... } ... }` block.
    ///
    /// Each variant inside the set is represented as a child prim under a variant set
    /// spec in the scene hierarchy: `/{prim}{vset=name}{variant}`.
    fn read_variant_set(
        &mut self,
        prim_path: &sdf::Path,
        data: &mut HashMap<sdf::Path, sdf::SpecData>,
    ) -> Result<String, RawError> {
        self.cursor.bump()?; // consume `variantSet`

        let name = self
            .cursor
            .expect_string()
            .context("Expected variant set name")?
            .to_string();
        self.cursor.expect_punctuation('=')?;

        // Create the variant set spec.
        let vset_path = prim_path.append_variant_selection(&name, "")?;
        let mut vset_spec = sdf::SpecData::new(sdf::SpecType::VariantSet);
        let mut variant_children = Vec::new();

        // Parse each variant: "VariantName" (...) { ... }
        self.parse_block('{', '}', |this| {
            let variant_name = this
                .cursor
                .expect_string()
                .context("Expected variant name")?
                .to_string();

            variant_children.push(variant_name.clone());

            let variant_path = prim_path.append_variant_selection(&name, &variant_name)?;
            let mut variant_spec = sdf::SpecData::new(sdf::SpecType::Variant);

            // Optional metadata block.
            if this.cursor.at_punctuation('(')? {
                this.parse_block('(', ')', |this| {
                    this.read_prim_metadata_entry(&mut variant_spec)
                        .context("Unable to parse variant metadata entry")
                })?;
            }

            // Variant body.
            let (children, properties, variant_sets) = this.read_prim_body(&variant_path, &mut variant_spec, data)?;
            if !children.is_empty() {
                variant_spec.add(ChildrenKey::PrimChildren, sdf::Value::token_vec(children));
            }
            if !properties.is_empty() {
                variant_spec.add(ChildrenKey::PropertyChildren, sdf::Value::token_vec(properties));
            }
            if !variant_sets.is_empty() {
                variant_spec.add(ChildrenKey::VariantSetChildren, sdf::Value::token_vec(variant_sets));
            }
            data.insert(variant_path, variant_spec);
            Ok(())
        })?;

        vset_spec.add(ChildrenKey::VariantChildren, sdf::Value::token_vec(variant_children));
        data.insert(vset_path, vset_spec);

        Ok(name)
    }

    /// Merge a spec's fields into an existing spec at the given path, or insert it.
    fn merge_spec(data: &mut HashMap<sdf::Path, sdf::SpecData>, path: sdf::Path, spec: sdf::SpecData) {
        use std::collections::hash_map::Entry;
        match data.entry(path) {
            Entry::Occupied(mut e) => e.get_mut().extend_from(spec),
            Entry::Vacant(e) => {
                e.insert(spec);
            }
        }
    }

    /// Create an attribute spec with the standard type/custom/variability fields.
    fn make_attribute_spec(type_info: &TypeInfo<'_>, custom: bool, variability: sdf::Variability) -> sdf::SpecData {
        let mut spec = sdf::SpecData::new(sdf::SpecType::Attribute);
        spec.add(FieldKey::TypeName, sdf::Value::token(type_info.to_string()));
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
        data: &mut HashMap<sdf::Path, sdf::SpecData>,
    ) -> Result<(), RawError> {
        let mut custom = false;
        let list_op = self.try_list_op()?;

        if self.cursor.eat(&Token::Custom)? {
            custom = true;
        }

        // `varying` precedes `rel` for a varying relationship, and precedes the
        // type name for an attribute, so it is consumed before either.
        let varying = self.cursor.eat(&Token::Varying)?;
        if self.cursor.eat(&Token::Rel)? {
            let variability = match varying {
                true => sdf::Variability::Varying,
                false => sdf::Variability::Uniform,
            };
            return self.read_relationship(current_path, custom, variability, properties, data, list_op);
        }

        let mut spec = sdf::SpecData::new(sdf::SpecType::Attribute);
        let mut variability = sdf::Variability::Varying;
        if !varying && self.cursor.eat(&Token::Uniform)? {
            variability = sdf::Variability::Uniform;
        }

        let type_info = types::parse_type(&mut self.cursor)?.context("attribute type expected")?;

        let name = self.expect_name().context("attribute name expected")?;

        // Read optional `.suffix` (e.g. `.connect`, `.timeSamples`, `.spline`).
        let suffix = if self.cursor.eat_punctuation('.')? {
            Some(self.cursor.bump()?)
        } else {
            None
        };

        // Check for metadata before checking for assignment
        if self.cursor.at_punctuation('(')? {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse attribute metadata")?;
        }

        if matches!(suffix, Some(Token::Connect)) {
            push_unique(suffixed_properties, name);
            if self.cursor.eat_punctuation('=')? {
                let list_op = match list_op {
                    Some(op) => Some(op),
                    None => self.try_list_op()?,
                };
                // Connection targets are anchored to the owning prim, like
                // relationship targets, so a relative path (`<../sibling>`) is
                // stored absolute.
                let targets: Vec<sdf::Path> = self
                    .parse_one_or_list(|c| types::parse_path_reference(c).context("Connection path expected"))
                    .context("Unable to parse connection targets")?
                    .into_iter()
                    .map(|p| current_path.make_absolute(&p))
                    .collect();
                let path = current_path.append_property(name)?;

                let spec = data
                    .entry(path)
                    .or_insert_with(|| Self::make_attribute_spec(&type_info, custom, variability));

                let list_op = apply_list_op(list_op, targets).context("Unable to build connection listOp")?;
                spec.add_list_op(FieldKey::ConnectionPaths, sdf::Value::PathListOp(list_op));
            }
            return Ok(());
        }

        if matches!(suffix, Some(Token::TimeSamples)) {
            push_unique(suffixed_properties, name);
            self.cursor.expect_punctuation('=')?;
            let samples = types::parse_time_samples(&mut self.cursor, type_info)?;
            let path = current_path.append_property(name)?;

            let spec = data
                .entry(path)
                .or_insert_with(|| Self::make_attribute_spec(&type_info, custom, variability));
            spec.add(FieldKey::TimeSamples, sdf::Value::TimeSamples(samples));
            return Ok(());
        }

        if matches!(suffix, Some(Token::Spline)) {
            push_unique(suffixed_properties, name);
            self.cursor.expect_punctuation('=')?;
            let spline = types::parse_spline(&mut self.cursor)?;
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
        if !self.cursor.at_punctuation('=')? {
            let path = current_path.append_property(name)?;
            push_unique(properties, name);

            let mut base = Self::make_attribute_spec(&type_info, custom, variability);
            base.extend_from(spec);
            Self::merge_spec(data, path, base);
            return Ok(());
        }

        self.cursor.expect_punctuation('=')?;
        let value = types::parse_value(&mut self.cursor, type_info)?;
        let path = current_path.append_property(name)?;

        if self.cursor.at_punctuation('(')? {
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

    /// Parse the metadata block attached to a property and stash entries on the spec.
    fn parse_property_metadata(&mut self, spec: &mut sdf::SpecData) -> Result<(), RawError> {
        self.parse_block('(', ')', |this| {
            let list_op = this.try_list_op()?;

            let name_token = this.cursor.bump()?;
            let name = match name_token {
                // Bare string in property metadata is a comment.
                Token::String(s) => {
                    spec.add(FieldKey::Comment, sdf::Value::String(s.into_owned()));
                    return Ok(());
                }
                Token::Identifier(s) | Token::NamespacedIdentifier(s) => s.to_owned(),
                Token::CustomData => "customData".to_owned(),
                Token::Doc => FieldKey::Documentation.as_str().to_owned(),
                other => other
                    .keyword_lexeme()
                    .map(str::to_owned)
                    .ok_or_else(|| RawError::new(format!("Unexpected attribute metadata name token: {other:?}")))?,
            };

            this.cursor.expect_punctuation('=')?;
            let value = types::parse_untyped_value(&mut this.cursor)
                .with_context(|| format!("Unable to parse attribute metadata value for {name}"))?;

            // Some attribute metadata fields are registered as `token` in their
            // schema's plugInfo (UsdGeom's `interpolation`, UsdShade's
            // `renderType`); an untyped metadata value parses as a string, so
            // retag those as tokens.
            let value = match (name.as_str(), value) {
                ("interpolation" | "renderType", sdf::Value::String(s)) => sdf::Value::token(s),
                (_, value) => value,
            };

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

    fn read_relationship(
        &mut self,
        current_path: &sdf::Path,
        custom: bool,
        variability: sdf::Variability,
        properties: &mut Vec<String>,
        data: &mut HashMap<sdf::Path, sdf::SpecData>,
        outer_list_op: Option<Token<'a>>,
    ) -> Result<(), RawError> {
        let name = self.expect_name().context("relationship name expected")?;

        let mut spec = sdf::SpecData::new(sdf::SpecType::Relationship);
        if custom {
            spec.add(FieldKey::Custom, sdf::Value::Bool(true));
        }
        // `variability` falls back to varying, so only a uniform relationship —
        // the plain `rel` spelling — carries the field.
        if variability == sdf::Variability::Uniform {
            spec.add(FieldKey::Variability, sdf::Value::Variability(variability));
        }

        // Check for metadata before or instead of assignment
        if self.cursor.at_punctuation('(')? {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse relationship metadata")?;
        }

        let path = current_path.append_property(name)?;
        push_unique(properties, name);

        // Check if there's an assignment
        if !self.cursor.at_punctuation('=')? {
            Self::merge_spec(data, path, spec);
            return Ok(());
        }

        self.cursor.expect_punctuation('=')?;
        let list_op = match outer_list_op {
            Some(op) => Some(op),
            None => self.try_list_op()?,
        };
        let targets: Vec<sdf::Path> = self
            .parse_one_or_list(types::parse_path_reference)
            .context("Unable to parse relationship targets")?
            .into_iter()
            .filter(|p| !p.is_empty())
            .map(|p| path.make_absolute(&p))
            .collect();

        let list_op = apply_list_op(list_op, targets).context("Unable to build relationship targets listOp")?;
        spec.add_list_op(FieldKey::TargetPaths, sdf::Value::PathListOp(list_op));

        if self.cursor.at_punctuation('(')? {
            self.parse_property_metadata(&mut spec)
                .context("Unable to parse relationship metadata")?;
        }

        Self::merge_spec(data, path, spec);
        Ok(())
    }

    /// Parse prim metadata contained either within parentheses or directly after the prim
    /// declaration (until `{` is encountered).
    /// Parse a single prim metadata assignment, honoring list ops for supported fields.
    fn read_prim_metadata_entry(&mut self, spec: &mut sdf::SpecData) -> Result<(), RawError> {
        let list_op = self.try_list_op()?;
        let name_token = self.cursor.bump()?;

        let name = match name_token {
            // Bare string in metadata is a comment.
            Token::String(s) => {
                spec.add(FieldKey::Comment, sdf::Value::String(s.into_owned()));
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

        self.cursor.expect_punctuation('=')?;

        match name {
            n if n == FieldKey::Active.as_str() => {
                let value = types::parse_token::<bool>(&mut self.cursor).context("Unable to parse active flag")?;
                spec.add(FieldKey::Active, sdf::Value::Bool(value));
            }
            "apiSchemas" => {
                let values = self
                    .parse_one_or_list(types::parse_token::<tf::Token>)
                    .context("Unable to parse apiSchemas list")?;
                let list_op = apply_list_op(list_op, values).context("Unable to build apiSchemas listOp")?;
                spec.add_list_op("apiSchemas", sdf::Value::TokenListOp(list_op));
            }
            n if n == FieldKey::References.as_str() => {
                let references = self
                    .parse_one_or_list(types::parse_reference)
                    .context("Unable to parse references")?;
                let list_op = apply_list_op(list_op, references).context("Unable to build references listOp")?;
                spec.add_list_op(FieldKey::References, sdf::Value::ReferenceListOp(list_op));
            }
            n if n == FieldKey::Payload.as_str() => {
                let payloads = self
                    .parse_one_or_list(types::parse_payload)
                    .context("Unable to parse payloads")?;
                let list_op = apply_list_op(list_op, payloads).context("Unable to build payload listOp")?;
                spec.add_list_op(FieldKey::Payload, sdf::Value::PayloadListOp(list_op));
            }
            n if n == FieldKey::InheritPaths.as_str() => {
                let paths = self.parse_one_or_list(types::parse_path_reference)?;
                // Arc targets address prims. Relationship-target and connection
                // paths share this production and do allow a variant selection,
                // so the restriction is applied here rather than in the parse.
                for p in &paths {
                    types::reject_variant_selection_in_path(p, "Inherit")?;
                }
                let list_op = apply_list_op(list_op, paths).context("Unable to build inherits listOp")?;
                spec.add_list_op(FieldKey::InheritPaths, sdf::Value::PathListOp(list_op));
            }
            n if n == FieldKey::Kind.as_str() => {
                ensure!(list_op.is_none(), "kind metadata does not support list ops");
                let value = types::parse_token::<String>(&mut self.cursor).context("Unable to parse kind metadata")?;
                spec.add(FieldKey::Kind, sdf::Value::token(value));
            }
            "customData" => {
                ensure!(list_op.is_none(), "customData metadata does not support list ops");
                let value =
                    types::parse_untyped_value(&mut self.cursor).context("Unable to parse customData dictionary")?;
                spec.add("customData", value);
            }
            n if n == FieldKey::Documentation.as_str() => {
                ensure!(list_op.is_none(), "doc metadata does not support list ops");
                let value = types::parse_token::<String>(&mut self.cursor).context("Unable to parse doc metadata")?;
                spec.add(FieldKey::Documentation, sdf::Value::String(value));
            }
            n if n == FieldKey::AssetInfo.as_str() => {
                ensure!(list_op.is_none(), "assetInfo does not support list ops");
                let value = types::parse_dictionary(&mut self.cursor).context("Unable to parse assetInfo")?;
                spec.add(FieldKey::AssetInfo, value);
            }
            n if n == FieldKey::VariantSelection.as_str() => {
                ensure!(list_op.is_none(), "variants does not support list ops");
                let dict = types::parse_dictionary(&mut self.cursor).context("Unable to parse variants")?;
                if let sdf::Value::Dictionary(map) = dict {
                    let selections: HashMap<String, String> = map
                        .into_iter()
                        .filter_map(|(k, v)| v.try_as_string().map(|s| (k, s.clone())))
                        .collect();
                    spec.add(FieldKey::VariantSelection, sdf::Value::VariantSelectionMap(selections));
                }
            }
            n if n == FieldKey::VariantSetNames.as_str() => {
                let values = self
                    .parse_one_or_list(types::parse_token::<tf::Token>)
                    .context("Unable to parse variantSets")?;
                let list_op = apply_list_op(list_op, values).context("Unable to build variantSets listOp")?;
                spec.add_list_op(FieldKey::VariantSetNames, sdf::Value::TokenListOp(list_op));
            }
            n if n == FieldKey::Specializes.as_str() => {
                let paths = self.parse_one_or_list(types::parse_path_reference)?;
                for p in &paths {
                    types::reject_variant_selection_in_path(p, "Specializes")?;
                }
                let list_op = apply_list_op(list_op, paths).context("Unable to build specializes listOp")?;
                spec.add_list_op(FieldKey::Specializes, sdf::Value::PathListOp(list_op));
            }
            n if n == FieldKey::Instanceable.as_str() => {
                ensure!(list_op.is_none(), "instanceable metadata does not support list ops");
                let value = types::parse_bool(&mut self.cursor).context("Unable to parse instanceable flag")?;
                spec.add(FieldKey::Instanceable, sdf::Value::Bool(value));
            }
            n if n == FieldKey::Relocates.as_str() => {
                ensure!(list_op.is_none(), "relocates does not support list ops");
                let pairs = types::parse_relocates(&mut self.cursor).context("Unable to parse relocates")?;
                spec.add(FieldKey::Relocates, sdf::Value::Relocates(pairs));
            }
            "displayName" => {
                ensure!(list_op.is_none(), "displayName does not support list ops");
                let value = self.cursor.expect_string().context("Unable to parse displayName")?;
                spec.add("displayName", sdf::Value::String(value.into_owned()));
            }
            n if n == FieldKey::Permission.as_str() => {
                ensure!(list_op.is_none(), "permission does not support list ops");
                let value = self.cursor.expect_identifier().context("Unable to parse permission")?;
                let perm = match value {
                    "public" => sdf::Permission::Public,
                    "private" => sdf::Permission::Private,
                    other => bail!("Invalid permission value: {other}"),
                };
                spec.add(FieldKey::Permission, sdf::Value::Permission(perm));
            }
            n if n == FieldKey::Prefix.as_str() => {
                ensure!(list_op.is_none(), "prefix does not support list ops");
                let value = self.cursor.expect_string().context("Unable to parse prefix")?;
                spec.add(FieldKey::Prefix, sdf::Value::String(value.into_owned()));
            }
            n if n == FieldKey::Clips.as_str() => {
                ensure!(list_op.is_none(), "clips metadata does not support list ops");
                let value = types::parse_dictionary(&mut self.cursor).context("Unable to parse clips dictionary")?;
                spec.add(FieldKey::Clips, value);
            }
            n if n == FieldKey::ClipSets.as_str() => {
                let values = self
                    .parse_one_or_list(|c| Ok(c.expect_string()?.into_owned()))
                    .context("Unable to parse clipSets list")?;
                let list_op = apply_list_op(list_op, values).context("Unable to build clipSets listOp")?;
                spec.add_list_op(FieldKey::ClipSets, sdf::Value::StringListOp(list_op));
            }
            // Unknown prim metadata - e.g. DCC / Omniverse hints like
            // `hide_in_stage_window` or `no_delete`. The Sdf grammar accepts
            // arbitrary identifier-keyed fields in the metadata block, so
            // tolerate and stash them on the spec rather than failing the
            // parse (matches Pixar, which preserves unrecognized metadata).
            other => {
                ensure!(
                    list_op.is_none(),
                    "list ops are not supported for unknown prim metadata: {other}"
                );
                let value = types::parse_untyped_value(&mut self.cursor)
                    .with_context(|| format!("Unable to parse prim metadata value for {other}"))?;
                spec.add(other, value);
            }
        }

        Ok(())
    }
}

/// Wrap `items` in the list op the `op` keyword names, or an explicit list when
/// no keyword was authored.
fn apply_list_op<T: Default + Clone + PartialEq>(
    op: Option<Token<'_>>,
    items: Vec<T>,
) -> Result<sdf::ListOp<T>, RawError> {
    match op {
        None => Ok(sdf::ListOp::explicit(items)),
        Some(Token::Prepend) => Ok(sdf::ListOp::prepended(items)),
        Some(Token::Append) => Ok(sdf::ListOp::appended(items)),
        Some(Token::Add) => Ok(sdf::ListOp::added(items)),
        Some(Token::Delete) => Ok(sdf::ListOp::deleted(items)),
        Some(Token::Reorder) => Ok(sdf::ListOp::ordered(items)),
        other => bail!("Unsupported list op: {other:?}"),
    }
}

/// Push a string into a Vec if it's not already present.
fn push_unique(vec: &mut Vec<String>, name: &str) {
    if !vec.iter().any(|s| s == name) {
        vec.push(name.to_owned());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf;
    use std::error::Error as StdError;
    use std::fs;
    use std::path::PathBuf;

    #[test]
    fn relationship_variability() {
        let data = crate::usda::parse(
            r#"#usda 1.0

def "Mesh"
{
    rel plain
    varying rel moving
    custom varying rel both
    custom rel owned
}
"#,
        )
        .expect("parses");
        let variability = |path: &str| {
            data.spec(&sdf::Path::new(path).unwrap())
                .expect("spec")
                .fields
                .iter()
                .find(|(key, _)| key == FieldKey::Variability.as_str())
                .map(|(_, value)| value.clone())
        };

        // A relationship is uniform unless it spells `varying`, the reverse of
        // an attribute, and only the uniform case carries the field.
        let uniform = Some(sdf::Value::Variability(sdf::Variability::Uniform));
        assert_eq!(variability("/Mesh.plain"), uniform);
        assert_eq!(variability("/Mesh.owned"), uniform);
        assert_eq!(variability("/Mesh.moving"), None);
        assert_eq!(variability("/Mesh.both"), None);
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
                framePrecision = 6

                defaultPrim = "World"
            )
            "#,
        );

        let pseudo_root = parser.read_pseudo_root().unwrap();

        assert!(
            pseudo_root
                .get(FieldKey::Documentation.as_str())
                .and_then(|v| v.try_as_string_ref())
                .unwrap()
                .eq("test string")
        );

        assert!(
            pseudo_root
                .get("upAxis")
                .and_then(|v| v.try_as_token_ref())
                .unwrap()
                .as_str()
                == "Y"
        );

        // `framePrecision` is an int field — it must decode to `Value::Int`,
        // not the type-blind fallback's `Value::Int64`, so `frame_precision()`
        // reads it back.
        assert_eq!(
            pseudo_root
                .get(FieldKey::FramePrecision.as_str())
                .and_then(|v| v.try_as_int_ref())
                .copied(),
            Some(6)
        );
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
            sdf::Value::Vec3d(values) => assert_eq!(*values, gf::vec3d(5.0, 0.0, 0.0)),
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
            sdf::Value::Token(value) => assert_eq!(value.as_str(), "/OmniverseKit_Persp"),
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

        let render_passes = dict
            .get("RENDER_PASSES")
            .expect("RENDER_PASSES entry")
            .try_as_string_vec_ref()
            .expect("string[] entry");
        assert_eq!(render_passes, &["beauty", "shadow", "reflection"]);

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
        let parser = Parser::new(
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
            prim_children
                .try_as_token_vec()
                .unwrap()
                .into_iter()
                .map(String::from)
                .collect::<Vec<_>>(),
            vec![String::from("Forest_set")]
        );

        let forest_set_prim = data.get(&sdf::path("/Forest_set").unwrap()).unwrap();
        let prim_children = forest_set_prim.get("primChildren").unwrap().to_owned();
        assert_eq!(
            prim_children
                .try_as_token_vec()
                .unwrap()
                .into_iter()
                .map(String::from)
                .collect::<Vec<_>>(),
            vec![String::from("Outskirts"), String::from("Glade")]
        );

        assert!(data.contains_key(&sdf::path("/Forest_set/Outskirts").unwrap()));
        assert!(data.contains_key(&sdf::path("/Forest_set/Glade").unwrap()));
    }

    #[test]
    // Ensures attribute metadata blocks are captured on the owning spec.
    fn parse_attribute_metadata_interpolation() {
        let parser = Parser::new(
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
            .try_as_token_ref()
            .expect("interpolation metadata must be a token");

        assert_eq!(interpolation.as_str(), "faceVarying");
    }

    #[test]
    // Verifies the parser tolerates custom/asset/connect syntax and records connection props.
    fn parse_unsanitized_attributes() {
        let parser = Parser::new(
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
            Some(sdf::Value::Token(t)) if t.as_str() == "token"
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
                sdf::Value::TokenVec(tokens) => Some(tokens.iter().map(|t| t.to_string()).collect::<Vec<String>>()),
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
        let parser = Parser::new(
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
            sdf::Value::Matrix4d(m) => {
                assert_eq!(m.0.len(), 16);
                assert_eq!(m[(0, 0)], 1.0);
                assert_eq!(m[(1, 1)], 1.0);
                assert_eq!(m[(2, 2)], 1.0);
                assert_eq!(m[(3, 3)], 1.0);
            }
            other => panic!("expected gf::Matrix4d, got {other:?}"),
        }
    }

    #[test]
    // Ensures matrix4d array attributes parse into contiguous row-major data.
    fn parse_matrix4d_array_attribute() {
        let parser = Parser::new(
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
    // Every array element type decodes into its own value variant: the unsigned
    // integers carry arrays like their signed counterparts, and `string[]` stays
    // distinct from `token[]` rather than collapsing onto the interned one.
    fn parse_array_element_types() {
        let data = crate::usda::parse(
            r#"#usda 1.0

def "Root"
{
    uint[] small = [1, 2, 4294967295]
    uint64[] big = [1000, 18446744073709551615]
    string[] names = ["a b", "c"]
    token[] ids = ["a b", "c"]
}
"#,
        )
        .expect("parses");

        let value = |name: &str| {
            data.spec(&sdf::path(format!("/Root.{name}")).unwrap())
                .expect("spec")
                .get(FieldKey::Default.as_str())
                .expect("default")
                .clone()
        };

        assert_eq!(value("small").try_as_uint_vec().expect("uint[]"), vec![1, 2, u32::MAX]);
        assert_eq!(
            value("big").try_as_uint_64_vec().expect("uint64[]"),
            vec![1000, u64::MAX]
        );
        assert_eq!(
            value("names").try_as_string_vec().expect("string[]"),
            vec!["a b".to_string(), "c".to_string()]
        );
        assert_eq!(
            value("ids").try_as_token_vec().expect("token[]"),
            vec![tf::Token::from("a b"), tf::Token::from("c")]
        );
    }

    #[test]
    // Validates output declarations and connection attributes produce specs with connection paths.
    fn parse_material_output_connections() {
        let parser = Parser::new(
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
        assert!(props.iter().any(|t| t.as_str() == "outputs:surface"));

        let output = data
            .get(&sdf::path("/Mat.outputs:surface").unwrap())
            .expect("missing outputs:surface spec");
        assert!(matches!(
            output.get(FieldKey::TypeName.as_str()),
            Some(sdf::Value::Token(t)) if t.as_str() == "token"
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
        let parser = Parser::new(
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
    fn error_span_pseudo_root() {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let fixture_path = manifest_dir.join("fixtures/invalid_pseudo_root.usda");
        let data = fs::read_to_string(&fixture_path).expect("read invalid pseudo-root fixture content");

        let error = Parser::new(&data)
            .parse()
            .expect_err("parser should fail for malformed pseudo-root");

        assert_eq!(error.line(), 4, "unexpected error line");
        assert_eq!(error.column(), 5, "unexpected error column");
        assert!(
            error.snippet().trim_start().starts_with('='),
            "snippet should hold the offending line, got: {:?}",
            error.snippet()
        );

        let message = error.to_string();
        assert!(
            message.contains("Unable to parse pseudo root"),
            "error should mention pseudo-root parse failure, got: {message}"
        );
        assert!(message.contains(" --> 4:5"), "got: {message}");
        assert!(
            message.ends_with("4 |     =\n  |     ^"),
            "caret should align with the offending token, got: {message}"
        );
    }

    #[test]
    fn error_renders_caret() {
        let error = Parser::new("#usda 1.0\ndef Scope \"A\"\n{\n    float x = =\n}\n")
            .parse()
            .expect_err("`=` is not a value");

        assert!(
            error
                .to_string()
                .ends_with("  |\n4 |     float x = =\n  |               ^"),
            "caret should sit under the offending token, got: {error}"
        );
    }

    #[test]
    fn error_chain_exposes_cause() {
        let error = Parser::new(
            "#usda 1.0
def Scope \"A\"
{
    rel r = </Bad..Path>
}
",
        )
        .parse()
        .expect_err("malformed target path");

        // The wrapper must not truncate the chain: the typed root error stays
        // reachable through `std::error::Error::source`.
        let mut link: Option<&(dyn StdError + 'static)> = Some(&error);
        let mut found = false;
        while let Some(current) = link {
            if current.downcast_ref::<sdf::PathParseError>().is_some() {
                found = true;
                break;
            }
            link = current.source();
        }
        assert!(found, "typed path error should survive the wrapper, got: {error}");
    }

    #[test]
    fn error_names_source() {
        let error = Parser::new("nope\n")
            .parse()
            .expect_err("missing magic token")
            .with_source_name("scene.usda");

        assert!(error.to_string().contains(" --> scene.usda:1:1"), "got: {error}");
    }

    #[test]
    fn error_at_eof() {
        // The prim body is never closed, so the failure lands at end of input.
        let input = "#usda 1.0\ndef Scope \"A\"\n{\n";
        let error = Parser::new(input).parse().expect_err("unterminated prim body");

        // The last line of the file, not the empty one past its final newline.
        assert_eq!(error.line(), 3);
        assert_eq!(error.snippet(), "{");
    }

    #[test]
    fn error_at_lex_failure() {
        let error = Parser::new("#usda 1.0\ndef Scope \"A\"\n{\n    float x = %\n}\n")
            .parse()
            .expect_err("`%` does not lex");

        // The location points at the invalid lexeme.
        assert_eq!(error.line(), 4);
        assert_eq!(error.column(), 15);
    }

    #[test]
    fn error_tab_alignment() {
        let error = Parser::new("#usda 1.0\ndef Scope \"A\"\n{\n\tfloat x = =\n}\n")
            .parse()
            .expect_err("`=` is not a value");

        let rendered = error.to_string();
        let caret = rendered.lines().last().expect("caret line");
        assert!(caret.starts_with("  | \t"), "tabs must be preserved, got: {caret:?}");
    }

    #[test]
    fn parse_crlf_line_endings() {
        // Simulate Windows line endings (\r\n) throughout the file.
        let input = "#usda 1.0\r\n(\r\n    defaultPrim = \"World\"\r\n)\r\n\r\ndef Scope \"World\"\r\n{\r\n}\r\n";
        let parser = Parser::new(input);
        let data = parser.parse().unwrap();

        let root = data.get(&sdf::Path::abs_root()).unwrap();
        assert_eq!(root.ty, sdf::SpecType::PseudoRoot);
    }

    #[test]
    // Exercises a wide set of attribute types to validate scalar/array decoding.
    fn parse_attributes() {
        let parser = Parser::new(
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
            props.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
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
                gf::vec3f(0.0, 1.0, 0.0),
                gf::vec3f(1.0, 0.0, 0.0),
                gf::vec3f(0.0, 1.0, 0.0),
                gf::vec3f(0.0, 0.0, 1.0),
                gf::vec3f(0.0, 1.0, 0.0),
                gf::vec3f(0.0, 0.0, 1.0),
                gf::vec3f(1.0, 0.0, 0.0),
            ]
        );

        let order = data.get(&sdf::path("/World.xformOpOrder").unwrap()).unwrap();

        assert_eq!(
            order
                .get("default")
                .unwrap()
                .to_owned()
                .try_as_token_vec()
                .unwrap()
                .into_iter()
                .map(String::from)
                .collect::<Vec<_>>(),
            vec![String::from("xformOp:translate"), String::from("xformOp:rotateXYZ")]
        );
    }

    #[test]
    // Ensures pseudo-root parsing records sublayer paths and their offsets.
    fn test_parse_sublayers_in_pseudo_root() {
        let parser = Parser::new(
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
        let parser = Parser::new(
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

        assert!(
            mesh.get(FieldKey::Active.as_str())
                .unwrap()
                .to_owned()
                .try_as_bool()
                .unwrap()
        );

        let api = mesh
            .get("apiSchemas")
            .unwrap()
            .to_owned()
            .try_as_token_list_op()
            .unwrap();

        assert!(api.explicit_items.is_empty());
        assert_eq!(api.prepended_items, vec![tf::Token::from("MaterialBindingAPI")]);
    }

    #[test]
    // Ensures prim reference metadata is parsed with asset/prim path and default offsets.
    fn parse_prim_metadata_references() {
        let parser = Parser::new(
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
    fn prim_metadata_inherits_merge_operators() {
        let parser = Parser::new(
            r#"
#usda 1.0

def "A" (
    prepend inherits = </Pre>
    append inherits = </Post>
)
{
}
            "#,
        );

        let data = parser.parse().unwrap();
        let prim = data.get(&sdf::path("/A").unwrap()).unwrap();
        let inherits = prim
            .get(FieldKey::InheritPaths.as_str())
            .unwrap()
            .to_owned()
            .try_as_path_list_op()
            .unwrap();

        // The second operator statement must not overwrite the first.
        assert_eq!(inherits.prepended_items, vec![sdf::path("/Pre").unwrap()]);
        assert_eq!(inherits.appended_items, vec![sdf::path("/Post").unwrap()]);
    }

    #[test]
    fn test_inf_value() {
        let data = r#"#usda 1.0

def "Test" {
    float value = -inf
}
"#;
        let parser = Parser::new(data);
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
        let parser = Parser::new(data);
        let result = parser.parse();
        assert!(result.is_ok(), "Parse failed: {:?}", result.err());
        let data = result.unwrap();
        assert_ne!(data.len(), 0);
    }

    #[test]
    fn parse_schema_issue14() {
        let data = std::fs::read_to_string("fixtures/usdPhysics_schema.usda").unwrap();
        let parser = Parser::new(&data);

        let specs = parser.parse().unwrap();

        // Basic sanity checks
        assert_ne!(specs.len(), 0, "Should have parsed some specs");

        // Check that GLOBAL prim exists and has customData
        let global_path = sdf::Path::new("/GLOBAL").unwrap();
        assert!(specs.contains_key(&global_path), "Should have /GLOBAL prim");

        let global_spec = &specs[&global_path];
        assert!(global_spec.contains("customData"), "GLOBAL should have customData");

        // Check that PhysicsScene class exists
        let physics_scene_path = sdf::Path::new("/PhysicsScene").unwrap();
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
        let gravity_attr_path = sdf::Path::new("/PhysicsScene.physics:gravityDirection").unwrap();
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
        let parser = Parser::new(
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

    /// An `asset` value inside `.timeSamples = { ... }` parses as an
    /// `AssetPath`, scalar and array alike. The type-blind per-time parser had
    /// no `@...@` arm, so an asset-valued sample failed to parse at all.
    #[test]
    fn parse_asset_time_samples() {
        let parser = Parser::new(
            r#"#usda 1.0
def Material "M"
{
    asset inputs:file.timeSamples = {
        0: @./a.png@,
    }
    asset[] inputs:files.timeSamples = {
        0: [@./a.png@, @./b.png@],
    }
}
"#,
        );
        let specs = parser.parse().expect("asset timeSamples parsed");

        let sample = |path: &str| {
            let value = specs
                .get(&sdf::Path::new(path).unwrap())
                .and_then(|s| s.get(FieldKey::TimeSamples.as_str()))
                .expect("timeSamples present");
            match value {
                sdf::Value::TimeSamples(s) => s[0].1.clone(),
                other => panic!("expected TimeSamples, got {other:?}"),
            }
        };
        match sample("/M.inputs:file") {
            sdf::Value::AssetPath(a) => assert_eq!(a.as_str(), "./a.png"),
            other => panic!("expected AssetPath, got {other:?}"),
        }
        match sample("/M.inputs:files") {
            sdf::Value::AssetPathVec(v) => {
                assert_eq!(v.len(), 2);
                assert_eq!(v[1].as_str(), "./b.png");
            }
            other => panic!("expected AssetPathVec, got {other:?}"),
        }
    }

    /// Regression: per-time values inside `.timeSamples = { ... }` must be
    /// parsed under the property's declared type so typed-tuple forms
    /// (`(w, x, y, z)` for `quatf[]`, `(r, g, b)` for `float3[]`,
    /// matrix rows for `matrix4d`) round-trip into the matching
    /// `Value::QuatfVec` / `Vec3fVec` / `gf::Matrix4d` variants. Pixar's
    /// `UsdSkelExamples/HumanFemale.walk.usd` is the canonical example
    /// — its rotation samples are arrays of quaternion tuples and
    /// failed with `Unsupported property metadata value token: Punctuation('(')`
    /// before the type-aware dispatch landed.
    #[test]
    fn parse_typed_tuple_time_samples() {
        let parser = Parser::new(
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
                assert_eq!(v[0], gf::quatf(1.0, 0.0, 0.0, 0.0));
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
                assert_eq!(v[1], gf::vec3f(1.0, 2.0, 3.0));
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
            other => panic!("expected gf::Matrix4d for matrix4d sample, got {other:?}"),
        }
    }

    /// Regression: per-time values authored as scalar arrays against a
    /// typed `T[]` property must land in the precise typed `Vec`
    /// variant, not the type-blind `Int64Vec` / `DoubleVec` /
    /// `StringVec` fallbacks that `types::parse_untyped_value`
    /// produces.
    #[test]
    fn parse_typed_scalar_array_time_samples() {
        let parser = Parser::new(
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
            sdf::Value::TokenVec(v) => assert_eq!(
                v.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
                ["Root", "Hip", "Knee"]
            ),
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
        let parser = Parser::new(
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

    /// A composition-arc target path containing a variant selection is rejected
    /// at parse time, mirroring C++ `Sdf_TextFileFormatParser`. The selection
    /// may sit anywhere in the path, not only as the final element.
    #[test]
    fn arc_path_variant_selection_rejected() {
        let arc = |meta: &str| {
            let text = format!("#usda 1.0\ndef \"A\" (\n{meta}\n)\n{{\n}}\n");
            Parser::new(&text).parse()
        };
        assert!(arc("    inherits = </Class{vset=sel}_class>").is_err(), "inherit");
        assert!(arc("    specializes = </Base{vset=sel}Sub>").is_err(), "specializes");
        assert!(
            arc("    references = @./r.usd@</Group{v=x}Model>").is_err(),
            "reference"
        );
        assert!(arc("    payload = @./p.usd@</Group{v=x}Model>").is_err(), "payload");
        assert!(
            arc("    relocates = { </A{v=x}B>: </A/C> }").is_err(),
            "relocate source"
        );
        assert!(
            arc("    relocates = { </A/B>: </A{v=x}C> }").is_err(),
            "relocate target"
        );
    }

    /// Valid arc paths without variant selections still parse, and a variant
    /// selection in a `variants` opinion (which is not a path) is unaffected.
    #[test]
    fn arc_path_without_variant_selection_ok() {
        let text = "#usda 1.0\ndef \"A\" (\n    inherits = </Class>\n    references = @./r.usd@</Model>\n    variants = { string v = \"x\" }\n)\n{\n}\n";
        assert!(Parser::new(text).parse().is_ok());
    }

    /// Layer-level `reorder rootPrims` sets `primOrder` on the pseudo-root,
    /// the same field `reorder nameChildren` uses inside a prim body.
    #[test]
    fn reorder_root_prims() {
        let text = "#usda 1.0\nreorder rootPrims = [\"B\", \"A\"]\ndef \"A\" {}\ndef \"B\" {}\n";
        let data = Parser::new(text).parse().expect("reorder rootPrims parses");
        let order = data
            .get(&sdf::Path::abs_root())
            .unwrap()
            .get(FieldKey::PrimOrder.as_str())
            .expect("primOrder on pseudo-root")
            .clone()
            .try_as_token_vec()
            .expect("primOrder is a token vec");
        assert_eq!(
            order.into_iter().map(String::from).collect::<Vec<_>>(),
            vec!["B".to_string(), "A".to_string()]
        );
    }

    /// Array type with space between type name and `[]` parses correctly in a full attribute.
    #[test]
    fn parse_attribute_array_type_with_space() {
        let parser = Parser::new(
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
        let parser = Parser::new(
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

    /// `timecode` / `timecode[]` attributes parse to `Value::TimeCode(Vec)`.
    #[test]
    fn parse_timecode_attribute() {
        let parser = Parser::new(
            r#"#usda 1.0
def "P" {
    uniform timecode startTime = 24
    timecode[] beats = [0, 12, 24]
}
"#,
        );
        let data = parser.parse().unwrap();
        assert_eq!(
            data.get(&sdf::path("/P.startTime").unwrap()).unwrap().get("default"),
            Some(&sdf::Value::TimeCode(sdf::TimeCode(24.0))),
        );
        assert_eq!(
            data.get(&sdf::path("/P.beats").unwrap()).unwrap().get("default"),
            Some(&sdf::Value::TimeCodeVec(vec![
                sdf::TimeCode(0.0),
                sdf::TimeCode(12.0),
                sdf::TimeCode(24.0)
            ])),
        );
    }

    /// Scalar `timecode` time samples resolve to `Value::TimeCode` per
    /// sample rather than the type-blind path's `Int64` / `Double`.
    #[test]
    fn parse_timecode_time_samples() {
        let parser = Parser::new(
            r#"#usda 1.0
def "P" {
    timecode cue.timeSamples = {
        0: 24,
        1: 48.5,
    }
}
"#,
        );
        let data = parser.parse().unwrap();
        let cue = data
            .get(&sdf::path("/P.cue").unwrap())
            .unwrap()
            .get(sdf::FieldKey::TimeSamples.as_str())
            .expect("cue.timeSamples present");
        let samples = cue.try_as_time_samples_ref().expect("TimeSamples");
        assert_eq!(samples[0].1, sdf::Value::TimeCode(sdf::TimeCode(24.0)));
        assert_eq!(samples[1].1, sdf::Value::TimeCode(sdf::TimeCode(48.5)));
    }

    /// Prim metadata `displayName` should be parsed as a string.
    #[test]
    fn parse_prim_display_name() {
        let parser = Parser::new(
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
    fn parse_tolerates_unknown_prim_metadata() {
        // DCC / Omniverse author non-standard prim metadata; the parser must
        // not choke on it, and should stash the fields on the spec.
        let parser = Parser::new(
            r#"#usda 1.0

def Xform "Root" (
    hide_in_stage_window = false
    no_delete = true
    custom_label = "hi"
    custom_rank = 5
)
{
}
"#,
        );
        let data = parser.parse().unwrap();
        let spec = data.get(&sdf::path("/Root").unwrap()).unwrap();
        assert_eq!(
            spec.get("hide_in_stage_window"),
            Some(&sdf::Value::Token("false".into()))
        );
        assert_eq!(spec.get("no_delete"), Some(&sdf::Value::Token("true".into())));
        assert_eq!(spec.get("custom_label"), Some(&sdf::Value::String("hi".into())));
        assert_eq!(spec.get("custom_rank"), Some(&sdf::Value::Int64(5)));
    }

    #[test]
    fn parse_prim_display_name_utf8() {
        let input = "#usda 1.0\ndef Scope \"R\" (\n    displayName = \"\u{1F680}\"\n)\n{\n}\n";
        let parser = Parser::new(input);
        let data = parser.parse().unwrap();
        let spec = data.get(&sdf::path("/R").unwrap()).unwrap();
        assert_eq!(spec.get("displayName"), Some(&sdf::Value::String("\u{1F680}".into())));
    }

    #[test]
    fn parse_spline_empty() {
        let parser = Parser::new(
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
        let parser = Parser::new(
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
        let parser = Parser::new(
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
