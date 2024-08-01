use std::{any::type_name, collections::HashMap, fmt::Debug, iter::Peekable, str::FromStr};

use anyhow::{anyhow, bail, ensure, Context, Result};

use crate::sdf::{self, schema::FieldKey};

use super::tok;

/// Parser translates a list of tokens into structured data.
pub struct Parser<'a> {
    iter: Peekable<tok::Tokenizer<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(data: &'a str) -> Self {
        let tok = tok::Tokenizer::new(data);
        Self { iter: tok.peekable() }
    }

    #[inline]
    fn fetch_next(&mut self) -> Result<(tok::Type, &'a str)> {
        let next = self.iter.next().context("Unexpected end of tokens")?;
        let token = next?;

        Ok((token.ty, token.str))
    }

    #[inline]
    fn peek_next(&mut self) -> Option<(tok::Type, &'a str)> {
        self.iter
            .peek()
            .and_then(|result| result.as_ref().ok())
            .map(|pair| (pair.ty, pair.str))
    }

    fn ensure_next(&mut self, ty: tok::Type, value: &str) -> Result<()> {
        let (nty, str) = self.fetch_next()?;

        ensure!(nty == ty, "Unexpected token type (want: {:?}, got {:?})", ty, nty);
        ensure!(str == value, "Unexpected token value (want: {}, got: {})", value, str);

        Ok(())
    }

    #[inline]
    fn ensure_pun(&mut self, value: &str) -> Result<()> {
        self.ensure_next(tok::Type::Punctuation, value)
    }

    fn fetch_str(&mut self) -> Result<&str> {
        let (ty, str) = self.fetch_next()?;

        ensure!(
            ty == tok::Type::String,
            "Unexpected token type {:?} (want {:?})",
            ty,
            tok::Type::String
        );

        Ok(str)
    }

    /// Parse tokens to specs.
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

        pseudo_root_spec.add("primChildren", sdf::Value::TokenVec(root_children));

        data.insert(current_path.clone(), pseudo_root_spec);
        Ok(data)
    }

    fn read_pseudo_root(&mut self) -> Result<sdf::Spec> {
        // Make sure text file starts with #usda...
        {
            let (ty, str) = self.fetch_next().context("Unable to read first line")?;

            ensure!(
                ty == tok::Type::Magic,
                "Text file must start with magic token, got {:?}",
                ty
            );

            ensure!(str == "#usda 1.0", "File must start with '#usda 1.0', got: {:?}", str);
        }

        let mut root = sdf::Spec::new(sdf::SpecType::PseudoRoot);

        if self.peek_next() != Some((tok::Type::Punctuation, "(")) {
            return Ok(root);
        }

        // Eat (
        self.ensure_next(tok::Type::Punctuation, "(")?;

        const KNOWN_PROPS: &[(&str, sdf::ValueType)] = &[
            ("defaultPrim", sdf::ValueType::Token),
            ("doc", sdf::ValueType::String),
            ("endTimeCode", sdf::ValueType::Uint64),
            ("framesPerSecond", sdf::ValueType::Uint64),
            ("metersPerUnit", sdf::ValueType::Double),
            ("startTimeCode", sdf::ValueType::Uint64),
            ("subLayers", sdf::ValueType::StringVec),
            ("timeCodesPerSecond", sdf::ValueType::Uint64),
            ("upAxis", sdf::ValueType::String),
        ];

        // Read pseudo root properties
        loop {
            let next = self.fetch_next().context("Unable to fetch next pseudo root property")?;

            match next {
                (tok::Type::Punctuation, ")") => break,

                // String without doc = ?
                (tok::Type::String, str) => {
                    root.add(FieldKey::Documentation.as_str(), sdf::Value::String(str.to_string()));
                }

                // doc = "?"
                (tok::Type::Doc, _) => {
                    self.ensure_pun("=")?;
                    let value = self.fetch_str()?;
                    root.add("doc", sdf::Value::String(value.to_string()))
                }

                // Known type
                (tok::Type::Identifier, name) => {
                    if let Some((name, ty)) = KNOWN_PROPS.iter().copied().find(|(n, _)| *n == name) {
                        self.ensure_pun("=")?;

                        let value = self
                            .parse_value(ty)
                            .with_context(|| format!("Unable to parse value for {}", name))?;
                        root.add(name, value);
                    }
                }

                _ => bail!("Unexpected token {:?}", next),
            }
        }

        Ok(root)
    }

    /// Reads a single primitive.
    ///
    /// This function is called recusrively for nested primitives.
    fn read_prim(
        &mut self,
        current_path: &sdf::Path,
        parent_children: &mut Vec<String>,
        data: &mut HashMap<sdf::Path, sdf::Spec>,
    ) -> Result<()> {
        let mut spec = sdf::Spec::new(sdf::SpecType::Prim);

        // Each primitive starts with specifier.
        // Possible options are:
        //   def - a concrete, defined prim.
        //   over - a speculative override.
        //   class - prims from which other prims inherit.
        //
        // See https://openusd.org/release/usdfaq.html#what-s-the-difference-between-an-over-and-a-typeless-def
        let specifier = {
            let (specifier, _) = self.fetch_next().context("Unable to read prim specifier")?;
            match specifier {
                tok::Type::Def => sdf::Specifier::Def,
                tok::Type::Over => sdf::Specifier::Over,
                tok::Type::Class => sdf::Specifier::Class,
                _ => bail!("Unexpected prim specifier: {:?}", specifier),
            }
        };

        spec.add("specifier", sdf::Value::Specifier(specifier));

        // For "def", read prim schema.
        if specifier == sdf::Specifier::Def {
            let (ty, prim_type) = self.fetch_next().context("Unable to read prim type")?;
            ensure!(ty == tok::Type::Identifier);

            spec.add("typeName", sdf::Value::Token(prim_type.to_string()));
        }

        // Read prim name.
        let name = self.fetch_str().context("Prim name expected")?;
        parent_children.push(name.to_string());

        let prim_path = current_path.append_path(name)?;

        // Either block with () or {}
        let brace = self.fetch_next()?;
        match brace {
            (tok::Type::Punctuation, "(") => {
                todo!("Parse prim properties")
            }
            (tok::Type::Punctuation, "{") => {
                // Parse prim body.

                let mut children = Vec::new();

                loop {
                    // At this point we expect either nested primitives or properties.
                    let next = self.peek_next().context("Unexpected end of prim body")?;

                    match next {
                        // End of block (or empty block).
                        (tok::Type::Punctuation, "}") => {
                            self.fetch_next()?;
                            break;
                        }
                        // Read nested primitive.
                        (ty, _) if ty == tok::Type::Def || ty == tok::Type::Over || ty == tok::Type::Class => {
                            self.read_prim(&prim_path, &mut children, data)
                                .context("Unable to read nested primitive")?;
                        }
                        // Otherwise read property.
                        _ => {
                            self.read_attribute(&prim_path, data)
                                .context("Unable to read attribute")?;
                        }
                    }
                }

                spec.add("primChildren", sdf::Value::TokenVec(children));
            }
            _ => bail!(
                "Unexpected token after prim name, must be either () or {{}}, got: {:?}",
                brace
            ),
        }

        data.insert(prim_path, spec);

        Ok(())
    }

    fn read_attribute(&mut self, _current_path: &sdf::Path, _data: &mut HashMap<sdf::Path, sdf::Spec>) -> Result<()> {
        todo!("not yet implemented")
    }

    fn parse_value(&mut self, ty: sdf::ValueType) -> Result<sdf::Value> {
        let value = match ty {
            // Bool
            sdf::ValueType::Bool => sdf::Value::Bool(self.parse_token()?),
            sdf::ValueType::BoolVec => sdf::Value::BoolVec(self.parse_array()?),

            // Ints
            sdf::ValueType::Uchar => sdf::Value::Uchar(self.parse_token()?),
            sdf::ValueType::Int => sdf::Value::Int(self.parse_token()?),
            sdf::ValueType::Int2 => sdf::Value::Int2(self.parse_tuple::<_, 2>()?),
            sdf::ValueType::Int3 => sdf::Value::Int3(self.parse_tuple::<_, 3>()?),
            sdf::ValueType::Int4 => sdf::Value::Int4(self.parse_tuple::<_, 4>()?),
            sdf::ValueType::IntVec => sdf::Value::IntVec(self.parse_array()?),
            sdf::ValueType::Int2Vec => sdf::Value::Int2Vec(self.parse_tuple_array::<_, 2>()?),
            sdf::ValueType::Int3Vec => sdf::Value::Int3Vec(self.parse_tuple_array::<_, 3>()?),
            sdf::ValueType::Int4Vec => sdf::Value::Int4Vec(self.parse_tuple_array::<_, 4>()?),
            sdf::ValueType::Uint => sdf::Value::Uint(self.parse_token()?),
            sdf::ValueType::Int64 => sdf::Value::Int64(self.parse_token()?),
            sdf::ValueType::Uint64 => sdf::Value::Uint64(self.parse_token()?),

            // Half
            sdf::ValueType::Half => sdf::Value::Half(self.parse_token()?),
            sdf::ValueType::Half2 => sdf::Value::Half2(self.parse_tuple::<_, 2>()?),
            sdf::ValueType::Half3 => sdf::Value::Half3(self.parse_tuple::<_, 3>()?),
            sdf::ValueType::Half4 => sdf::Value::Half4(self.parse_tuple::<_, 4>()?),

            sdf::ValueType::HalfVec => sdf::Value::HalfVec(self.parse_array()?),
            sdf::ValueType::Half2Vec => sdf::Value::Half2Vec(self.parse_tuple_array::<_, 2>()?),
            sdf::ValueType::Half3Vec => sdf::Value::Half3Vec(self.parse_tuple_array::<_, 3>()?),
            sdf::ValueType::Half4Vec => sdf::Value::Half4Vec(self.parse_tuple_array::<_, 4>()?),

            // Float
            sdf::ValueType::Float => sdf::Value::Float(self.parse_token()?),
            sdf::ValueType::Float2 => sdf::Value::Float2(self.parse_tuple::<_, 2>()?),
            sdf::ValueType::Float3 => sdf::Value::Float3(self.parse_tuple::<_, 3>()?),
            sdf::ValueType::Float4 => sdf::Value::Float4(self.parse_tuple::<_, 4>()?),
            sdf::ValueType::FloatVec => sdf::Value::FloatVec(self.parse_array()?),
            sdf::ValueType::Float2Vec => sdf::Value::Float2Vec(self.parse_tuple_array::<_, 2>()?),
            sdf::ValueType::Float3Vec => sdf::Value::Float3Vec(self.parse_tuple_array::<_, 3>()?),
            sdf::ValueType::Float4Vec => sdf::Value::Float4Vec(self.parse_tuple_array::<_, 4>()?),

            // Double
            sdf::ValueType::Double => sdf::Value::Double(self.parse_token()?),
            sdf::ValueType::Double2 => sdf::Value::Double2(self.parse_tuple::<_, 2>()?),
            sdf::ValueType::Double3 => sdf::Value::Double3(self.parse_tuple::<_, 3>()?),
            sdf::ValueType::Double4 => sdf::Value::Double4(self.parse_tuple::<_, 4>()?),
            sdf::ValueType::DoubleVec => sdf::Value::DoubleVec(self.parse_array()?),
            sdf::ValueType::Double2Vec => sdf::Value::Double2Vec(self.parse_tuple_array::<_, 2>()?),
            sdf::ValueType::Double3Vec => sdf::Value::Double3Vec(self.parse_tuple_array::<_, 3>()?),
            sdf::ValueType::Double4Vec => sdf::Value::Double4Vec(self.parse_tuple_array::<_, 4>()?),

            // String
            sdf::ValueType::String => sdf::Value::String(self.fetch_str()?.to_owned()),
            sdf::ValueType::Token => sdf::Value::Token(self.fetch_str()?.to_owned()),

            _ => bail!("Unsupported usda data type: {:?}", ty),
        };

        Ok(value)
    }

    /// Parse a key value pair with type specified (e.g. `type name = value`).
    #[allow(dead_code)]
    fn parse_kv(&mut self) -> Result<(&str, sdf::Value)> {
        // See https://docs.omniverse.nvidia.com/usd/latest/technical_reference/usd-types.html#openusd-data-types
        let (ty, type_str) = self.fetch_next()?;
        ensure!(
            ty == tok::Type::Identifier,
            "Data type must start with identifier, got {:?}",
            ty
        );

        let data_type = match type_str {
            // Bool
            "bool" => sdf::ValueType::Bool,
            "bool[]" => sdf::ValueType::BoolVec,

            // Ints
            "uchar" => sdf::ValueType::Uchar,
            "int" => sdf::ValueType::Int,
            "int2" => sdf::ValueType::Int2,
            "int3" => sdf::ValueType::Int3,
            "int4" => sdf::ValueType::Int4,
            "int[]" => sdf::ValueType::IntVec,
            "int2[]" => sdf::ValueType::Int2Vec,
            "int3[]" => sdf::ValueType::Int3Vec,
            "int4[]" => sdf::ValueType::Int4Vec,
            "uint" => sdf::ValueType::Uint,
            "int64" => sdf::ValueType::Int64,
            "uint64" => sdf::ValueType::Uint64,

            // Half
            "half" => sdf::ValueType::Half,
            "half2" => sdf::ValueType::Half2,
            "half3" => sdf::ValueType::Half3,
            "half4" => sdf::ValueType::Half4,
            "half[]" => sdf::ValueType::HalfVec,
            "half2[]" => sdf::ValueType::Half2Vec,
            "half3[]" => sdf::ValueType::Half3Vec,
            "half4[]" => sdf::ValueType::Half4Vec,

            // Float
            "float" => sdf::ValueType::Float,
            "float2" => sdf::ValueType::Float2,
            "float3" => sdf::ValueType::Float3,
            "float4" => sdf::ValueType::Float4,
            "float[]" => sdf::ValueType::FloatVec,
            "float2[]" => sdf::ValueType::Float2Vec,
            "float3[]" => sdf::ValueType::Float3Vec,
            "float4[]" => sdf::ValueType::Float4Vec,

            // Double
            "double" => sdf::ValueType::Double,
            "double2" => sdf::ValueType::Double2,
            "double3" => sdf::ValueType::Double3,
            "double4" => sdf::ValueType::Double4,
            "double[]" => sdf::ValueType::DoubleVec,
            "double2[]" => sdf::ValueType::Double2Vec,
            "double3[]" => sdf::ValueType::Double3Vec,
            "double4[]" => sdf::ValueType::Double4Vec,

            // String
            "string" => sdf::ValueType::String,

            _ => bail!("Unsupported data type: {}", type_str),
        };

        let (ty, name) = self.fetch_next()?;
        ensure!(ty == tok::Type::Identifier, "Name token is expected, got {:?}", ty);

        self.ensure_next(tok::Type::Punctuation, "=")
            .context("Failed to parse data type")?;

        let value = self.parse_value(data_type)?;

        Ok((name, value))
    }

    /// Parse single token as `T` which can be deserialized from string (such as `int`, `float`, etc).
    fn parse_token<T: FromStr>(&mut self) -> Result<T>
    where
        <T as FromStr>::Err: std::fmt::Debug,
    {
        let (ty, value) = self.fetch_next()?;
        let value = T::from_str(value).map_err(|err| {
            anyhow!(
                "Failed to parse {} from '{}' of type {:?}: {:?}",
                type_name::<T>(),
                value,
                ty,
                err
            )
        })?;

        Ok(value)
    }

    fn parse_tuple<T, const N: usize>(&mut self) -> Result<[T; N]>
    where
        T: FromStr + Default + Copy,
        <T as FromStr>::Err: std::fmt::Debug,
    {
        self.ensure_next(tok::Type::Punctuation, "(")
            .context("Tuples must start with (")?;

        let mut result = [T::default(); N];
        for (i, item) in result.iter_mut().enumerate() {
            if i > 0 {
                self.ensure_next(tok::Type::Punctuation, ",")
                    .context("Comma is expected between tuple values")?
            }

            *item = self.parse_token::<T>()?;
        }

        self.ensure_next(tok::Type::Punctuation, ")")
            .context("Tuples must be closed with )")?;

        Ok(result)
    }

    fn parse_array<T>(&mut self) -> Result<Vec<T>>
    where
        T: FromStr + Default + Copy,
        <T as FromStr>::Err: Debug,
    {
        self.ensure_next(tok::Type::Punctuation, "[")
            .context("Array must start with [")?;

        let mut result = Vec::new();

        loop {
            // Special case - empty array like []
            if self.peek_next() == Some((tok::Type::Punctuation, "]")) {
                self.fetch_next()?; // Consume it.
                break;
            }

            let value = self.parse_token::<T>()?;
            result.push(value);

            match self.fetch_next()? {
                (tok::Type::Punctuation, ",") => continue,
                (tok::Type::Punctuation, "]") => break,
                t => bail!("Either comma or closing bracket expected after value, got: {:?}", t),
            }
        }

        Ok(result)
    }

    fn parse_tuple_array<T, const N: usize>(&mut self) -> Result<Vec<[T; N]>>
    where
        T: FromStr + Default + Copy,
        <T as FromStr>::Err: Debug,
    {
        debug_assert!(N >= 1 && N <= 4);

        self.ensure_next(tok::Type::Punctuation, "[")
            .context("Array must start with [")?;

        let mut result = Vec::new();

        loop {
            if self.peek_next() == Some((tok::Type::Punctuation, "]")) {
                self.fetch_next()?; // Consume closing bracket
                break;
            }

            let tuple = self.parse_tuple()?;
            result.push(tuple);

            match self.fetch_next()? {
                (tok::Type::Punctuation, ",") => continue,
                (tok::Type::Punctuation, "]") => break,
                t => bail!("Unexpected token: {:?}", t),
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let result = parser.parse_tuple_array::<u32, 2>().unwrap();
        assert_eq!(result, vec![[1_u32, 2], [3, 4]]);
    }

    #[test]
    fn parse_bool_type() {
        let mut parser = Parser::new("bool flip = true");
        let (name, value) = parser.parse_kv().unwrap();

        assert_eq!(name, "flip");
        assert_eq!(value.try_as_bool(), Some(true));
    }

    #[test]
    fn parse_str_type() {
        let mut parser = Parser::new(
            r#"
            string upAxis = "y"
            "#,
        );
        let (name, value) = parser.parse_kv().unwrap();
        assert_eq!(name, "upAxis");
        assert_eq!(value.try_as_string(), Some(String::from("y")));
    }

    #[test]
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
            .and_then(|v| v.try_as_string_ref())
            .unwrap()
            .eq("Y"));
    }

    #[test]
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
}
