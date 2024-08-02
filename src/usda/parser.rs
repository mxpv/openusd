use anyhow::{anyhow, bail, ensure, Context, Result};
use std::mem::MaybeUninit;
use std::{any::type_name, collections::HashMap, fmt::Debug, iter::Peekable, str::FromStr};

use crate::sdf::{
    self,
    schema::{ChildrenKey, FieldKey},
};

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

        pseudo_root_spec.add(ChildrenKey::PrimChildren, sdf::Value::TokenVec(root_children));

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
                (tok::Type::Punctuation, ")") => break,

                // String without doc keyword
                (tok::Type::String, str) => {
                    root.add(FieldKey::Documentation, str);
                }

                // doc = "?"
                (tok::Type::Doc, _) => {
                    self.ensure_pun("=")?;
                    let value = self.fetch_str()?;
                    root.add("doc", value);
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

        // For "def", read prim schema.
        if specifier == sdf::Specifier::Def {
            let (ty, prim_type) = self.fetch_next().context("Unable to read prim type")?;
            ensure!(ty == tok::Type::Identifier);

            spec.add(FieldKey::TypeName, sdf::Value::Token(prim_type.to_string()));
        }

        // Read prim name.
        let name = self.fetch_str().context("Prim name expected")?;
        parent_children.push(name.to_string());
        let prim_path = current_path.append_path(name)?;

        let mut properties = Vec::new();

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
                            self.read_attribute(&prim_path, &mut properties, data)
                                .context("Unable to read attribute")?;
                        }
                    }
                }

                spec.add(ChildrenKey::PrimChildren, sdf::Value::TokenVec(children));
            }
            _ => bail!(
                "Unexpected token after prim name, must be either () or {{}}, got: {:?}",
                brace
            ),
        };

        spec.add(FieldKey::Specifier, sdf::Value::Specifier(specifier));
        spec.add(ChildrenKey::PropertyChildren, sdf::Value::TokenVec(properties));

        data.insert(prim_path, spec);

        Ok(())
    }

    fn read_attribute(
        &mut self,
        current_path: &sdf::Path,
        properties: &mut Vec<String>,
        data: &mut HashMap<sdf::Path, sdf::Spec>,
    ) -> Result<()> {
        let mut spec = sdf::Spec::new(sdf::SpecType::Attribute);

        // TODO: Handle 'custom' field.
        let custom = false;

        let mut variability = sdf::Variability::Varying;
        match self.peek_next() {
            Some((tok::Type::Varying, _)) => {
                // Varying by default, just consume token.
                self.fetch_next()?;
            }
            Some((tok::Type::Uniform, _)) => {
                variability = sdf::Variability::Uniform;
                self.fetch_next()?;
            }
            _ => {}
        };

        let (ty, type_name) = self.fetch_next().context("Unable to fetch data type token")?;
        ensure!(
            ty == tok::Type::Identifier,
            "Unexpected token type for attribute type: {:?}",
            ty
        );
        let data_type = Self::parse_data_type(type_name)?;

        let (ty, name) = self.fetch_next().context("Unable to parse attribute name")?;
        ensure!(
            ty == tok::Type::Identifier || ty == tok::Type::NamespacedIdentifier,
            "Unexpected token type for attribute name: {:?}",
            ty
        );
        let path = current_path.append_property(name)?;
        properties.push(name.to_string());

        self.ensure_next(tok::Type::Punctuation, "=")?;

        let value = self.parse_value(data_type)?;

        spec.add(FieldKey::Custom, sdf::Value::Bool(custom));
        spec.add(FieldKey::Variability, sdf::Value::Variability(variability));
        spec.add(FieldKey::TypeName, sdf::Value::Token(type_name.to_string()));
        spec.add(FieldKey::Default, value);

        data.insert(path, spec);

        Ok(())
    }

    fn parse_value(&mut self, ty: Type) -> Result<sdf::Value> {
        let value = match ty {
            // Bool
            Type::Bool => sdf::Value::Bool(self.parse_token()?),
            Type::BoolVec => sdf::Value::BoolVec(self.parse_array::<_, 1>()?),

            // Ints
            Type::Uchar => sdf::Value::Uchar(self.parse_token()?),
            Type::UcharVec => sdf::Value::UcharVec(self.parse_array::<_, 1>()?),

            Type::Int => sdf::Value::Int(self.parse_token()?),
            Type::Int2 => sdf::Value::Vec2i(self.parse_tuple::<_, 2>()?.into()),
            Type::Int3 => sdf::Value::Vec3i(self.parse_tuple::<_, 3>()?.into()),
            Type::Int4 => sdf::Value::Vec4i(self.parse_tuple::<_, 4>()?.into()),
            Type::IntVec => sdf::Value::IntVec(self.parse_array::<_, 1>()?),
            Type::Int2Vec => sdf::Value::Vec2i(self.parse_array::<_, 2>()?),
            Type::Int3Vec => sdf::Value::Vec3i(self.parse_array::<_, 3>()?),
            Type::Int4Vec => sdf::Value::Vec4i(self.parse_array::<_, 4>()?),
            Type::Uint => sdf::Value::Uint(self.parse_token()?),
            Type::Int64 => sdf::Value::Int64(self.parse_token()?),
            Type::Uint64 => sdf::Value::Uint64(self.parse_token()?),

            // Half
            Type::Half => sdf::Value::Half(self.parse_token()?),
            Type::Half2 => sdf::Value::HalfVec(self.parse_tuple::<_, 2>()?.into()),
            Type::Half3 => sdf::Value::Vec3h(self.parse_tuple::<_, 3>()?.into()),
            Type::Half4 => sdf::Value::Vec4h(self.parse_tuple::<_, 4>()?.into()),

            Type::HalfVec => sdf::Value::HalfVec(self.parse_array::<_, 1>()?),
            Type::Half2Vec => sdf::Value::Vec2h(self.parse_array::<_, 2>()?),
            Type::Half3Vec => sdf::Value::Vec3h(self.parse_array::<_, 3>()?),
            Type::Half4Vec => sdf::Value::Vec4h(self.parse_array::<_, 4>()?),

            // Float
            Type::Float => sdf::Value::Float(self.parse_token()?),
            Type::Float2 => sdf::Value::Vec2f(self.parse_tuple::<_, 2>()?.into()),
            Type::Float3 => sdf::Value::Vec3f(self.parse_tuple::<_, 3>()?.into()),
            Type::Float4 => sdf::Value::Vec4f(self.parse_tuple::<_, 4>()?.into()),
            Type::FloatVec => sdf::Value::FloatVec(self.parse_array::<_, 1>()?),
            Type::Float2Vec => sdf::Value::Vec2f(self.parse_array::<_, 2>()?),
            Type::Float3Vec => sdf::Value::Vec3f(self.parse_array::<_, 3>()?),
            Type::Float4Vec => sdf::Value::Vec4f(self.parse_array::<_, 4>()?),

            // Double
            Type::Double => sdf::Value::Double(self.parse_token()?),
            Type::Double2 => sdf::Value::Vec2d(self.parse_tuple::<_, 2>()?.into()),
            Type::Double3 => sdf::Value::Vec3d(self.parse_tuple::<_, 3>()?.into()),
            Type::Double4 => sdf::Value::Vec4d(self.parse_tuple::<_, 4>()?.into()),
            Type::DoubleVec => sdf::Value::DoubleVec(self.parse_array::<_, 1>()?),
            Type::Double2Vec => sdf::Value::Vec2d(self.parse_array::<_, 2>()?),
            Type::Double3Vec => sdf::Value::Vec3d(self.parse_array::<_, 3>()?),
            Type::Double4Vec => sdf::Value::Vec4d(self.parse_array::<_, 4>()?),

            // Quats
            Type::Quath => sdf::Value::Quath(self.parse_tuple::<_, 4>()?.into()),
            Type::Quatf => sdf::Value::Quatf(self.parse_tuple::<_, 4>()?.into()),
            Type::Quatd => sdf::Value::Quatd(self.parse_tuple::<_, 4>()?.into()),

            // String and tokens
            Type::String => sdf::Value::String(self.fetch_str()?.to_owned()),
            Type::Token => sdf::Value::Token(self.fetch_str()?.to_owned()),

            Type::StringVec => sdf::Value::StringVec(self.parse_array::<_, 1>()?),
            Type::TokenVec => sdf::Value::TokenVec(self.parse_array::<_, 1>()?),

            _ => bail!("Unimplemented data type: {:?}", ty),
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

            _ => bail!("Unsupported data type: {}", ty),
        };

        Ok(data_type)
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
        T: FromStr + Default,
        <T as FromStr>::Err: Debug,
    {
        self.ensure_next(tok::Type::Punctuation, "(")
            .context("Tuples must start with (")?;

        // TODO: array::try_map would be nice to have here once stable, see https://github.com/rust-lang/rust/issues/79711
        // or consider fixed vec crates.
        let mut result: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };

        for (i, element) in result.iter_mut().enumerate() {
            if i > 0 {
                self.ensure_next(tok::Type::Punctuation, ",")
                    .context("Comma is expected between tuple values")?
            }

            *element = MaybeUninit::new(self.parse_token::<T>()?);

            if i == N - 1 {
                self.ensure_next(tok::Type::Punctuation, ")")
                    .context("Tuples must be closed with )")?;
            }
        }

        // SAFETY: All elements are initialized, so transmute the array to [T; N]
        let result = unsafe { std::mem::transmute_copy::<_, [T; N]>(&result) };

        Ok(result)
    }

    /// Parse array or array of tuples.
    fn parse_array<T, const N: usize>(&mut self) -> Result<Vec<T>>
    where
        T: FromStr + Default,
        <T as FromStr>::Err: Debug,
    {
        debug_assert!(N >= 1 && N <= 4);

        self.ensure_next(tok::Type::Punctuation, "[")
            .context("Array must start with [")?;

        let is_tuple = N > 1;
        let mut result = Vec::new();

        loop {
            // Special case - empty array like []
            if self.peek_next() == Some((tok::Type::Punctuation, "]")) {
                self.fetch_next()?; // Consume it.
                break;
            }

            if is_tuple {
                let tuple = self.parse_tuple::<T, N>()?;
                result.extend(tuple);
            } else {
                let value = self.parse_token::<T>()?;
                result.push(value);
            }

            match self.fetch_next()? {
                (tok::Type::Punctuation, ",") => continue,
                (tok::Type::Punctuation, "]") => break,
                t => bail!("Either comma or closing bracket expected after value, got: {:?}", t),
            }
        }

        Ok(result)
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
    StringVec,
    TokenVec,
    Matrix2d,
    Matrix3d,
    Matrix4d,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_empty_array() {
        let mut parser = Parser::new("[]");
        let array = parser.parse_array::<u32, 1>().unwrap();
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
        let result = parser.parse_array::<u32, 1>().unwrap();
        assert_eq!(result, vec![1_u32, 2, 3]);
    }

    #[test]
    fn parse_array_of_tuples() {
        let mut parser = Parser::new("[(1, 2), (3, 4)]");
        let result = parser.parse_array::<u32, 2>().unwrap();
        assert_eq!(result, vec![1_u32, 2, 3, 4]);
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
            .and_then(|v| v.try_as_token_ref())
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

    #[test]
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
}
