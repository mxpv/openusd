use std::{collections::HashMap, vec};

use anyhow::bail;
use half::f16;

use super::*;

/// `Value` is a type that can hold data type loaded from USD file.
///
/// Suffixes:
/// - d: double
/// - f: float
/// - h: half
/// - i: int
///
/// NOTE: Halfs are not supported in Rust by default, so floats are used instead.
#[derive(Debug)]
pub enum Value {
    Bool(bool),
    Uchar(u8),
    Int(Vec<i32>),
    Uint(Vec<u32>),
    Int64(i64),
    Uint64(u64),

    Half(Vec<f16>),
    Float(Vec<f32>),
    Double(Vec<f64>),

    String(String),
    Token(Vec<String>),
    AssetPath(String),

    Quath(Vec<f16>),
    Quatd(Vec<f64>),
    Quatf(Vec<f32>),

    Vec2d(Vec<f64>),
    Vec2f(Vec<f32>),
    Vec2i(Vec<i32>),

    Vec3d(Vec<f64>),
    Vec3f(Vec<f32>),
    Vec3i(Vec<i32>),

    Vec4d(Vec<f64>),
    Vec4f(Vec<f32>),
    Vec4i(Vec<i32>),

    Matrix2d(Vec<f64>),
    Matrix3d(Vec<f64>),
    Matrix4d(Vec<f64>),

    Dictionary(HashMap<String, Value>),
    TokenListOp(TokenListOp),
    StringListOp(StringListOp),
    PathListOp(PathListOp),
    ReferenceListOp(ReferenceListOp),
    IntListOp(IntListOp),
    Int64ListOp(Int64ListOp),
    UIntListOp(UintListOp),
    UInt64ListOp(Uint64ListOp),

    PathVector,
    TokenVector(Vec<String>),
    Specifier(Specifier),
    Permission(Permission),
    Variability(Variability),

    VariantSelectionMap(HashMap<String, String>),
    TimeSamples(TimeSampleMap),
    Payload(Payload),
    DoubleVector(Vec<f64>),
    LayerOffsetVector(Vec<LayerOffset>),
    StringVector(Vec<String>),
    ValueBlock,
    Value,

    UnregisteredValue,
    UnregisteredValueListOp,
    PayloadListOp(PayloadListOp),

    TimeCode(f64),
    PathExpression,
}

impl Value {
    pub fn as_int_slice(&self) -> Option<&[i32]> {
        match self {
            Value::Int(vec) => Some(vec.as_slice()),
            _ => None,
        }
    }

    pub fn as_f64_slice(&self) -> Option<&[f64]> {
        let slice = match self {
            Value::Vec2d(vec)
            | Value::Vec3d(vec)
            | Value::Vec4d(vec)
            | Value::Matrix2d(vec)
            | Value::Matrix3d(vec)
            | Value::Matrix4d(vec) => vec.as_slice(),
            _ => return None,
        };

        Some(slice)
    }

    pub fn as_f32_slice(&self) -> Option<&[f32]> {
        let slice = match self {
            Value::Vec2f(vec) | Value::Vec3f(vec) | Value::Vec4f(vec) => vec.as_slice(),
            _ => return None,
        };

        Some(slice)
    }

    pub fn as_dict(&self) -> Option<&HashMap<String, Value>> {
        match self {
            Value::Dictionary(dict) => Some(dict),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Value::String(string) => string.as_str(),
            Value::Token(tokens) if tokens.len() == 1 => tokens[0].as_str(),
            _ => panic!("Expected string"),
        }
    }
}

impl TryFrom<Value> for Vec<f16> {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::prelude::v1::Result<Self, Self::Error> {
        match value {
            Value::Half(vec) | Value::Quath(vec) => Ok(vec),
            _ => bail!("Unable to unpack half"),
        }
    }
}

impl TryFrom<Value> for Vec<f32> {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::prelude::v1::Result<Self, Self::Error> {
        match value {
            Value::Float(vec) | Value::Quatf(vec) | Value::Vec2f(vec) | Value::Vec3f(vec) | Value::Vec4f(vec) => {
                Ok(vec)
            }

            _ => bail!("Unable to unpack float"),
        }
    }
}

impl TryFrom<Value> for Vec<f64> {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::prelude::v1::Result<Self, Self::Error> {
        match value {
            Value::Double(vec)
            | Value::Quatd(vec)
            | Value::Vec2d(vec)
            | Value::Vec3d(vec)
            | Value::Vec4d(vec)
            | Value::Matrix2d(vec)
            | Value::Matrix3d(vec)
            | Value::Matrix4d(vec)
            | Value::DoubleVector(vec) => Ok(vec),

            _ => bail!("Unable to unpack double"),
        }
    }
}

impl From<Value> for Vec<String> {
    fn from(value: Value) -> Self {
        match value {
            Value::String(str) => vec![str],
            Value::StringVector(vec) => vec,
            Value::Token(tokens) => tokens,
            Value::TokenVector(tokens) => tokens,
            Value::AssetPath(path) => vec![path],
            _ => Vec::new(),
        }
    }
}

impl TryFrom<Value> for LayerOffset {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::result::Result<Self, Self::Error> {
        match value {
            Value::LayerOffsetVector(vec) if vec.len() == 1 => Ok(vec[0]),
            _ => bail!("Unable to unpack layer offset"),
        }
    }
}

impl TryFrom<Value> for StringListOp {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::result::Result<Self, Self::Error> {
        match value {
            Value::StringListOp(list) => Ok(list),
            _ => bail!("Unable to unpack string list op"),
        }
    }
}

impl TryFrom<Value> for PathListOp {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::result::Result<Self, Self::Error> {
        match value {
            Value::PathListOp(list) => Ok(list),
            _ => bail!("Unable to unpack path list op"),
        }
    }
}

impl TryFrom<Value> for HashMap<String, String> {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::result::Result<Self, Self::Error> {
        match value {
            Value::VariantSelectionMap(map) => Ok(map),
            _ => bail!("Unable to unpack variant selection map"),
        }
    }
}

impl TryFrom<Value> for ReferenceListOp {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::result::Result<Self, Self::Error> {
        match value {
            Value::ReferenceListOp(list) => Ok(list),
            _ => bail!("Unable to unpack reference list op"),
        }
    }
}

impl TryFrom<Value> for Payload {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::result::Result<Self, Self::Error> {
        match value {
            Value::Payload(payload) => Ok(payload),
            _ => bail!("Unable to unpack payload"),
        }
    }
}

impl TryFrom<Value> for PayloadListOp {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::result::Result<Self, Self::Error> {
        match value {
            Value::PayloadListOp(list) => Ok(list),
            _ => bail!("Unable to unpack payload list op"),
        }
    }
}

impl TryFrom<Value> for TimeSampleMap {
    type Error = anyhow::Error;

    fn try_from(value: Value) -> std::prelude::v1::Result<Self, Self::Error> {
        match value {
            Value::TimeSamples(samples) => Ok(samples),
            _ => bail!("Unable to unpack time samples"),
        }
    }
}
