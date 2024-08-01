use std::collections::HashMap;

use half::f16;
use strum::{EnumDiscriminants, EnumIs, EnumTryAs};

use super::*;

/// `Value` is a type that can hold data type loaded from USD file.
///
/// Suffixes:
/// - d: double
/// - f: float
/// - h: half
/// - i: int
///
#[derive(Debug, Clone, EnumIs, EnumTryAs, EnumDiscriminants)]
#[strum_discriminants(name(ValueType))]
pub enum Value {
    Bool(bool),
    BoolVec(Vec<bool>),

    Uchar(u8),
    UcharVec(Vec<u8>),

    Int(i32),
    Int2([i32; 2]),
    Int3([i32; 3]),
    Int4([i32; 4]),
    IntVec(Vec<i32>),
    Int2Vec(Vec<[i32; 2]>),
    Int3Vec(Vec<[i32; 3]>),
    Int4Vec(Vec<[i32; 4]>),

    Uint(u32),
    UintVec(Vec<u32>),

    Int64(i64),
    Int64Vec(Vec<i64>),

    Uint64(u64),
    Uint64Vec(Vec<u64>),

    // TODO: Consolidate this with binary reader.
    Half(f16),
    Half2([f16; 2]),
    Half3([f16; 3]),
    Half4([f16; 4]),
    HalfVec(Vec<f16>),
    Half2Vec(Vec<[f16; 2]>),
    Half3Vec(Vec<[f16; 3]>),
    Half4Vec(Vec<[f16; 4]>),

    Float(f32),
    Float2([f32; 2]),
    Float3([f32; 3]),
    Float4([f32; 4]),
    FloatVec(Vec<f32>),
    Float2Vec(Vec<[f32; 2]>),
    Float3Vec(Vec<[f32; 3]>),
    Float4Vec(Vec<[f32; 4]>),

    Double(f64),
    Double2([f64; 2]),
    Double3([f64; 3]),
    Double4([f64; 4]),
    DoubleVec(Vec<f64>),
    Double2Vec(Vec<[f64; 2]>),
    Double3Vec(Vec<[f64; 3]>),
    Double4Vec(Vec<[f64; 4]>),

    String(String),
    StringVec(Vec<String>),

    Token(String),
    TokenVec(Vec<String>),

    AssetPath(String),

    Quath(Vec<f16>),
    Quatf(Vec<f32>),
    Quatd(Vec<f64>),

    Vec2h(Vec<f16>),
    Vec2f(Vec<f32>),
    Vec2d(Vec<f64>),
    Vec2i(Vec<i32>),

    Vec3h(Vec<f16>),
    Vec3f(Vec<f32>),
    Vec3d(Vec<f64>),
    Vec3i(Vec<i32>),

    Vec4h(Vec<f16>),
    Vec4f(Vec<f32>),
    Vec4d(Vec<f64>),
    Vec4i(Vec<i32>),

    Matrix2d(Vec<f64>),
    Matrix3d(Vec<f64>),
    Matrix4d(Vec<f64>),

    Specifier(Specifier),
    Permission(Permission),
    Variability(Variability),

    Dictionary(HashMap<String, Value>),

    TokenListOp(TokenListOp),
    StringListOp(StringListOp),
    PathListOp(PathListOp),
    ReferenceListOp(ReferenceListOp),
    IntListOp(IntListOp),
    Int64ListOp(Int64ListOp),
    UIntListOp(UintListOp),
    UInt64ListOp(Uint64ListOp),
    PayloadListOp(PayloadListOp),

    Payload(Payload),
    PathVec,
    VariantSelectionMap(HashMap<String, String>),
    TimeSamples(TimeSampleMap),

    LayerOffsetVec(Vec<LayerOffset>),

    ValueBlock,
    Value,

    UnregisteredValue,
    UnregisteredValueListOp,

    TimeCode(f64),
    PathExpression,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is() {
        // Basic sanity checks
        assert!(Value::Bool(true).is_bool());
        assert!(!Value::Bool(true).is_bool_vec());

        assert!(Value::Float(1.44).is_float());
        assert!(!Value::Float(1.44).is_bool());
        assert!(!Value::Float(1.44).is_float_vec());

        assert!(Value::PayloadListOp(Default::default()).is_payload_list_op());
        assert!(Value::UnregisteredValue.is_unregistered_value());
    }
}
