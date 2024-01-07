use glam::*;

use super::*;

/// Variant is a type that can hold any of the SDF types.
///
/// Suffixes:
/// - d: double
/// - f: float
/// - h: half
/// - i: int
///
/// NOTE: Halfs are not supported in Rust by default, so floats are used instead.
#[derive(Debug)]
pub enum Variant {
    Bool(bool),
    Uchar(u8),
    Int(i32),
    Uint(u32),
    Int64(i64),
    Uint64(u64),

    Half(f32),
    Float(f32),
    Double(f64),

    String(String),
    Token(String),
    AssetPath(String),

    Quatd(DQuat),
    Quatf(Quat),

    Vec2d(DVec2),
    Vec2f(Vec2),
    Vec2i(IVec2),

    Vec3d(DVec3),
    Vec3f(Vec3),
    Vec3i(IVec3),

    Vec4d(DVec4),
    Vec4f(Vec4),
    Vec4i(IVec4),

    Matrix2d(DMat2),
    Matrix3d(DMat3),
    Matrix4d(DMat4),

    Dictionary,
    TokenListOp(TokenListOp),
    StringListOp(StringListOp),
    PathListOp(PathListOp),
    ReferenceListOp,
    IntListOp(IntListOp),
    Int64ListOp(Int64ListOp),
    UIntListOp(UintListOp),
    UInt64ListOp(Uint64ListOp),

    PathVector,
    TokenVector(Vec<String>),
    Specifier(Specifier),
    Permission(Permission),
    Variability(Variability),

    VariantSelectionMap,
    TimeSamples,
    Payload(Payload),
    DoubleVector(Vec<f32>),
    LayerOffsetVector(Vec<LayerOffset>),
    StringVector(Vec<String>),
    ValueBlock,
    Value,

    UnregisteredValue,
    UnregisteredValueListOp,
    PayloadListOp,

    TimeCode(f64),
    PathExpression,

    /// Values not yet supported.
    Unimplemented,
}
