//! What a schema's value types become in generated code.
//!
//! Two answers per property, and only one of them lives here. [`rust_type`] is
//! the type its accessor reads and writes, so a `point3f` attribute hands back
//! a `gf::Vec3f`. The constant its creator declares it with comes from
//! [`sdf::ValueTypeName::constant_ident`], since `sdf` is what names its own
//! constants.

use openusd::sdf;

/// The Rust type a value of `kind` reads back as, or `None` for a kind no
/// attribute can hold — `opaque`, which carries no value, and the metadata-only
/// kinds.
///
/// Paths are spelled the way generated code spells them, module-qualified
/// against what a schema module imports.
pub fn rust_type(kind: sdf::ValueKind) -> Option<String> {
    if let Some(element) = kind.element_kind() {
        return Some(format!("Vec<{}>", scalar_type(element)?));
    }
    scalar_type(kind).map(str::to_owned)
}

/// The Rust type one scalar value reads back as. A role does not change it: a
/// point, a normal and a colour are all one vector type, as they are one kind.
///
/// The pairing restates what `sdf::Value` declares, [`sdf::ValueKind`] being
/// derived from it, as the module-qualified source text a generated file
/// spells. That spelling is the part `sdf` has no reason to know.
fn scalar_type(kind: sdf::ValueKind) -> Option<&'static str> {
    Some(match kind {
        sdf::ValueKind::Bool => "bool",
        sdf::ValueKind::Uchar => "u8",
        sdf::ValueKind::Int => "i32",
        sdf::ValueKind::Uint => "u32",
        sdf::ValueKind::Int64 => "i64",
        sdf::ValueKind::Uint64 => "u64",
        sdf::ValueKind::Half => "gf::f16",
        sdf::ValueKind::Float => "f32",
        sdf::ValueKind::Double => "f64",
        sdf::ValueKind::String => "String",
        sdf::ValueKind::Token => "tf::Token",
        sdf::ValueKind::AssetPath => "sdf::AssetPath",
        sdf::ValueKind::TimeCode => "sdf::TimeCode",
        sdf::ValueKind::PathExpression => "sdf::PathExpression",

        sdf::ValueKind::Vec2h => "gf::Vec2h",
        sdf::ValueKind::Vec2f => "gf::Vec2f",
        sdf::ValueKind::Vec2d => "gf::Vec2d",
        sdf::ValueKind::Vec2i => "gf::Vec2i",
        sdf::ValueKind::Vec3h => "gf::Vec3h",
        sdf::ValueKind::Vec3f => "gf::Vec3f",
        sdf::ValueKind::Vec3d => "gf::Vec3d",
        sdf::ValueKind::Vec3i => "gf::Vec3i",
        sdf::ValueKind::Vec4h => "gf::Vec4h",
        sdf::ValueKind::Vec4f => "gf::Vec4f",
        sdf::ValueKind::Vec4d => "gf::Vec4d",
        sdf::ValueKind::Vec4i => "gf::Vec4i",

        sdf::ValueKind::Quath => "gf::Quath",
        sdf::ValueKind::Quatf => "gf::Quatf",
        sdf::ValueKind::Quatd => "gf::Quatd",

        sdf::ValueKind::Matrix2d => "gf::Mat2d",
        sdf::ValueKind::Matrix3d => "gf::Mat3d",
        sdf::ValueKind::Matrix4d => "gf::Matrix4d",

        // `opaque` carries no value, and the rest are metadata kinds no
        // attribute is declared with.
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every type an attribute can be declared with has a Rust type to read
    /// it back as, and an array reads back as a `Vec` of its element's.
    #[test]
    fn every_attribute_type_maps() {
        for type_name in sdf::ValueTypeName::all() {
            let Some(kind) = type_name.kind() else { continue };
            if kind == sdf::ValueKind::Opaque {
                continue;
            }
            assert!(
                rust_type(kind).is_some(),
                "{} has no Rust type",
                type_name.serialization_name()
            );
        }

        assert_eq!(rust_type(sdf::ValueKind::Float).as_deref(), Some("f32"));
        assert_eq!(rust_type(sdf::ValueKind::Vec3fVec).as_deref(), Some("Vec<gf::Vec3f>"));
        assert_eq!(rust_type(sdf::ValueKind::TokenVec).as_deref(), Some("Vec<tf::Token>"));
    }

    /// A role does not change the Rust type: a point, a normal and a colour
    /// are all one vector type.
    #[test]
    fn roles_share_a_type() {
        for spelling in ["float3", "point3f", "normal3f", "vector3f", "color3f"] {
            let kind = sdf::ValueTypeName::find(spelling).and_then(|type_name| type_name.kind());
            assert_eq!(kind.and_then(rust_type).as_deref(), Some("gf::Vec3f"), "{spelling}");
        }
    }

    /// `opaque` carries no value, so it has no type to read.
    #[test]
    fn opaque_has_no_type() {
        assert_eq!(rust_type(sdf::ValueKind::Opaque), None);
    }
}
