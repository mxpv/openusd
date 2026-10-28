//! What a schema's value types become in generated code.
//!
//! Two answers per property, and only one of them lives here. [`rust_type`] is
//! the type its accessor reads and writes, so a `point3f` attribute hands back
//! a `gf::Vec3f`. The constant its creator declares it with comes from
//! [`sdf::ValueTypeName::constant_ident`], since `sdf` is what names its own
//! constants.
//!
//! [`sdf::ValueTypeName::constant_ident`]: openusd::sdf::ValueTypeName::constant_ident

use openusd::vt;

/// The Rust type a value of `kind` reads back as, or `None` for a kind no
/// attribute can hold — `opaque`, which carries no value, and the metadata-only
/// kinds.
///
/// Paths are spelled the way generated code spells them: in full, since the
/// generated file is included bare into a consumer's module and carries no
/// `use` block of its own.
pub fn rust_type(kind: vt::ValueKind) -> Option<syn::Type> {
    let spelled = match kind.element_kind() {
        Some(element) => format!("::std::vec::Vec<{}>", scalar_type(element)?),
        None => scalar_type(kind)?.to_owned(),
    };
    Some(syn::parse_str(&spelled).expect("every spelling below is a Rust type"))
}

/// The Rust type one scalar value reads back as. A role does not change it: a
/// point, a normal and a colour are all one vector type, as they are one kind.
///
/// The pairing restates what `vt::Value` declares, [`vt::ValueKind`] being
/// derived from it, as the module-qualified source text a generated file
/// spells. That spelling is the part `vt` has no reason to know.
fn scalar_type(kind: vt::ValueKind) -> Option<&'static str> {
    Some(match kind {
        vt::ValueKind::Bool => "bool",
        vt::ValueKind::Uchar => "u8",
        vt::ValueKind::Int => "i32",
        vt::ValueKind::Uint => "u32",
        vt::ValueKind::Int64 => "i64",
        vt::ValueKind::Uint64 => "u64",
        vt::ValueKind::Half => "::openusd::gf::f16",
        vt::ValueKind::Float => "f32",
        vt::ValueKind::Double => "f64",
        vt::ValueKind::String => "::std::string::String",
        vt::ValueKind::Token => "::openusd::tf::Token",
        vt::ValueKind::AssetPath => "::openusd::sdf::AssetPath",
        vt::ValueKind::TimeCode => "::openusd::sdf::TimeCode",
        vt::ValueKind::PathExpression => "::openusd::sdf::PathExpression",

        vt::ValueKind::Vec2h => "::openusd::gf::Vec2h",
        vt::ValueKind::Vec2f => "::openusd::gf::Vec2f",
        vt::ValueKind::Vec2d => "::openusd::gf::Vec2d",
        vt::ValueKind::Vec2i => "::openusd::gf::Vec2i",
        vt::ValueKind::Vec3h => "::openusd::gf::Vec3h",
        vt::ValueKind::Vec3f => "::openusd::gf::Vec3f",
        vt::ValueKind::Vec3d => "::openusd::gf::Vec3d",
        vt::ValueKind::Vec3i => "::openusd::gf::Vec3i",
        vt::ValueKind::Vec4h => "::openusd::gf::Vec4h",
        vt::ValueKind::Vec4f => "::openusd::gf::Vec4f",
        vt::ValueKind::Vec4d => "::openusd::gf::Vec4d",
        vt::ValueKind::Vec4i => "::openusd::gf::Vec4i",

        vt::ValueKind::Quath => "::openusd::gf::Quath",
        vt::ValueKind::Quatf => "::openusd::gf::Quatf",
        vt::ValueKind::Quatd => "::openusd::gf::Quatd",

        vt::ValueKind::Matrix2d => "::openusd::gf::Mat2d",
        vt::ValueKind::Matrix3d => "::openusd::gf::Mat3d",
        vt::ValueKind::Matrix4d => "::openusd::gf::Mat4d",

        // `opaque` carries no value, and the rest are metadata kinds no
        // attribute is declared with.
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use openusd::sdf;

    use quote::ToTokens;

    /// `kind`'s Rust type as source text, spaces removed.
    fn spelled(kind: vt::ValueKind) -> Option<String> {
        rust_type(kind).map(|ty| ty.to_token_stream().to_string().replace(' ', ""))
    }

    /// Every type an attribute can be declared with has a Rust type to read
    /// it back as, and an array reads back as a `Vec` of its element's.
    #[test]
    fn every_attribute_type_maps() {
        for type_name in sdf::ValueTypeName::all() {
            let Some(kind) = type_name.kind() else { continue };
            if kind == vt::ValueKind::Opaque {
                continue;
            }
            assert!(
                rust_type(kind).is_some(),
                "{} has no Rust type",
                type_name.serialization_name()
            );
        }

        assert_eq!(spelled(vt::ValueKind::Float).as_deref(), Some("f32"));
        assert_eq!(
            spelled(vt::ValueKind::Vec3fVec).as_deref(),
            Some("::std::vec::Vec<::openusd::gf::Vec3f>")
        );
        assert_eq!(
            spelled(vt::ValueKind::TokenVec).as_deref(),
            Some("::std::vec::Vec<::openusd::tf::Token>")
        );
    }

    /// A role does not change the Rust type: a point, a normal and a colour
    /// are all one vector type.
    #[test]
    fn roles_share_a_type() {
        for spelling in ["float3", "point3f", "normal3f", "vector3f", "color3f"] {
            let kind = sdf::ValueTypeName::find(spelling).and_then(|type_name| type_name.kind());
            assert_eq!(
                kind.and_then(spelled).as_deref(),
                Some("::openusd::gf::Vec3f"),
                "{spelling}"
            );
        }
    }

    /// `opaque` carries no value, so it has no type to read.
    #[test]
    fn opaque_has_no_type() {
        assert!(rust_type(vt::ValueKind::Opaque).is_none());
    }
}
