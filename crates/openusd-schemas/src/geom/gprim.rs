//! What `UsdGeomGprim` answers beyond its own properties.

use openusd::sdf;
use openusd::usd::SchemaBase;

use super::{GprimSchema, Interpolation, Primvar, PrimvarsAPI, tokens};
use crate::SchemaError;

/// A gprim's `displayColor` and `displayOpacity` as the primvars they are.
///
/// Every [`GprimSchema`] answers them, so a view of any gprim type has them
/// wherever the generated accessors are.
///
/// # Example
///
/// ```
/// use openusd::usd;
/// use openusd::{gf, sdf};
/// use openusd_schemas::geom::{self, GprimExt, Interpolation};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let mesh = geom::Mesh::define(&stage, "/Mesh")?;
///
/// // One color for each of two faces.
/// let color = mesh.create_display_color_primvar(Interpolation::Uniform, None)?;
/// color
///     .into_attribute()
///     .set(sdf::Value::Vec3fVec(vec![gf::vec3f(1.0, 0.0, 0.0), gf::vec3f(0.0, 0.0, 1.0)]))?;
///
/// assert_eq!(mesh.display_color_primvar().interpolation()?, Interpolation::Uniform);
/// // Opacity is declared by the schema and authored by nothing.
/// assert!(!mesh.display_opacity_primvar().attribute().has_authored_value()?);
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
pub trait GprimExt: GprimSchema {
    /// The `displayColor` attribute as a primvar (C++
    /// `GetDisplayColorPrimvar`), whether or not a layer authors it.
    fn display_color_primvar(&self) -> Primvar {
        Primvar::new(self.display_color_attr())
    }

    /// Author `displayColor` as a `color3f[]` primvar holding no value,
    /// together with its `interpolation` and `elementSize` where they are
    /// given, as one edit (C++ `CreateDisplayColorPrimvar`).
    ///
    /// An `element_size` below one is [`SchemaError::InvalidElementSize`],
    /// and nothing is authored.
    fn create_display_color_primvar(
        &self,
        interpolation: impl Into<Option<Interpolation>>,
        element_size: impl Into<Option<i32>>,
    ) -> Result<Primvar, SchemaError> {
        create_primvar(
            self,
            tokens::PRIMVARS_DISPLAY_COLOR,
            sdf::ValueTypeName::COLOR3F_ARRAY,
            interpolation.into(),
            element_size.into(),
        )
    }

    /// The `displayOpacity` attribute as a primvar (C++
    /// `GetDisplayOpacityPrimvar`), whether or not a layer authors it.
    fn display_opacity_primvar(&self) -> Primvar {
        Primvar::new(self.display_opacity_attr())
    }

    /// Author `displayOpacity` as a `float[]` primvar holding no value,
    /// together with its `interpolation` and `elementSize` where they are
    /// given, as one edit (C++ `CreateDisplayOpacityPrimvar`).
    ///
    /// An `element_size` below one is [`SchemaError::InvalidElementSize`],
    /// and nothing is authored.
    fn create_display_opacity_primvar(
        &self,
        interpolation: impl Into<Option<Interpolation>>,
        element_size: impl Into<Option<i32>>,
    ) -> Result<Primvar, SchemaError> {
        create_primvar(
            self,
            tokens::PRIMVARS_DISPLAY_OPACITY,
            sdf::ValueTypeName::FLOAT_ARRAY,
            interpolation.into(),
            element_size.into(),
        )
    }
}

impl<T: GprimSchema> GprimExt for T {}

/// Author the primvar `name` of `gprim` as a `type_name` attribute, with the
/// metadata given.
fn create_primvar(
    gprim: &(impl SchemaBase + ?Sized),
    name: &str,
    type_name: sdf::ValueTypeName,
    interpolation: Option<Interpolation>,
    element_size: Option<i32>,
) -> Result<Primvar, SchemaError> {
    let mut builder = PrimvarsAPI::from_prim_unchecked(gprim.prim().clone()).primvar_builder(name, type_name);
    if let Some(interpolation) = interpolation {
        builder = builder.interpolation(interpolation);
    }
    if let Some(element_size) = element_size {
        builder = builder.element_size(element_size);
    }
    builder.build()
}

#[cfg(test)]
mod tests {
    use openusd::sdf;

    use super::GprimExt;
    use crate::SchemaError;
    use crate::geom::{Gprim, GprimSchema, Interpolation, Mesh, PrimvarDeclaration, Sphere};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// The display primvars are the schema's attributes, defined before any
    /// layer authors them.
    #[test]
    fn display_primvars_wrap_attrs() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = Mesh::define(&stage, "/Mesh")?;

        let color = mesh.display_color_primvar();
        assert_eq!(color.attribute(), &mesh.display_color_attr());
        assert_eq!(color.primvar_name(), "displayColor");
        assert!(color.attribute().is_defined()?);
        assert!(!color.has_authored_interpolation()?);

        let opacity = mesh.display_opacity_primvar();
        assert_eq!(opacity.attribute(), &mesh.display_opacity_attr());
        assert_eq!(opacity.primvar_name(), "displayOpacity");
        Ok(())
    }

    /// The gprim display primvar cases of C++ `testUsdGeomPrimvar`: each is
    /// created with the declaration asked for.
    #[test]
    fn create_display_primvars() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = Mesh::define(&stage, "/myMesh")?;

        let color = mesh.create_display_color_primvar(Interpolation::Vertex, 3)?;
        assert_eq!(
            color.declaration_info()?,
            PrimvarDeclaration {
                name: "displayColor".to_owned(),
                type_name: Some(sdf::ValueTypeName::COLOR3F_ARRAY),
                interpolation: Interpolation::Vertex,
                element_size: 3,
            }
        );

        let opacity = mesh.create_display_opacity_primvar(Interpolation::Constant, None)?;
        assert_eq!(
            opacity.declaration_info()?,
            PrimvarDeclaration {
                name: "displayOpacity".to_owned(),
                type_name: Some(sdf::ValueTypeName::FLOAT_ARRAY),
                interpolation: Interpolation::Constant,
                element_size: 1,
            }
        );
        assert!(opacity.has_authored_interpolation()?);
        assert!(!opacity.has_authored_element_size()?);
        Ok(())
    }

    /// Metadata left out is not authored, and the primvar, its metadata and
    /// all, is one edit.
    #[test]
    fn create_authors_once() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = Mesh::define(&stage, "/Mesh")?;

        let commits = crate::tests::commits(&stage);
        let color = mesh.create_display_color_primvar(None, None)?;
        assert_eq!(commits.get(), 1);
        assert!(!color.attribute().property_stack()?.is_empty());
        assert!(!color.attribute().has_authored_value()?);
        assert!(!color.has_authored_interpolation()?);
        assert!(!color.has_authored_element_size()?);

        mesh.create_display_opacity_primvar(Interpolation::Uniform, 2)?;
        assert_eq!(commits.get(), 2);
        Ok(())
    }

    /// An element size below one fails the creation, and authors nothing.
    #[test]
    fn create_rejects_size() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = Mesh::define(&stage, "/Mesh")?;
        for size in [0, -1] {
            let error = mesh
                .create_display_color_primvar(Interpolation::Vertex, size)
                .expect_err("below one");
            assert!(matches!(
                error,
                SchemaError::InvalidElementSize { element_size, .. } if element_size == size
            ));
        }
        assert!(mesh.display_color_attr().property_stack()?.is_empty());
        Ok(())
    }

    /// Every gprim view has them, the abstract one included.
    #[test]
    fn any_gprim_view() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let sphere = Sphere::define(&stage, "/Sphere")?;
        sphere.create_display_opacity_primvar(Interpolation::Constant, None)?;

        let gprim = Gprim::get(&stage, "/Sphere")?.expect("a gprim");
        let opacity = gprim.display_opacity_primvar();
        assert_eq!(opacity.attribute().path(), sphere.display_opacity_attr().path());
        assert_eq!(opacity.interpolation()?, Interpolation::Constant);
        Ok(())
    }
}
