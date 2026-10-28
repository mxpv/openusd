//! Inbetween shapes: the intermediate targets a blend shape interpolates
//! through, each an `inbetweens:<name>` attribute on the `BlendShape` prim
//! (C++ `UsdSkelInbetweenShape`).

use openusd::Result;
use openusd::gf;
use openusd::sdf;
use openusd::usd::{Attribute, Object, StageAuthoringError};
use openusd::vt::Value;

use super::{AttributeMetadata, BlendShape, tokens};
use crate::namespaced;

/// The namespace an inbetween shape is authored under (C++'s own
/// `inbetweensPrefix`), which names no property and so has no token.
pub const INBETWEENS_NAMESPACE: &str = "inbetweens:";

/// The suffix of the attribute that holds an inbetween's normal offsets,
/// beside the inbetween's own.
const NORMAL_OFFSETS_SUFFIX: &str = ":normalOffsets";

/// One inbetween shape of a [`BlendShape`]: a view over its
/// `inbetweens:<name>` attribute, which holds the shape's point offsets and,
/// as `weight` metadata, the blend-shape weight it applies at (C++
/// `UsdSkelInbetweenShape`). Its normal offsets live in the sibling
/// `inbetweens:<name>:normalOffsets` attribute.
#[derive(Debug, Clone, PartialEq)]
pub struct InbetweenShape {
    attribute: Attribute,
}

impl InbetweenShape {
    /// A view over `attribute`, whether or not it is an inbetween (C++
    /// `UsdSkelInbetweenShape(const UsdAttribute&)`);
    /// [`is_defined`](Self::is_defined) tells.
    pub fn new(attribute: Attribute) -> Self {
        Self { attribute }
    }

    /// `true` when `attribute` exists, is in the `inbetweens:` namespace, and
    /// is not an inbetween's normal offsets (C++ `IsInbetween`).
    pub fn is_inbetween(attribute: &Attribute) -> Result<bool> {
        let name = attribute.name();
        Ok(name.starts_with(INBETWEENS_NAMESPACE)
            && !name.ends_with(NORMAL_OFFSETS_SUFFIX)
            && attribute.is_defined()?)
    }

    /// `true` when the view's attribute is an inbetween (C++ `IsDefined`).
    pub fn is_defined(&self) -> Result<bool> {
        Self::is_inbetween(&self.attribute)
    }

    /// The inbetween's attribute.
    pub fn attribute(&self) -> &Attribute {
        &self.attribute
    }

    /// The blend-shape weight the inbetween applies at, its `weight`
    /// metadata (C++ `GetWeight`). `None` where none is authored, or the
    /// metadata holds other than a `float`, where C++ `GetMetadata` fails.
    pub fn weight(&self) -> Result<Option<f32>> {
        Ok(match self.attribute.metadata::<Value>(tokens::WEIGHT)? {
            Some(Value::Float(weight)) => Some(weight),
            _ => None,
        })
    }

    /// Author the inbetween's `weight` (C++ `SetWeight`).
    pub fn set_weight(&self, weight: f32) -> Result<(), StageAuthoringError> {
        self.attribute.clone().set_weight(weight)?;
        Ok(())
    }

    /// Whether a layer authors the inbetween's `weight` (C++
    /// `HasAuthoredWeight`).
    pub fn has_authored_weight(&self) -> Result<bool> {
        self.attribute.has_authored_metadata(tokens::WEIGHT)
    }

    /// The inbetween's point offsets, read at the default time (C++
    /// `GetOffsets`).
    pub fn offsets(&self) -> Result<Option<Vec<gf::Vec3f>>> {
        self.attribute.cast()
    }

    /// Author the inbetween's point offsets at the default time (C++
    /// `SetOffsets`).
    pub fn set_offsets(&self, offsets: Vec<gf::Vec3f>) -> Result<(), StageAuthoringError> {
        self.attribute.clone().set(Value::Vec3fVec(offsets))?;
        Ok(())
    }

    /// The `<name>:normalOffsets` attribute beside the inbetween, whether or
    /// not it exists (C++ `GetNormalOffsetsAttr`).
    pub fn normal_offsets_attr(&self) -> Attribute {
        self.attribute.prim().attribute(self.normal_offsets_name())
    }

    /// Author the `<name>:normalOffsets` attribute, a non-custom `vector3f[]`
    /// (C++ `CreateNormalOffsetsAttr`).
    pub fn create_normal_offsets_attr(&self) -> Result<Attribute, StageAuthoringError> {
        self.attribute
            .prim()
            .attribute_builder(self.normal_offsets_name(), "vector3f[]")
            .custom(false)
            .build()
    }

    /// The inbetween's normal offsets, read at the default time, where its
    /// `<name>:normalOffsets` attribute holds them (C++ `GetNormalOffsets`).
    pub fn normal_offsets(&self) -> Result<Option<Vec<gf::Vec3f>>> {
        self.normal_offsets_attr().cast()
    }

    /// Author the inbetween's normal offsets at the default time, creating
    /// the `<name>:normalOffsets` attribute where it does not exist (C++
    /// `SetNormalOffsets`).
    pub fn set_normal_offsets(&self, offsets: Vec<gf::Vec3f>) -> Result<(), StageAuthoringError> {
        self.create_normal_offsets_attr()?.set(Value::Vec3fVec(offsets))?;
        Ok(())
    }

    /// The name of the attribute that holds the inbetween's normal offsets.
    fn normal_offsets_name(&self) -> String {
        format!("{}{NORMAL_OFFSETS_SUFFIX}", self.attribute.name())
    }
}

impl BlendShape {
    /// Author the inbetween `name`, a non-custom, uniform `point3f[]` in the
    /// `inbetweens:` namespace, which `name` may already carry (C++
    /// `CreateInbetween`). `None`, with nothing authored, for a name ending in
    /// `:normalOffsets`, which names an inbetween's normal offsets.
    pub fn create_inbetween(&self, name: &str) -> Result<Option<InbetweenShape>, StageAuthoringError> {
        if name.ends_with(NORMAL_OFFSETS_SUFFIX) {
            return Ok(None);
        }
        let attribute = self
            .attribute_builder(namespaced(INBETWEENS_NAMESPACE, name).as_ref(), "point3f[]")
            .custom(false)
            .variability(sdf::Variability::Uniform)
            .build()?;
        Ok(Some(InbetweenShape::new(attribute)))
    }

    /// The view over the inbetween `name`, whether or not it exists (C++
    /// `GetInbetween`).
    pub fn inbetween(&self, name: &str) -> InbetweenShape {
        InbetweenShape::new(self.attribute(namespaced(INBETWEENS_NAMESPACE, name).as_ref()))
    }

    /// `true` when the inbetween `name` exists (C++ `HasInbetween`).
    pub fn has_inbetween(&self, name: &str) -> Result<bool> {
        self.inbetween(name).is_defined()
    }

    /// The prim's inbetweens, in property order (C++ `GetInbetweens`).
    pub fn inbetweens(&self) -> Result<Vec<InbetweenShape>> {
        Ok(inbetweens_among(self.attributes_in_namespace(INBETWEENS_NAMESPACE)?))
    }

    /// The prim's inbetweens with authored opinions, in property order (C++
    /// `GetAuthoredInbetweens`).
    pub fn authored_inbetweens(&self) -> Result<Vec<InbetweenShape>> {
        Ok(inbetweens_among(
            self.authored_attributes_in_namespace(INBETWEENS_NAMESPACE)?,
        ))
    }
}

/// The inbetweens among `attributes`, each in the `inbetweens:` namespace:
/// every one but an inbetween's normal offsets.
fn inbetweens_among(attributes: Vec<Attribute>) -> Vec<InbetweenShape> {
    attributes
        .into_iter()
        .filter(|attribute| !attribute.name().ends_with(NORMAL_OFFSETS_SUFFIX))
        .map(InbetweenShape::new)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skel::BlendShapeSchema;

    #[test]
    fn inbetween_authoring() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shape = BlendShape::define(&stage, "/Smile")?;
        shape
            .create_offsets_attr()?
            .set(Value::Vec3fVec(vec![gf::vec3f(0.0, 1.0, 0.0)]))?;
        assert!(!shape.has_inbetween("half")?);
        assert!(shape.inbetweens()?.is_empty());

        let half = shape.create_inbetween("half")?.expect("an inbetween name");
        assert!(shape.create_inbetween("half:normalOffsets")?.is_none());
        assert_eq!(half.attribute().name(), "inbetweens:half");
        assert!(half.is_defined()?);
        assert!(!half.has_authored_weight()?);
        assert_eq!(half.weight()?, None);
        half.set_weight(0.5)?;
        assert!(half.has_authored_weight()?);
        assert_eq!(half.weight()?, Some(0.5));
        half.set_offsets(vec![gf::vec3f(0.0, 0.4, 0.0)])?;
        assert_eq!(half.offsets()?, Some(vec![gf::vec3f(0.0, 0.4, 0.0)]));

        assert_eq!(half.normal_offsets()?, None);
        half.set_normal_offsets(vec![gf::vec3f(0.0, 0.0, 1.0)])?;
        assert_eq!(half.normal_offsets_attr().name(), "inbetweens:half:normalOffsets");
        assert_eq!(half.normal_offsets()?, Some(vec![gf::vec3f(0.0, 0.0, 1.0)]));

        // The normal offsets are not an inbetween of their own.
        assert!(!InbetweenShape::is_inbetween(&half.normal_offsets_attr())?);
        assert!(shape.has_inbetween("inbetweens:half")?);
        assert_eq!(shape.inbetweens()?, vec![half.clone()]);
        assert_eq!(shape.authored_inbetweens()?, vec![half]);
        // Neither the primary offsets nor a missing name are inbetweens.
        assert!(!InbetweenShape::is_inbetween(&shape.offsets_attr())?);
        assert!(!shape.inbetween("missing").is_defined()?);
        Ok(())
    }
}
