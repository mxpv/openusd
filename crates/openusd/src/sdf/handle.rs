//! Live handles to a shared layer's specs, and the layer-level reads a
//! [`LayerHandle`] makes on its own.
//!
//! A [`PrimHandle`], [`AttributeHandle`], [`RelationshipHandle`] or
//! [`PseudoRootHandle`] names a spec by its layer and path, and holds no
//! borrow of the layer. Each query borrows the layer for its own duration,
//! reads, and returns an owned value, so holding a handle never stops an
//! edit, a load or a traversal. Two queries can therefore see different
//! content; a [`LayerGuard`](super::LayerGuard) is the tool for several reads
//! of one unchanged layer.
//!
//! A query fails with [`LayerError::Busy`] where the layer cannot be
//! borrowed, most often inside an edit of any layer of its registry, which
//! borrows them all (see [`LayerError::Busy`] for every case).
//!
//! Unlike a C++ spec handle, a handle here names a path: a spec moved to
//! another path by a namespace edit is not followed, and the handle reads
//! whatever spec of its kind is at its path. It also holds its layer open,
//! as a [`LayerHandle`] does, where a C++ handle lets the layer expire.
//!
//! The typed accessors answer as the borrowed views' do, so a field that
//! fails to decode reads as unauthored there. A handle's `field(key)` reports
//! the decode failure as [`LayerError::Data`].

use std::collections::HashMap;
use std::fmt;

use crate::{tf, vt};

use super::{
    AttributeSpecRef, Data, IntoPath, Layer, LayerError, LayerHandle, Path, PathListOp, PrimSpecRef, PseudoRootSpecRef,
    RelationshipSpecRef, RelocateList, SpecType, Specifier, StringListOp, TokenListOp, Unit, ValueTypeName,
    Variability, try_into_path,
};

/// A live handle to the prim spec at a path of a shared layer (C++
/// `SdfPrimSpecHandle`). A variant spec is a prim spec here, as
/// [`Layer::prim`] views it.
///
/// Each query revalidates the spec: when no prim or variant spec is at the
/// path, it answers as for a spec with no fields, and
/// [`spec_type`](Self::spec_type) is `None`. A prim spec created again at
/// the path is read as it is now.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PrimHandle {
    /// The layer.
    layer: LayerHandle,
    /// The spec's path.
    path: Path,
}

/// A live handle to the attribute spec at a path of a shared layer (C++
/// `SdfAttributeSpecHandle`).
///
/// Each query revalidates the spec: when no attribute spec is at the path,
/// a relationship spec created there included, it answers as for a spec
/// with no fields, and [`spec_type`](Self::spec_type) is `None`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AttributeHandle {
    /// The layer.
    layer: LayerHandle,
    /// The spec's path.
    path: Path,
}

/// A live handle to the relationship spec at a path of a shared layer (C++
/// `SdfRelationshipSpecHandle`).
///
/// Each query revalidates the spec: when no relationship spec is at the
/// path, it answers as for a spec with no fields, and
/// [`spec_type`](Self::spec_type) is `None`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct RelationshipHandle {
    /// The layer.
    layer: LayerHandle,
    /// The spec's path.
    path: Path,
}

/// A live handle to a shared layer's pseudo-root spec, which holds the
/// layer's metadata (C++ `SdfPseudoRootSpec`).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct PseudoRootHandle {
    /// The layer.
    layer: LayerHandle,
}

impl LayerHandle {
    /// A live handle to the layer's pseudo-root spec, or `None` when the
    /// layer has none now (see [`Layer::pseudo_root`]).
    pub fn pseudo_root(&self) -> Result<Option<PseudoRootHandle>, LayerError> {
        let present = self.read(|layer| layer.pseudo_root().is_some())?;
        Ok(present.then(|| PseudoRootHandle { layer: self.clone() }))
    }

    /// The layer's content as text in its format (see
    /// [`Layer::export_to_string`]).
    pub fn export_to_string(&self) -> Result<String, LayerError> {
        Ok(self.read(Layer::export_to_string)??)
    }

    /// `asset_path` anchored to the layer (see [`Layer::absolute_path`]).
    pub fn absolute_path(&self, asset_path: &str) -> Result<String, LayerError> {
        self.read(|layer| layer.absolute_path(asset_path))
    }

    /// Write the layer to `filename` (see [`Layer::export`]).
    pub fn export(&self, filename: impl AsRef<str>) -> Result<(), LayerError> {
        Ok(self.read(|layer| layer.export(filename))??)
    }
}

/// Forward each listed [`Layer`] metadata read to a live query on a
/// [`LayerHandle`].
macro_rules! layer_reads {
    ($($name:ident -> $ret:ty;)*) => {
        impl LayerHandle {
            $(
                #[doc = concat!("[`Layer::", stringify!($name), "`], read now.")]
                pub fn $name(&self) -> Result<$ret, LayerError> {
                    self.read(Layer::$name)
                }
            )*
        }
    };
}

layer_reads! {
    is_dirty -> bool;
    default_prim -> Option<tf::Token>;
    default_prim_path -> Option<Path>;
    relocates -> RelocateList;
    has_relocates -> bool;
    start_time_code -> f64;
    has_start_time_code -> bool;
    end_time_code -> f64;
    has_end_time_code -> bool;
    time_codes_per_second -> f64;
    has_time_codes_per_second -> bool;
    frames_per_second -> f64;
    has_frames_per_second -> bool;
    frame_precision -> i32;
    has_frame_precision -> bool;
}

/// The read accessors every spec view has (`Spec`'s), forwarded on a live
/// handle type.
macro_rules! spec_reads {
    ($handle:ty) => {
        impl $handle {
            /// The layer the spec belongs to.
            pub fn layer(&self) -> &LayerHandle {
                &self.layer
            }

            /// The spec type at the path now, when it is a spec this handle
            /// accepts; `None` otherwise.
            pub fn spec_type(&self) -> Result<Option<SpecType>, LayerError> {
                self.query(|view| view.spec_type())
            }

            /// The field `key` as authored now, `Ok(None)` when unauthored.
            /// A field that cannot be decoded fails with [`LayerError::Data`].
            pub fn field(&self, key: &str) -> Result<Option<vt::Value>, LayerError> {
                Ok(self.query(|view| view.field(key))??)
            }

            /// The field `key` as authored now, read as `T`; `None` when it is
            /// unauthored, fails to decode, or holds another type (see
            /// [`Spec::get`](super::Spec::get)).
            pub fn get<T: TryFrom<vt::Value>>(&self, key: impl AsRef<str>) -> Result<Option<T>, LayerError> {
                self.query(|view| view.get(key))
            }

            /// Whether `key` is authored now.
            pub fn has_field(&self, key: &str) -> Result<bool, LayerError> {
                self.query(|view| view.has_field(key))
            }

            /// The authored field names now, in authored order.
            pub fn fields(&self) -> Result<Vec<String>, LayerError> {
                self.query(|view| view.fields())
            }
        }

        impl fmt::Debug for $handle {
            /// Names the layer and path, reading no content.
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($handle))
                    .field("layer", &self.layer.identifier())
                    .field("path", &self.path())
                    .finish()
            }
        }
    };
}

/// Forward each listed view accessor as a live query on `$handle`. Each
/// entry names the view type that defines the accessor, for its doc link.
macro_rules! view_reads {
    ($handle:ty: $($owner:ident :: $name:ident -> $ret:ty;)*) => {
        impl $handle {
            $(
                #[doc = concat!(
                    "[`", stringify!($owner), "::", stringify!($name), "`](super::", stringify!($owner), "::",
                    stringify!($name), "), read now.",
                )]
                pub fn $name(&self) -> Result<$ret, LayerError> {
                    self.query(|view| view.$name())
                }
            )*
        }
    };
}

/// The pieces of a live handle to the spec at a path: its
/// [`LayerHandle`] entry point `$ctor`, its `path`, and its `query`, which
/// runs a closure on a `$view` of the spec under one borrow of the layer.
/// `$what` names the specs it accepts, for the docs.
macro_rules! path_handle {
    ($handle:ident, $view:ident, $ctor:ident, $what:literal) => {
        impl LayerHandle {
            #[doc = concat!(
                "A live handle to the ", $what, " at `path`, or `None` when there is none now (see [`Layer::",
                stringify!($ctor), "`]).",
            )]
            pub fn $ctor(&self, path: impl IntoPath) -> crate::Result<Option<$handle>> {
                let path = try_into_path(path)?;
                let present = self.read(|layer| $view::get(layer.data(), path.clone()).is_some())?;
                Ok(present.then(|| $handle {
                    layer: self.clone(),
                    path,
                }))
            }
        }

        impl $handle {
            /// The spec's path.
            pub fn path(&self) -> &Path {
                &self.path
            }

            #[doc = concat!(
                "Run `read` on a view of the spec, under one borrow of the layer. When no ", $what,
                " is at the path, the view is over no data, so every accessor answers as for an unauthored field.",
            )]
            fn query<T>(&self, read: impl FnOnce(&$view<'_>) -> T) -> Result<T, LayerError> {
                self.layer.read(|layer| {
                    let empty = Data::new();
                    let view = $view::get(layer.data(), self.path.clone())
                        .unwrap_or_else(|| $view::at(&empty, self.path.clone()));
                    read(&view)
                })
            }
        }
    };
}

path_handle!(PrimHandle, PrimSpecRef, prim, "prim or variant spec");
path_handle!(AttributeHandle, AttributeSpecRef, attribute, "attribute spec");
path_handle!(
    RelationshipHandle,
    RelationshipSpecRef,
    relationship,
    "relationship spec"
);

impl PseudoRootHandle {
    /// The pseudo-root's path, `/`.
    pub fn path(&self) -> Path {
        Path::abs_root()
    }

    /// Run `read` on a view of the pseudo-root spec, under one borrow of the
    /// layer. When the layer has no pseudo-root spec, the view is over no
    /// data, so every accessor answers as for an unauthored field.
    fn query<T>(&self, read: impl FnOnce(&PseudoRootSpecRef<'_>) -> T) -> Result<T, LayerError> {
        self.layer.read(|layer| {
            let empty = Data::new();
            let view = PseudoRootSpecRef::get(layer.data()).unwrap_or_else(|| PseudoRootSpecRef::at(&empty));
            read(&view)
        })
    }
}

spec_reads!(PrimHandle);
spec_reads!(AttributeHandle);
spec_reads!(RelationshipHandle);
spec_reads!(PseudoRootHandle);

view_reads! { PrimHandle:
    PrimSpec::type_name -> Option<tf::Token>;
    PrimSpec::specifier -> Option<Specifier>;
    PrimSpec::kind -> Option<tf::Token>;
    PrimSpec::is_active -> Option<bool>;
    PrimSpec::is_hidden -> Option<bool>;
    PrimSpec::is_instanceable -> Option<bool>;
    PrimSpec::prim_children -> Option<Vec<tf::Token>>;
    PrimSpec::property_children -> Option<Vec<tf::Token>>;
    PrimSpec::api_schemas -> Option<TokenListOp>;
    PrimSpec::variant_selections -> HashMap<String, String>;
    PrimSpec::variant_set_names -> Option<StringListOp>;
}

view_reads! { PseudoRootHandle:
    PseudoRootSpec::default_prim -> Option<tf::Token>;
    PseudoRootSpec::sublayers -> Option<Vec<String>>;
    PseudoRootSpec::relocates -> Option<RelocateList>;
    PseudoRootSpec::doc -> Option<String>;
    PseudoRootSpec::start_time_code -> Option<f64>;
    PseudoRootSpec::end_time_code -> Option<f64>;
    PseudoRootSpec::time_codes_per_second -> Option<f64>;
    PseudoRootSpec::frames_per_second -> Option<f64>;
    PseudoRootSpec::frame_precision -> Option<i32>;
    PseudoRootSpec::prim_children -> Option<Vec<tf::Token>>;
}

view_reads! { AttributeHandle:
    PropertySpec::variability -> Variability;
    PropertySpec::is_custom -> bool;
    AttributeSpec::type_name -> Option<ValueTypeName>;
    AttributeSpec::default -> Option<vt::Value>;
    AttributeSpec::time_samples -> Option<Vec<(f64, vt::Value)>>;
    AttributeSpec::display_unit -> Unit;
    AttributeSpec::color_space -> Option<tf::Token>;
    AttributeSpec::allowed_tokens -> Option<Vec<tf::Token>>;
    AttributeSpec::connection_path_list -> Option<PathListOp>;
    AttributeSpec::has_connection_paths -> bool;
}

view_reads! { RelationshipHandle:
    PropertySpec::variability -> Variability;
    PropertySpec::is_custom -> bool;
    RelationshipSpec::target_path_list -> Option<PathListOp>;
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;
    use std::collections::HashSet;
    use std::fs;

    use super::*;
    use crate::sdf::layer_store::tests::inside_edit;
    use crate::sdf::{self, AbstractData, DataError};

    /// A layer holding the prim `/P`, its attribute `/P.x` (a double whose
    /// default is `x`), and its relationship `/P.r`.
    fn layer_with(x: f64) -> sdf::Layer {
        let mut layer = sdf::Layer::new_anonymous("handles.usda");
        layer
            .edit(|e| {
                sdf::PrimSpec::new(e.data_mut(), "/P", sdf::Specifier::Def, "Xform")?.set_kind("component");
                sdf::AttributeSpec::new(
                    e.data_mut(),
                    "/P.x",
                    sdf::ValueTypeName::DOUBLE,
                    Variability::Varying,
                    false,
                )?
                .set_default(x)?;
                sdf::RelationshipSpec::new(e.data_mut(), "/P.r", Variability::Uniform, true)?;
                let mut root = e.pseudo_root_mut()?;
                root.set_default_prim("P");
                root.set_start_time_code(1.0);
                Ok(())
            })
            .unwrap();
        layer
    }

    /// The double `value` holds.
    fn double(value: Option<vt::Value>) -> Option<f64> {
        value.map(|value| value.try_as_double().expect("a double"))
    }

    /// A query reads the layer as it is at the call: a value read before an
    /// edit keeps what it read, and the next query sees the edit.
    #[test]
    fn reads_follow_edits() -> crate::Result<()> {
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with(1.0)).unwrap();
        let attr = handle.attribute("/P.x")?.expect("authored");

        let before = attr.default()?;
        handle
            .edit(|e| e.attribute_mut("/P.x")?.expect("authored").set_default(2.0))
            .expect("the edit lands");
        assert_eq!(double(before), Some(1.0));
        assert_eq!(double(attr.default()?), Some(2.0));
        Ok(())
    }

    /// Holding handles blocks no edit of their layer, and no layer added to
    /// or loaded into the registry.
    #[test]
    fn handles_block_nothing() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let file = dir.path().join("loaded.usda");
        fs::write(&file, "#usda 1.0\ndef \"Loaded\" {}\n")?;
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with(1.0)).unwrap();
        let prim = handle.prim("/P")?.expect("authored");
        let attr = handle.attribute("/P.x")?.expect("authored");
        let root = handle.pseudo_root()?.expect("authored");

        handle
            .edit(|e| {
                sdf::PrimSpec::new(e.data_mut(), "/Q", sdf::Specifier::Def, "")?;
                Ok(())
            })
            .expect("the edit lands");
        assert!(registry.adopt(sdf::Layer::new_anonymous("other.usda")).is_ok());
        let loaded = registry.find_or_open(&file.to_string_lossy())?.expect("resolves");
        assert!(loaded.prim("/Loaded")?.is_some());
        assert_eq!(prim.kind()?.as_deref(), Some("component"));
        assert_eq!(double(attr.default()?), Some(1.0));
        assert_eq!(root.default_prim()?.as_deref(), Some("P"));
        Ok(())
    }

    /// A reload goes through while a handle is held, and the handle reads
    /// the reloaded content.
    #[test]
    fn reload_with_handle() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("reload.usda");
        let text = |x: f64| {
            format!(
                "#usda 1.0
def \"P\"
{{
    double x = {x}
}}
"
            )
        };
        fs::write(&path, text(1.0))?;
        let registry = sdf::LayerRegistry::default();
        let handle = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        let attr = handle.attribute("/P.x")?.expect("authored");
        let guard = handle.borrow();
        assert_eq!(handle.resolved_path(), guard.resolved_path(), "read without a borrow");
        assert!(handle.resolved_path().is_some());
        drop(guard);

        sdf::layer::tests::rewrite(&path, &text(3.0))?;
        assert!(handle.reload(false)?);
        assert_eq!(double(attr.default()?), Some(3.0));
        Ok(())
    }

    /// A removed spec reads as a spec with no fields: `None`, and each
    /// accessor's default.
    #[test]
    fn removed_reads_absent() -> crate::Result<()> {
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with(1.0)).unwrap();
        let attr = handle.attribute("/P.x")?.expect("authored");
        let rel = handle.relationship("/P.r")?.expect("authored");

        handle
            .edit(|e| {
                e.data_mut().erase_spec(&sdf::path("/P.x")?);
                e.data_mut().erase_spec(&sdf::path("/P.r")?);
                Ok(())
            })
            .expect("the edit lands");
        assert_eq!(attr.spec_type()?, None);
        assert_eq!(attr.default()?, None);
        assert_eq!(attr.type_name()?, None);
        assert_eq!(attr.fields()?, Vec::<String>::new());
        assert!(!attr.is_custom()?);
        assert_eq!(attr.variability()?, Variability::Varying);
        assert_eq!(attr.display_unit()?, Unit::Default);
        assert!(
            !rel.is_custom()?,
            "the relationship was custom; removed, it reads the default"
        );
        assert_eq!(rel.target_path_list()?, None);
        Ok(())
    }

    /// An attribute removed and a relationship created at its path: the
    /// attribute handle reads as removed, and a relationship handle made
    /// after reads the relationship.
    #[test]
    fn replaced_kind_reads_absent() -> crate::Result<()> {
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with(1.0)).unwrap();
        let attr = handle.attribute("/P.x")?.expect("authored");

        handle
            .edit(|e| {
                e.data_mut().erase_spec(&sdf::path("/P.x")?);
                sdf::RelationshipSpec::new(e.data_mut(), "/P.x", Variability::Uniform, true)?;
                Ok(())
            })
            .expect("the edit lands");
        assert_eq!(attr.spec_type()?, None);
        assert!(!attr.is_custom()?, "never the relationship's field");
        assert_eq!(attr.variability()?, Variability::Varying);
        assert!(handle.attribute("/P.x")?.is_none());
        let rel = handle.relationship("/P.x")?.expect("created");
        assert_eq!(rel.spec_type()?, Some(SpecType::Relationship));
        assert!(rel.is_custom()?);
        Ok(())
    }

    /// A spec created again with the same kind reads as it is now.
    #[test]
    fn recreated_reads_new() -> crate::Result<()> {
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with(1.0)).unwrap();
        let attr = handle.attribute("/P.x")?.expect("authored");

        handle
            .edit(|e| {
                e.data_mut().erase_spec(&sdf::path("/P.x")?);
                sdf::AttributeSpec::new(
                    e.data_mut(),
                    "/P.x",
                    sdf::ValueTypeName::FLOAT,
                    Variability::Uniform,
                    true,
                )?
                .set_default(5.0_f32)?;
                Ok(())
            })
            .expect("the edit lands");
        assert_eq!(attr.type_name()?, Some(sdf::ValueTypeName::FLOAT));
        assert_eq!(attr.variability()?, Variability::Uniform);
        assert!(attr.is_custom()?);
        assert!(attr.default()?.is_some());
        Ok(())
    }

    /// Inside an edit of the registry, a query through any of its handles
    /// fails with `Busy`, never a panic; the identifier-only reads and
    /// `Debug` still answer.
    #[test]
    fn query_inside_edit_busy() -> crate::Result<()> {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with(1.0)).unwrap();
        let b = registry.adopt(layer_with(2.0)).unwrap();
        let attr_a = a.attribute("/P.x")?.expect("authored");
        let attr_b = b.attribute("/P.x")?.expect("authored");

        let (own, other, relocates, prim, anonymous, debug) = inside_edit(&a, || {
            (
                attr_a.default(),
                attr_b.default(),
                a.relocates(),
                b.prim("/P").map(|prim| prim.is_some()),
                a.is_anonymous(),
                format!("{attr_a:?}"),
            )
        });
        assert!(matches!(own, Err(LayerError::Busy)), "{own:?}");
        assert!(matches!(other, Err(LayerError::Busy)), "{other:?}");
        assert!(matches!(relocates, Err(LayerError::Busy)), "{relocates:?}");
        assert!(matches!(prim, Err(crate::Error::Layer(LayerError::Busy))), "{prim:?}");
        assert!(anonymous);
        assert!(debug.contains(a.identifier()) && debug.contains("/P.x"), "{debug}");
        Ok(())
    }

    /// A backend whose field `broken` fails to decode.
    struct Broken(Data);

    impl AbstractData for Broken {
        fn has_spec(&self, path: &Path) -> bool {
            self.0.has_spec(path)
        }

        fn has_field(&self, path: &Path, field: &str) -> bool {
            field == "broken" || self.0.has_field(path, field)
        }

        fn spec_type(&self, path: &Path) -> Option<SpecType> {
            self.0.spec_type(path)
        }

        fn try_field(&self, path: &Path, field: &str) -> Result<Option<Cow<'_, vt::Value>>, DataError> {
            if field == "broken" {
                return Err(DataError::Decode {
                    path: path.clone(),
                    field: field.to_owned(),
                    source: "undecodable".into(),
                });
            }
            self.0.try_field(path, field)
        }

        fn list_fields(&self, path: &Path) -> Option<Vec<String>> {
            self.0.list_fields(path)
        }

        fn spec_paths(&self) -> Vec<Path> {
            self.0.spec_paths()
        }

        fn create_spec(&mut self, path: Path, ty: SpecType) {
            self.0.create_spec(path, ty);
        }

        fn erase_spec(&mut self, path: &Path) {
            self.0.erase_spec(path);
        }

        fn set_field(&mut self, path: &Path, field: &str, value: vt::Value) {
            self.0.set_field(path, field, value);
        }

        fn erase_field(&mut self, path: &Path, field: &str) {
            self.0.erase_field(path, field);
        }
    }

    /// `field` reports a decode failure and `Busy` as one flat
    /// `LayerError`.
    #[test]
    fn field_errors_flat() -> crate::Result<()> {
        let mut data = Data::rooted();
        data.create_spec(sdf::path("/P")?, SpecType::Prim);
        data.set_field(&sdf::path("/P")?, "kind", vt::Value::Token(tf::Token::from("group")));
        let registry = sdf::LayerRegistry::default();
        let handle = registry
            .adopt(Layer::new("broken.usda", Box::new(Broken(data))))
            .unwrap();
        let prim = handle.prim("/P")?.expect("present");

        assert!(prim.field("kind")?.is_some());
        let broken = prim.field("broken");
        assert!(
            matches!(broken, Err(LayerError::Data(DataError::Decode { .. }))),
            "{broken:?}"
        );
        let inside = inside_edit(&handle, || prim.field("kind"));
        assert!(matches!(inside, Err(LayerError::Busy)), "{inside:?}");
        Ok(())
    }

    /// A prim handle reads a variant spec, as `PrimSpecRef` views one.
    #[test]
    fn prim_handle_variant() -> crate::Result<()> {
        let mut layer = layer_with(1.0);
        layer
            .edit(|e| {
                e.prim_mut("/P")?.expect("authored").add_variant("look", "red")?;
                Ok(())
            })
            .unwrap();
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer).unwrap();
        let variant = handle.prim("/P{look=red}")?.expect("a variant is a prim spec here");
        assert_eq!(variant.spec_type()?, Some(SpecType::Variant));
        assert!(handle.attribute("/P{look=red}")?.is_none());
        Ok(())
    }

    /// Every forwarded accessor answers what the borrowed view's accessor
    /// answers, on one layer: the live handles share the views' field logic.
    #[test]
    fn parity_with_views() -> crate::Result<()> {
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with(1.0)).unwrap();
        let prim = handle.prim("/P")?.expect("authored");
        let attr = handle.attribute("/P.x")?.expect("authored");
        let rel = handle.relationship("/P.r")?.expect("authored");
        let root = handle.pseudo_root()?.expect("authored");
        let guard = handle.borrow();
        let v_prim = guard.prim("/P")?.expect("authored");
        let v_attr = guard.attribute("/P.x")?.expect("authored");
        let v_rel = guard.relationship("/P.r")?.expect("authored");
        let v_root = guard.pseudo_root().expect("authored");

        // `Spec`'s accessors, on each handle.
        assert_eq!(prim.spec_type()?, v_prim.spec_type());
        assert_eq!(prim.fields()?, v_prim.fields());
        assert_eq!(prim.has_field("kind")?, v_prim.has_field("kind"));
        assert_eq!(prim.field("kind")?, v_prim.field("kind")?);
        assert_eq!(prim.get::<tf::Token>("kind")?, v_prim.get::<tf::Token>("kind"));
        assert_eq!(attr.spec_type()?, v_attr.spec_type());
        assert_eq!(attr.fields()?, v_attr.fields());
        assert_eq!(rel.spec_type()?, v_rel.spec_type());
        assert_eq!(rel.fields()?, v_rel.fields());
        assert_eq!(root.spec_type()?, v_root.spec_type());
        assert_eq!(root.fields()?, v_root.fields());
        for key in ["default", "variability", "custom"] {
            assert_eq!(attr.field(key)?, v_attr.field(key)?, "{key}");
            assert_eq!(attr.has_field(key)?, v_attr.has_field(key), "{key}");
            assert_eq!(attr.get::<vt::Value>(key)?, v_attr.get::<vt::Value>(key), "{key}");
            assert_eq!(rel.field(key)?, v_rel.field(key)?, "{key}");
            assert_eq!(rel.has_field(key)?, v_rel.has_field(key), "{key}");
            assert_eq!(rel.get::<vt::Value>(key)?, v_rel.get::<vt::Value>(key), "{key}");
        }
        for key in ["defaultPrim", "startTimeCode"] {
            assert_eq!(root.field(key)?, v_root.field(key)?, "{key}");
            assert_eq!(root.has_field(key)?, v_root.has_field(key), "{key}");
            assert_eq!(root.get::<vt::Value>(key)?, v_root.get::<vt::Value>(key), "{key}");
        }

        // `PrimSpec`'s.
        assert_eq!(prim.type_name()?, v_prim.type_name());
        assert_eq!(prim.specifier()?, v_prim.specifier());
        assert_eq!(prim.kind()?, v_prim.kind());
        assert_eq!(prim.is_active()?, v_prim.is_active());
        assert_eq!(prim.is_hidden()?, v_prim.is_hidden());
        assert_eq!(prim.is_instanceable()?, v_prim.is_instanceable());
        assert_eq!(prim.prim_children()?, v_prim.prim_children());
        assert_eq!(prim.property_children()?, v_prim.property_children());
        assert_eq!(prim.api_schemas()?, v_prim.api_schemas());
        assert_eq!(prim.variant_selections()?, v_prim.variant_selections());
        assert_eq!(prim.variant_set_names()?, v_prim.variant_set_names());

        // `PropertySpec`'s and `AttributeSpec`'s.
        assert_eq!(attr.variability()?, v_attr.variability());
        assert_eq!(attr.is_custom()?, v_attr.is_custom());
        assert_eq!(attr.type_name()?, v_attr.type_name());
        assert_eq!(attr.default()?, v_attr.default());
        assert_eq!(attr.time_samples()?, v_attr.time_samples());
        assert_eq!(attr.display_unit()?, v_attr.display_unit());
        assert_eq!(attr.color_space()?, v_attr.color_space());
        assert_eq!(attr.allowed_tokens()?, v_attr.allowed_tokens());
        assert_eq!(attr.connection_path_list()?, v_attr.connection_path_list());
        assert_eq!(attr.has_connection_paths()?, v_attr.has_connection_paths());

        // `PropertySpec`'s and `RelationshipSpec`'s.
        assert_eq!(rel.variability()?, v_rel.variability());
        assert_eq!(rel.is_custom()?, v_rel.is_custom());
        assert_eq!(rel.target_path_list()?, v_rel.target_path_list());

        // `PseudoRootSpec`'s.
        assert_eq!(root.default_prim()?, v_root.default_prim());
        assert_eq!(root.sublayers()?, v_root.sublayers());
        assert_eq!(root.relocates()?, v_root.relocates());
        assert_eq!(root.doc()?, v_root.doc());
        assert_eq!(root.start_time_code()?, v_root.start_time_code());
        assert_eq!(root.end_time_code()?, v_root.end_time_code());
        assert_eq!(root.time_codes_per_second()?, v_root.time_codes_per_second());
        assert_eq!(root.frames_per_second()?, v_root.frames_per_second());
        assert_eq!(root.frame_precision()?, v_root.frame_precision());
        assert_eq!(root.prim_children()?, v_root.prim_children());

        // `Layer`'s metadata reads.
        assert_eq!(handle.relocates()?, guard.relocates());
        assert_eq!(handle.has_relocates()?, guard.has_relocates());
        assert_eq!(handle.start_time_code()?, guard.start_time_code());
        assert_eq!(handle.has_start_time_code()?, guard.has_start_time_code());
        assert_eq!(handle.end_time_code()?, guard.end_time_code());
        assert_eq!(handle.has_end_time_code()?, guard.has_end_time_code());
        assert_eq!(handle.time_codes_per_second()?, guard.time_codes_per_second());
        assert_eq!(handle.has_time_codes_per_second()?, guard.has_time_codes_per_second());
        assert_eq!(handle.frames_per_second()?, guard.frames_per_second());
        assert_eq!(handle.has_frames_per_second()?, guard.has_frames_per_second());
        assert_eq!(handle.frame_precision()?, guard.frame_precision());
        assert_eq!(handle.has_frame_precision()?, guard.has_frame_precision());
        assert_eq!(handle.is_anonymous(), guard.is_anonymous());
        assert_eq!(handle.resolved_path(), guard.resolved_path());
        assert_eq!(handle.default_prim()?, v_root.default_prim());
        assert_eq!(handle.default_prim_path()?, guard.default_prim_path());
        assert_eq!(guard.default_prim_path(), Some(sdf::path("/P")?));
        assert_eq!(handle.attribute("/P.x")?.expect("authored"), attr);
        let specs: HashSet<_> = [handle.prim("/P")?.expect("authored"), prim.clone()].into();
        assert_eq!(specs.len(), 1, "handles to one spec hash alike");
        assert_eq!(handle.export_to_string()?, guard.export_to_string()?);
        assert_eq!(handle.absolute_path("./tex.png")?, guard.absolute_path("./tex.png"));
        assert_eq!(handle.is_dirty()?, guard.is_dirty());
        let dir = tempfile::tempdir()?;
        let (live, borrowed) = (dir.path().join("live.usda"), dir.path().join("borrowed.usda"));
        handle.export(live.to_string_lossy())?;
        guard.export(borrowed.to_string_lossy())?;
        assert_eq!(fs::read_to_string(live)?, fs::read_to_string(borrowed)?);
        let missing = dir.path().join("missing").join("out.usda");
        let failed = crate::Error::from(handle.export(missing.to_string_lossy()).unwrap_err());
        assert!(matches!(failed, crate::Error::Export(_)), "{failed:?}");
        Ok(())
    }
}
