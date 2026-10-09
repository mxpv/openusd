//! What `UsdGeomPrimvarsAPI` answers: the primvars a prim holds, the ones it
//! inherits down namespace, and how one is created, blocked and removed.

use std::borrow::Cow;

use openusd::Result;
use openusd::usd::{self, SchemaBase};
use openusd::{sdf, tf};

use super::primvar::{INDICES_SUFFIX, element_stride};
use super::{Interpolation, PRIMVARS_NAMESPACE, Primvar, PrimvarsAPI, tokens};
use crate::SchemaError;

/// A prim's primvars (C++ `UsdGeomPrimvarsAPI`), which any prim can hold.
///
/// A primvar is named with or without the `primvars:` namespace: `st` and
/// `primvars:st` are the same one. A name ending in `:indices` names the
/// indices attribute of a primvar, never a primvar, and is
/// [`SchemaError::InvalidPrimvarName`].
///
/// # Inheritance
///
/// A primvar of constant interpolation with an authored value is inherited
/// by the prims beneath it. A descendant that authors a value for the same
/// primvar stops it there: a constant one replaces it for the prims further
/// down, and one of any other interpolation ends the inheritance without
/// being inherited itself. A primvar with no authored value — one only
/// declared, one that is blocked, a schema's built-in left at its fallback —
/// takes no part.
///
/// To read every prim of a hierarchy, carry the inherited set down the
/// traversal with
/// [`find_incrementally_inheritable_primvars`](Self::find_incrementally_inheritable_primvars)
/// and resolve each prim against it with the `_from` queries. The queries
/// that take no set walk every ancestor of the prim they are asked about.
///
/// # Example
///
/// ```
/// use openusd::usd::{self, SchemaBase};
/// use openusd::gf;
/// use openusd_schemas::geom::{self, PrimvarsAPI};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let set = geom::Xform::define(&stage, "/Set")?;
/// let prop = geom::Mesh::define(&stage, "/Set/Prop")?;
///
/// // The set authors a constant primvar.
/// PrimvarsAPI::from_prim_unchecked(set.prim().clone())
///     .primvar_builder("tint", "color3f")
///     .set(gf::vec3f(1.0, 0.5, 0.0))
///     .build()?;
///
/// // The prop defines no `tint` of its own and inherits the set's.
/// let prop = PrimvarsAPI::from_prim_unchecked(prop.prim().clone());
/// assert!(!prop.has_primvar("tint")?);
/// let tint = prop.find_primvar_with_inheritance("tint")?.expect("inherited");
/// assert_eq!(tint.attribute().path().as_str(), "/Set.primvars:tint");
/// assert_eq!(tint.get_at::<gf::Vec3f>(None)?, Some(gf::vec3f(1.0, 0.5, 0.0)));
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
///
/// A traversal that carries the inherited set down reads each prim's own
/// primvars once:
///
/// ```
/// use openusd::usd::{self, SchemaBase};
/// use openusd_schemas::geom::{self, Primvar, PrimvarsAPI};
///
/// /// Records the primvars that apply to `prim` and to each prim beneath it.
/// fn visit(prim: &usd::Prim, inherited: &[Primvar], found: &mut Vec<String>) -> openusd::Result<()> {
///     let api = PrimvarsAPI::from_prim_unchecked(prim.clone());
///     for primvar in api.find_primvars_with_inheritance_from(inherited)? {
///         found.push(format!("{} <- {}", prim.path(), primvar.attribute().path()));
///     }
///     // `None` says this prim hands on exactly what reached it.
///     let handed_down = api.find_incrementally_inheritable_primvars(inherited)?;
///     let inherited = handed_down.as_deref().unwrap_or(inherited);
///     for child in prim.children()? {
///         visit(&child, inherited, found)?;
///     }
///     Ok(())
/// }
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let set = geom::Xform::define(&stage, "/Set")?;
/// geom::Mesh::define(&stage, "/Set/Prop")?;
/// PrimvarsAPI::from_prim_unchecked(set.prim().clone())
///     .primvar_builder("id", "int")
///     .set(7)
///     .build()?;
///
/// let mut found = Vec::new();
/// visit(set.prim(), &[], &mut found)?;
/// assert_eq!(
///     found,
///     ["/Set <- /Set.primvars:id", "/Set/Prop <- /Set.primvars:id"]
/// );
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
impl PrimvarsAPI {
    /// Author the primvar `name` as a `type_name` attribute holding no value
    /// (C++ `CreatePrimvar`). A primvar that already exists keeps the
    /// declaration it has, and its indices are left as they are.
    pub fn create_primvar(&self, name: &str, type_name: impl Into<sdf::ValueTypeName>) -> Result<Primvar, SchemaError> {
        let name = attribute_name(name)?;
        Ok(Primvar::new(
            self.attribute_builder(name.as_ref(), type_name).custom(false).build()?,
        ))
    }

    /// The primvar `name` to author together with its value, its metadata
    /// and its indices, as one edit.
    pub fn primvar_builder(&self, name: &str, type_name: impl Into<sdf::ValueTypeName>) -> PrimvarBuilder<'static> {
        PrimvarBuilder::new(self.prim().clone(), None, name, type_name.into())
    }

    /// The primvar `name` (C++ `GetPrimvar`), whether or not anything defines
    /// it.
    pub fn primvar(&self, name: &str) -> Result<Primvar, SchemaError> {
        Ok(Primvar::new(self.attribute(attribute_name(name)?.as_ref())))
    }

    /// Whether the prim defines the primvar `name` (C++ `HasPrimvar`). A name
    /// no primvar can have is not one the prim has.
    pub fn has_primvar(&self, name: &str) -> Result<bool> {
        match attribute_name(name) {
            Ok(name) => self.attribute(name.as_ref()).is_defined(),
            Err(_) => Ok(false),
        }
    }

    /// Remove the primvar `name` and its indices attribute from the edit
    /// target (C++ `RemovePrimvar`).
    ///
    /// `false` where the prim defines no such primvar, and where the edit
    /// target held no spec to remove for one of the two: a primvar composed
    /// from elsewhere, across a reference for one, stays.
    pub fn remove_primvar(&self, name: &str) -> Result<bool, SchemaError> {
        let primvar = self.primvar(name)?;
        if !primvar.attribute().is_defined()? {
            return Ok(false);
        }
        // TODO(perf): two layer transactions, each with its own invalidation
        // and notice. A `usd::StageEdit` batches property authoring only;
        // removing a spec inside one is the missing piece.
        let stage = self.stage();
        let indices = primvar.indices_attr();
        let indices_removed = !indices.is_defined()? || stage.remove_property(indices.path().clone())?;
        let removed = stage.remove_property(primvar.attribute().path().clone())?;
        Ok(removed && indices_removed)
    }

    /// Block the primvar `name`, so it reads no value whatever weaker layers
    /// author (C++ `BlockPrimvar`), as one edit. An array-valued primvar has
    /// its indices blocked with it, the indices attribute being created to
    /// hold the block where the primvar had none.
    ///
    /// `false` where the prim defines no such primvar, and nothing is
    /// authored. The primvar's metadata is left as it is.
    pub fn block_primvar(&self, name: &str) -> Result<bool, SchemaError> {
        let primvar = self.primvar(name)?;
        let attribute = primvar.attribute();
        if !attribute.is_defined()? {
            return Ok(false);
        }
        // The primvar is defined, so the block stamps the declaration it
        // already has and this one declares nothing.
        let type_name = primvar.type_name()?.ok_or(sdf::ValueTypeError::Empty)?;
        self.stage().edit(|edit| {
            let prim = edit.prim(self.path().clone())?;
            if type_name.is_array() {
                indices_builder(&prim, attribute.name()).block().build()?;
            }
            prim.attribute_builder(attribute.name(), type_name).block().build()?;
            Ok::<_, SchemaError>(())
        })?;
        Ok(true)
    }

    /// The prim's primvars, in its property order (C++ `GetPrimvars`): the
    /// ones layers author and the ones its schemas declare, whether or not
    /// they hold a value.
    pub fn primvars(&self) -> Result<Vec<Primvar>> {
        Ok(primvars_among(self.attributes_in_namespace(PRIMVARS_NAMESPACE)?))
    }

    /// The primvars layers author on the prim, in its property order (C++
    /// `GetAuthoredPrimvars`).
    pub fn authored_primvars(&self) -> Result<Vec<Primvar>> {
        Ok(primvars_among(
            self.authored_attributes_in_namespace(PRIMVARS_NAMESPACE)?,
        ))
    }

    /// The prim's primvars that have a value, authored or a schema's
    /// fallback (C++ `GetPrimvarsWithValues`).
    pub fn primvars_with_values(&self) -> Result<Vec<Primvar>> {
        keeping(self.primvars()?, |primvar| primvar.attribute().has_value())
    }

    /// The prim's primvars that have an authored value (C++
    /// `GetPrimvarsWithAuthoredValues`): the ones a renderer reads from this
    /// prim.
    pub fn primvars_with_authored_values(&self) -> Result<Vec<Primvar>> {
        keeping(self.authored_primvars()?, |primvar| {
            primvar.attribute().has_authored_value()
        })
    }

    /// The primvars the prims beneath this one inherit from it and its
    /// ancestors (C++ `FindInheritablePrimvars`), root-most first and, among
    /// the primvars of one prim, in its property order. A primvar a nearer
    /// prim replaces keeps the place of the one it replaced.
    pub fn find_inheritable_primvars(&self) -> Result<Vec<Primvar>> {
        self.inherited_through(false)
    }

    /// The primvars the prims beneath this one inherit, given the ones this
    /// prim's parent hands down (C++ `FindIncrementallyInheritablePrimvars`).
    ///
    /// `None` where this prim changes nothing, so the parent's set is the one
    /// to hand on. A set comes back wherever the prim adds, replaces or stops
    /// a primvar, and is empty where it stops the last of them.
    pub fn find_incrementally_inheritable_primvars(&self, inherited: &[Primvar]) -> Result<Option<Vec<Primvar>>> {
        inherit(self.prim(), inherited, false)
    }

    /// The primvars that apply to this prim (C++
    /// `FindPrimvarsWithInheritance`): each of its own that has an authored
    /// value, whatever its interpolation, and the ones it inherits, ordered
    /// as [`find_inheritable_primvars`](Self::find_inheritable_primvars)
    /// orders them.
    pub fn find_primvars_with_inheritance(&self) -> Result<Vec<Primvar>> {
        self.inherited_through(true)
    }

    /// [`find_primvars_with_inheritance`](Self::find_primvars_with_inheritance),
    /// given the primvars this prim's parent hands down.
    pub fn find_primvars_with_inheritance_from(&self, inherited: &[Primvar]) -> Result<Vec<Primvar>> {
        Ok(inherit(self.prim(), inherited, true)?.unwrap_or_else(|| inherited.to_vec()))
    }

    /// The primvar `name` as it applies to this prim (C++
    /// `FindPrimvarWithInheritance`).
    ///
    /// The prim's own where that has an authored value. Otherwise the one on
    /// the nearest ancestor that authors a value for it, where that one is of
    /// constant interpolation; an ancestor's primvar of any other
    /// interpolation is not inherited, and hides the ones above it. Where
    /// nothing is inherited, the prim's own primvar if the prim defines it,
    /// which then holds no authored value, and `None` if it does not.
    pub fn find_primvar_with_inheritance(&self, name: &str) -> Result<Option<Primvar>, SchemaError> {
        let local = self.primvar(name)?;
        if local.attribute().has_authored_value()? {
            return Ok(Some(local));
        }
        match self.inherited(&local)? {
            Some(inherited) => Ok(Some(inherited)),
            None => Ok(defined(local)?),
        }
    }

    /// [`find_primvar_with_inheritance`](Self::find_primvar_with_inheritance),
    /// given the primvars this prim's parent hands down.
    pub fn find_primvar_with_inheritance_from(
        &self,
        name: &str,
        inherited: &[Primvar],
    ) -> Result<Option<Primvar>, SchemaError> {
        let local = self.primvar(name)?;
        if local.attribute().has_authored_value()? {
            return Ok(Some(local));
        }
        let handed_down = inherited
            .iter()
            .find(|primvar| primvar.attribute().name() == local.attribute().name());
        match handed_down {
            Some(primvar) => Ok(Some(primvar.clone())),
            None => Ok(defined(local)?),
        }
    }

    /// Whether the primvar `name` has an authored value on this prim, or
    /// reaches it from an ancestor (C++ `HasPossiblyInheritedPrimvar`).
    pub fn has_possibly_inherited_primvar(&self, name: &str) -> Result<bool, SchemaError> {
        let local = self.primvar(name)?;
        if local.attribute().has_authored_value()? {
            return Ok(true);
        }
        Ok(self.inherited(&local)?.is_some())
    }

    /// The primvar named as `local` is that this prim inherits: the one on
    /// the nearest ancestor that authors a value for it, where that one is of
    /// constant interpolation. `None` where no ancestor authors a value, and
    /// where the nearest that does is not constant.
    fn inherited(&self, local: &Primvar) -> Result<Option<Primvar>> {
        let stage = self.stage();
        let name = tf::Token::from(local.attribute().name());
        for path in self.path().strict_ancestors_below_root() {
            let attribute = stage.prim(path)?.attribute(&name);
            if attribute.has_authored_value()? && attribute.is_defined()? {
                let nearest = Primvar::new(attribute);
                return Ok(nearest.is_constant()?.then_some(nearest));
            }
        }
        Ok(None)
    }

    /// The set inherited through this prim from the root-most ancestor down,
    /// this prim taking all of its own primvars where `accept_all` says so.
    fn inherited_through(&self, accept_all: bool) -> Result<Vec<Primvar>> {
        let stage = self.stage();
        let mut lineage: Vec<sdf::Path> = self.path().ancestors_below_root().collect();
        lineage.reverse();

        let mut inherited = Vec::new();
        for path in lineage {
            let accept_all = accept_all && path == *self.path();
            if let Some(changed) = inherit(&stage.prim(path)?, &inherited, accept_all)? {
                inherited = changed;
            }
        }
        Ok(inherited)
    }
}

/// A primvar to author, and everything it is authored with: its value, its
/// `interpolation` and `elementSize`, and its indices.
///
/// All of it is one edit of the target layer, written at
/// [`build`](Self::build), and a primvar that cannot be built authors none of
/// it. A builder from [`PrimvarsAPI::primvar_builder`] commits on its own;
/// one from [`in_edit`](Self::in_edit) joins that transaction instead, with
/// the primvar and its indices queued together or not at all.
///
/// # Example
///
/// ```
/// use openusd::usd::{self, SchemaBase};
/// use openusd::{gf, sdf};
/// use openusd_schemas::SchemaError;
/// use openusd_schemas::geom::{self, Interpolation, PrimvarBuilder};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let mesh = geom::Mesh::define(&stage, "/Mesh")?;
///
/// // Both primvars, with their metadata and indices, are one edit of the
/// // layer.
/// stage.edit(|edit| {
///     let prim = edit.prim(mesh.path().clone())?;
///     PrimvarBuilder::in_edit(&prim, "st", "texCoord2f[]")
///         .interpolation(Interpolation::FaceVarying)
///         .set(sdf::Value::Vec2fVec(vec![gf::vec2f(0.0, 0.0), gf::vec2f(1.0, 1.0)]))
///         .indices(vec![0, 1, 0])
///         .build()?;
///     PrimvarBuilder::in_edit(&prim, "displayOpacity", "float[]")
///         .set(sdf::Value::FloatVec(vec![0.5]))
///         .build()?;
///     Ok::<_, SchemaError>(())
/// })?;
///
/// let primvars = geom::PrimvarsAPI::from_prim_unchecked(mesh.prim().clone());
/// let st = primvars.primvar("st")?;
/// assert_eq!(st.interpolation()?, Interpolation::FaceVarying);
/// assert_eq!(st.indices(None)?, Some(vec![0, 1, 0]));
/// assert!(primvars.has_primvar("displayOpacity")?);
/// # Ok::<(), SchemaError>(())
/// ```
#[derive(Debug)]
pub struct PrimvarBuilder<'a> {
    prim: usd::Prim,
    /// The transaction to join, where the builder came from one.
    edit: Option<&'a usd::PrimEdit<'a>>,
    name: String,
    type_name: sdf::ValueTypeName,
    interpolation: Option<Interpolation>,
    element_size: Option<i32>,
    /// The value to author, and when it is for.
    value: Option<(sdf::Value, Option<usd::TimeCode>)>,
    indexing: Indexing,
}

/// What a [`PrimvarBuilder`] does with the primvar's indices.
#[derive(Debug)]
enum Indexing {
    /// Leaves them as they are.
    Untouched,
    /// Authors these, at the value's time.
    Indexed(Vec<i32>),
    /// Blocks them.
    Unindexed,
}

impl<'a> PrimvarBuilder<'a> {
    fn new(prim: usd::Prim, edit: Option<&'a usd::PrimEdit<'a>>, name: &str, type_name: sdf::ValueTypeName) -> Self {
        PrimvarBuilder {
            prim,
            edit,
            name: name.to_owned(),
            type_name,
            interpolation: None,
            element_size: None,
            value: None,
            indexing: Indexing::Untouched,
        }
    }

    /// The primvar `name` on the prim of `edit`, authored as part of that
    /// transaction.
    pub fn in_edit(edit: &'a usd::PrimEdit<'a>, name: &str, type_name: impl Into<sdf::ValueTypeName>) -> Self {
        Self::new(edit.prim().clone(), Some(edit), name, type_name.into())
    }

    /// The `interpolation` to author with it.
    pub fn interpolation(mut self, interpolation: Interpolation) -> Self {
        self.interpolation = Some(interpolation);
        self
    }

    /// The `elementSize` to author with it. A size below one fails the
    /// build.
    pub fn element_size(mut self, element_size: i32) -> Self {
        self.element_size = Some(element_size);
        self
    }

    /// The default value to author with it.
    pub fn set(self, value: impl Into<sdf::Value>) -> Self {
        self.set_at(value, None)
    }

    /// The value to author at `time`, or the default where `time` is `None`.
    pub fn set_at(mut self, value: impl Into<sdf::Value>, time: impl Into<Option<usd::TimeCode>>) -> Self {
        self.value = Some((value.into(), time.into()));
        self
    }

    /// The indices to author with it, at the value's time (C++
    /// `CreateIndexedPrimvar`).
    pub fn indices(mut self, indices: Vec<i32>) -> Self {
        self.indexing = Indexing::Indexed(indices);
        self
    }

    /// Blocks the primvar's indices, so the value reads as it is authored
    /// here whatever a weaker layer indexes the primvar with (C++
    /// `CreateNonIndexedPrimvar`).
    pub fn unindexed(mut self) -> Self {
        self.indexing = Indexing::Unindexed;
        self
    }

    /// Authors the primvar and hands back its view.
    ///
    /// The name and the element size are checked before anything is planned.
    /// Indices, given or blocked, need an array-valued primvar, and the type
    /// that decides is the one the primvar will have: its schema's
    /// declaration, else the strongest authored one, and only for a new
    /// primvar the type this builder was given. A primvar that is not an
    /// array there is [`SchemaError::PrimvarNotArray`], whatever type the
    /// builder asked for and whatever the edit target's own spec says.
    pub fn build(self) -> Result<Primvar, SchemaError> {
        let name = attribute_name(&self.name)?.into_owned();
        let path = self.prim.path().append_property(name.as_str())?;
        if let Some(element_size) = self.element_size {
            element_stride(&path, element_size)?;
        }

        if let Some(edit) = self.edit {
            return edit.group(|group| self.queue(group, &name, path));
        }
        let stage = self.prim.stage().clone();
        stage.edit(|edit| self.queue(&edit.prim(path.prim_path())?, &name, path.clone()))
    }

    /// Queues the primvar and its indices into `edit`.
    fn queue(self, edit: &usd::PrimEdit<'_>, name: &str, path: sdf::Path) -> Result<Primvar, SchemaError> {
        let time = self.value.as_ref().and_then(|(_, time)| *time);
        let mut primvar = edit.attribute_builder(name, self.type_name).custom(false);
        if let Some(interpolation) = self.interpolation {
            primvar = primvar.metadata(tokens::INTERPOLATION, interpolation);
        }
        if let Some(element_size) = self.element_size {
            primvar = primvar.metadata(tokens::ELEMENT_SIZE, sdf::Value::Int(element_size));
        }
        if let Some((value, time)) = self.value {
            primvar = primvar.set_at(value, time);
        }

        let indices = match self.indexing {
            Indexing::Untouched => None,
            Indexing::Indexed(indices) => Some(indices_builder(edit, name).set_at(sdf::Value::IntVec(indices), time)),
            Indexing::Unindexed => Some(indices_builder(edit, name).block()),
        };
        // A builder with no declaration to report holds a failure, which its
        // own build returns below.
        if indices.is_some()
            && let Some(declared) = primvar.declared_type()?
            && !declared.is_array()
        {
            return Err(SchemaError::PrimvarNotArray {
                primvar: path,
                type_name: declared.as_token(),
            });
        }

        let attribute = primvar.build()?;
        if let Some(indices) = indices {
            indices.build()?;
        }
        Ok(Primvar::new(attribute))
    }
}

/// The attribute name of the primvar `name`: the name itself where it is
/// already in the `primvars:` namespace, else the name put in it (C++
/// `UsdGeomPrimvar::_MakeNamespaced`).
fn attribute_name(name: &str) -> Result<Cow<'_, str>, SchemaError> {
    let namespaced = match name.starts_with(PRIMVARS_NAMESPACE) {
        true => Cow::Borrowed(name),
        false => Cow::Owned(format!("{PRIMVARS_NAMESPACE}{name}")),
    };
    match Primvar::is_valid_primvar_name(&namespaced) {
        true => Ok(namespaced),
        false => Err(SchemaError::InvalidPrimvarName { name: name.to_owned() }),
    }
}

/// The indices attribute of the primvar `name`, to author in `edit`'s
/// transaction.
fn indices_builder<'a>(edit: &usd::PrimEdit<'a>, name: &str) -> usd::AttributeBuilder<'a> {
    edit.attribute_builder(format!("{name}{INDICES_SUFFIX}"), sdf::ValueTypeName::INT_ARRAY)
        .custom(false)
}

/// The primvars among `attributes`, in the order given: an indices attribute
/// is in the namespace without being one.
fn primvars_among(attributes: Vec<usd::Attribute>) -> Vec<Primvar> {
    attributes.into_iter().filter_map(Primvar::from_attribute).collect()
}

/// The primvars among `primvars` that `keep` answers `true` for, in the order
/// given.
fn keeping(primvars: Vec<Primvar>, keep: impl Fn(&Primvar) -> Result<bool>) -> Result<Vec<Primvar>> {
    let mut kept = Vec::with_capacity(primvars.len());
    for primvar in primvars {
        if keep(&primvar)? {
            kept.push(primvar);
        }
    }
    Ok(kept)
}

/// `primvar` where its prim defines it, and `None` where nothing does.
fn defined(primvar: Primvar) -> Result<Option<Primvar>> {
    Ok(primvar.attribute().is_defined()?.then_some(primvar))
}

/// The inherited set as it leaves `prim`, given the one that reaches it, or
/// `None` where the prim changes nothing (C++ `_AddPrimToInheritedPrimvars`).
///
/// Each of the prim's primvars with an authored value acts on the set. One it
/// keeps — a constant one, or any at all where `accept_all` — replaces the
/// primvar of its name in place, or joins the end. One it does not keep
/// removes the primvar of its name, and the rest keep their order.
///
/// TODO(perf): each call recomposes the prim's property names, walking every
/// layer of every node of its index, and then asks each primvar for its value
/// source and its interpolation. A per-index memo of the composed property
/// names would let a traversal pay for each prim's names once. The prims of
/// one generation are independent of each other given their parent's set, so
/// a traversal can fan out over siblings. The namespace listing also resolves
/// the spec type of every `:indices` attribute before it is dropped here; a
/// listing filtered by name first would skip those.
fn inherit(prim: &usd::Prim, inherited: &[Primvar], accept_all: bool) -> Result<Option<Vec<Primvar>>> {
    let mut set = Cow::Borrowed(inherited);
    for primvar in primvars_among(prim.authored_attributes_in_namespace(PRIMVARS_NAMESPACE)?) {
        if !primvar.attribute().has_authored_value()? {
            continue;
        }
        let keeps = accept_all || primvar.is_constant()?;
        let name: &str = primvar.attribute().name();
        let held = set.iter().position(|other| other.attribute().name() == name);
        match (held, keeps) {
            (Some(at), true) => set.to_mut()[at] = primvar,
            (Some(at), false) => {
                set.to_mut().remove(at);
            }
            (None, true) => set.to_mut().push(primvar),
            (None, false) => {}
        }
    }
    Ok(match set {
        Cow::Borrowed(_) => None,
        Cow::Owned(set) => Some(set),
    })
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::fs;
    use std::rc::Rc;

    use openusd::usd::{self, SchemaBase, Stage};
    use openusd::{sdf, tf};

    use super::PrimvarBuilder;
    use crate::SchemaError;
    use crate::geom::{Interpolation, Mesh, Primvar, PrimvarsAPI, Xform, tokens};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    fn stage() -> Result<Stage> {
        Ok(crate::tests::stage("anon.usda")?)
    }

    fn api(prim: &usd::Prim) -> PrimvarsAPI {
        PrimvarsAPI::from_prim_unchecked(prim.clone())
    }

    /// The mesh `/Mesh` of a new stage, seen as its primvars.
    fn mesh() -> Result<PrimvarsAPI> {
        Ok(api(Mesh::define(&stage()?, "/Mesh")?.prim()))
    }

    fn floats(values: &[f32]) -> sdf::Value {
        sdf::Value::FloatVec(values.to_vec())
    }

    /// How many edits the stage commits from here on.
    fn commits(stage: &Stage) -> Rc<Cell<usize>> {
        let commits = Rc::new(Cell::new(0));
        let counted = commits.clone();
        stage.add_sink(move |_stage: &Stage, _change: &usd::CommittedChange<'_>| counted.set(counted.get() + 1));
        commits
    }

    /// The attribute path of each primvar, in the order given.
    fn paths(primvars: &[Primvar]) -> Vec<&str> {
        primvars
            .iter()
            .map(|primvar| primvar.attribute().path().as_str())
            .collect()
    }

    /// The name of each primvar, namespace stripped, in the order given.
    fn names(primvars: &[Primvar]) -> Vec<&str> {
        primvars.iter().map(Primvar::primvar_name).collect()
    }

    /// A name is the same primvar with or without the namespace, and the
    /// attribute it authors is no custom property.
    #[test]
    fn create_namespaces_name() -> Result {
        let mesh = mesh()?;
        let st = mesh.create_primvar("st", "texCoord2f[]")?;
        let uv = mesh.create_primvar("primvars:uv", "texCoord2f[]")?;

        assert_eq!(st.attribute().name(), "primvars:st");
        assert_eq!(uv.attribute().name(), "primvars:uv");
        assert!(!st.attribute().is_custom()?);
        assert_eq!(st.attribute().get::<sdf::Value>()?, None);
        for name in ["st", "primvars:st", "uv"] {
            assert!(mesh.has_primvar(name)?, "{name}");
        }
        assert_eq!(mesh.primvar("primvars:st")?, st);
        assert!(!mesh.has_primvar("nope")?);
        Ok(())
    }

    /// `indices` at the end of a name is the indices attribute's, so no
    /// primvar is created, looked up or found under one.
    #[test]
    fn create_rejects_indices() -> Result {
        let mesh = mesh()?;
        for name in ["indices", "multi:aggregate:indices", "primvars:st:indices"] {
            let error = mesh.create_primvar(name, "int[]").expect_err("a reserved name");
            assert!(matches!(error, SchemaError::InvalidPrimvarName { name: named } if named == name));
            assert!(mesh.primvar(name).is_err());
            assert!(!mesh.has_primvar(name)?);
        }
        assert!(mesh.authored_primvars()?.is_empty());
        Ok(())
    }

    /// The value, the metadata and the indices are one edit.
    #[test]
    fn builder_one_transaction() -> Result {
        let mesh = mesh()?;
        let commits = commits(mesh.stage());
        let primvar = mesh
            .primvar_builder("st", "float[]")
            .interpolation(Interpolation::FaceVarying)
            .element_size(2)
            .set(floats(&[0.0, 0.0, 1.0, 1.0]))
            .indices(vec![1, 0])
            .build()?;

        assert_eq!(commits.get(), 1);
        assert_eq!(primvar.interpolation()?, Interpolation::FaceVarying);
        assert_eq!(primvar.element_size()?, 2);
        assert_eq!(primvar.indices(None)?, Some(vec![1, 0]));
        assert_eq!(
            primvar.compute_flattened::<Vec<f32>>(None)?,
            Some(vec![1.0, 1.0, 0.0, 0.0])
        );
        Ok(())
    }

    /// An unindexed build blocks the indices already there, samples and all.
    #[test]
    fn builder_unindexed_blocks() -> Result {
        let mesh = mesh()?;
        let indexed = mesh
            .primvar_builder("x", "float[]")
            .set(floats(&[1.0, 2.0]))
            .indices(vec![1, 1])
            .build()?;
        indexed.set_indices(vec![0], usd::TimeCode::new(1.0))?;

        let primvar = mesh
            .primvar_builder("x", "float[]")
            .set(floats(&[3.0]))
            .unindexed()
            .build()?;
        assert!(!primvar.is_indexed()?);
        assert!(primvar.indices_attr().resolve_info()?.value_is_blocked());
        assert_eq!(primvar.compute_flattened::<Vec<f32>>(None)?, Some(vec![3.0]));
        Ok(())
    }

    /// Creating a primvar that is already indexed leaves its indices alone.
    #[test]
    fn plain_create_keeps_indices() -> Result {
        let mesh = mesh()?;
        mesh.primvar_builder("x", "float[]")
            .set(floats(&[1.0, 2.0]))
            .indices(vec![1])
            .build()?;

        let again = mesh.create_primvar("x", "float[]")?;
        assert!(again.is_indexed()?);
        let reset = mesh.primvar_builder("x", "float[]").set(floats(&[5.0, 6.0])).build()?;
        assert_eq!(reset.compute_flattened::<Vec<f32>>(None)?, Some(vec![6.0]));
        Ok(())
    }

    /// Indices on a scalar primvar fail the build, and the value that came
    /// with them is not authored either.
    #[test]
    fn scalar_indices_author_nothing() -> Result {
        let mesh = mesh()?;
        let commits = commits(mesh.stage());
        for builder in [
            mesh.primvar_builder("x", "float").set(1.0_f32).indices(vec![0]),
            mesh.primvar_builder("x", "float").set(1.0_f32).unindexed(),
        ] {
            let error = builder.build().expect_err("a float is no array");
            assert!(matches!(
                error,
                SchemaError::PrimvarNotArray { type_name, .. } if type_name == "float"
            ));
        }
        assert_eq!(commits.get(), 0);
        assert!(!mesh.has_primvar("x")?);
        assert!(!mesh.attribute("primvars:x:indices").is_defined()?);
        Ok(())
    }

    /// A builder made in a transaction commits with it, beside the
    /// properties the caller queued.
    #[test]
    fn builder_joins_edit() -> Result {
        let mesh = mesh()?;
        let commits = commits(mesh.stage());
        mesh.stage().edit(|edit| {
            let prim = edit.prim(mesh.path().clone())?;
            prim.attribute_builder("other", "double").set(1.0).build()?;
            PrimvarBuilder::in_edit(&prim, "st", "float[]")
                .set(floats(&[1.0, 2.0]))
                .indices(vec![1])
                .build()?;
            assert!(!mesh.has_primvar("st")?, "nothing is written yet");
            Ok::<_, SchemaError>(())
        })?;

        assert_eq!(commits.get(), 1);
        assert!(mesh.attribute("other").is_defined()?);
        assert_eq!(
            mesh.primvar("st")?.compute_flattened::<Vec<f32>>(None)?,
            Some(vec![2.0])
        );
        Ok(())
    }

    /// A build that fails on a schema rule fails the transaction it is in
    /// with that error, and the transaction writes nothing.
    #[test]
    fn schema_error_rolls_back() -> Result {
        let mesh = mesh()?;
        let failed = mesh.stage().edit(|edit| {
            let prim = edit.prim(mesh.path().clone())?;
            prim.attribute_builder("other", "double").set(1.0).build()?;
            PrimvarBuilder::in_edit(&prim, "st", "float[]")
                .element_size(0)
                .set(floats(&[1.0]))
                .build()?;
            Ok::<_, SchemaError>(())
        });

        assert!(matches!(
            failed,
            Err(SchemaError::InvalidElementSize { element_size: 0, .. })
        ));
        assert!(!mesh.attribute("other").is_defined()?);
        assert!(!mesh.has_primvar("st")?);
        Ok(())
    }

    /// A build that fails after queueing the primvar leaves none of it in the
    /// transaction, so a caller that goes on commits only its own property.
    #[test]
    fn failed_build_leaks_nothing() -> Result {
        let mesh = mesh()?;
        mesh.stage().edit(|edit| {
            let prim = edit.prim(mesh.path().clone())?;
            prim.attribute_builder("primvars:st:indices", "int[]").build()?;
            let failed = PrimvarBuilder::in_edit(&prim, "st", "float[]")
                .interpolation(Interpolation::Vertex)
                .set(floats(&[1.0]))
                .indices(vec![0])
                .build();
            assert!(matches!(
                failed,
                Err(SchemaError::Core(openusd::Error::Authoring(
                    usd::StageAuthoringError::DuplicateProperty { .. }
                )))
            ));
            Ok::<_, SchemaError>(())
        })?;

        assert!(mesh.attribute("primvars:st:indices").is_defined()?);
        assert!(!mesh.has_primvar("st")?);
        let st = mesh.primvar("st")?;
        assert!(!st.has_authored_interpolation()?);
        assert!(!st.is_indexed()?);
        Ok(())
    }

    /// The type that decides whether a primvar takes indices is the one it
    /// has: a scalar stays one, whatever array the builder asks for.
    #[test]
    fn scalar_declared_rejects_indices() -> Result {
        let mesh = mesh()?;
        mesh.create_primvar("x", "float")?;
        let error = mesh
            .primvar_builder("x", "float[]")
            .indices(vec![0])
            .build()
            .expect_err("the primvar is a float");

        assert!(matches!(
            error,
            SchemaError::PrimvarNotArray { type_name, .. } if type_name == "float"
        ));
        assert!(!mesh.attribute("primvars:x:indices").is_defined()?);
        Ok(())
    }

    /// An array stays an array too: asking for a scalar over it indexes the
    /// array it is.
    #[test]
    fn array_declared_keeps_type() -> Result {
        let mesh = mesh()?;
        mesh.primvar_builder("x", "float[]").set(floats(&[1.0, 2.0])).build()?;
        let primvar = mesh.primvar_builder("x", "float").indices(vec![1]).build()?;

        assert_eq!(primvar.type_name()?, Some(sdf::ValueTypeName::FLOAT_ARRAY));
        assert_eq!(primvar.compute_flattened::<Vec<f32>>(None)?, Some(vec![2.0]));
        Ok(())
    }

    /// A schema's declaration is the type, for a primvar no layer authors.
    #[test]
    fn schema_declared_type_wins() -> Result {
        let mesh = mesh()?;
        let color = mesh
            .primvar_builder("displayColor", "color3f")
            .indices(vec![0])
            .build()?;
        assert_eq!(color.type_name()?, Some(sdf::ValueTypeName::COLOR3F_ARRAY));
        assert!(color.is_indexed()?);
        Ok(())
    }

    /// The edit target's own spec does not make a primvar an array: a
    /// stronger layer declares it a scalar, and a scalar takes no indices.
    #[test]
    fn weaker_local_array_rejected() -> Result {
        let dir = tempfile::tempdir().map_err(openusd::Error::from)?;
        let write = |name: &str, declaration: &str| {
            let text = format!("#usda 1.0\ndef \"A\"\n{{\n    {declaration}\n}}\n");
            fs::write(dir.path().join(name), text).map_err(openusd::Error::from)
        };
        write("session.usda", "float primvars:x")?;
        write("root.usda", "float[] primvars:x")?;
        let stage = Stage::builder()
            .session_layer(dir.path().join("session.usda").to_str().expect("utf-8 path"))
            .open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        let prim = api(&stage.prim("/A")?);

        let error = prim
            .primvar_builder("x", "float[]")
            .indices(vec![0])
            .build()
            .expect_err("the composed type is a float");
        assert!(matches!(
            error,
            SchemaError::PrimvarNotArray { type_name, .. } if type_name == "float"
        ));
        assert!(!prim.attribute("primvars:x:indices").is_defined()?);
        Ok(())
    }

    /// The primvars come back in the prim's property order, with the indices
    /// attribute and the id relationship the order names left out.
    #[test]
    fn primvars_follow_property_order() -> Result {
        let mesh = mesh()?;
        for name in ["c", "a", "b"] {
            mesh.primvar_builder(name, "float[]").set(floats(&[1.0])).build()?;
        }
        mesh.primvar("a")?.set_indices(vec![0], None)?;
        let id = mesh.create_primvar("s", "string")?;
        id.set_id_target(mesh.path())?;
        assert_eq!(names(&mesh.authored_primvars()?), ["c", "a", "b", "s"]);

        let order = [
            "primvars:displayOpacity",
            "primvars:b",
            "primvars:a:indices",
            "primvars:c",
            "primvars:s:idFrom",
            "primvars:a",
            "primvars:s",
            "primvars:displayColor",
        ];
        let order = order.into_iter().map(tf::Token::from).collect();
        mesh.prim()
            .clone()
            .set_metadata("propertyOrder", sdf::Value::TokenVec(order))?;

        assert_eq!(
            names(&mesh.primvars()?),
            ["displayOpacity", "b", "c", "a", "s", "displayColor"]
        );
        assert_eq!(names(&mesh.authored_primvars()?), ["b", "c", "a", "s"]);
        Ok(())
    }

    /// A schema's own primvars are listed with the authored ones, and are not
    /// authored.
    #[test]
    fn primvars_include_builtins() -> Result {
        let mesh = mesh()?;
        mesh.create_primvar("st", "float[]")?;

        let mut listed = names(&mesh.primvars()?)
            .into_iter()
            .map(str::to_owned)
            .collect::<Vec<_>>();
        listed.sort();
        assert_eq!(listed, ["displayColor", "displayOpacity", "st"]);
        assert_eq!(names(&mesh.authored_primvars()?), ["st"]);
        Ok(())
    }

    /// The id relationship sits in the namespace without being a primvar.
    #[test]
    fn id_rel_not_primvar() -> Result {
        let mesh = mesh()?;
        let id = mesh.create_primvar("id", "string")?;
        id.set_id_target(mesh.path())?;
        assert_eq!(names(&mesh.authored_primvars()?), ["id"]);
        assert_eq!(mesh.primvars()?.len(), 3);
        Ok(())
    }

    /// A schema's fallback is a value, though not an authored one.
    #[cfg(feature = "skel")]
    #[test]
    fn with_values_counts_fallback() -> Result {
        let mesh = mesh()?;
        crate::skel::BindingAPI::apply(mesh.prim())?;
        assert_eq!(names(&mesh.primvars_with_values()?), ["skel:skinningMethod"]);
        assert!(mesh.primvars_with_authored_values()?.is_empty());
        Ok(())
    }

    /// A primvar only declared and one blocked hold no value.
    #[test]
    fn authored_values_skip_blocked() -> Result {
        let mesh = mesh()?;
        mesh.primvar_builder("a", "float[]").set(floats(&[1.0])).build()?;
        mesh.create_primvar("declared", "float[]")?;
        mesh.primvar_builder("blocked", "float[]").set(floats(&[1.0])).build()?;
        assert!(mesh.block_primvar("blocked")?);

        assert_eq!(names(&mesh.authored_primvars()?).len(), 3);
        assert_eq!(names(&mesh.primvars_with_authored_values()?), ["a"]);
        assert_eq!(names(&mesh.primvars_with_values()?), ["a"]);
        Ok(())
    }

    #[test]
    fn remove_takes_indices() -> Result {
        let mesh = mesh()?;
        let primvar = mesh
            .primvar_builder("x", "float[]")
            .set(floats(&[1.0]))
            .indices(vec![0])
            .build()?;

        assert!(mesh.remove_primvar("x")?);
        assert!(!mesh.has_primvar("x")?);
        assert!(!primvar.indices_attr().is_defined()?);
        assert!(!mesh.remove_primvar("x")?);
        Ok(())
    }

    /// A primvar composed across a reference has no spec on the edit target
    /// to remove, so it stays.
    #[test]
    fn remove_across_reference() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            "#usda 1.0\ndef \"Source\"\n{\n    float[] primvars:x = [1]\n    int[] primvars:x:indices = [0]\n}\n\
             def \"Ref\" (\n    references = </Source>\n)\n{\n}\n",
        )?;
        let referencing = api(&stage.prim("/Ref")?);
        assert!(!referencing.remove_primvar("x")?);
        assert!(referencing.has_primvar("x")?);
        assert!(referencing.primvar("x")?.is_indexed()?);
        Ok(())
    }

    #[test]
    fn remove_reserved_errors() -> Result {
        let error = mesh()?.remove_primvar("indices").expect_err("a reserved name");
        assert!(matches!(error, SchemaError::InvalidPrimvarName { .. }));
        Ok(())
    }

    /// Either spelling of the name blocks the primvar.
    #[test]
    fn block_accepts_bare_name() -> Result {
        let mesh = mesh()?;
        for name in ["x", "primvars:y"] {
            let primvar = mesh.primvar_builder(name, "float[]").set(floats(&[1.0])).build()?;
            assert!(mesh.block_primvar(name)?);
            assert!(!primvar.attribute().has_authored_value()?, "{name}");
            assert!(primvar.attribute().resolve_info()?.value_is_blocked(), "{name}");
        }
        Ok(())
    }

    /// Blocking an array primvar blocks its indices with it, creating the
    /// attribute for the block, as one edit, and leaves the metadata.
    #[test]
    fn block_unindexed_blocks_indices() -> Result {
        let mesh = mesh()?;
        let primvar = mesh
            .primvar_builder("x", "float[]")
            .interpolation(Interpolation::Vertex)
            .set(floats(&[1.0]))
            .build()?;
        assert!(!primvar.indices_attr().is_defined()?);

        let commits = commits(mesh.stage());
        assert!(mesh.block_primvar("x")?);
        assert_eq!(commits.get(), 1);
        assert!(primvar.indices_attr().resolve_info()?.value_is_blocked());
        assert!(primvar.has_authored_interpolation()?);
        Ok(())
    }

    /// A scalar primvar has no indices to block.
    #[test]
    fn block_scalar_value_only() -> Result {
        let mesh = mesh()?;
        let primvar = mesh.primvar_builder("s", "float").set(1.0_f32).build()?;
        assert!(mesh.block_primvar("s")?);
        assert!(primvar.attribute().resolve_info()?.value_is_blocked());
        assert!(!primvar.indices_attr().is_defined()?);
        Ok(())
    }

    #[test]
    fn block_undefined_noop() -> Result {
        let mesh = mesh()?;
        let commits = commits(mesh.stage());
        assert!(!mesh.block_primvar("nope")?);
        assert_eq!(commits.get(), 0);
        assert!(!mesh.has_primvar("nope")?);
        Ok(())
    }

    /// The prims `/s0`, `/s0/s1`, … `/s0/s1/s2/s3/s4`: four transforms and a
    /// mesh beneath them, each seen as its primvars.
    fn chain() -> Result<Vec<PrimvarsAPI>> {
        let stage = stage()?;
        let mut path = String::new();
        let mut prims = Vec::new();
        for level in 0..5 {
            path.push_str(&format!("/s{level}"));
            let prim = match level {
                4 => Mesh::define(&stage, path.as_str())?.prim().clone(),
                _ => Xform::define(&stage, path.as_str())?.prim().clone(),
            };
            prims.push(api(&prim));
        }
        Ok(prims)
    }

    /// The `float` primvar `name` on `prim`, holding a value, constant where
    /// `interpolation` is `None`.
    fn valued(prim: &PrimvarsAPI, name: &str, interpolation: Option<Interpolation>) -> Result<Primvar> {
        let builder = prim.primvar_builder(name, "float").set(1.0_f32);
        match interpolation {
            Some(interpolation) => builder.interpolation(interpolation).build(),
            None => builder.build(),
        }
    }

    /// A constant primvar with a value reaches the prims beneath its own, and
    /// its own prim hands it down.
    #[test]
    fn inherits_constant() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;

        assert!(s[0].find_inheritable_primvars()?.is_empty());
        for prim in &s[1..] {
            assert_eq!(
                paths(&prim.find_inheritable_primvars()?),
                ["/s0/s1.primvars:u1"],
                "{}",
                prim.path()
            );
        }
        Ok(())
    }

    /// The nearest prim that authors the primvar is the one handed down.
    #[test]
    fn nearest_replaces() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        valued(&s[3], "u1", None)?;

        assert_eq!(paths(&s[2].find_inheritable_primvars()?), ["/s0/s1.primvars:u1"]);
        assert_eq!(paths(&s[4].find_inheritable_primvars()?), ["/s0/s1/s2/s3.primvars:u1"]);
        Ok(())
    }

    /// The set lists the root-most prim's primvars first, and each prim's in
    /// its property order.
    #[test]
    fn inherited_order_root_down() -> Result {
        let s = chain()?;
        valued(&s[3], "d", None)?;
        valued(&s[2], "c", None)?;
        valued(&s[2], "a", None)?;
        valued(&s[1], "b", None)?;

        assert_eq!(
            paths(&s[4].find_inheritable_primvars()?),
            [
                "/s0/s1.primvars:b",
                "/s0/s1/s2.primvars:c",
                "/s0/s1/s2.primvars:a",
                "/s0/s1/s2/s3.primvars:d",
            ]
        );
        Ok(())
    }

    /// A primvar that replaces an inherited one takes its place in the set.
    #[test]
    fn replace_keeps_position() -> Result {
        let s = chain()?;
        for name in ["a", "b", "c"] {
            valued(&s[1], name, None)?;
        }
        valued(&s[2], "b", None)?;

        assert_eq!(
            paths(&s[2].find_inheritable_primvars()?),
            ["/s0/s1.primvars:a", "/s0/s1/s2.primvars:b", "/s0/s1.primvars:c"]
        );
        Ok(())
    }

    /// A primvar that stops an inherited one leaves the rest in their order,
    /// from the full walk and from the incremental step alike.
    #[test]
    fn removal_keeps_order() -> Result {
        let s = chain()?;
        for name in ["a", "b", "c", "d"] {
            valued(&s[1], name, None)?;
        }
        valued(&s[2], "b", Some(Interpolation::Varying))?;
        let expected = ["/s0/s1.primvars:a", "/s0/s1.primvars:c", "/s0/s1.primvars:d"];

        assert_eq!(paths(&s[2].find_inheritable_primvars()?), expected);
        let handed_down = s[1].find_inheritable_primvars()?;
        let stepped = s[2]
            .find_incrementally_inheritable_primvars(&handed_down)?
            .expect("the prim stops `b`");
        assert_eq!(paths(&stepped), expected);
        Ok(())
    }

    /// Only a constant primvar is handed down.
    #[test]
    fn nonconstant_not_inherited() -> Result {
        let s = chain()?;
        for interpolation in [
            Interpolation::Uniform,
            Interpolation::Varying,
            Interpolation::Vertex,
            Interpolation::FaceVarying,
        ] {
            valued(&s[1], "u1", Some(interpolation))?;
            assert!(s[2].find_inheritable_primvars()?.is_empty(), "{interpolation:?}");
        }
        Ok(())
    }

    /// A primvar of another interpolation with a value stops the inherited
    /// one of its name, and is not handed down in its place.
    #[test]
    fn nonconstant_removes_inherited() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        valued(&s[1], "u2", None)?;
        valued(&s[3], "u1", Some(Interpolation::Vertex))?;

        assert_eq!(paths(&s[4].find_inheritable_primvars()?), ["/s0/s1.primvars:u2"]);
        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, None);
        assert!(!s[4].has_possibly_inherited_primvar("u1")?);
        Ok(())
    }

    /// A primvar with no authored value takes no part, whatever its
    /// interpolation.
    #[test]
    fn valueless_ignored() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        s[3].create_primvar("u1", "float")?
            .set_interpolation(Interpolation::Vertex)?;

        assert_eq!(paths(&s[4].find_inheritable_primvars()?), ["/s0/s1.primvars:u1"]);
        assert!(s[4].has_possibly_inherited_primvar("u1")?);
        Ok(())
    }

    /// A block is no value, so blocking the primvar that stopped the
    /// inheritance lets it through again.
    #[test]
    fn blocked_restores_inheritance() -> Result {
        let s = chain()?;
        let inherited = valued(&s[1], "u1", None)?;
        valued(&s[3], "u1", Some(Interpolation::Varying))?;
        assert!(s[4].find_inheritable_primvars()?.is_empty());

        assert!(s[3].block_primvar("u1")?);
        assert_eq!(paths(&s[4].find_inheritable_primvars()?), ["/s0/s1.primvars:u1"]);
        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, Some(inherited));
        Ok(())
    }

    /// An interpolation that names none is not `constant`, so it stops the
    /// inheritance as any other does, without an error.
    #[test]
    fn unknown_interp_blocks() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        valued(&s[3], "u1", None)?
            .into_attribute()
            .set_metadata(tokens::INTERPOLATION, sdf::Value::Token(tf::Token::from("frobosity")))?;

        assert!(s[4].find_inheritable_primvars()?.is_empty());
        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, None);
        Ok(())
    }

    /// A schema's fallback is no authored value, so it is not handed down.
    #[cfg(feature = "skel")]
    #[test]
    fn fallback_not_inherited() -> Result {
        let s = chain()?;
        crate::skel::BindingAPI::apply(s[1].prim())?;
        assert!(s[1].primvar("skel:skinningMethod")?.attribute().has_value()?);
        assert!(s[2].find_inheritable_primvars()?.is_empty());
        assert!(!s[2].has_possibly_inherited_primvar("skel:skinningMethod")?);
        Ok(())
    }

    /// A prim that authors no value for a primvar changes nothing.
    #[test]
    fn incremental_none_unchanged() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        s[2].create_primvar("declared", "float")?;
        let handed_down = s[1].find_inheritable_primvars()?;

        assert_eq!(s[2].find_incrementally_inheritable_primvars(&handed_down)?, None);
        assert_eq!(s[2].find_incrementally_inheritable_primvars(&[])?, None);
        Ok(())
    }

    /// A prim that stops the last inherited primvar hands down an empty set,
    /// which is not the parent's.
    #[test]
    fn incremental_empties_set() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        valued(&s[2], "u1", Some(Interpolation::Varying))?;
        let handed_down = s[1].find_inheritable_primvars()?;

        assert_eq!(
            s[2].find_incrementally_inheritable_primvars(&handed_down)?,
            Some(Vec::new())
        );
        Ok(())
    }

    /// Carrying the set down a traversal gives each prim what the full walk
    /// gives it.
    #[test]
    fn incremental_matches_full() -> Result {
        let s = chain()?;
        valued(&s[0], "a", None)?;
        valued(&s[1], "b", None)?;
        valued(&s[2], "a", Some(Interpolation::Vertex))?;
        valued(&s[3], "c", None)?;
        valued(&s[3], "b", None)?;

        let mut carried = Vec::new();
        for prim in &s {
            if let Some(changed) = prim.find_incrementally_inheritable_primvars(&carried)? {
                carried = changed;
            }
            assert_eq!(carried, prim.find_inheritable_primvars()?, "{}", prim.path());
        }
        assert_eq!(paths(&carried), ["/s0/s1/s2/s3.primvars:b", "/s0/s1/s2/s3.primvars:c"]);
        Ok(())
    }

    /// The prim's own primvar answers where it holds a value, whatever its
    /// interpolation.
    #[test]
    fn find_local_wins() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        let local = valued(&s[4], "u1", Some(Interpolation::Vertex))?;
        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, Some(local));
        assert!(s[4].has_possibly_inherited_primvar("u1")?);
        Ok(())
    }

    /// An inherited primvar is the ancestor's own: it reads from where the
    /// value is authored.
    #[test]
    fn find_binds_ancestor() -> Result {
        let s = chain()?;
        let inherited = valued(&s[1], "u1", None)?;
        let found = s[4].find_primvar_with_inheritance("primvars:u1")?.expect("inherited");
        assert_eq!(found, inherited);
        assert_eq!(found.attribute().path().as_str(), "/s0/s1.primvars:u1");
        assert_eq!(found.get_at::<f32>(None)?, Some(1.0));
        Ok(())
    }

    /// The nearest ancestor with a value decides: one that is not constant is
    /// not inherited, and hides a constant one above it.
    #[test]
    fn find_nonconstant_blocks() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        valued(&s[2], "u1", Some(Interpolation::Varying))?;

        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, None);
        assert!(!s[4].has_possibly_inherited_primvar("u1")?);
        assert!(s[2].has_possibly_inherited_primvar("u1")?);
        Ok(())
    }

    /// With nothing inherited, the prim's own primvar comes back where the
    /// prim defines it, valueless as it is.
    #[test]
    fn find_returns_defined_local() -> Result {
        let s = chain()?;
        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, None);

        let declared = s[4].create_primvar("u1", "float")?;
        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, Some(declared.clone()));

        valued(&s[2], "u1", Some(Interpolation::Varying))?;
        assert_eq!(s[4].find_primvar_with_inheritance("u1")?, Some(declared));
        Ok(())
    }

    /// The query that walks the ancestors and the one handed the parent's set
    /// answer alike.
    #[test]
    fn find_forms_agree() -> Result {
        let s = chain()?;
        valued(&s[1], "inherited", None)?;
        valued(&s[1], "stopped", None)?;
        valued(&s[2], "stopped", Some(Interpolation::Varying))?;
        valued(&s[1], "overridden", None)?;
        valued(&s[4], "overridden", Some(Interpolation::Vertex))?;
        valued(&s[2], "hidden", Some(Interpolation::Varying))?;
        s[4].create_primvar("stopped", "float")?;
        s[4].create_primvar("declared", "float")?;

        let handed_down = s[3].find_inheritable_primvars()?;
        for name in ["inherited", "stopped", "overridden", "hidden", "declared", "absent"] {
            assert_eq!(
                s[4].find_primvar_with_inheritance_from(name, &handed_down)?,
                s[4].find_primvar_with_inheritance(name)?,
                "{name}"
            );
        }
        Ok(())
    }

    /// The prim asked about takes every one of its primvars that holds a
    /// value, and the constant ones it inherits.
    #[test]
    fn leaf_accepts_all() -> Result {
        let s = chain()?;
        valued(&s[1], "u1", None)?;
        valued(&s[1], "u2", None)?;
        valued(&s[4], "u2", Some(Interpolation::Vertex))?;
        valued(&s[4], "u3", Some(Interpolation::FaceVarying))?;
        s[4].create_primvar("declared", "float")?;
        let expected = [
            "/s0/s1.primvars:u1",
            "/s0/s1/s2/s3/s4.primvars:u2",
            "/s0/s1/s2/s3/s4.primvars:u3",
        ];

        assert_eq!(paths(&s[4].find_primvars_with_inheritance()?), expected);
        let handed_down = s[3].find_inheritable_primvars()?;
        assert_eq!(
            paths(&s[4].find_primvars_with_inheritance_from(&handed_down)?),
            expected
        );
        // A prim with nothing of its own takes what reaches it.
        assert_eq!(s[3].find_primvars_with_inheritance_from(&handed_down)?, handed_down);
        Ok(())
    }

    #[test]
    fn possibly_inherited_blocked() -> Result {
        let s = chain()?;
        let inherited = valued(&s[1], "u1", None)?;
        assert!(s[4].has_possibly_inherited_primvar("u1")?);
        assert!(!s[0].has_possibly_inherited_primvar("u1")?);

        inherited.set_interpolation(Interpolation::Varying)?;
        assert!(!s[4].has_possibly_inherited_primvar("u1")?);
        assert!(s[1].has_possibly_inherited_primvar("u1")?);
        Ok(())
    }

    /// A schema's own primvar inherits like any other: the mesh's
    /// `displayColor`, left unauthored, is the ancestor's.
    #[test]
    fn builtin_inherits() -> Result {
        let s = chain()?;
        let color = s[1]
            .primvar_builder("displayColor", "color3f[]")
            .set(sdf::Value::Vec3fVec(vec![[1.0, 0.0, 0.0].into()]))
            .build()?;

        assert!(s[4].has_primvar("displayColor")?);
        assert_eq!(s[4].find_primvar_with_inheritance("displayColor")?, Some(color));
        Ok(())
    }

    /// An instance proxy inherits from the instance and from the prims above
    /// it, as the prim it stands for would in their place.
    #[test]
    fn inherits_through_instance() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            "#usda 1.0\ndef Xform \"Source\"\n{\n    float primvars:p = 2\n    def Mesh \"geo\"\n    {\n    }\n}\n\
             def Xform \"World\"\n{\n    float primvars:u = 1\n    def Xform \"inst\" (\n        instanceable = true\n        references = </Source>\n    )\n    {\n    }\n}\n",
        )?;
        let proxy = stage.prim("/World/inst/geo")?;
        assert!(proxy.is_instance_proxy()?);
        let proxy = api(&proxy);

        assert_eq!(
            paths(&proxy.find_inheritable_primvars()?),
            ["/World.primvars:u", "/World/inst.primvars:p"]
        );
        let inherited = proxy.find_primvar_with_inheritance("p")?.expect("the instance's");
        assert_eq!(inherited.get_at::<f32>(None)?, Some(2.0));
        Ok(())
    }
}
