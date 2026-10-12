//! What `UsdGeomBoundable` answers beyond its own properties: the extent a
//! prim authors, and the one its type computes from the attributes that size
//! it.

use std::collections::HashMap;

use openusd::{gf, tf, usd};

use super::{
    Axis, BoundableSchema, Capsule, Capsule_1, Capsule_1Schema, CapsuleSchema, Cone, ConeSchema, Cube, CubeSchema,
    Curves, CurvesSchema, Cylinder, Cylinder_1, Cylinder_1Schema, CylinderSchema, Extent, Plane, PlaneSchema,
    PointBased, PointBasedSchema, Points, PointsSchema, Sphere, SphereSchema, tokens,
};
use crate::SchemaError;

/// The extent of a boundable prim, authored or computed.
///
/// Every [`BoundableSchema`] answers it, so a view of any boundable type has
/// it wherever the generated accessors are. The types that compute an extent
/// are the ones [`extent_registry`](crate::extent_registry) holds; an
/// [`ExtentRegistry`] of the caller's own answers the same questions with
/// other types added.
///
/// # Example
///
/// ```
/// use openusd::gf;
/// use openusd::usd;
/// use openusd_schemas::geom::{self, BoundableExt, BoundableSchema, SphereSchema};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let sphere = geom::Sphere::define(&stage, "/Sphere")?;
/// sphere.create_radius_attr()?.set(2.0)?;
///
/// // Nothing authors `extent`, so the radius gives it.
/// let corner = gf::vec3f(2.0, 2.0, 2.0);
/// assert_eq!(sphere.compute_extent(None)?, Some([-corner, corner]));
///
/// // An authored extent is taken as it is.
/// let authored = vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 1.0, 1.0)];
/// sphere.create_extent_attr()?.set(authored.clone())?;
/// assert_eq!(sphere.compute_extent(None)?, Some([authored[0], authored[1]]));
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
pub trait BoundableExt: BoundableSchema {
    /// The prim's extent at `time`, where `None` is the default time: the
    /// authored `extent` where a layer authors one, else its
    /// [`shape_extent`](Self::shape_extent) (C++
    /// `UsdGeomBoundable::ComputeExtent`).
    ///
    /// An authored extent that is blocked, or that does not hold two
    /// corners, is passed over for the computed one. `None` is a prim with
    /// neither.
    fn compute_extent(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<Option<Extent>, SchemaError> {
        crate::extent_registry().compute_extent(self, time)
    }

    /// The extent the prim's type computes at `time`, where `None` is the
    /// default time, from the attributes that size it, under `transform`
    /// where one is given (C++ `UsdGeomBoundable::ComputeExtentFromPlugins`).
    /// An authored `extent` plays no part.
    ///
    /// `None` is a prim whose type computes no extent, or one of whose
    /// sizing attributes reads no value. A `Points` prim whose `widths` read
    /// no value is bounded by its points alone.
    ///
    /// Sizing attributes that cannot size the shape are an error where C++
    /// answers `false`: an `axis` that names no axis, and `widths` that are
    /// not one for each point ([`SchemaError::WidthCountMismatch`]).
    fn shape_extent(
        &self,
        time: impl Into<Option<usd::TimeCode>>,
        transform: impl Into<Option<gf::Mat4d>>,
    ) -> Result<Option<Extent>, SchemaError> {
        crate::extent_registry().shape_extent(self.prim(), time, transform)
    }
}

impl<T: BoundableSchema> BoundableExt for T {}

/// Computes the extent of a prim of one schema type at a time, where `None`
/// is the default time, under a transform where one is given (C++
/// `UsdGeomComputeExtentFunction`). `None` is a prim one of whose sizing
/// attributes reads no value.
pub type ExtentFn = fn(&usd::Prim, Option<usd::TimeCode>, Option<gf::Mat4d>) -> Result<Option<Extent>, SchemaError>;

/// The function that computes the extent of each schema type that has one,
/// by the identifier of the schema (the registry behind C++
/// `UsdGeomRegisterComputeExtentFunction`).
///
/// [`extent_registry`](crate::extent_registry) holds the functions of this
/// crate's schemas. A clone of it takes the functions of schemas declared
/// elsewhere, and answers for them where it is asked directly.
///
/// # Example
///
/// ```
/// use openusd::{gf, usd};
/// use openusd_schemas::geom::{self, SphereSchema};
///
/// // Bound every sphere by the cube two units wide, whatever its radius.
/// let mut extents = openusd_schemas::extent_registry().clone();
/// extents.register("Sphere", |_prim, _time, transform| Ok(Some(geom::Cube::extent_from(2.0, transform))));
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let sphere = geom::Sphere::define(&stage, "/Sphere")?;
/// sphere.create_radius_attr()?.set(5.0)?;
/// let corner = gf::vec3f(1.0, 1.0, 1.0);
/// assert_eq!(extents.shape_extent(&sphere, None, None)?, Some([-corner, corner]));
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
#[derive(Debug, Clone, Default)]
pub struct ExtentRegistry {
    fns: HashMap<tf::Token, ExtentFn>,
}

impl ExtentRegistry {
    /// A registry with no functions.
    pub fn new() -> Self {
        Self::default()
    }

    /// Compute the extent of prims of the type `schema` with `compute`,
    /// which replaces a function already registered for that type. Prims of
    /// a type deriving from `schema` take it too, unless a type earlier
    /// among their ancestors has a function of its own.
    ///
    /// C++ refuses a second function for one type, and a type that does
    /// not derive from `Boundable`. Type information belongs to a stage's
    /// schema registry, so the second is checked where a function is looked
    /// up, in [`extent_fn`](Self::extent_fn).
    pub fn register(&mut self, schema: impl Into<tf::Token>, compute: ExtentFn) -> &mut Self {
        self.fns.insert(schema.into(), compute);
        self
    }

    /// The function for `prim`: the one registered for its schema type, or
    /// else for the first of the types it derives from that has one, in the
    /// order of [`usd::SchemaRegistry::ancestors`]. A `Mesh` is bounded as
    /// the `PointBased` it is.
    ///
    /// Only a type deriving from `Boundable` answers, as in C++: a function
    /// registered for any other type is passed over.
    // TODO(perf): the answer depends on the schema type and the stage's
    // schema registry alone, so a cache over one stage, as `BBoxCache` is,
    // could keep it for each type the way C++ `_FunctionRegistry` does,
    // types with no function included.
    pub fn extent_fn(&self, prim: &usd::Prim) -> openusd::Result<Option<ExtentFn>> {
        let info = prim.prim_type_info()?;
        let schema = info.schema_type_name();
        let registry = prim.stage().schema_registry();
        let boundable = tf::Token::new(tokens::BOUNDABLE);
        let registered = |schema: &tf::Token| {
            let compute = self.fns.get(schema).copied();
            compute.filter(|_| registry.is_a(schema, &boundable))
        };
        // The type's own function is found without ordering its ancestors.
        Ok(registered(schema).or_else(|| registry.ancestors(schema).into_iter().skip(1).find_map(registered)))
    }

    /// The extent `prim`'s type computes at `time`, where `None` is the
    /// default time, under `transform` where one is given: what
    /// [`BoundableExt::shape_extent`] answers, with this registry's
    /// functions.
    pub fn shape_extent(
        &self,
        prim: &usd::Prim,
        time: impl Into<Option<usd::TimeCode>>,
        transform: impl Into<Option<gf::Mat4d>>,
    ) -> Result<Option<Extent>, SchemaError> {
        match self.extent_fn(prim)? {
            Some(compute) => compute(prim, time.into(), transform.into()),
            None => Ok(None),
        }
    }

    /// `boundable`'s extent at `time`, where `None` is the default time,
    /// authored or computed: what [`BoundableExt::compute_extent`] answers,
    /// with this registry's functions.
    pub fn compute_extent(
        &self,
        boundable: &(impl BoundableSchema + ?Sized),
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<Option<Extent>, SchemaError> {
        let time = time.into();
        let authored: Option<Vec<gf::Vec3f>> = crate::authored_at(&boundable.extent_attr(), time)?;
        match authored.map(Extent::try_from) {
            Some(Ok(extent)) => Ok(Some(extent)),
            _ => self.shape_extent(boundable.prim(), time, None),
        }
    }
}

/// Add the extent function of each `UsdGeom` type that has one.
// TODO: `PointInstancer` has none. Its extent unions the bounds of its
// prototypes under each instance transform (C++ `ComputeExtentAtTime`),
// which needs `BBoxCache`.
pub(crate) fn register_extents(registry: &mut ExtentRegistry) {
    registry
        .register(tokens::SPHERE, sphere)
        .register(tokens::CUBE, cube)
        .register(tokens::CONE, cone)
        .register(tokens::CYLINDER, cylinder)
        .register(tokens::CYLINDER_1, cylinder_1)
        .register(tokens::CAPSULE, capsule)
        .register(tokens::CAPSULE_1, capsule_1)
        .register(tokens::PLANE, plane)
        .register(tokens::POINT_BASED, point_based)
        .register(tokens::POINTS_, points)
        .register(tokens::CURVES, curves);
}

/// A `Sphere` from its `radius`.
fn sphere(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let radius = Sphere::from_prim_unchecked(prim.clone()).radius_at(time)?;
    Ok(radius.map(|radius| Sphere::extent_from(radius, transform)))
}

/// A `Cube` from its `size`.
fn cube(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let size = Cube::from_prim_unchecked(prim.clone()).size_at(time)?;
    Ok(size.map(|size| Cube::extent_from(size, transform)))
}

/// A `Cone` from its `height`, `radius` and `axis`.
fn cone(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let cone = Cone::from_prim_unchecked(prim.clone());
    let sizes = (cone.height_at(time)?)
        .zip(cone.radius_at(time)?)
        .zip(cone.axis_attr().get::<Axis>()?);
    Ok(sizes.map(|((height, radius), axis)| Cone::extent_from(height, radius, axis, transform)))
}

/// A `Cylinder` from its `height`, `radius` and `axis`.
fn cylinder(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let cylinder = Cylinder::from_prim_unchecked(prim.clone());
    let sizes = (cylinder.height_at(time)?)
        .zip(cylinder.radius_at(time)?)
        .zip(cylinder.axis_attr().get::<Axis>()?);
    Ok(sizes.map(|((height, radius), axis)| Cylinder::extent_from(height, radius, axis, transform)))
}

/// A `Cylinder_1` from its `height`, `radiusTop`, `radiusBottom` and
/// `axis`.
fn cylinder_1(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let cylinder = Cylinder_1::from_prim_unchecked(prim.clone());
    let sizes = (cylinder.height_at(time)?)
        .zip(cylinder.radius_top_at(time)?)
        .zip(cylinder.radius_bottom_at(time)?)
        .zip(cylinder.axis_attr().get::<Axis>()?);
    Ok(sizes.map(|(((height, top), bottom), axis)| Cylinder_1::extent_from(height, top, bottom, axis, transform)))
}

/// A `Capsule` from its `height`, `radius` and `axis`.
fn capsule(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let capsule = Capsule::from_prim_unchecked(prim.clone());
    let sizes = (capsule.height_at(time)?)
        .zip(capsule.radius_at(time)?)
        .zip(capsule.axis_attr().get::<Axis>()?);
    Ok(sizes.map(|((height, radius), axis)| Capsule::extent_from(height, radius, axis, transform)))
}

/// A `Capsule_1` from its `height`, `radiusTop`, `radiusBottom` and
/// `axis`.
fn capsule_1(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let capsule = Capsule_1::from_prim_unchecked(prim.clone());
    let sizes = (capsule.height_at(time)?)
        .zip(capsule.radius_top_at(time)?)
        .zip(capsule.radius_bottom_at(time)?)
        .zip(capsule.axis_attr().get::<Axis>()?);
    Ok(sizes.map(|(((height, top), bottom), axis)| Capsule_1::extent_from(height, top, bottom, axis, transform)))
}

/// A `Plane` from its `width`, `length` and `axis`. C++ sizes a plane at
/// the default time whatever time it is asked for, where this reads `width`
/// and `length` at `time`.
fn plane(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let plane = Plane::from_prim_unchecked(prim.clone());
    let sizes = (plane.width_at(time)?)
        .zip(plane.length_at(time)?)
        .zip(plane.axis_attr().get::<Axis>()?);
    Ok(sizes.map(|((width, length), axis)| Plane::extent_from(width, length, axis, transform)))
}

/// A `PointBased` prim from its `points`.
fn point_based(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let points = PointBased::from_prim_unchecked(prim.clone()).points_at(time)?;
    Ok(points.map(|points| PointBased::extent_from(&points, transform)))
}

/// `Points` from their `points` and `widths`. Points whose `widths` read no
/// value are bounded by the points alone.
fn points(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let view = Points::from_prim_unchecked(prim.clone());
    let Some(points) = view.points_at(time)? else {
        return Ok(None);
    };
    let extent = match view.widths_at(time)? {
        Some(widths) => Points::extent_from(&points, &widths, transform)?,
        None => PointBased::extent_from(&points, transform),
    };
    Ok(Some(extent))
}

/// `Curves` from their `points` and `widths`, where no widths read grow
/// the extent by nothing.
fn curves(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
) -> Result<Option<Extent>, SchemaError> {
    let view = Curves::from_prim_unchecked(prim.clone());
    let Some(points) = view.points_at(time)? else {
        return Ok(None);
    };
    let widths = view.widths_at(time)?.unwrap_or_default();
    Ok(Some(Curves::extent_from(&points, &widths, transform)))
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase, SchemaDecl, SchemaFamily, SchemaKind, SchemaRegistry};
    use openusd::{gf, tf};

    use super::{BoundableExt, ExtentFn};
    use crate::SchemaError;
    use crate::geom::extent::tests::extent;
    use crate::geom::{
        Axis, BasisCurves, Boundable, BoundableSchema, Capsule_1, Cone, Cube, CurvesSchema, Extent, Mesh, Plane,
        PointBased, PointBasedSchema, PointInstancer, Points, PointsSchema, Sphere, SphereSchema, Xform, tokens,
    };

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    fn triangle() -> Vec<gf::Vec3f> {
        vec![
            gf::vec3f(0.0, 0.0, 0.0),
            gf::vec3f(4.0, 0.0, 0.0),
            gf::vec3f(0.0, 2.0, -1.0),
        ]
    }

    /// An authored extent wins, and one that is blocked or does not hold
    /// two corners gives way to the computed one.
    #[test]
    fn authored_extent() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let sphere = Sphere::define(&stage, "/Sphere")?;
        sphere.create_radius_attr()?.set(2.0)?;
        let computed = Some(extent([-2.0; 3], [2.0; 3]));
        assert_eq!(sphere.compute_extent(None)?, computed);

        let attr = sphere.create_extent_attr()?;
        let attr = attr.set(vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 2.0, 3.0)])?;
        assert_eq!(sphere.compute_extent(None)?, Some(extent([0.0; 3], [1.0, 2.0, 3.0])));
        assert_eq!(sphere.shape_extent(None, None)?, computed);

        let attr = attr.set(vec![gf::vec3f(0.0, 0.0, 0.0)])?;
        assert_eq!(sphere.compute_extent(None)?, computed);
        attr.block()?;
        assert_eq!(sphere.compute_extent(None)?, computed);
        Ok(())
    }

    /// An authored extent is read at the time asked for.
    #[test]
    fn authored_extent_sampled() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let sphere = Sphere::define(&stage, "/Sphere")?;
        sphere.create_extent_attr()?.set_at(
            vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(1.0, 1.0, 1.0)],
            usd::TimeCode::new(1.0),
        )?;
        sphere.create_radius_attr()?.set(3.0)?;
        assert_eq!(
            sphere.compute_extent(usd::TimeCode::new(1.0))?,
            Some(extent([0.0; 3], [1.0; 3]))
        );
        Ok(())
    }

    /// A type with no function of its own takes the one of the type it
    /// derives from.
    #[test]
    fn derived_types() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = Mesh::define(&stage, "/Mesh")?;
        assert_eq!(mesh.shape_extent(None, None)?, None);
        mesh.create_points_attr()?.set(triangle())?;
        assert_eq!(
            mesh.compute_extent(None)?,
            Some(extent([0.0, 0.0, -1.0], [4.0, 2.0, 0.0]))
        );

        let curves = BasisCurves::define(&stage, "/Curves")?;
        curves.create_points_attr()?.set(triangle())?;
        assert_eq!(
            curves.compute_extent(None)?,
            Some(extent([0.0, 0.0, -1.0], [4.0, 2.0, 0.0]))
        );
        curves.create_widths_attr()?.set(vec![2.0f32, 1.0])?;
        assert_eq!(
            curves.compute_extent(None)?,
            Some(extent([-1.0, -1.0, -2.0], [5.0, 3.0, 1.0]))
        );
        Ok(())
    }

    /// Points without widths are bounded by the points, and widths that
    /// are not one for each point are an error.
    #[test]
    fn points_widths() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let points = Points::define(&stage, "/Points")?;
        points.create_points_attr()?.set(triangle())?;
        assert_eq!(
            points.compute_extent(None)?,
            Some(extent([0.0, 0.0, -1.0], [4.0, 2.0, 0.0]))
        );

        let widths = points.create_widths_attr()?;
        let widths = widths.set(vec![2.0f32; 3])?;
        assert_eq!(
            points.compute_extent(None)?,
            Some(extent([-1.0, -1.0, -2.0], [5.0, 3.0, 1.0]))
        );

        widths.set(vec![2.0f32; 2])?;
        assert!(matches!(
            points.compute_extent(None),
            Err(SchemaError::WidthCountMismatch { found: 2, expected: 3 })
        ));
        Ok(())
    }

    /// The shapes sized by an axis read it with their dimensions, each at
    /// the time asked for and under the transform given.
    #[test]
    fn axis_shapes() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let time = usd::TimeCode::new(1.0);

        // The fallbacks size a cone: two high on Z, with a radius of one.
        let cone = Cone::define(&stage, "/Cone")?;
        assert_eq!(cone.compute_extent(None)?, Some(extent([-1.0; 3], [1.0; 3])));
        cone.attribute(tokens::AXIS).set(Axis::X)?;
        cone.attribute(tokens::HEIGHT).set_at(6.0, time)?;
        assert_eq!(
            cone.compute_extent(time)?,
            Some(extent([-3.0, -1.0, -1.0], [3.0, 1.0, 1.0]))
        );

        let capsule = Capsule_1::define(&stage, "/Capsule")?;
        capsule.attribute(tokens::RADIUS_TOP).set(2.0)?;
        let moved = gf::Mat4d::translation([10.0, 0.0, 0.0]);
        assert_eq!(
            capsule.shape_extent(None, moved)?,
            Some(extent([8.0, -2.0, -2.5], [12.0, 2.0, 2.5]))
        );

        let plane = Plane::define(&stage, "/Plane")?;
        plane.attribute(tokens::WIDTH).set_at(4.0, time)?;
        assert_eq!(
            plane.compute_extent(time)?,
            Some(extent([-2.0, -1.0, 0.0], [2.0, 1.0, 0.0]))
        );
        Ok(())
    }

    /// A type with no function, and a prim of no type, compute nothing.
    #[test]
    fn no_function() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let instancer = PointInstancer::define(&stage, "/Instancer")?;
        assert_eq!(instancer.compute_extent(None)?, None);

        let untyped = Sphere::from_prim_unchecked(stage.define_prim("/Untyped")?);
        assert_eq!(untyped.compute_extent(None)?, None);

        // A function registered for a type that is not boundable bounds
        // nothing, the boundable types deriving from it included.
        let mut extents = crate::extent_registry().clone();
        extents.register(tokens::XFORMABLE, boxed::<2> as ExtentFn);
        let xform = Xform::define(&stage, "/Xform")?;
        assert_eq!(extents.shape_extent(&xform, None, None)?, None);
        assert_eq!(extents.shape_extent(&instancer, None, None)?, None);
        Ok(())
    }

    /// The cube `size` wide, for a type to be bounded by whatever it holds.
    fn boxed<const SIZE: u8>(
        _prim: &usd::Prim,
        _time: Option<usd::TimeCode>,
        transform: Option<gf::Mat4d>,
    ) -> Result<Option<Extent>> {
        Ok(Some(Cube::extent_from(SIZE.into(), transform)))
    }

    /// A stage that knows this crate's schemas and the family `decls` make.
    fn stage_with(decls: &[SchemaDecl<'_>]) -> Result<usd::Stage> {
        let family = SchemaFamily::new("mine", decls);
        let registry = crate::ALL
            .iter()
            .fold(SchemaRegistry::builder(), |builder, family| builder.register(family))
            .register(&family)
            .build()
            .expect("the family registers");
        Ok(usd::Stage::builder().schema_registry(registry).in_memory("anon.usda")?)
    }

    fn typed<'a>(name: &'a str, bases: &'a [&'a str]) -> SchemaDecl<'a> {
        SchemaDecl::new(name, SchemaKind::ConcreteTyped).bases(bases)
    }

    /// A type declared outside this crate is bounded as the type it derives
    /// from, until a registry holds a function of its own.
    #[test]
    fn external_type() -> Result {
        let stage = stage_with(&[typed("Widget", &[tokens::MESH])])?;
        let widget = Boundable::from_prim_unchecked(stage.define_typed_prim("/Widget", "Widget")?);
        PointBased::from_prim_unchecked(widget.prim().clone())
            .create_points_attr()?
            .set(triangle())?;
        let points = Some(extent([0.0, 0.0, -1.0], [4.0, 2.0, 0.0]));
        assert_eq!(widget.compute_extent(None)?, points);

        let mut extents = crate::extent_registry().clone();
        extents.register("Widget", boxed::<2> as ExtentFn);
        let cube = Some(extent([-1.0; 3], [1.0; 3]));
        assert_eq!(extents.compute_extent(&widget, None)?, cube);
        assert_eq!(extents.shape_extent(&widget, None, None)?, cube);
        // A mesh is still bounded by its points, and the registry of this
        // crate's schemas is as it was.
        let mesh = Mesh::define(&stage, "/Mesh")?;
        mesh.create_points_attr()?.set(triangle())?;
        assert_eq!(extents.compute_extent(&mesh, None)?, points);
        assert_eq!(widget.compute_extent(None)?, points);

        // An authored extent is taken ahead of any function.
        let authored = vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(9.0, 9.0, 9.0)];
        widget.create_extent_attr()?.set(authored)?;
        assert_eq!(extents.compute_extent(&widget, None)?, Some(extent([0.0; 3], [9.0; 3])));
        assert_eq!(extents.shape_extent(&widget, None, None)?, cube);
        Ok(())
    }

    /// With several bases, a direct base answers ahead of another base's
    /// ancestors, and the first direct base ahead of the second.
    #[test]
    fn base_precedence() -> Result {
        let stage = stage_with(&[
            typed("Deep", &[tokens::BOUNDABLE]),
            typed("Left", &["Deep"]),
            typed("Right", &[tokens::BOUNDABLE]),
            typed("Both", &["Left", "Right"]),
        ])?;
        let both = stage.define_typed_prim("/Both", "Both")?;
        let cube = |size: f32| Some(extent([-size / 2.0; 3], [size / 2.0; 3]));

        let mut extents = crate::extent_registry().clone();
        assert_eq!(extents.shape_extent(&both, None, None)?, None);
        extents.register("Deep", boxed::<2> as ExtentFn);
        assert_eq!(extents.shape_extent(&both, None, None)?, cube(2.0));
        extents.register("Right", boxed::<4> as ExtentFn);
        assert_eq!(extents.shape_extent(&both, None, None)?, cube(4.0));
        extents.register("Left", boxed::<6> as ExtentFn);
        assert_eq!(extents.shape_extent(&both, None, None)?, cube(6.0));
        extents.register(tf::Token::new("Both"), boxed::<8> as ExtentFn);
        assert_eq!(extents.shape_extent(&both, None, None)?, cube(8.0));
        Ok(())
    }
}
