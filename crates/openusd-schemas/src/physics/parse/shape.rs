//! Colliders (C++ `_GetCollisionType`, the shape parsers and
//! `_FinalizeCollisionDesc`).

use openusd::gf;
use openusd::sdf::Path;
use openusd::tf;
use openusd::usd::{self, SchemaBase};

use super::{ParseDiagnostic, Parser, filtered_pairs, read, token_or};
use crate::SchemaError;
use crate::geom::{
    self, Axis, Capsule, Capsule_1, Capsule_1Schema, CapsuleSchema, Cone, ConeSchema, Cube, CubeSchema, Cylinder,
    Cylinder_1, Cylinder_1Schema, CylinderSchema, ElementType, GprimSchema, Mesh, Plane, PlaneSchema, PointBasedSchema,
    Points, PointsSchema, Sphere, SphereSchema, Subset,
};
use crate::physics::tokens::NONE;
use crate::physics::{CollisionAPI, MaterialAPI, MeshCollisionAPI, desc};
use crate::shade::MaterialBindingAPI;

/// The shape a collider prim's type maps to (the shape values of C++
/// `UsdPhysicsObjectType`); a custom shape carries the token that matched.
#[derive(Debug, Clone, PartialEq, Eq)]
enum ShapeType {
    Sphere,
    Cube,
    Capsule,
    Capsule1,
    Cylinder,
    Cylinder1,
    Cone,
    Plane,
    Mesh,
    SpherePoints,
    Custom(tf::Token),
}

impl Parser<'_> {
    /// The colliders among `prims`, in order, leaving out and recording the
    /// prims of no supported shape and the `Points` colliders without usable
    /// widths (the entry point's collision passes).
    pub(super) fn shapes(
        &mut self,
        prims: &[usd::Prim],
        custom: &[tf::Token],
    ) -> Result<Vec<desc::Shape>, SchemaError> {
        let mut shapes = Vec::with_capacity(prims.len());
        for prim in prims {
            match collision_type(prim, custom)? {
                Some(kind) => shapes.extend(self.shape(prim, kind)?),
                None => self
                    .diagnostics
                    .push(ParseDiagnostic::UnknownShape(prim.path().clone())),
            }
        }
        Ok(shapes)
    }

    /// `prim`'s collider as a `kind` shape, `None` for a `Points` collider
    /// without usable widths, which is recorded instead.
    fn shape(&mut self, prim: &usd::Prim, kind: ShapeType) -> Result<Option<desc::Shape>, SchemaError> {
        let mut materials = Vec::new();
        let geometry = match kind {
            ShapeType::Sphere => {
                let shape = Sphere::from_prim_unchecked(prim.clone());
                let radius: f64 = read(&shape.radius_attr())?;
                desc::Geometry::Sphere {
                    radius: (largest_scale(self.world_scale(prim)?) * radius as f32).abs(),
                }
            }
            ShapeType::Cube => {
                let shape = Cube::from_prim_unchecked(prim.clone());
                let size: f64 = read(&shape.size_attr())?;
                desc::Geometry::Cube {
                    half_extents: self.world_scale(prim)?.to_f32() * (size.abs() * 0.5) as f32,
                }
            }
            ShapeType::Capsule => {
                let shape = Capsule::from_prim_unchecked(prim.clone());
                let (axis, along, across) = self.axis_scales(prim, &shape.axis_attr())?;
                desc::Geometry::Capsule {
                    radius: radius(read(&shape.radius_attr())?, across),
                    half_height: half_height(read(&shape.height_attr())?, along),
                    axis,
                }
            }
            ShapeType::Capsule1 => {
                let shape = Capsule_1::from_prim_unchecked(prim.clone());
                let (axis, along, across) = self.axis_scales(prim, &shape.axis_attr())?;
                desc::Geometry::Capsule1 {
                    top_radius: radius(read(&shape.radius_top_attr())?, across),
                    bottom_radius: radius(read(&shape.radius_bottom_attr())?, across),
                    half_height: half_height(read(&shape.height_attr())?, along),
                    axis,
                }
            }
            ShapeType::Cylinder => {
                let shape = Cylinder::from_prim_unchecked(prim.clone());
                let (axis, along, across) = self.axis_scales(prim, &shape.axis_attr())?;
                desc::Geometry::Cylinder {
                    radius: radius(read(&shape.radius_attr())?, across),
                    half_height: half_height(read(&shape.height_attr())?, along),
                    axis,
                }
            }
            ShapeType::Cylinder1 => {
                let shape = Cylinder_1::from_prim_unchecked(prim.clone());
                let (axis, along, across) = self.axis_scales(prim, &shape.axis_attr())?;
                desc::Geometry::Cylinder1 {
                    top_radius: radius(read(&shape.radius_top_attr())?, across),
                    bottom_radius: radius(read(&shape.radius_bottom_attr())?, across),
                    half_height: half_height(read(&shape.height_attr())?, along),
                    axis,
                }
            }
            ShapeType::Cone => {
                let shape = Cone::from_prim_unchecked(prim.clone());
                let (axis, along, across) = self.axis_scales(prim, &shape.axis_attr())?;
                desc::Geometry::Cone {
                    radius: radius(read(&shape.radius_attr())?, across),
                    half_height: half_height(read(&shape.height_attr())?, along),
                    axis,
                }
            }
            ShapeType::Plane => {
                let shape = Plane::from_prim_unchecked(prim.clone());
                desc::Geometry::Plane {
                    axis: token_or(&shape.axis_attr(), Axis::from_token, Axis::X)?,
                }
            }
            ShapeType::Mesh => {
                let shape = Mesh::from_prim_unchecked(prim.clone());
                let approximation = match MeshCollisionAPI::from_prim(prim.clone())? {
                    Some(api) => read(&api.approximation_attr())?,
                    None => tf::Token::from(NONE),
                };
                // The physics materials of the face subsets, of any family.
                for subset in Subset::in_family(&shape, Some(ElementType::Face), None)? {
                    materials.extend(bound_material(subset.prim())?);
                }
                desc::Geometry::Mesh {
                    approximation,
                    scale: self.world_scale(prim)?.to_f32(),
                    double_sided: read(&shape.double_sided_attr())?,
                }
            }
            ShapeType::SpherePoints => {
                let shape = Points::from_prim_unchecked(prim.clone());
                let widths: Vec<f32> = shape.widths()?.unwrap_or_default();
                if widths.is_empty() {
                    self.diagnostics
                        .push(ParseDiagnostic::PointsWithoutWidths(prim.path().clone()));
                    return Ok(None);
                }
                let points: Vec<gf::Vec3f> = shape.points()?.unwrap_or_default();
                if points.len() != widths.len() {
                    self.diagnostics.push(ParseDiagnostic::PointsWidthCount {
                        path: prim.path().clone(),
                        points: points.len(),
                        widths: widths.len(),
                    });
                    return Ok(None);
                }
                let scale = largest_scale(self.world_scale(prim)?);
                desc::Geometry::SpherePoints(
                    points
                        .into_iter()
                        .zip(widths)
                        .map(|(center, width)| desc::SpherePoint {
                            center,
                            radius: scale * width * 0.5,
                        })
                        .collect(),
                )
            }
            ShapeType::Custom(token) => desc::Geometry::Custom(token),
        };

        // C++ `_FinalizeCollisionDesc`: the prim's own physics material after
        // any subset materials, its filtered pairs, flag and owners.
        materials.extend(bound_material(prim)?);
        let collision = CollisionAPI::from_prim_unchecked(prim.clone());
        Ok(Some(desc::Shape {
            path: prim.path().clone(),
            rigid_body: None,
            local_pos: gf::Vec3f::default(),
            local_rot: gf::Quatf::IDENTITY,
            local_scale: gf::vec3f(1.0, 1.0, 1.0),
            materials,
            simulation_owners: collision.simulation_owner_rel().targets()?,
            filtered_collisions: filtered_pairs(prim)?,
            collision_groups: Vec::new(),
            collision_enabled: read(&collision.collision_enabled_attr())?,
            geometry,
        }))
    }

    /// The axis `attribute` names on `prim` with the prim's world scale along
    /// it and the larger scale across it, what a capsule, cylinder or cone is
    /// sized by (C++ `_GetAxisRadiusHalfHeight`).
    fn axis_scales(&mut self, prim: &usd::Prim, attribute: &usd::Attribute) -> Result<(Axis, f32, f32), SchemaError> {
        let axis = token_or(attribute, Axis::from_token, Axis::X)?;
        let scale = self.world_scale(prim)?.to_f32();
        let (along, across) = match axis {
            Axis::X => (scale.x, scale.y.abs().max(scale.z.abs())),
            Axis::Y => (scale.y, scale.x.abs().max(scale.z.abs())),
            Axis::Z => (scale.z, scale.x.abs().max(scale.y.abs())),
        };
        Ok((axis, along, across))
    }
}

/// The shape `prim` is (C++ `_GetCollisionType`): a custom shape where one of
/// `custom` is among its authored API schemas or is its type name, with that
/// token; else by its gprim type; `None` for anything else.
fn collision_type(prim: &usd::Prim, custom: &[tf::Token]) -> Result<Option<ShapeType>, SchemaError> {
    if !custom.is_empty() {
        // The authored list (C++ `UsdPrimTypeInfo::GetAppliedAPISchemas`),
        // which keeps a name no registered schema answers to.
        let applied = prim.authored_api_schemas()?;
        let type_name = prim.type_name()?;
        if let Some(token) = custom
            .iter()
            .find(|token| applied.contains(token) || type_name.as_ref() == Some(token))
        {
            return Ok(Some(ShapeType::Custom(token.clone())));
        }
    }
    if !prim.is_a(geom::tokens::GPRIM)? {
        return Ok(None);
    }
    let by_type = [
        (geom::tokens::MESH, ShapeType::Mesh),
        (geom::tokens::CUBE, ShapeType::Cube),
        (geom::tokens::SPHERE, ShapeType::Sphere),
        (geom::tokens::CAPSULE, ShapeType::Capsule),
        (geom::tokens::CAPSULE_1, ShapeType::Capsule1),
        (geom::tokens::CYLINDER, ShapeType::Cylinder),
        (geom::tokens::CYLINDER_1, ShapeType::Cylinder1),
        (geom::tokens::CONE, ShapeType::Cone),
        (geom::tokens::PLANE, ShapeType::Plane),
        (geom::tokens::POINTS_, ShapeType::SpherePoints),
    ];
    for (type_name, kind) in by_type {
        if prim.is_a(type_name)? {
            return Ok(Some(kind));
        }
    }
    Ok(None)
}

/// A radius scaled by the larger world scale across the shape's axis, as a
/// magnitude.
fn radius(radius: f64, across: f32) -> f32 {
    (radius as f32 * across).abs()
}

/// Half a `height` scaled by the world scale along the shape's axis, as a
/// magnitude.
fn half_height(height: f64, along: f32) -> f32 {
    (height as f32 * 0.5 * along).abs()
}

/// The largest magnitude among `scale`'s components, what a sphere's radius
/// scales by.
fn largest_scale(scale: gf::Vec3d) -> f32 {
    let scale = scale.to_f32();
    scale.x.abs().max(scale.y.abs()).max(scale.z.abs())
}

/// The physics material bound to `prim` where it carries
/// `MaterialBindingAPI` (C++ `_GetMaterialBinding`, whose binding view is
/// valid only on such a prim, followed by `HasAPI<UsdPhysicsMaterialAPI>`).
///
/// TODO(perf): each call resolves the binding from scratch. A
/// `shade::BindingCache` held by the parser and handed to `resolve_binding`
/// would share the ancestors' bindings and collection queries across a parse,
/// as C++ shares its `BindingsCache` and `CollectionQueryCache`;
/// `MaterialAPI::bound` would need to take one.
fn bound_material(prim: &usd::Prim) -> Result<Option<Path>, SchemaError> {
    let Some(binding) = MaterialBindingAPI::from_prim(prim.clone())? else {
        return Ok(None);
    };
    Ok(MaterialAPI::bound(&binding)?.map(|material| material.path().clone()))
}
