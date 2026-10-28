//! A rigid body's mass properties, computed from its colliders (C++
//! `UsdPhysicsRigidBodyAPI::ComputeMassProperties`).
//!
//! The schema knows nothing of geometry. The caller describes each
//! collider's shape through a [`MassInformation`] callback. What a `MassAPI`
//! authors overrides what the shapes give: the body's `MassAPI` over each
//! collider's, and a collider's over its shape. The density a shape is
//! weighed at is the collider's, then the body's, then that of the material
//! bound to the collider for the `physics` purpose, then 1000 kg/m³ in the
//! stage's units.

use openusd::gf;
use openusd::usd::{self, PrimPredicate, SchemaBase};

use super::tokens::{PHYSICS_COLLISION_API, PHYSICS_RIGID_BODY_API};
use super::{MassAPI, MassProperties, MaterialAPI, RigidBodyAPI, mass_units};
use crate::SchemaError;
use crate::geom::{self, XformCache};
use crate::shade::MaterialBindingAPI;

/// How far from zero an authored vector must be to count as authored (C++
/// `COMPARE_TOLERANCE`).
const COMPARE_TOLERANCE: f64 = 1e-5;

/// What a collider's shape weighs, as the caller of
/// [`RigidBodyAPI::mass_properties`] describes it (C++
/// `UsdPhysicsRigidBodyAPI::MassInformation`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MassInformation {
    /// The shape's volume, in scene units cubed; negative for a shape the
    /// caller does not describe, as [`UNSUPPORTED`](Self::UNSUPPORTED) is.
    pub volume: f64,
    /// The inertia tensor about `center_of_mass` at unit density: the
    /// shape's mass distribution before a density or a mass scales it.
    pub inertia: gf::Mat3d,
    /// The center of mass, in the shape's frame.
    pub center_of_mass: gf::Vec3d,
    /// Where the shape sits in the body's frame.
    pub local_pos: gf::Vec3d,
    /// How the shape is turned in the body's frame.
    pub local_rot: gf::Quatd,
}

impl MassInformation {
    /// The answer for a prim whose shape the caller does not describe: a
    /// negative volume, which [`RigidBodyAPI::mass_properties`] counts as a
    /// unit mass with a unit inertia tensor, as C++ does beside a warning.
    pub const UNSUPPORTED: Self = Self {
        volume: -1.0,
        inertia: gf::Mat3d::IDENTITY,
        center_of_mass: gf::Vec3d { x: 0.0, y: 0.0, z: 0.0 },
        local_pos: gf::Vec3d { x: 0.0, y: 0.0, z: 0.0 },
        local_rot: gf::Quatd::IDENTITY,
    };
}

/// A rigid body's mass properties, as [`RigidBodyAPI::mass_properties`]
/// computes them: the mass C++ `ComputeMassProperties` returns and the three
/// values it fills in.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct BodyMass {
    /// The mass, in the stage's mass units; negative where neither the
    /// body's `MassAPI` nor a collider gives one.
    pub mass: f64,
    /// The principal moments of inertia, about `center_of_mass` along
    /// `principal_axes`.
    pub diagonal_inertia: gf::Vec3d,
    /// The center of mass, in the body's frame.
    pub center_of_mass: gf::Vec3d,
    /// The rotation from the body's frame to its principal axes.
    pub principal_axes: gf::Quatd,
}

impl RigidBodyAPI {
    /// The body's mass, principal inertia and center of mass (C++
    /// `UsdPhysicsRigidBodyAPI::ComputeMassProperties`).
    ///
    /// The body's own `MassAPI` answers first: a positive mass, a non-zero
    /// diagonal inertia and a finite center of mass, the center scaled by
    /// the body's world scale since a simulation carries no scale. With all
    /// three in hand the colliders are not consulted. Whatever it leaves
    /// open comes from them: the prims at and beneath the body that carry
    /// `CollisionAPI`, instance proxies included, leaving out everything
    /// beneath a descendant with a `RigidBodyAPI` of its own. `mass_info`
    /// describes each collider's shape, and its error is this method's. The
    /// colliders' properties are summed in the body's frame; an authored
    /// body mass rescales the summed inertia to it, an authored center moves
    /// the sum there, and non-zero authored principal axes stand whatever
    /// the sum says.
    ///
    /// A body with no collider keeps an authored mass and, lacking an
    /// authored inertia, takes that of a sphere 0.1 m in radius, where C++
    /// warns; with no mass either its mass is negative, where C++ warns too.
    /// Principal axes nothing determines are the identity.
    ///
    /// The arithmetic is `f64` throughout, where C++ computes in `f32`.
    pub fn mass_properties(
        &self,
        mut mass_info: impl FnMut(&usd::Prim) -> Result<MassInformation, SchemaError>,
    ) -> Result<BodyMass, SchemaError> {
        let body = self.prim();
        let mut xform_cache = XformCache::new(None);
        let authored = MassApiData::parse(body, &mut xform_cache)?;
        let mut result = BodyMass {
            mass: authored.mass.unwrap_or(-1.0),
            diagonal_inertia: authored.diagonal_inertia.unwrap_or(gf::vec3d(1.0, 1.0, 1.0)),
            center_of_mass: authored.center_of_mass.unwrap_or_default(),
            principal_axes: authored.principal_axes.unwrap_or(gf::Quatd::IDENTITY),
        };
        if authored.mass.is_some() && authored.diagonal_inertia.is_some() && authored.center_of_mass.is_some() {
            return Ok(result);
        }

        let parts = colliders(body)?
            .iter()
            .map(|collider| collider_mass(collider, authored.density, &mut xform_cache, &mut mass_info))
            .collect::<Result<Vec<_>, _>>()?;
        if parts.is_empty() {
            // An authored mass with nothing to sum takes the inertia of a
            // small sphere, 0.1 m in radius, standing in for a point (C++
            // warns).
            if authored.diagonal_inertia.is_none() && result.mass > 0.0 {
                let radius = 0.1 / geom::stage_meters_per_unit(self.stage())?;
                let moment = 0.4 * result.mass * radius * radius;
                result.diagonal_inertia = gf::vec3d(moment, moment, moment);
            }
            return Ok(result);
        }

        let mut summed = MassProperties::sum(&parts);
        match authored.mass {
            Some(mass) => {
                summed.inertia = summed.inertia * (mass / summed.mass);
                summed.mass = mass;
            }
            None => result.mass = summed.mass,
        }
        match authored.center_of_mass {
            Some(com) => summed.translate(com - summed.center_of_mass),
            None => result.center_of_mass = summed.center_of_mass,
        }
        let (moments, axes) = MassProperties::mass_space_inertia(summed.inertia);
        if authored.diagonal_inertia.is_none() {
            result.diagonal_inertia = moments;
        }
        if authored.principal_axes.is_none() {
            result.principal_axes = axes;
        }
        Ok(result)
    }
}

/// What a prim's `MassAPI` authors (C++ `_MassApiData`, with the center of
/// mass C++ `_GetCoM` reads beside it); nothing, for a prim without one.
#[derive(Debug, Clone, Copy, Default)]
struct MassApiData {
    /// The mass, where positive.
    mass: Option<f64>,
    /// The density, where positive.
    density: Option<f64>,
    /// The diagonal inertia, unless it is the zero sentinel.
    diagonal_inertia: Option<gf::Vec3d>,
    /// The principal axes, unless they are the zero sentinel.
    principal_axes: Option<gf::Quatd>,
    /// The center of mass, scaled by the prim's world scale since a
    /// simulation carries no scale, unless it is the sentinel: the fallback
    /// is `(-inf, -inf, -inf)`, and any non-finite component is that.
    center_of_mass: Option<gf::Vec3d>,
}

impl MassApiData {
    /// Read `prim`'s `MassAPI` (C++ `_ParseMassApi` and `_GetCoM`).
    fn parse(prim: &usd::Prim, xform_cache: &mut XformCache) -> Result<Self, SchemaError> {
        let Some(mass_api) = MassAPI::from_prim(prim.clone())? else {
            return Ok(Self::default());
        };
        let positive = |value: Option<f32>| value.map(f64::from).filter(|value| *value > 0.0);
        let inertia: Option<gf::Vec3f> = mass_api.diagonal_inertia_attr().get()?;
        let axes: Option<gf::Quatf> = mass_api.principal_axes_attr().get()?;
        let center: Option<gf::Vec3f> = mass_api.center_of_mass_attr().get()?;
        let mut center_of_mass = center
            .map(gf::Vec3d::from)
            .filter(|center| center.x.is_finite() && center.y.is_finite() && center.z.is_finite());
        if let Some(center) = &mut center_of_mass {
            let scale = xform_cache
                .local_to_world_transform(prim)?
                .factor(gf::Mat4d::FACTOR_EPSILON)
                .scale;
            *center = center.comp_mult(scale);
        }
        Ok(Self {
            mass: positive(mass_api.mass_attr().get()?),
            density: positive(mass_api.density_attr().get()?),
            diagonal_inertia: inertia
                .map(gf::Vec3d::from)
                .filter(|inertia| !inertia.is_close(gf::Vec3d::default(), COMPARE_TOLERANCE)),
            principal_axes: axes.map(gf::Quatd::from).filter(|axes| {
                !axes.imaginary().is_close(gf::Vec3d::default(), COMPARE_TOLERANCE) || axes.w.abs() > COMPARE_TOLERANCE
            }),
            center_of_mass,
        })
    }
}

/// The colliders whose mass is `body`'s: the prims at and beneath it that
/// carry `CollisionAPI`, instance proxies included, leaving out everything
/// beneath a descendant with a `RigidBodyAPI` of its own.
fn colliders(body: &usd::Prim) -> Result<Vec<usd::Prim>, SchemaError> {
    let mut colliders = Vec::new();
    let mut walk = body.filtered_subtree(PrimPredicate::DEFAULT_PROXIES)?;
    while let Some(prim) = walk.next() {
        let prim = prim?;
        let schemas = prim.api_schemas()?;
        let carries = |name: &str| schemas.iter().any(|schema| schema.as_str() == name);
        if &prim != body && carries(PHYSICS_RIGID_BODY_API) {
            walk.prune_children();
        } else if carries(PHYSICS_COLLISION_API) {
            colliders.push(prim);
        }
    }
    Ok(colliders)
}

/// The density `collider` is weighed at: its own `MassAPI`'s, then the
/// body's `body_density`, then that of the `MaterialAPI` on the material
/// bound to it for the `physics` purpose; `None` for the default (C++
/// `_GetCollisionShapeMassAPIData`).
fn density(collider: &usd::Prim, shape: &MassApiData, body_density: Option<f64>) -> Result<Option<f64>, SchemaError> {
    if let Some(density) = shape.density.or(body_density) {
        return Ok(Some(density));
    }
    // TODO(perf): C++ resolves every collider's binding in one
    // `UsdShadeMaterialBindingAPI::ComputeBoundMaterials` call, sharing the
    // collection membership queries across them, and a material bound to
    // several colliders could be read once; each collider resolves and reads
    // its own here.
    let binding = MaterialBindingAPI::from_prim_unchecked(collider.clone());
    let Some(material) = MaterialAPI::bound(&binding)? else {
        return Ok(None);
    };
    Ok(material
        .density_attr()
        .get::<f32>()?
        .map(f64::from)
        .filter(|density| *density > 0.0))
}

/// The default density, 1000 kg/m³ in the stage's units.
fn default_density(stage: &usd::Stage) -> Result<f64, SchemaError> {
    let meters = geom::stage_meters_per_unit(stage)?;
    let kilograms = mass_units::stage_kilograms_per_unit(stage)?;
    Ok(1000.0 * meters * meters * meters / kilograms)
}

/// `collider`'s mass properties in its own frame, with its pose in the
/// body's frame (C++ `_ParseCollisionShapeForMass`).
///
/// `mass_info` describes the shape, which the collider's density, the
/// body's `body_density`, the bound material's or the default weighs. The
/// collider's `MassAPI` overrides that: a mass scales the shape's inertia
/// to it, a diagonal inertia and principal axes replace the shape's tensor,
/// and a center of mass moves the tensor there.
fn collider_mass(
    collider: &usd::Prim,
    body_density: Option<f64>,
    xform_cache: &mut XformCache,
    mass_info: &mut impl FnMut(&usd::Prim) -> Result<MassInformation, SchemaError>,
) -> Result<(MassProperties, gf::Mat4d), SchemaError> {
    let shape = MassApiData::parse(collider, xform_cache)?;
    let info = mass_info(collider)?;
    let mut pose = gf::Mat4d::from_quat(info.local_rot);
    pose.set_translation(info.local_pos);
    if info.volume < 0.0 {
        // A shape the caller does not describe (C++ warns).
        return Ok((MassProperties::default(), pose));
    }
    let (mass, mut inertia) = if let Some(mass) = shape.mass {
        (mass, info.inertia * (mass / info.volume))
    } else {
        let density = match density(collider, &shape, body_density)? {
            Some(density) => density,
            None => default_density(collider.stage())?,
        };
        (info.volume * density, info.inertia * density)
    };
    if let Some(diagonal) = shape.diagonal_inertia {
        inertia = gf::Mat3d::diagonal(diagonal);
    }
    if let Some(axes) = shape.principal_axes {
        inertia = MassProperties::rotate_inertia(inertia, axes);
    }
    let mut center_of_mass = info.center_of_mass;
    if let Some(authored) = shape.center_of_mass {
        if shape.diagonal_inertia.is_none() {
            inertia = MassProperties::translate_inertia(inertia, mass, authored - center_of_mass);
        }
        center_of_mass = authored;
    }
    Ok((
        MassProperties {
            mass,
            inertia,
            center_of_mass,
        },
        pose,
    ))
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf, vt};

    use super::{BodyMass, MassInformation};
    use crate::SchemaError;
    use crate::geom::{self, Cube, CubeSchema, StageMetadata as _, UpAxis, Xform, XformCache, XformableExt};
    use crate::physics::{CollisionAPI, MATERIAL_PURPOSE, MassAPI, MaterialAPI, RigidBodyAPI, StageMetadata as _};
    use crate::shade::{Material, MaterialBindingAPI};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// The tolerance the C++ tests compare at.
    const TOLERANCE: f64 = 0.01;
    /// The principal moments of a unit cube at the default density.
    const UNIT_CUBE: f64 = 166.667;
    const ORIGIN: Option<gf::Vec3d> = Some(gf::Vec3d { x: 0.0, y: 0.0, z: 0.0 });

    /// A stage with `Z` up and the given units (C++ `setup_scene`).
    fn scene(meters_per_unit: f64, kilograms_per_unit: f64) -> Result<usd::Stage> {
        let stage = crate::tests::stage("anon.usda")?;
        geom::set_stage_up_axis(&stage, UpAxis::Z)?;
        stage.set_meters_per_unit(meters_per_unit)?;
        stage.set_kilograms_per_unit(kilograms_per_unit)?;
        Ok(stage)
    }

    /// A `Cube` of `size` carrying `CollisionAPI` at `path`.
    fn collider_cube(stage: &usd::Stage, path: &str, size: f64) -> Result<Cube> {
        let cube = Cube::define(stage, path)?;
        cube.create_size_attr()?.set(size)?;
        CollisionAPI::apply(cube.prim())?;
        Ok(cube)
    }

    /// A rigid body `Xform` at `/xform` over a unit cube collider at
    /// `/xform/cube`: the body and the cube's prim.
    fn body_over_cube(stage: &usd::Stage) -> Result<(RigidBodyAPI, usd::Prim)> {
        let body = RigidBodyAPI::apply(Xform::define(stage, "/xform")?.prim())?;
        let cube = collider_cube(stage, "/xform/cube", 1.0)?;
        Ok((body, cube.prim().clone()))
    }

    /// The mass information of a `Cube` collider, posed in `body`'s frame,
    /// and the unsupported answer for any other prim (C++
    /// `mass_information_fn`). The shape's inertia is that of the cube's
    /// extents, its world scale included, as the C++ callback computes it.
    fn cube_mass(body: &usd::Prim) -> Result<impl FnMut(&usd::Prim) -> Result<MassInformation>> {
        let body = body.clone();
        let body_world = XformCache::new(None).local_to_world_transform(&body)?;
        let body_scale = body_world.factor(gf::Mat4d::FACTOR_EPSILON).scale;
        Ok(move |prim: &usd::Prim| -> Result<MassInformation> {
            let Some(cube) = Cube::from_prim(prim.clone())? else {
                return Ok(MassInformation::UNSUPPORTED);
            };
            let world = XformCache::new(None).local_to_world_transform(prim)?;
            let size = cube.size_attr().get::<f64>()?.unwrap_or_default().abs();
            let extents = world.factor(gf::Mat4d::FACTOR_EPSILON).scale * size;
            let (x, y, z) = (extents.x, extents.y, extents.z);
            let (local_pos, local_rot) = if prim == &body {
                (gf::Vec3d::default(), gf::Quatd::IDENTITY)
            } else {
                let local = (world * body_world.inverse_or_max()).factor(gf::Mat4d::FACTOR_EPSILON);
                (
                    local.translation.comp_mult(body_scale),
                    local.rotation.extract_rotation_quat(),
                )
            };
            Ok(MassInformation {
                volume: x * y * z,
                inertia: gf::Mat3d::diagonal([(y * y + z * z) / 12.0, (x * x + z * z) / 12.0, (x * x + y * y) / 12.0]),
                center_of_mass: gf::Vec3d::default(),
                local_pos,
                local_rot,
            })
        })
    }

    /// `body`'s mass properties with its cubes described.
    fn mass_of(body: &RigidBodyAPI) -> Result<BodyMass> {
        body.mass_properties(cube_mass(body.prim())?)
    }

    /// Asserts `got`'s mass, and each of the inertia and center given (C++
    /// `compare_mass_information`).
    fn assert_mass(got: &BodyMass, mass: f64, inertia: Option<gf::Vec3d>, center_of_mass: Option<gf::Vec3d>) {
        assert!((got.mass - mass).abs() < TOLERANCE, "mass {} != {mass}", got.mass);
        if let Some(inertia) = inertia {
            assert!(
                got.diagonal_inertia.is_close(inertia, TOLERANCE),
                "inertia {:?} != {inertia:?}",
                got.diagonal_inertia
            );
        }
        if let Some(center) = center_of_mass {
            assert!(
                got.center_of_mass.is_close(center, TOLERANCE),
                "center {:?} != {center:?}",
                got.center_of_mass
            );
        }
    }

    fn uniform(value: f64) -> Option<gf::Vec3d> {
        Some(gf::vec3d(value, value, value))
    }

    /// A `Material` at `/basePhysicsMaterial` with `MaterialAPI` and
    /// `density`, bound to `prim` for the `physics` purpose.
    fn bind_material(stage: &usd::Stage, prim: &usd::Prim, density: f32) -> Result {
        let material = Material::define(stage, "/basePhysicsMaterial")?;
        MaterialAPI::apply(material.prim())?
            .create_density_attr()?
            .set(density)?;
        MaterialBindingAPI::apply(prim)?.bind_for_purpose(MATERIAL_PURPOSE, material.path().clone(), None)?;
        Ok(())
    }

    /// A cube that is its own rigid body weighs its volume at the default
    /// density, 1000 kg/m³ (C++ `test_mass_rigid_body_cube`).
    #[test]
    fn cube_body() -> Result {
        let stage = scene(1.0, 1.0)?;
        let body = RigidBodyAPI::apply(collider_cube(&stage, "/cube", 1.0)?.prim())?;
        assert_mass(&mass_of(&body)?, 1000.0, uniform(UNIT_CUBE), ORIGIN);
        Ok(())
    }

    /// A density on the body weighs its colliders (C++
    /// `test_mass_rigid_body_cube_rigid_body_density`).
    #[test]
    fn body_density() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, _) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?.create_density_attr()?.set(500.0_f32)?;
        assert_mass(&mass_of(&body)?, 500.0, uniform(UNIT_CUBE * 0.5), ORIGIN);
        Ok(())
    }

    /// A density on the collider weighs it (C++
    /// `test_mass_rigid_body_cube_collider_density`).
    #[test]
    fn collider_density() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(&cube)?.create_density_attr()?.set(500.0_f32)?;
        assert_mass(&mass_of(&body)?, 500.0, uniform(UNIT_CUBE * 0.5), ORIGIN);
        Ok(())
    }

    /// The material bound for the `physics` purpose weighs a collider
    /// without a density (C++ `test_mass_rigid_body_cube_material_density`).
    #[test]
    fn material_density() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        bind_material(&stage, &cube, 500.0)?;
        assert_mass(&mass_of(&body)?, 500.0, uniform(UNIT_CUBE * 0.5), ORIGIN);
        Ok(())
    }

    /// The collider's density outranks the body's and the material's (C++
    /// `test_mass_rigid_body_cube_density_precedence`).
    #[test]
    fn density_precedence() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?.create_density_attr()?.set(5000.0_f32)?;
        MassAPI::apply(&cube)?.create_density_attr()?.set(500.0_f32)?;
        bind_material(&stage, &cube, 2000.0)?;
        assert_mass(&mass_of(&body)?, 500.0, uniform(UNIT_CUBE * 0.5), ORIGIN);
        Ok(())
    }

    /// A mass on the body scales the summed inertia to it (C++
    /// `test_mass_rigid_body_cube_rigid_body_mass`).
    #[test]
    fn body_mass() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, _) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?.create_mass_attr()?.set(2000.0_f32)?;
        assert_mass(&mass_of(&body)?, 2000.0, uniform(UNIT_CUBE * 2.0), ORIGIN);
        Ok(())
    }

    /// A mass on the collider scales its inertia to it (C++
    /// `test_mass_rigid_body_cube_collider_mass`).
    #[test]
    fn collider_mass() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(&cube)?.create_mass_attr()?.set(2000.0_f32)?;
        assert_mass(&mass_of(&body)?, 2000.0, uniform(UNIT_CUBE * 2.0), ORIGIN);
        Ok(())
    }

    /// The body's mass outranks the collider's (C++
    /// `test_mass_rigid_body_cube_mass_precedence`).
    #[test]
    fn mass_precedence() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?.create_mass_attr()?.set(2000.0_f32)?;
        MassAPI::apply(&cube)?.create_mass_attr()?.set(500.0_f32)?;
        assert_mass(&mass_of(&body)?, 2000.0, uniform(UNIT_CUBE * 2.0), ORIGIN);
        Ok(())
    }

    /// A center of mass on the body is the body's (C++
    /// `test_mass_rigid_body_cube_rigid_body_com`).
    #[test]
    fn body_com() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, _) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?
            .create_center_of_mass_attr()?
            .set(gf::vec3f(2.0, 2.0, 2.0))?;
        assert_mass(&mass_of(&body)?, 1000.0, None, uniform(2.0));
        Ok(())
    }

    /// A center of mass on the collider moves the summed one (C++
    /// `test_mass_rigid_body_cube_collider_com`).
    #[test]
    fn collider_com() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(&cube)?
            .create_center_of_mass_attr()?
            .set(gf::vec3f(2.0, 2.0, 2.0))?;
        assert_mass(&mass_of(&body)?, 1000.0, None, uniform(2.0));
        Ok(())
    }

    /// The body's center of mass outranks the collider's (C++
    /// `test_mass_rigid_body_cube_com_precedence`).
    #[test]
    fn com_precedence() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?
            .create_center_of_mass_attr()?
            .set(gf::vec3f(2.0, 2.0, 2.0))?;
        MassAPI::apply(&cube)?
            .create_center_of_mass_attr()?
            .set(gf::vec3f(1.0, 1.0, 1.0))?;
        assert_mass(&mass_of(&body)?, 1000.0, None, uniform(2.0));
        Ok(())
    }

    /// A diagonal inertia on the body is the body's (C++
    /// `test_mass_rigid_body_cube_rigid_body_inertia`).
    #[test]
    fn body_inertia() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, _) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?
            .create_diagonal_inertia_attr()?
            .set(gf::vec3f(2.0, 2.0, 2.0))?;
        assert_mass(&mass_of(&body)?, 1000.0, uniform(2.0), None);
        Ok(())
    }

    /// A diagonal inertia on the collider replaces its shape's (C++
    /// `test_mass_rigid_body_cube_collider_inertia`).
    #[test]
    fn collider_inertia() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(&cube)?
            .create_diagonal_inertia_attr()?
            .set(gf::vec3f(2.0, 2.0, 2.0))?;
        assert_mass(&mass_of(&body)?, 1000.0, uniform(2.0), None);
        Ok(())
    }

    /// The body's inertia outranks the collider's (C++
    /// `test_mass_rigid_body_cube_inertia_precedence`).
    #[test]
    fn inertia_precedence() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, cube) = body_over_cube(&stage)?;
        MassAPI::apply(body.prim())?
            .create_diagonal_inertia_attr()?
            .set(gf::vec3f(2.0, 2.0, 2.0))?;
        MassAPI::apply(&cube)?
            .create_diagonal_inertia_attr()?
            .set(gf::vec3f(1.0, 1.0, 1.0))?;
        assert_mass(&mass_of(&body)?, 1000.0, uniform(2.0), None);
        Ok(())
    }

    /// Two scaled, turned colliders sum to the same principal inertia after
    /// one turns a quarter about an axis its extents are symmetric in (C++
    /// `test_mass_rigid_body_cube_rigid_body_compound`).
    #[test]
    fn compound_rotated() -> Result {
        let stage = scene(1.0, 1.0)?;
        let body = RigidBodyAPI::apply(Xform::define(&stage, "/xform")?.prim())?;
        let scale = gf::vec3f(3.0, 2.0, 3.0);
        let cube0 = collider_cube(&stage, "/xform/cube0", 1.0)?
            .set_translate(gf::vec3d(100.0, 20.0, 10.0))?
            .set_rotate_xyz(gf::vec3f(0.0, 0.0, 45.0))?
            .set_scale(scale)?;
        collider_cube(&stage, "/xform/cube1", 1.0)?
            .set_translate(gf::vec3d(-100.0, 20.0, 10.0))?
            .set_rotate_xyz(gf::vec3f(0.0, 0.0, 45.0))?
            .set_scale(scale)?;

        let before = mass_of(&body)?;
        cube0.set_rotate_xyz(gf::vec3f(0.0, 90.0, 45.0))?;
        let after = mass_of(&body)?;
        assert!(
            after.diagonal_inertia.is_close(before.diagonal_inertia, 1.0),
            "{:?} != {:?}",
            after.diagonal_inertia,
            before.diagonal_inertia
        );
        Ok(())
    }

    /// Principal axes on the body are the body's (C++
    /// `test_mass_rigid_body_cube_rigid_body_principal_axes`).
    #[test]
    fn body_principal_axes() -> Result {
        let stage = scene(1.0, 1.0)?;
        let (body, _) = body_over_cube(&stage)?;
        let axes = gf::quatf(0.707, 0.0, 0.707, 0.0);
        MassAPI::apply(body.prim())?.create_principal_axes_attr()?.set(axes)?;
        let got = mass_of(&body)?;
        assert_mass(&got, 1000.0, None, None);
        let axes = gf::Quatd::from(axes);
        assert!(got.principal_axes.imaginary().is_close(axes.imaginary(), TOLERANCE));
        assert!((got.principal_axes.w - axes.w).abs() < TOLERANCE);
        Ok(())
    }

    /// The default density follows the stage's `metersPerUnit` (C++
    /// `test_mass_rigid_body_cube_cm_units`).
    #[test]
    fn centimeter_units() -> Result {
        let stage = scene(0.01, 1.0)?;
        let body = RigidBodyAPI::apply(collider_cube(&stage, "/cube", 1.0)?.prim())?;
        let scale = 0.01 * 0.01 * 0.01;
        assert_mass(&mass_of(&body)?, 1000.0 * scale, uniform(UNIT_CUBE * scale), ORIGIN);
        Ok(())
    }

    /// The default density follows the stage's `kilogramsPerUnit` (C++
    /// `test_mass_rigid_body_cube_decagram_units`).
    #[test]
    fn decagram_units() -> Result {
        let stage = scene(1.0, 0.1)?;
        let body = RigidBodyAPI::apply(collider_cube(&stage, "/cube", 1.0)?.prim())?;
        let scale = 1.0 / 0.1;
        assert_mass(&mass_of(&body)?, 1000.0 * scale, uniform(UNIT_CUBE * scale), ORIGIN);
        Ok(())
    }

    /// Two colliders either side of the body sum to twice the mass about
    /// the body's origin (C++ `test_mass_rigid_body_cube_compound`).
    #[test]
    fn compound_translated() -> Result {
        let stage = scene(1.0, 1.0)?;
        let body = RigidBodyAPI::apply(Xform::define(&stage, "/xform")?.prim())?;
        collider_cube(&stage, "/xform/cube0", 1.0)?.set_translate(gf::vec3d(0.0, 0.0, -2.0))?;
        collider_cube(&stage, "/xform/cube1", 1.0)?.set_translate(gf::vec3d(0.0, 0.0, 2.0))?;
        assert_mass(&mass_of(&body)?, 2000.0, None, ORIGIN);
        Ok(())
    }

    /// A body beneath a body keeps its colliders to itself (C++
    /// `test_mass_rigid_body_nested`).
    #[test]
    fn nested_bodies() -> Result {
        let stage = scene(1.0, 1.0)?;
        let outer = RigidBodyAPI::apply(Xform::define(&stage, "/rbo0")?.prim())?;
        collider_cube(&stage, "/rbo0/cube", 1.0)?;
        let inner = RigidBodyAPI::apply(Xform::define(&stage, "/rbo0/rbo1")?.prim())?;
        collider_cube(&stage, "/rbo0/rbo1/cube", 2.0)?;

        assert_mass(&mass_of(&outer)?, 1000.0, uniform(UNIT_CUBE), ORIGIN);
        assert_mass(&mass_of(&inner)?, 8000.0, None, ORIGIN);
        Ok(())
    }

    /// A collider reached through an instance is the body's (C++
    /// `test_mass_rigid_body_instance_proxy_collider`).
    #[test]
    fn instance_proxy_collider() -> Result {
        let stage = scene(1.0, 1.0)?;
        collider_cube(&stage, "/Prototype_Collisions/cube", 1.0)?;

        let body = RigidBodyAPI::apply(Xform::define(&stage, "/World/Body")?.prim())?;
        MassAPI::apply(body.prim())?.create_density_attr()?.set(1000.0_f32)?;
        stage
            .define_prim("/World/Body/collisions")?
            .set_metadata(
                sdf::FieldKey::References.as_str(),
                vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    prim_path: sdf::path("/Prototype_Collisions")?,
                    ..Default::default()
                }])),
            )?
            .set_instanceable(true)?;
        assert!(stage.prim("/World/Body/collisions/cube")?.is_instance_proxy()?);

        assert_mass(&mass_of(&body)?, 1000.0, uniform(UNIT_CUBE), ORIGIN);
        Ok(())
    }
}
