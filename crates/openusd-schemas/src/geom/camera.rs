//! What `UsdGeomCamera` answers beyond its own properties: the camera as a
//! [`gf::Camera`], and the exposure it scales by.

use openusd::usd::{self, SchemaBase};
use openusd::{Result, gf, sdf, tf};

use super::xformable::StackEdit;
use super::{Camera, CameraSchema, ImageableExt, Projection, tokens};
use crate::SchemaError;

impl Camera {
    /// The camera at `time` as a value, placed in the world (C++
    /// `UsdGeomCamera::GetCamera`). A `time` of `None` reads the default
    /// values.
    ///
    /// The transform is the prim's local-to-world transform, and each other
    /// field is read from its attribute. A field keeps the value of
    /// [`gf::Camera::default`] where its attribute reads none: the prim has
    /// no such attribute, the value is blocked, or it is of another type
    /// than the schema declares. A `projection` token that names no
    /// projection reads as perspective.
    ///
    /// C++ answers a camera of defaults whatever goes wrong. Here a failure
    /// of the stage to compose or read a value is an error, as is a
    /// transform that cannot be computed.
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::gf;
    /// use openusd::usd;
    /// use openusd_schemas::geom::{self, CameraSchema};
    ///
    /// let stage = usd::Stage::builder()
    ///     .schema_registry(openusd_schemas::schema_registry())
    ///     .in_memory("scene.usda")?;
    /// let prim = geom::Camera::define(&stage, "/Cam")?;
    /// assert_eq!(prim.camera_at(None)?, gf::Camera::default());
    ///
    /// let mut camera = gf::Camera::default();
    /// camera.transform = gf::Mat4d::translation([0.0, 2.0, 10.0]);
    /// camera.set_perspective(16.0 / 9.0, 60.0, gf::FovDirection::Horizontal, 36.0);
    /// prim.set_from_camera(&camera, None)?;
    ///
    /// assert_eq!(prim.camera_at(None)?, camera);
    /// assert_eq!(prim.focal_length()?, Some(camera.focal_length));
    /// # Ok::<(), openusd_schemas::SchemaError>(())
    /// ```
    pub fn camera_at(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<gf::Camera, SchemaError> {
        let time = time.into();
        let default = gf::Camera::default();
        let projection = self.projection_attr().get_at::<tf::Token>(time)?;
        Ok(gf::Camera {
            transform: self.local_to_world_transform(time)?,
            projection: projection.map_or(default.projection, |token| match Projection::from_token(&token) {
                Some(Projection::Orthographic) => gf::Projection::Orthographic,
                Some(Projection::Perspective) | None => gf::Projection::Perspective,
            }),
            horizontal_aperture: self
                .horizontal_aperture_at(time)?
                .unwrap_or(default.horizontal_aperture),
            vertical_aperture: self.vertical_aperture_at(time)?.unwrap_or(default.vertical_aperture),
            horizontal_aperture_offset: self
                .horizontal_aperture_offset_at(time)?
                .unwrap_or(default.horizontal_aperture_offset),
            vertical_aperture_offset: self
                .vertical_aperture_offset_at(time)?
                .unwrap_or(default.vertical_aperture_offset),
            focal_length: self.focal_length_at(time)?.unwrap_or(default.focal_length),
            clipping_range: self
                .clipping_range_at(time)?
                .map_or(default.clipping_range, |range| gf::Range1f::new(range.x, range.y)),
            clipping_planes: self.clipping_planes_at(time)?.unwrap_or(default.clipping_planes),
            f_stop: self.f_stop_at(time)?.unwrap_or(default.f_stop),
            focus_distance: self.focus_distance_at(time)?.unwrap_or(default.focus_distance),
        })
    }

    /// Author `camera` on the prim at `time` (C++
    /// `UsdGeomCamera::SetFromCamera`). A `time` of `None` authors default
    /// values.
    ///
    /// The transform stack is replaced by one `xformOp:transform` that
    /// places the prim where `camera` is in the world, under whatever its
    /// parent's transform is at `time`, and each other field is authored on
    /// its attribute. The matrix, the order and the ten attributes are one
    /// edit of the stage's edit target: either all of them are authored or
    /// none is.
    ///
    /// Success means what any authoring means: the values are on the edit
    /// target. It does not mean [`camera_at`](Self::camera_at) reads them
    /// back, since a stronger layer's value for the matrix or for any of the
    /// attributes still wins.
    ///
    /// Two things are refused before anything is authored. A parent
    /// transform with no inverse is [`SchemaError::SingularParentTransform`],
    /// where C++ authors a matrix that places the camera nowhere. A stronger
    /// value for `xformOpOrder` is [`SchemaError::XformOpOrderShadowed`], as
    /// for [`make_matrix_xform`](super::XformableExt::make_matrix_xform).
    pub fn set_from_camera(
        &self,
        camera: &gf::Camera,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<(), SchemaError> {
        let time = time.into();
        let prim = self.prim();
        let to_parent =
            self.parent_to_world_transform(time)?
                .inverse()
                .ok_or_else(|| SchemaError::SingularParentTransform {
                    prim: prim.path().clone(),
                })?;
        let stack = StackEdit::matrix(prim, Some(camera.transform * to_parent), time)?;

        let projection = match camera.projection {
            gf::Projection::Perspective => Projection::Perspective,
            gf::Projection::Orthographic => Projection::Orthographic,
        };
        let range = camera.clipping_range;
        let floats = [
            (tokens::HORIZONTAL_APERTURE, camera.horizontal_aperture),
            (tokens::VERTICAL_APERTURE, camera.vertical_aperture),
            (tokens::HORIZONTAL_APERTURE_OFFSET, camera.horizontal_aperture_offset),
            (tokens::VERTICAL_APERTURE_OFFSET, camera.vertical_aperture_offset),
            (tokens::FOCAL_LENGTH, camera.focal_length),
            (tokens::F_STOP, camera.f_stop),
            (tokens::FOCUS_DISTANCE, camera.focus_distance),
        ];
        let floats = floats.map(|(name, value)| (name, sdf::ValueTypeName::FLOAT, sdf::Value::from(value)));
        let others = [
            (tokens::PROJECTION, sdf::ValueTypeName::TOKEN, projection.into()),
            (
                tokens::CLIPPING_RANGE,
                sdf::ValueTypeName::FLOAT2,
                gf::vec2f(range.min(), range.max()).into(),
            ),
            (
                tokens::CLIPPING_PLANES,
                sdf::ValueTypeName::FLOAT4_ARRAY,
                sdf::Value::Vec4fVec(camera.clipping_planes.clone()),
            ),
        ];

        // TODO: the generated `*_attr_builder`s carry these declarations, but
        // a builder taken from the prim commits on its own. Queue them here
        // once a builder can join a `usd::StageEdit` it was not made by.
        //
        // The attributes are queued through the transaction's own view of
        // the prim, which is what makes them part of it.
        prim.stage().edit(|edit| -> Result<(), SchemaError> {
            let prim = edit.prim(prim.path())?;
            stack.apply(&prim)?;
            for (name, type_name, value) in floats.into_iter().chain(others) {
                prim.attribute_builder(name, type_name)
                    .custom(false)
                    .set_at(value, time)
                    .build()?;
            }
            Ok(())
        })
    }

    /// The factor a renderer multiplies its image by to expose it as this
    /// camera does at `time` (C++
    /// `UsdGeomCamera::ComputeLinearExposureScale`). A `time` of `None`
    /// reads the default values.
    ///
    /// It is `time · iso · 2^exposure · responsivity / (100 · fStop²)` over
    /// the `exposure` attributes, so a camera at the schema's fallbacks
    /// scales by one. An attribute that reads no value counts as its
    /// fallback.
    pub fn linear_exposure_scale(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<f32> {
        let time = time.into();
        let exposure_time = self.exposure_time_at(time)?.unwrap_or(1.0);
        let iso = self.exposure_iso_at(time)?.unwrap_or(100.0);
        let f_stop = self.exposure_f_stop_at(time)?.unwrap_or(1.0);
        let responsivity = self.exposure_responsivity_at(time)?.unwrap_or(1.0);
        let exponent = self.exposure_at(time)?.unwrap_or(0.0);
        Ok((exposure_time * iso * 2f32.powf(exponent) * responsivity) / (100.0 * f_stop * f_stop))
    }
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf};

    use crate::SchemaError;
    use crate::geom::xformable::tests::assert_close;
    use crate::geom::{Camera, CameraSchema, Xform, XformableExt, XformableSchema};
    use crate::tests::{commits, from_usda, layer_text, layered, stage, target_layer};

    /// A camera with every field off its default.
    fn busy_camera() -> gf::Camera {
        gf::Camera {
            transform: gf::Mat4d::rotation_y(0.3) * gf::Mat4d::translation([4.0, 5.0, 6.0]),
            projection: gf::Projection::Orthographic,
            horizontal_aperture: 5.1,
            vertical_aperture: 2.0,
            horizontal_aperture_offset: 0.13,
            vertical_aperture_offset: -0.14,
            focal_length: 28.0,
            clipping_range: gf::Range1f::new(5.0, 15.0),
            clipping_planes: vec![gf::vec4f(1.0, 2.0, 3.0, 4.0), gf::vec4f(8.0, 7.0, 6.0, 5.0)],
            f_stop: 1.2,
            focus_distance: 300.0,
        }
    }

    /// A camera nothing is authored on is the default camera, at any time.
    #[test]
    fn fallback_camera() -> Result<(), SchemaError> {
        let stage = stage("anon.usda")?;
        let prim = Camera::define(&stage, "/camera")?;
        assert_eq!(prim.camera_at(None)?, gf::Camera::default());
        assert_eq!(prim.camera_at(usd::TimeCode::new(1.0))?, gf::Camera::default());
        Ok(())
    }

    /// Each attribute is read into its field.
    #[test]
    fn authored_fields_read() -> Result<(), SchemaError> {
        let stage = stage("anon.usda")?;
        let prim = Camera::define(&stage, "/camera")?;
        let matrix = gf::Mat4d::scale([3.0, 3.0, 3.0]);
        prim.make_matrix_xform()?.set(matrix)?;
        prim.projection_attr().set(sdf::Value::token("orthographic"))?;
        prim.horizontal_aperture_attr().set(5.1_f32)?;
        prim.vertical_aperture_attr().set(2.0_f32)?;
        prim.horizontal_aperture_offset_attr().set(-0.11_f32)?;
        prim.vertical_aperture_offset_attr().set(0.12_f32)?;
        prim.focal_length_attr().set(28.0_f32)?;
        prim.clipping_range_attr().set(gf::vec2f(5.0, 15.0))?;
        let planes = vec![gf::vec4f(1.0, 2.0, 3.0, 4.0), gf::vec4f(8.0, 7.0, 6.0, 5.0)];
        prim.clipping_planes_attr().set(sdf::Value::Vec4fVec(planes.clone()))?;
        prim.f_stop_attr().set(1.2_f32)?;
        prim.focus_distance_attr().set(300.0_f32)?;

        let expected = gf::Camera {
            transform: matrix,
            projection: gf::Projection::Orthographic,
            horizontal_aperture: 5.1,
            vertical_aperture: 2.0,
            horizontal_aperture_offset: -0.11,
            vertical_aperture_offset: 0.12,
            focal_length: 28.0,
            clipping_range: gf::Range1f::new(5.0, 15.0),
            clipping_planes: planes,
            f_stop: 1.2,
            focus_distance: 300.0,
        };
        assert_eq!(prim.camera_at(usd::TimeCode::new(1.0))?, expected);
        Ok(())
    }

    /// Every field written is the field read back, as samples at the time
    /// given and as defaults.
    #[test]
    fn all_fields_round_trip() -> Result<(), SchemaError> {
        let camera = busy_camera();
        for time in [None, Some(usd::TimeCode::new(1.0))] {
            let stage = stage("anon.usda")?;
            let prim = Camera::define(&stage, "/camera")?;
            let commits = commits(&stage);
            prim.set_from_camera(&camera, time)?;
            assert_eq!(commits.get(), 1, "one edit authors the whole camera");
            assert_eq!(prim.camera_at(time)?, camera);
            assert_eq!(prim.xform_op_order()?.expect("authored"), vec!["xformOp:transform"]);

            // Authoring it again changes nothing.
            prim.set_from_camera(&camera, time)?;
            assert_eq!(prim.camera_at(time)?, camera);
        }
        Ok(())
    }

    /// The matrix authored is the one that puts the camera where it was
    /// asked to be in the world, whatever its parent does.
    #[test]
    fn round_trip_under_parent() -> Result<(), SchemaError> {
        let stage = stage("anon.usda")?;
        Xform::define(&stage, "/Rig")?
            .set_translate(gf::vec3d(10.0, -2.0, 3.0))?
            .set_rotate_xyz(gf::vec3f(20.0, 40.0, 60.0))?
            .set_scale(gf::vec3f(2.0, 0.5, 3.0))?;
        let prim = Camera::define(&stage, "/Rig/camera")?;
        let camera = busy_camera();

        prim.set_from_camera(&camera, None)?;
        let read = prim.camera_at(None)?;
        assert_close(read.transform, camera.transform);
        assert_ne!(prim.local_transform(None)?, camera.transform);
        assert_eq!(
            gf::Camera {
                transform: camera.transform,
                ..read
            },
            camera
        );
        Ok(())
    }

    /// A stack that reset its parent's transform is replaced with one that
    /// does not, and the matrix accounts for the parent.
    #[test]
    fn round_trip_over_reset() -> Result<(), SchemaError> {
        let stage = stage("anon.usda")?;
        Xform::define(&stage, "/Rig")?.set_translate(gf::vec3d(10.0, 0.0, 0.0))?;
        let prim = Camera::define(&stage, "/Rig/camera")?
            .set_translate(gf::vec3d(1.0, 1.0, 1.0))?
            .set_reset_xform_stack(true)?;
        let camera = busy_camera();

        prim.set_from_camera(&camera, None)?;
        assert!(!prim.resets_xform_stack()?);
        assert_close(prim.camera_at(None)?.transform, camera.transform);
        Ok(())
    }

    const CAMERA: &str = "def Camera \"camera\"\n{\n}";

    /// A stronger layer's op order refuses the whole camera, not only its
    /// transform.
    #[test]
    fn shadowed_order_authors_nothing() -> Result<(), SchemaError> {
        let ordered = "over \"camera\"\n{\n    uniform token[] xformOpOrder = []\n}";
        let (_dir, stage) = layered(&[("strong.usda", ordered), ("weak.usda", CAMERA)])?;
        let weak = target_layer(&stage, "weak.usda")?;
        let before = layer_text(&stage, &weak);
        let commits = commits(&stage);

        let prim = Camera::get(&stage, "/camera")?.expect("Camera");
        let error = prim.set_from_camera(&busy_camera(), None).expect_err("shadowed");
        assert!(matches!(error, SchemaError::XformOpOrderShadowed { .. }), "{error:?}");
        assert_eq!(layer_text(&stage, &weak), before);
        assert_eq!(commits.get(), 0);
        Ok(())
    }

    /// A parent that flattens space has no local matrix to offer.
    #[test]
    fn singular_parent_authors_nothing() -> Result<(), SchemaError> {
        let stage = stage("anon.usda")?;
        Xform::define(&stage, "/Flat")?.set_scale(gf::vec3f(1.0, 0.0, 1.0))?;
        let prim = Camera::define(&stage, "/Flat/camera")?;
        let root = stage.root_layer().identifier().to_string();
        let before = layer_text(&stage, &root);
        let commits = commits(&stage);

        let error = prim.set_from_camera(&busy_camera(), None).expect_err("singular");
        let SchemaError::SingularParentTransform { prim } = &error else {
            panic!("{error:?}");
        };
        assert_eq!(prim.as_str(), "/Flat/camera");
        assert_eq!(layer_text(&stage, &root), before);
        assert_eq!(commits.get(), 0);
        Ok(())
    }

    /// An attribute that cannot be authored takes the matrix and the
    /// attributes queued before it down with it.
    #[test]
    fn failed_attribute_authors_nothing() -> Result<(), SchemaError> {
        let (_dir, stage) = from_usda("#usda 1.0\ndef Camera \"camera\"\n{\n    custom rel fStop\n}\n")?;
        let root = stage.root_layer().identifier().to_string();
        let before = layer_text(&stage, &root);
        let commits = commits(&stage);

        let prim = Camera::get(&stage, "/camera")?.expect("Camera");
        prim.set_from_camera(&busy_camera(), None)
            .expect_err("fStop is a relationship here");
        assert_eq!(layer_text(&stage, &root), before);
        assert_eq!(commits.get(), 0);
        assert_eq!(prim.xform_op_order()?, None);
        Ok(())
    }

    /// Authoring succeeds on the edit target while a stronger layer's values
    /// are still the ones read.
    #[test]
    fn authored_beneath_stronger_values() -> Result<(), SchemaError> {
        let strong = "over \"camera\"\n{\n    float focalLength = 85\n    \
                      matrix4d xformOp:transform = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (9, 9, 9, 1))\n}";
        let (_dir, stage) = layered(&[("strong.usda", strong), ("weak.usda", CAMERA)])?;
        let weak = target_layer(&stage, "weak.usda")?;
        let prim = Camera::get(&stage, "/camera")?.expect("Camera");
        let camera = busy_camera();

        prim.set_from_camera(&camera, None)?;
        let text = layer_text(&stage, &weak);
        assert!(text.contains("float focalLength = 28"), "{text}");
        assert!(text.contains("xformOp:transform"), "{text}");

        let read = prim.camera_at(None)?;
        assert_eq!(read.focal_length, 85.0);
        assert_eq!(read.transform, gf::Mat4d::translation([9.0, 9.0, 9.0]));
        assert_eq!(read.f_stop, camera.f_stop);
        Ok(())
    }

    /// A projection token that names none reads as perspective.
    #[test]
    fn unknown_projection_perspective() -> Result<(), SchemaError> {
        let (_dir, stage) = from_usda("#usda 1.0\ndef Camera \"camera\"\n{\n    token projection = \"fisheye\"\n}\n")?;
        let prim = Camera::get(&stage, "/camera")?.expect("Camera");
        assert_eq!(prim.camera_at(None)?.projection, gf::Projection::Perspective);
        Ok(())
    }

    /// A prim with none of the attributes is the default camera where it
    /// stands.
    #[test]
    fn missing_attributes_default() -> Result<(), SchemaError> {
        let stage = stage("anon.usda")?;
        let xform = Xform::define(&stage, "/NotACamera")?.set_translate(gf::vec3d(1.0, 2.0, 3.0))?;
        let prim = Camera::from_prim_unchecked(xform.prim().clone());
        let expected = gf::Camera {
            transform: gf::Mat4d::translation([1.0, 2.0, 3.0]),
            ..gf::Camera::default()
        };
        assert_eq!(prim.camera_at(None)?, expected);
        assert_eq!(prim.linear_exposure_scale(None)?, 1.0);
        Ok(())
    }

    /// A blocked value reads as the default.
    #[test]
    fn blocked_value_defaults() -> Result<(), SchemaError> {
        let (_dir, stage) = from_usda("#usda 1.0\ndef Camera \"camera\"\n{\n    float focalLength = None\n}\n")?;
        let prim = Camera::get(&stage, "/camera")?.expect("Camera");
        assert_eq!(prim.camera_at(None)?, gf::Camera::default());
        Ok(())
    }

    /// A value of another type than the schema declares reads as the
    /// default, at the default time and at a numeric one.
    #[test]
    fn mistyped_value_defaults() -> Result<(), SchemaError> {
        let (_dir, stage) = from_usda("#usda 1.0\ndef Camera \"camera\"\n{\n    string focalLength = \"long\"\n}\n")?;
        let prim = Camera::get(&stage, "/camera")?.expect("Camera");
        assert_eq!(prim.camera_at(None)?, gf::Camera::default());
        assert_eq!(prim.camera_at(usd::TimeCode::new(1.0))?, gf::Camera::default());
        Ok(())
    }

    /// The scale is one at the fallbacks and follows each exposure
    /// attribute.
    #[test]
    fn exposure_scale() -> Result<(), SchemaError> {
        let stage = stage("anon.usda")?;
        let prim = Camera::define(&stage, "/camera")?;
        assert_eq!(prim.linear_exposure_scale(None)?, 1.0);

        prim.exposure_attr().set(1.0_f32)?;
        prim.exposure_time_attr().set(0.01_f32)?;
        prim.exposure_f_stop_attr().set(4.0_f32)?;
        prim.exposure_iso_attr().set(400.0_f32)?;
        prim.exposure_responsivity_attr().set(3.0_f32)?;
        assert!((prim.linear_exposure_scale(None)? - 0.015).abs() < 1e-6);
        Ok(())
    }
}
