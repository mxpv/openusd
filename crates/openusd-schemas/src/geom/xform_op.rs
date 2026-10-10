//! `UsdGeomXformOp` — one entry of an `xformOpOrder` stack.
//!
//! An op is an `xformOp:<kind>[:suffix]` attribute, possibly listed through
//! the `!invert!` prefix, whose value is turned into a 4×4 matrix by its kind.

use openusd::gf;
use openusd::sdf;
use openusd::tf;
use openusd::usd;

use super::XformOpPrecision;
use crate::SchemaError;

/// The prefix an `xformOpOrder` entry carries to apply its op inverted.
pub(super) const TOKEN_INVERT_PREFIX: &str = "!invert!";
/// The `xformOpOrder` entry that opts a prim out of its parent's transform.
pub(super) const TOKEN_RESET_XFORM_STACK: &str = "!resetXformStack!";
/// The namespace every op attribute lives in.
pub(super) const NS_XFORM_OP: &str = "xformOp:";

/// The kind of transform an op applies (C++ `UsdGeomXformOp::Type`), named by
/// the second component of its attribute name: `xformOp:rotateXYZ:pivot` is a
/// [`RotateXYZ`](Self::RotateXYZ).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum XformOpKind {
    /// `translate`, a `double3` / `float3` / `half3` offset.
    Translate,
    /// `translateX`, a scalar offset along X.
    TranslateX,
    /// `translateY`, a scalar offset along Y.
    TranslateY,
    /// `translateZ`, a scalar offset along Z.
    TranslateZ,
    /// `scale`, a per-axis factor.
    Scale,
    /// `scaleX`, a scalar factor along X.
    ScaleX,
    /// `scaleY`, a scalar factor along Y.
    ScaleY,
    /// `scaleZ`, a scalar factor along Z.
    ScaleZ,
    /// `rotateX`, degrees about X.
    RotateX,
    /// `rotateY`, degrees about Y.
    RotateY,
    /// `rotateZ`, degrees about Z.
    RotateZ,
    /// `rotateXYZ`, Euler degrees applied X, then Y, then Z.
    RotateXYZ,
    /// `rotateXZY`, Euler degrees applied X, then Z, then Y.
    RotateXZY,
    /// `rotateYXZ`, Euler degrees applied Y, then X, then Z.
    RotateYXZ,
    /// `rotateYZX`, Euler degrees applied Y, then Z, then X.
    RotateYZX,
    /// `rotateZXY`, Euler degrees applied Z, then X, then Y.
    RotateZXY,
    /// `rotateZYX`, Euler degrees applied Z, then Y, then X.
    RotateZYX,
    /// `orient`, a quaternion rotation.
    Orient,
    /// `transform`, a full `matrix4d`.
    Transform,
}

impl XformOpKind {
    /// Every kind, in declaration order.
    const ALL: [XformOpKind; 19] = [
        Self::Translate,
        Self::TranslateX,
        Self::TranslateY,
        Self::TranslateZ,
        Self::Scale,
        Self::ScaleX,
        Self::ScaleY,
        Self::ScaleZ,
        Self::RotateX,
        Self::RotateY,
        Self::RotateZ,
        Self::RotateXYZ,
        Self::RotateXZY,
        Self::RotateYXZ,
        Self::RotateYZX,
        Self::RotateZXY,
        Self::RotateZYX,
        Self::Orient,
        Self::Transform,
    ];

    /// The op type token, the name component between `xformOp:` and any
    /// suffix (C++ `UsdGeomXformOp::GetOpTypeToken`).
    pub fn as_token(self) -> &'static str {
        match self {
            Self::Translate => "translate",
            Self::TranslateX => "translateX",
            Self::TranslateY => "translateY",
            Self::TranslateZ => "translateZ",
            Self::Scale => "scale",
            Self::ScaleX => "scaleX",
            Self::ScaleY => "scaleY",
            Self::ScaleZ => "scaleZ",
            Self::RotateX => "rotateX",
            Self::RotateY => "rotateY",
            Self::RotateZ => "rotateZ",
            Self::RotateXYZ => "rotateXYZ",
            Self::RotateXZY => "rotateXZY",
            Self::RotateYXZ => "rotateYXZ",
            Self::RotateYZX => "rotateYZX",
            Self::RotateZXY => "rotateZXY",
            Self::RotateZYX => "rotateZYX",
            Self::Orient => "orient",
            Self::Transform => "transform",
        }
    }

    /// The kind an op type token names (C++ `UsdGeomXformOp::GetOpTypeEnum`),
    /// or `None` for a token naming no kind.
    pub fn from_token(token: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|kind| kind.as_token() == token)
    }

    /// The kind an op attribute name names: its second namespace component,
    /// so `xformOp:translate:pivot` is [`Translate`](Self::Translate). `None`
    /// for a name with no second component or one naming no kind.
    pub fn from_attr_name(name: &str) -> Option<Self> {
        name.split(':').nth(1).and_then(Self::from_token)
    }

    /// The value type an op of this kind holds at `precision` (C++
    /// `UsdGeomXformOp::GetValueTypeName`). A `transform` is `matrix4d`
    /// whatever `precision` asks for, since Sdf has no other matrix type.
    pub fn value_type(self, precision: XformOpPrecision) -> sdf::ValueTypeName {
        use sdf::ValueTypeName as T;

        let [double, float, half] = match self {
            Self::Transform => return T::MATRIX4D,
            Self::Orient => [T::QUATD, T::QUATF, T::QUATH],
            Self::TranslateX
            | Self::TranslateY
            | Self::TranslateZ
            | Self::ScaleX
            | Self::ScaleY
            | Self::ScaleZ
            | Self::RotateX
            | Self::RotateY
            | Self::RotateZ => [T::DOUBLE, T::FLOAT, T::HALF],
            Self::Translate
            | Self::Scale
            | Self::RotateXYZ
            | Self::RotateXZY
            | Self::RotateYXZ
            | Self::RotateYZX
            | Self::RotateZXY
            | Self::RotateZYX => [T::DOUBLE3, T::FLOAT3, T::HALF3],
        };
        match precision {
            XformOpPrecision::Double => double,
            XformOpPrecision::Float => float,
            XformOpPrecision::Half => half,
        }
    }

    /// The matrix an op of this kind applies for `value`, inverted when
    /// `inverse` is set, on the terms [`XformOp::op_transform`] states. `None`
    /// when the inverse of a singular `transform` is asked for.
    fn matrix(self, value: sdf::Value, inverse: bool) -> Option<gf::Matrix4d> {
        let sign = if inverse { -1.0 } else { 1.0 };
        // C++ negates the value of an inverted `scaleX` / `scaleY` / `scaleZ`
        // as it does a translate's. The reciprocal is that op's inverse, and
        // matches what C++ does for a three-axis `scale`.
        let factor = |c: f64| if inverse { 1.0 / c } else { c };
        let matrix = match self {
            Self::Transform => match value {
                sdf::Value::Matrix4d(m) if inverse => return m.inverse(),
                sdf::Value::Matrix4d(m) => Some(m),
                _ => None,
            },
            Self::TranslateX | Self::TranslateY | Self::TranslateZ => value.cast::<f64>().ok().map(|v| {
                let mut t = [0.0; 3];
                t[self.axes()[0]] = sign * v;
                gf::Matrix4d::translation(t)
            }),
            Self::ScaleX | Self::ScaleY | Self::ScaleZ => value.cast::<f64>().ok().map(|v| {
                let mut s = [1.0; 3];
                s[self.axes()[0]] = factor(v);
                gf::Matrix4d::scale(s)
            }),
            Self::RotateX | Self::RotateY | Self::RotateZ => {
                value.cast::<f64>().ok().map(|v| rotation(self.axes()[0], sign * v))
            }
            Self::Translate => value
                .cast::<[f64; 3]>()
                .ok()
                .map(|v| gf::Matrix4d::translation(v.map(|c| sign * c))),
            Self::Scale => value
                .cast::<[f64; 3]>()
                .ok()
                .map(|v| gf::Matrix4d::scale(v.map(factor))),
            Self::RotateXYZ
            | Self::RotateXZY
            | Self::RotateYXZ
            | Self::RotateYZX
            | Self::RotateZXY
            | Self::RotateZYX => value.cast::<[f64; 3]>().ok().map(|degrees| {
                // The inverse applies the negated rotations in reverse order.
                let rotations = self.axes().iter().map(|&a| rotation(a, sign * degrees[a]));
                match inverse {
                    true => rotations.rev().fold(gf::Matrix4d::IDENTITY, |m, r| m * r),
                    false => rotations.fold(gf::Matrix4d::IDENTITY, |m, r| m * r),
                }
            }),
            Self::Orient => value.cast::<[f64; 4]>().ok().map(|q| {
                let rotation = gf::Rotation::from_quat(gf::Quatd::from(q));
                let rotation = if inverse { rotation.inverse() } else { rotation };
                gf::Matrix4d::from_quat(rotation.quat())
            }),
        };
        Some(matrix.unwrap_or(gf::Matrix4d::IDENTITY))
    }

    /// The axes (0 = X, 1 = Y, 2 = Z) the kind acts along, in the order its
    /// name spells them, which is the order they apply to a point. Empty for
    /// a kind named for no axis.
    fn axes(self) -> &'static [usize] {
        match self {
            Self::TranslateX | Self::ScaleX | Self::RotateX => &[0],
            Self::TranslateY | Self::ScaleY | Self::RotateY => &[1],
            Self::TranslateZ | Self::ScaleZ | Self::RotateZ => &[2],
            Self::RotateXYZ => &[0, 1, 2],
            Self::RotateXZY => &[0, 2, 1],
            Self::RotateYXZ => &[1, 0, 2],
            Self::RotateYZX => &[1, 2, 0],
            Self::RotateZXY => &[2, 0, 1],
            Self::RotateZYX => &[2, 1, 0],
            Self::Translate | Self::Scale | Self::Orient | Self::Transform => &[],
        }
    }
}

/// One op of a prim's transform stack (C++ `UsdGeomXformOp`): the attribute
/// holding its value, the kind its name gives it, and whether the stack lists
/// it inverted.
///
/// The value is read through a [`usd::AttributeQuery`]. Evaluating the op at
/// many times resolves its value source once.
#[derive(Clone)]
pub struct XformOp {
    query: usd::AttributeQuery,
    kind: Option<XformOpKind>,
    inverse: bool,
}

impl XformOp {
    /// The op over `attr`, applied inverted when `inverse` is set.
    pub fn new(attr: &usd::Attribute, inverse: bool) -> Self {
        Self {
            query: attr.query(),
            kind: XformOpKind::from_attr_name(attr.name()),
            inverse,
        }
    }

    /// The attribute holding the op's value.
    pub fn attribute(&self) -> &usd::Attribute {
        self.query.attribute()
    }

    /// The op attribute's name, such as `xformOp:translate:pivot` (C++
    /// `GetName`).
    pub fn name(&self) -> &str {
        self.attribute().name()
    }

    /// The op's entry in `xformOpOrder`: its name, behind `!invert!` when it
    /// is applied inverted (C++ `GetOpName`).
    pub fn op_name(&self) -> tf::Token {
        match self.inverse {
            true => tf::Token::from(format!("{TOKEN_INVERT_PREFIX}{}", self.name())),
            false => tf::Token::from(self.name()),
        }
    }

    /// The kind the op's name gives it, or `None` for a name naming no kind,
    /// which contributes identity (C++ `TypeInvalid`).
    pub fn kind(&self) -> Option<XformOpKind> {
        self.kind
    }

    /// `true` when the stack applies the op inverted (C++ `IsInverseOp`).
    pub fn is_inverse_op(&self) -> bool {
        self.inverse
    }

    /// The op's matrix at `time`, where `None` is the default time (C++
    /// `GetOpTransform`), and identity when the op has no value or names no
    /// kind.
    ///
    /// Each kind inverts in closed form: a translate or rotation negates its
    /// values, a rotation also reverses its axis order, a scale takes the
    /// reciprocal, and an orient negates its rotation's angle. Only a
    /// `transform` goes through a general inverse, and a singular one is
    /// [`SchemaError::SingularTransform`]. A value of a type the kind does not
    /// take contributes identity.
    pub fn op_transform(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<gf::Matrix4d, SchemaError> {
        let Some(kind) = self.kind else {
            return Ok(gf::Matrix4d::IDENTITY);
        };
        let Some(value) = self.query.get_at::<sdf::Value>(time)? else {
            return Ok(gf::Matrix4d::IDENTITY);
        };
        kind.matrix(value, self.inverse)
            .ok_or_else(|| SchemaError::SingularTransform {
                op: self.op_name().to_string(),
            })
    }

    /// `true` when the op's value might differ between times (C++
    /// `MightBeTimeVarying`).
    pub fn might_be_time_varying(&self) -> openusd::Result<bool> {
        self.query.value_might_be_time_varying()
    }

    /// `true` when `self` and `other` apply the same attribute and exactly one
    /// of them is inverted. Together the two cancel out.
    pub(super) fn cancels(&self, other: &XformOp) -> bool {
        self.inverse != other.inverse && self.attribute() == other.attribute()
    }
}

/// The rotation by `degrees` about `axis` (0 = X, 1 = Y, 2 = Z), as C++
/// `GfMatrix4d(GfRotation(axis, degrees), GfVec3d(0))` makes it.
fn rotation(axis: usize, degrees: f64) -> gf::Matrix4d {
    let mut unit = gf::Vec3d::default();
    unit[axis] = 1.0;
    gf::Matrix4d::from_quat(gf::Rotation::new(unit, degrees).quat())
}

#[cfg(test)]
mod tests {
    use std::array;

    use super::*;

    /// The name's second component is the kind, whatever suffix follows.
    #[test]
    fn kind_from_attr_name() {
        assert_eq!(
            XformOpKind::from_attr_name("xformOp:rotateZYX:pivot"),
            Some(XformOpKind::RotateZYX)
        );
        assert_eq!(XformOpKind::from_attr_name("xformOp:bogus"), None);
        assert_eq!(XformOpKind::from_attr_name("transform"), None);
        for kind in XformOpKind::ALL {
            assert_eq!(XformOpKind::from_token(kind.as_token()), Some(kind));
        }
    }

    /// Every kind's inverse undoes it.
    #[test]
    fn inverse_undoes_kind() {
        let value = |kind: XformOpKind| match kind {
            XformOpKind::Transform => {
                sdf::Value::Matrix4d(gf::Matrix4d::translation([1.0, 2.0, 3.0]) * gf::Matrix4d::scale([2.0, 3.0, 4.0]))
            }
            XformOpKind::Orient => sdf::Value::Quatd(gf::quatd(0.5, 0.5, 0.5, 0.5)),
            k if k.value_type(XformOpPrecision::Double) == sdf::ValueTypeName::DOUBLE => sdf::Value::Double(30.0),
            _ => sdf::Value::Vec3d(gf::vec3d(10.0, 20.0, 30.0)),
        };
        for kind in XformOpKind::ALL {
            let v = value(kind);
            let forward = kind.matrix(v.clone(), false).expect("a forward op is never singular");
            let product = forward * kind.matrix(v, true).expect("the value is invertible");
            for (got, want) in product.0.iter().zip(gf::Matrix4d::IDENTITY.0) {
                assert!((got - want).abs() < 1e-9, "{kind:?}: {product:?}");
            }
        }
    }

    /// Rotation ops reproduce C++ `UsdGeomXformOp::GetOpTransform`; the
    /// expected rows are OpenUSD 26.08's on Linux. The `quatf` orients sit a
    /// few 1e-8 off unit length and the `quatd` one far from it: C++ takes the
    /// angle from the real part, so neither matrix is the normalized
    /// quaternion's. Entries agree to 1e-14, which leaves room for another
    /// platform's libm rounding `acos`, `sin` and `cos` differently in the
    /// last bit, far below the 3e-8 a normalized quaternion is off by.
    #[test]
    fn rotation_matches_cpp() {
        let quarter = sdf::Value::Quatf(gf::quatf(0.70710677, 0.70710677, 0.0, 0.0));
        let euler = sdf::Value::Vec3d(gf::vec3d(10.0, 20.0, 30.0));
        let cases = [
            (
                XformOpKind::Orient,
                sdf::Value::Quatf(gf::quatf(0.9511514, 0.04662174, -0.28952447, 0.096504346)),
                false,
                [
                    [0.8137250333625328, 0.15658419738533075, 0.559761519942499],
                    [-0.21057672212979378, 0.9770266546781312, 0.032807928089583355],
                    [-0.5417647221591828, -0.14456937842313441, 0.8280040341967738],
                ],
            ),
            (
                XformOpKind::Orient,
                quarter.clone(),
                false,
                [
                    [1.0, 0.0, 0.0],
                    [0.0, -3.422854177870249e-08, 0.9999999999999993],
                    [0.0, -0.9999999999999993, -3.422854177870249e-08],
                ],
            ),
            (
                XformOpKind::Orient,
                quarter,
                true,
                [
                    [1.0, 0.0, 0.0],
                    [0.0, -3.422854177870249e-08, -0.9999999999999993],
                    [0.0, 0.9999999999999993, -3.422854177870249e-08],
                ],
            ),
            (
                XformOpKind::Orient,
                sdf::Value::Quatd(gf::quatd(0.5, 1.0, 0.25, -0.75)),
                false,
                [
                    [0.423076923076923, -0.2787554345958372, -0.8621492474293819],
                    [0.7402938961342989, -0.4423076923076925, 0.5062892974098343],
                    [-0.5224661371860031, -0.8524431435636806, 0.01923076923076894],
                ],
            ),
            (
                XformOpKind::RotateX,
                sdf::Value::Double(30.0),
                false,
                [
                    [1.0, 0.0, 0.0],
                    [0.0, 0.8660254037844387, 0.49999999999999994],
                    [0.0, -0.49999999999999994, 0.8660254037844387],
                ],
            ),
            (
                XformOpKind::RotateXYZ,
                euler.clone(),
                false,
                [
                    [0.8137976813493738, 0.46984631039295416, -0.34202014332566877],
                    [-0.44096961052988237, 0.8825641192593856, 0.16317591116653482],
                    [0.3785223063697925, 0.01802831123629728, 0.9254165783983234],
                ],
            ),
            (
                XformOpKind::RotateXYZ,
                euler,
                true,
                [
                    [0.8137976813493738, -0.44096961052988237, 0.3785223063697925],
                    [0.46984631039295416, 0.8825641192593856, 0.01802831123629728],
                    [-0.34202014332566877, 0.16317591116653482, 0.9254165783983234],
                ],
            ),
        ];
        for (kind, value, inverse, want) in cases {
            let m = kind.matrix(value, inverse).expect("a rotation is never singular");
            let got: [[f64; 3]; 3] = array::from_fn(|r| array::from_fn(|c| m.0[r * 4 + c]));
            let close = got
                .iter()
                .flatten()
                .zip(want.iter().flatten())
                .all(|(g, w)| (g - w).abs() < 1e-14);
            assert!(close, "{kind:?} inverse={inverse}: {got:?} != {want:?}");
        }
    }
}
