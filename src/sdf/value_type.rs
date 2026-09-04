//! Attribute value type names (C++ `SdfValueTypeName`): the static table of
//! scene-description value types (C++ `Sdf_ValueTypeRegistry`), a constant
//! for each (`SdfValueTypeNames`), and the roles that make a foundational
//! type a semantic alias (`SdfValueRoleNames`).
//!
//! A registered name is one `(kind, role)` identity plus its spelling. The
//! [`ValueKind`] says which [`Value`] variant carries the type, the
//! [`Role`] is what turns `float3` into `color3f`, and two spellings with
//! the same identity are aliases of one type: `Color` and `color3d` are
//! equal, `color3f` and `float3` are not (§6.5 of the AOUSD core spec), and
//! neither is `EdgeIndex` equal to `int`. An array type is its element type's
//! spelling with `[]` appended and shares the element's role and dimensions;
//! `opaque` and `group` are the two scalars without an array form.
//!
//! A spelling the table does not know is carried verbatim as an unregistered
//! name (C++ `FindOrCreateType`'s temporary type): it round-trips through
//! layers untouched and answers `None` to every query about its type.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;

use strum::{Display, IntoStaticStr};

use crate::gf::{self, f16};
use crate::tf;

use super::value::{CastError, Value, ValueKind};
use super::{AssetPath, PathExpression, TimeCode};

/// The name of an attribute value type (C++ `SdfValueTypeName`), such as
/// `float3`, `color3f[]` or `token`.
///
/// Equality and hashing follow the type's identity, the `(kind, role)` pair,
/// so every alias of a type compares equal to it whatever its spelling;
/// [`as_str`](Self::as_str) is the spelling this name was found under and
/// [`serialization_name`](Self::serialization_name) the one a writer emits.
/// An unregistered name compares equal only to the same spelling and never
/// to a registered one. Constants for every standard type live on this type
/// (`ValueTypeName::COLOR3F`, `ValueTypeName::FLOAT_ARRAY`, …).
#[derive(Clone)]
pub struct ValueTypeName(Repr);

/// A registered row or a spelling the table does not know.
#[derive(Clone)]
enum Repr {
    Registered(Registered),
    /// A name the table does not know (C++ `FindOrCreateTypeName`'s
    /// temporary type): it round-trips verbatim and answers no query. Two
    /// unregistered names are equal when their spellings are, which C++
    /// does not distinguish (every temporary type compares equal there).
    Unregistered(tf::Token),
}

/// A row of the type table. Everything else a registered name answers
/// derives from `kind` and `role`.
#[derive(Clone, Copy)]
struct Registered {
    name: &'static str,
    kind: ValueKind,
    role: Option<Role>,
}

/// The semantic role a value type name carries (C++ `SdfValueRoleNames`),
/// what distinguishes `color3f` from `float3`. `Display` gives the C++
/// spelling (`TextureCoordinate`).
///
/// `Transform`, `PointIndex`, `EdgeIndex` and `FaceIndex` belong to legacy
/// spellings only; the AOUSD core spec knows the other seven.
// TODO(unit): C++ gives `Point`, `Vector` and `Normal` types a default length
// unit (`SdfDefaultUnit`, `SdfLengthUnit`); nothing here models units yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Display, IntoStaticStr)]
pub enum Role {
    Point,
    Normal,
    Vector,
    Color,
    Frame,
    Transform,
    PointIndex,
    EdgeIndex,
    FaceIndex,
    Group,
    TextureCoordinate,
}

/// The tuple nesting a value type's text literal has (C++
/// `SdfTupleDimensions`): none for a scalar such as `float`, one level with
/// a component count for a vector or quaternion, two for a matrix. An array
/// type reports its element's dimensions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Dimensions {
    Scalar,
    Tuple(usize),
    Matrix(usize, usize),
}

/// Why a value is not acceptable for a value type, or a type name is not
/// usable as a declaration.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ValueTypeError {
    /// The attribute declares no value type: an empty spelling, or a spec
    /// with no `typeName`.
    #[error("attribute declares no value type")]
    Empty,

    /// The declared type is not in the table, so no value but a block can be
    /// checked against it.
    #[error("value type {type_name} is not registered")]
    Unregistered {
        /// The unregistered spelling.
        type_name: tf::Token,
    },

    /// An `opaque` (or `group`) attribute never holds a value.
    #[error("an opaque attribute cannot hold a value")]
    Opaque,

    /// The value's kind is not the declared type's, and no coercion applies.
    #[error("value type {expected} cannot hold a {actual} value")]
    Mismatch {
        /// The declared type's spelling.
        expected: tf::Token,
        /// The kind of the offered value.
        actual: ValueKind,
    },

    /// A coercion applies but a component or element does not fit.
    #[error(transparent)]
    Cast(CastError),
}

// `ValueTypeError` rides inside `sdf::AuthoringError`, whose size the root
// `Error`'s inline budget bounds.
const _: () = assert!(mem::size_of::<ValueTypeError>() <= 48);

impl ValueTypeName {
    const fn registered(name: &'static str, kind: ValueKind, role: Option<Role>) -> Self {
        Self(Repr::Registered(Registered { name, kind, role }))
    }

    /// The registered type with this spelling (C++ `SdfSchema::FindType`):
    /// `None` for an empty or unknown spelling. Legacy spellings such as
    /// `Color` or `Vec3f` are found and equal their standard twins.
    pub fn find(name: &str) -> Option<Self> {
        let (base, array) = match name.strip_suffix("[]") {
            Some(base) => (base, true),
            None => (name, false),
        };
        let scalar = find_scalar(base)?;
        if array { scalar.array_type() } else { Some(scalar) }
    }

    /// Every registered type, the standard rows first and then the legacy
    /// spellings, each scalar followed by its array (C++ `GetAllTypes`).
    pub fn all() -> impl Iterator<Item = &'static Self> {
        STANDARD.iter().chain(LEGACY)
    }

    /// The spelling this name was found under.
    pub fn as_str(&self) -> &str {
        match &self.0 {
            Repr::Registered(row) => row.name,
            Repr::Unregistered(token) => token.as_str(),
        }
    }

    /// [`as_str`](Self::as_str) as a token, without allocating for a
    /// registered name.
    pub fn as_token(&self) -> tf::Token {
        match &self.0 {
            Repr::Registered(row) => tf::Token::new(row.name),
            Repr::Unregistered(token) => token.clone(),
        }
    }

    /// Whether `name` spells this type (C++ `SdfValueTypeName::operator==(TfToken)`):
    /// `COLOR3D.has_alias("Color")`. An unregistered name recognizes only
    /// its own spelling.
    pub fn has_alias(&self, name: &str) -> bool {
        match Self::find(name) {
            Some(other) => other == *self,
            None => self.as_str() == name,
        }
    }

    /// Whether the table knows this name.
    pub fn is_registered(&self) -> bool {
        matches!(self.0, Repr::Registered(_))
    }

    /// The [`Value`] variant carrying this type (C++ `GetType`); `None` for an
    /// unregistered name.
    pub fn kind(&self) -> Option<ValueKind> {
        match &self.0 {
            Repr::Registered(row) => Some(row.kind),
            Repr::Unregistered(_) => None,
        }
    }

    /// The semantic role, `None` for a foundational type and for an
    /// unregistered name (C++ `GetRole`).
    pub fn role(&self) -> Option<Role> {
        match &self.0 {
            Repr::Registered(row) => row.role,
            Repr::Unregistered(_) => None,
        }
    }

    /// The tuple nesting of this type's text literal (C++ `GetDimensions`).
    pub fn dimensions(&self) -> Option<Dimensions> {
        self.kind().map(ValueKind::dimensions)
    }

    /// The value an attribute of this type holds when nothing is authored
    /// (C++ `GetDefaultValue`): zero, empty, the identity for quaternions and
    /// matrices, [`Value::Opaque`] for `opaque` and `group`.
    pub fn default_value(&self) -> Option<Value> {
        self.kind().and_then(ValueKind::default_value)
    }

    /// Whether this is a registered array type (C++ `IsArray`). An
    /// unregistered name is neither array nor scalar.
    pub fn is_array(&self) -> bool {
        self.kind().is_some_and(|kind| kind.element_kind().is_some())
    }

    /// Whether this is a registered scalar type (C++ `IsScalar`), which
    /// `opaque` and `group` are despite having no array form.
    pub fn is_scalar(&self) -> bool {
        self.kind().is_some_and(|kind| kind.element_kind().is_none())
    }

    /// The element type of an array type, or a scalar type itself (C++
    /// `GetScalarType`); `None` for an unregistered name.
    pub fn scalar_type(&self) -> Option<Self> {
        let Repr::Registered(row) = &self.0 else {
            return None;
        };
        match row.kind.element_kind() {
            None => Some(self.clone()),
            Some(element) => Some(Self::registered(row.name.strip_suffix("[]")?, element, row.role)),
        }
    }

    /// The array type of a scalar type, or an array type itself (C++
    /// `GetArrayType`); `None` for `opaque`, `group` and an unregistered
    /// name.
    pub fn array_type(&self) -> Option<Self> {
        let Repr::Registered(row) = &self.0 else {
            return None;
        };
        if row.kind.element_kind().is_some() {
            return Some(self.clone());
        }
        let array = row.kind.array_kind()?;
        Some(Self::registered(array_name(row.name)?, array, row.role))
    }

    /// Every registered spelling of this type, standard first and in table
    /// order (C++ `GetAliasesAsTokens`); an unregistered name's only alias
    /// is itself.
    // TODO(perf): a scan of the table per call; index by identity if a hot
    // path appears.
    pub fn aliases(&self) -> Vec<tf::Token> {
        match &self.0 {
            Repr::Registered(_) => Self::all().filter(|row| *row == self).map(Self::as_token).collect(),
            Repr::Unregistered(token) => vec![token.clone()],
        }
    }

    /// The spelling a writer emits (C++ `GetSerializationName`): the standard
    /// spelling of this identity, so `Color` writes as `color3d`; a legacy
    /// identity with no standard spelling (`Transform`, `EdgeIndex`) and an
    /// unregistered name write as themselves.
    pub fn serialization_name(&self) -> tf::Token {
        match &self.0 {
            Repr::Registered(row) => tf::Token::new(preferred_spelling(row.kind, row.role).unwrap_or(row.name)),
            Repr::Unregistered(token) => token.clone(),
        }
    }

    /// Agreement as §6.5.1 of the AOUSD core spec defines it: a semantic
    /// alias agrees with its underlying type (`color3f` with `float3`,
    /// `color3f[]` with `float3[]`), a type agrees with itself, and two
    /// different aliases never agree (`color3f` and `point3f`).
    pub fn agrees_with(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Repr::Registered(a), Repr::Registered(b)) => {
                a.kind == b.kind && (a.role == b.role || a.role.is_none() || b.role.is_none())
            }
            _ => self == other,
        }
    }

    /// Whether `value` is of exactly this type's kind (C++ `CanRepresent`). A
    /// block is never represented; each authoring tier admits it explicitly.
    pub fn can_represent(&self, value: &Value) -> bool {
        self.kind() == Some(ValueKind::from(value))
    }

    /// The stage-tier check (C++ `UsdStage::_SetValue`): a block always
    /// passes; otherwise the type must be registered, not opaque, and hold
    /// exactly the value's kind. No coercion.
    pub fn validate(&self, value: &Value) -> Result<(), ValueTypeError> {
        let Some(kind) = self.storable_kind(value)? else {
            return Ok(());
        };
        let actual = ValueKind::from(value);
        if kind == actual {
            Ok(())
        } else {
            Err(ValueTypeError::Mismatch {
                expected: self.as_token(),
                actual,
            })
        }
    }

    /// The local-spec check (C++ `SdfPropertySpec::SetDefaultValue`): a block
    /// passes through; otherwise the type must be registered and not opaque,
    /// and the value is returned as is when it is of the type's kind or
    /// coerced through [`Value::coerce_to_kind`].
    pub fn coerce(&self, value: Value) -> Result<Value, ValueTypeError> {
        let Some(kind) = self.storable_kind(&value)? else {
            return Ok(value);
        };
        let actual = ValueKind::from(&value);
        value.coerce_to_kind(kind).map_err(|error| match error {
            CastError::TypeMismatch { .. } => ValueTypeError::Mismatch {
                expected: self.as_token(),
                actual,
            },
            CastError::OutOfRange { .. } => ValueTypeError::Cast(error),
        })
    }

    /// The gates [`validate`](Self::validate) and [`coerce`](Self::coerce)
    /// share: `Ok(None)` for a block, which every type stores as it is; else
    /// the kind to check `value` against, when the type is registered and
    /// not opaque.
    fn storable_kind(&self, value: &Value) -> Result<Option<ValueKind>, ValueTypeError> {
        if value.is_value_block() {
            return Ok(None);
        }
        let kind = self.registered_kind()?;
        if kind == ValueKind::Opaque {
            return Err(ValueTypeError::Opaque);
        }
        Ok(Some(kind))
    }

    /// The kind of a registered name, or why there is none.
    fn registered_kind(&self) -> Result<ValueKind, ValueTypeError> {
        match &self.0 {
            Repr::Registered(row) => Ok(row.kind),
            Repr::Unregistered(token) if token.is_empty() => Err(ValueTypeError::Empty),
            Repr::Unregistered(token) => Err(ValueTypeError::Unregistered {
                type_name: token.clone(),
            }),
        }
    }
}

impl PartialEq for ValueTypeName {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Repr::Registered(a), Repr::Registered(b)) => a.kind == b.kind && a.role == b.role,
            (Repr::Unregistered(a), Repr::Unregistered(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for ValueTypeName {}

impl Hash for ValueTypeName {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self.0 {
            Repr::Registered(row) => {
                0u8.hash(state);
                row.kind.hash(state);
                row.role.hash(state);
            }
            Repr::Unregistered(token) => {
                1u8.hash(state);
                token.hash(state);
            }
        }
    }
}

impl fmt::Display for ValueTypeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl fmt::Debug for ValueTypeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

/// C++ `FindOrCreateType`: the registered type, or the spelling carried as
/// an unregistered name.
impl From<&str> for ValueTypeName {
    fn from(name: &str) -> Self {
        Self::find(name).unwrap_or_else(|| Self(Repr::Unregistered(tf::Token::from(name))))
    }
}

impl From<String> for ValueTypeName {
    fn from(name: String) -> Self {
        Self::from(tf::Token::from(name))
    }
}

impl From<tf::Token> for ValueTypeName {
    fn from(name: tf::Token) -> Self {
        Self::find(name.as_str()).unwrap_or(Self(Repr::Unregistered(name)))
    }
}

/// The scalar/array pairing of the attribute kinds, written once.
macro_rules! array_pairs {
    ($($scalar:ident => $array:ident),* $(,)?) => {
        impl ValueKind {
            /// The kind of an array of this scalar kind; `None` for `Opaque`,
            /// for an array kind, and for every kind no attribute holds.
            pub const fn array_kind(self) -> Option<ValueKind> {
                match self {
                    $(ValueKind::$scalar => Some(ValueKind::$array),)*
                    _ => None,
                }
            }

            /// The element kind of this array kind; `None` for a scalar and for
            /// every kind that is not an attribute array (`PathVec`, `ValueVec`
            /// and `LayerOffsetVec` hold metadata, not attribute values).
            pub const fn element_kind(self) -> Option<ValueKind> {
                match self {
                    $(ValueKind::$array => Some(ValueKind::$scalar),)*
                    _ => None,
                }
            }

            /// The empty array of an array kind.
            fn empty_array(self) -> Option<Value> {
                match self {
                    $(ValueKind::$array => Some(Value::$array(Vec::new())),)*
                    _ => None,
                }
            }
        }
    };
}

array_pairs! {
    Bool => BoolVec,
    Uchar => UcharVec,
    Int => IntVec,
    Uint => UintVec,
    Int64 => Int64Vec,
    Uint64 => Uint64Vec,
    Half => HalfVec,
    Float => FloatVec,
    Double => DoubleVec,
    TimeCode => TimeCodeVec,
    String => StringVec,
    Token => TokenVec,
    AssetPath => AssetPathVec,
    PathExpression => PathExpressionVec,
    Vec2i => Vec2iVec,
    Vec2h => Vec2hVec,
    Vec2f => Vec2fVec,
    Vec2d => Vec2dVec,
    Vec3i => Vec3iVec,
    Vec3h => Vec3hVec,
    Vec3f => Vec3fVec,
    Vec3d => Vec3dVec,
    Vec4i => Vec4iVec,
    Vec4h => Vec4hVec,
    Vec4f => Vec4fVec,
    Vec4d => Vec4dVec,
    Quath => QuathVec,
    Quatf => QuatfVec,
    Quatd => QuatdVec,
    Matrix2d => Matrix2dVec,
    Matrix3d => Matrix3dVec,
    Matrix4d => Matrix4dVec,
}

impl ValueKind {
    /// The tuple nesting of a text literal of this kind; an array kind
    /// reports its element's.
    pub const fn dimensions(self) -> Dimensions {
        let element = match self.element_kind() {
            Some(element) => element,
            None => self,
        };
        match element {
            ValueKind::Vec2i | ValueKind::Vec2h | ValueKind::Vec2f | ValueKind::Vec2d => Dimensions::Tuple(2),
            ValueKind::Vec3i | ValueKind::Vec3h | ValueKind::Vec3f | ValueKind::Vec3d => Dimensions::Tuple(3),
            ValueKind::Vec4i
            | ValueKind::Vec4h
            | ValueKind::Vec4f
            | ValueKind::Vec4d
            | ValueKind::Quath
            | ValueKind::Quatf
            | ValueKind::Quatd => Dimensions::Tuple(4),
            ValueKind::Matrix2d => Dimensions::Matrix(2, 2),
            ValueKind::Matrix3d => Dimensions::Matrix(3, 3),
            ValueKind::Matrix4d => Dimensions::Matrix(4, 4),
            _ => Dimensions::Scalar,
        }
    }

    /// The default value of an attribute kind (C++ `GetDefaultValue`): zero
    /// or empty, the identity for quaternions and matrices,
    /// [`Value::Opaque`] for `Opaque`; `None` for a kind no attribute holds.
    /// Built per call, since a `Value` is not `const`-constructible for every
    /// payload; the empty containers allocate nothing.
    pub fn default_value(self) -> Option<Value> {
        Some(match self {
            ValueKind::Bool => Value::Bool(false),
            ValueKind::Uchar => Value::Uchar(0),
            ValueKind::Int => Value::Int(0),
            ValueKind::Uint => Value::Uint(0),
            ValueKind::Int64 => Value::Int64(0),
            ValueKind::Uint64 => Value::Uint64(0),
            ValueKind::Half => Value::Half(f16::ZERO),
            ValueKind::Float => Value::Float(0.0),
            ValueKind::Double => Value::Double(0.0),
            ValueKind::TimeCode => Value::TimeCode(TimeCode(0.0)),
            ValueKind::String => Value::String(String::new()),
            ValueKind::Token => Value::Token(tf::Token::default()),
            ValueKind::AssetPath => Value::AssetPath(AssetPath::default()),
            ValueKind::PathExpression => Value::PathExpression(PathExpression::default()),
            ValueKind::Opaque => Value::Opaque,
            ValueKind::Vec2i => Value::Vec2i(gf::Vec2i::default()),
            ValueKind::Vec2h => Value::Vec2h(gf::Vec2h::default()),
            ValueKind::Vec2f => Value::Vec2f(gf::Vec2f::default()),
            ValueKind::Vec2d => Value::Vec2d(gf::Vec2d::default()),
            ValueKind::Vec3i => Value::Vec3i(gf::Vec3i::default()),
            ValueKind::Vec3h => Value::Vec3h(gf::Vec3h::default()),
            ValueKind::Vec3f => Value::Vec3f(gf::Vec3f::default()),
            ValueKind::Vec3d => Value::Vec3d(gf::Vec3d::default()),
            ValueKind::Vec4i => Value::Vec4i(gf::Vec4i::default()),
            ValueKind::Vec4h => Value::Vec4h(gf::Vec4h::default()),
            ValueKind::Vec4f => Value::Vec4f(gf::Vec4f::default()),
            ValueKind::Vec4d => Value::Vec4d(gf::Vec4d::default()),
            ValueKind::Quath => Value::Quath(gf::Quath::IDENTITY),
            ValueKind::Quatf => Value::Quatf(gf::Quatf::IDENTITY),
            ValueKind::Quatd => Value::Quatd(gf::Quatd::IDENTITY),
            ValueKind::Matrix2d => Value::Matrix2d(gf::Mat2d::IDENTITY),
            ValueKind::Matrix3d => Value::Matrix3d(gf::Mat3d::IDENTITY),
            ValueKind::Matrix4d => Value::Matrix4d(gf::Matrix4d::IDENTITY),
            array => return array.empty_array(),
        })
    }

    /// The role-blind type name of this kind (C++ `SdfGetValueTypeNameForValue`):
    /// `Vec3f` is `float3`, never `color3f`; `None` for a kind no attribute
    /// holds.
    pub fn type_name(self) -> Option<ValueTypeName> {
        preferred_spelling(self, None).map(|name| ValueTypeName::registered(name, self, None))
    }
}

/// The array kind of a scalar row; a static initializer fails to compile if
/// a row names a kind with no array form.
const fn array_of(kind: ValueKind) -> ValueKind {
    match kind.array_kind() {
        Some(array) => array,
        None => panic!("value type row has no array kind"),
    }
}

/// The standard spelling of an identity, scalar or array (C++
/// `GetSerializationName`'s first alias); `None` for an identity only a
/// legacy spelling names.
fn preferred_spelling(kind: ValueKind, role: Option<Role>) -> Option<&'static str> {
    match kind.element_kind() {
        Some(element) => array_name(preferred_spelling_scalar(element, role)?),
        None => preferred_spelling_scalar(kind, role),
    }
}

impl ValueTypeName {
    /// The `opaque` value type: an attribute carrying no value (C++
    /// `SdfOpaqueValue`). It has no array form.
    pub const OPAQUE: ValueTypeName = ValueTypeName::registered("opaque", ValueKind::Opaque, None);

    /// The `group` value type: `opaque` with the [`Role::Group`] role, a proxy
    /// for several values. It has no array form.
    pub const GROUP: ValueTypeName = ValueTypeName::registered("group", ValueKind::Opaque, Some(Role::Group));
}

/// The type table. Each row declares a scalar spelling with its kind and
/// role, and the macro derives the `[]` row, the two constants, the standard
/// and legacy slices, and the lookups by spelling and by identity.
macro_rules! value_types {
    (
        $( pub $scalar:ident / $array:ident = $name:literal => $kind:ident $(as $role:ident)? ; )*
        legacy: $( $legacy:literal => $legacy_kind:ident $(as $legacy_role:ident)? ; )*
    ) => {
        impl ValueTypeName {
            $(
                #[doc = concat!("The `", $name, "` value type.")]
                pub const $scalar: ValueTypeName =
                    ValueTypeName::registered($name, ValueKind::$kind, value_types!(@role $($role)?));

                #[doc = concat!("The `", $name, "[]` value type.")]
                pub const $array: ValueTypeName = ValueTypeName::registered(
                    concat!($name, "[]"),
                    array_of(ValueKind::$kind),
                    value_types!(@role $($role)?),
                );
            )*
        }

        /// The standard rows, each scalar followed by its array, with the two
        /// array-less types last.
        static STANDARD: &[ValueTypeName] = &[
            $( ValueTypeName::$scalar, ValueTypeName::$array, )*
            ValueTypeName::OPAQUE,
            ValueTypeName::GROUP,
        ];

        /// The legacy spellings, each scalar followed by its array.
        static LEGACY: &[ValueTypeName] = &[
            $(
                ValueTypeName::registered($legacy, ValueKind::$legacy_kind, value_types!(@role $($legacy_role)?)),
                ValueTypeName::registered(
                    concat!($legacy, "[]"),
                    array_of(ValueKind::$legacy_kind),
                    value_types!(@role $($legacy_role)?),
                ),
            )*
        ];

        /// The registered scalar row with this spelling.
        fn find_scalar(name: &str) -> Option<ValueTypeName> {
            match name {
                $( $name => Some(ValueTypeName::$scalar), )*
                "opaque" => Some(ValueTypeName::OPAQUE),
                "group" => Some(ValueTypeName::GROUP),
                $(
                    $legacy => Some(ValueTypeName::registered(
                        $legacy,
                        ValueKind::$legacy_kind,
                        value_types!(@role $($legacy_role)?),
                    )),
                )*
                _ => None,
            }
        }

        /// The `[]` spelling of a registered scalar spelling.
        fn array_name(scalar: &str) -> Option<&'static str> {
            match scalar {
                $( $name => Some(concat!($name, "[]")), )*
                $( $legacy => Some(concat!($legacy, "[]")), )*
                _ => None,
            }
        }

        /// The standard scalar spelling of a scalar identity.
        fn preferred_spelling_scalar(kind: ValueKind, role: Option<Role>) -> Option<&'static str> {
            match (kind, role) {
                $( (ValueKind::$kind, value_types!(@role $($role)?)) => Some($name), )*
                (ValueKind::Opaque, None) => Some("opaque"),
                (ValueKind::Opaque, Some(Role::Group)) => Some("group"),
                _ => None,
            }
        }
    };
    (@role) => { None };
    (@role $role:ident) => { Some(Role::$role) };
}

value_types! {
    pub BOOL / BOOL_ARRAY = "bool" => Bool;
    pub UCHAR / UCHAR_ARRAY = "uchar" => Uchar;
    pub INT / INT_ARRAY = "int" => Int;
    pub UINT / UINT_ARRAY = "uint" => Uint;
    pub INT64 / INT64_ARRAY = "int64" => Int64;
    pub UINT64 / UINT64_ARRAY = "uint64" => Uint64;
    pub HALF / HALF_ARRAY = "half" => Half;
    pub FLOAT / FLOAT_ARRAY = "float" => Float;
    pub DOUBLE / DOUBLE_ARRAY = "double" => Double;
    pub TIME_CODE / TIME_CODE_ARRAY = "timecode" => TimeCode;
    pub STRING / STRING_ARRAY = "string" => String;
    pub TOKEN / TOKEN_ARRAY = "token" => Token;
    pub ASSET / ASSET_ARRAY = "asset" => AssetPath;
    pub PATH_EXPRESSION / PATH_EXPRESSION_ARRAY = "pathExpression" => PathExpression;
    pub DOUBLE2 / DOUBLE2_ARRAY = "double2" => Vec2d;
    pub DOUBLE3 / DOUBLE3_ARRAY = "double3" => Vec3d;
    pub DOUBLE4 / DOUBLE4_ARRAY = "double4" => Vec4d;
    pub FLOAT2 / FLOAT2_ARRAY = "float2" => Vec2f;
    pub FLOAT3 / FLOAT3_ARRAY = "float3" => Vec3f;
    pub FLOAT4 / FLOAT4_ARRAY = "float4" => Vec4f;
    pub HALF2 / HALF2_ARRAY = "half2" => Vec2h;
    pub HALF3 / HALF3_ARRAY = "half3" => Vec3h;
    pub HALF4 / HALF4_ARRAY = "half4" => Vec4h;
    pub INT2 / INT2_ARRAY = "int2" => Vec2i;
    pub INT3 / INT3_ARRAY = "int3" => Vec3i;
    pub INT4 / INT4_ARRAY = "int4" => Vec4i;
    pub POINT3H / POINT3H_ARRAY = "point3h" => Vec3h as Point;
    pub POINT3F / POINT3F_ARRAY = "point3f" => Vec3f as Point;
    pub POINT3D / POINT3D_ARRAY = "point3d" => Vec3d as Point;
    pub VECTOR3H / VECTOR3H_ARRAY = "vector3h" => Vec3h as Vector;
    pub VECTOR3F / VECTOR3F_ARRAY = "vector3f" => Vec3f as Vector;
    pub VECTOR3D / VECTOR3D_ARRAY = "vector3d" => Vec3d as Vector;
    pub NORMAL3H / NORMAL3H_ARRAY = "normal3h" => Vec3h as Normal;
    pub NORMAL3F / NORMAL3F_ARRAY = "normal3f" => Vec3f as Normal;
    pub NORMAL3D / NORMAL3D_ARRAY = "normal3d" => Vec3d as Normal;
    pub COLOR3H / COLOR3H_ARRAY = "color3h" => Vec3h as Color;
    pub COLOR3F / COLOR3F_ARRAY = "color3f" => Vec3f as Color;
    pub COLOR3D / COLOR3D_ARRAY = "color3d" => Vec3d as Color;
    pub COLOR4H / COLOR4H_ARRAY = "color4h" => Vec4h as Color;
    pub COLOR4F / COLOR4F_ARRAY = "color4f" => Vec4f as Color;
    pub COLOR4D / COLOR4D_ARRAY = "color4d" => Vec4d as Color;
    pub QUATH / QUATH_ARRAY = "quath" => Quath;
    pub QUATF / QUATF_ARRAY = "quatf" => Quatf;
    pub QUATD / QUATD_ARRAY = "quatd" => Quatd;
    pub MATRIX2D / MATRIX2D_ARRAY = "matrix2d" => Matrix2d;
    pub MATRIX3D / MATRIX3D_ARRAY = "matrix3d" => Matrix3d;
    pub MATRIX4D / MATRIX4D_ARRAY = "matrix4d" => Matrix4d;
    pub FRAME4D / FRAME4D_ARRAY = "frame4d" => Matrix4d as Frame;
    pub TEX_COORD2H / TEX_COORD2H_ARRAY = "texCoord2h" => Vec2h as TextureCoordinate;
    pub TEX_COORD2F / TEX_COORD2F_ARRAY = "texCoord2f" => Vec2f as TextureCoordinate;
    pub TEX_COORD2D / TEX_COORD2D_ARRAY = "texCoord2d" => Vec2d as TextureCoordinate;
    pub TEX_COORD3H / TEX_COORD3H_ARRAY = "texCoord3h" => Vec3h as TextureCoordinate;
    pub TEX_COORD3F / TEX_COORD3F_ARRAY = "texCoord3f" => Vec3f as TextureCoordinate;
    pub TEX_COORD3D / TEX_COORD3D_ARRAY = "texCoord3d" => Vec3d as TextureCoordinate;
    // Legacy spellings C++ still registers (`_AddLegacyTypesToRegistry`):
    // readable and equal to their standard twin, written back as it, with
    // no constants. `Transform`, `PointIndex`, `EdgeIndex` and `FaceIndex`
    // have no standard twin and write as themselves.
    legacy:
    "Vec2i" => Vec2i;
    "Vec2h" => Vec2h;
    "Vec2f" => Vec2f;
    "Vec2d" => Vec2d;
    "Vec3i" => Vec3i;
    "Vec3h" => Vec3h;
    "Vec3f" => Vec3f;
    "Vec3d" => Vec3d;
    "Vec4i" => Vec4i;
    "Vec4h" => Vec4h;
    "Vec4f" => Vec4f;
    "Vec4d" => Vec4d;
    "Point" => Vec3d as Point;
    "PointFloat" => Vec3f as Point;
    "Normal" => Vec3d as Normal;
    "NormalFloat" => Vec3f as Normal;
    "Vector" => Vec3d as Vector;
    "VectorFloat" => Vec3f as Vector;
    "Color" => Vec3d as Color;
    "ColorFloat" => Vec3f as Color;
    "Quath" => Quath;
    "Quatf" => Quatf;
    "Quatd" => Quatd;
    "Matrix2d" => Matrix2d;
    "Matrix3d" => Matrix3d;
    "Matrix4d" => Matrix4d;
    "Frame" => Matrix4d as Frame;
    "Transform" => Matrix4d as Transform;
    "PointIndex" => Int as PointIndex;
    "EdgeIndex" => Int as EdgeIndex;
    "FaceIndex" => Int as FaceIndex;
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashSet};
    use std::hash::DefaultHasher;

    use strum::IntoEnumIterator;

    use super::*;

    fn find(name: &str) -> ValueTypeName {
        ValueTypeName::find(name).unwrap_or_else(|| panic!("{name} is registered"))
    }

    fn hash_of(name: &ValueTypeName) -> u64 {
        let mut hasher = DefaultHasher::new();
        name.hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn find_registered() {
        assert_eq!(find("float3"), ValueTypeName::FLOAT3);
        assert_eq!(find("float3").as_str(), "float3");
        assert_eq!(find("color3f[]"), ValueTypeName::COLOR3F_ARRAY);
        assert_eq!(find("color3f[]").as_str(), "color3f[]");
        assert_eq!(find("opaque"), ValueTypeName::OPAQUE);
        assert_eq!(find("group"), ValueTypeName::GROUP);
        assert_eq!(find("timecode").kind(), Some(ValueKind::TimeCode));
        assert_eq!(find("color3f").role(), Some(Role::Color));
        assert_eq!(find("float3").role(), None);
    }

    #[test]
    fn find_empty_none() {
        assert!(ValueTypeName::find("").is_none());
        assert!(ValueTypeName::find("[]").is_none());
        assert!(ValueTypeName::find("float3d").is_none());
        assert!(ValueTypeName::find("opaque[]").is_none());
        assert!(ValueTypeName::find("group[]").is_none());
    }

    #[test]
    fn unknown_round_trips() {
        let unknown = ValueTypeName::from("double3d[]");
        assert!(!unknown.is_registered());
        assert_eq!(unknown.as_str(), "double3d[]");
        assert_eq!(unknown.as_token(), tf::Token::new("double3d[]"));
        assert_eq!(unknown.serialization_name(), tf::Token::new("double3d[]"));
        assert_eq!(unknown.kind(), None);
        assert_eq!(unknown.role(), None);
        assert_eq!(unknown.dimensions(), None);
        assert_eq!(unknown.default_value(), None);
        assert!(!unknown.is_array());
        assert!(!unknown.is_scalar());
        assert_eq!(unknown.scalar_type(), None);
        assert_eq!(unknown.array_type(), None);
        assert_eq!(ValueTypeName::from(tf::Token::new("float")), ValueTypeName::FLOAT);
        assert_eq!(ValueTypeName::from(String::from("Color")), ValueTypeName::COLOR3D);
    }

    #[test]
    fn alias_equality() {
        assert_eq!(find("Color"), ValueTypeName::COLOR3D);
        assert_eq!(find("Vec3f"), ValueTypeName::FLOAT3);
        assert_eq!(find("PointFloat"), ValueTypeName::POINT3F);
        assert_eq!(find("Frame[]"), ValueTypeName::FRAME4D_ARRAY);
        assert_eq!(find("Color").as_str(), "Color");
    }

    #[test]
    fn role_inequality() {
        assert_ne!(ValueTypeName::COLOR3F, ValueTypeName::FLOAT3);
        assert_ne!(ValueTypeName::COLOR3F, ValueTypeName::POINT3F);
        assert_ne!(find("EdgeIndex"), ValueTypeName::INT);
        assert_ne!(ValueTypeName::FLOAT3, ValueTypeName::FLOAT3_ARRAY);
        assert_ne!(ValueTypeName::OPAQUE, ValueTypeName::GROUP);
    }

    #[test]
    fn unknown_by_text() {
        assert_eq!(ValueTypeName::from("foo"), ValueTypeName::from("foo"));
        assert_ne!(ValueTypeName::from("foo"), ValueTypeName::from("bar"));
        assert_ne!(ValueTypeName::from("foo"), ValueTypeName::FLOAT);
        assert_ne!(ValueTypeName::FLOAT, ValueTypeName::from("foo"));
    }

    #[test]
    fn has_alias() {
        assert!(ValueTypeName::COLOR3D.has_alias("Color"));
        assert!(ValueTypeName::COLOR3D.has_alias("color3d"));
        assert!(!ValueTypeName::COLOR3D.has_alias("double3"));
        assert!(!ValueTypeName::COLOR3D.has_alias("foo"));
        assert!(ValueTypeName::from("foo").has_alias("foo"));
        assert!(!ValueTypeName::from("foo").has_alias("float"));
    }

    #[test]
    fn unknown_aliases_self() {
        assert_eq!(ValueTypeName::from("foo").aliases(), vec![tf::Token::new("foo")]);
    }

    #[test]
    fn hash_matches_eq() {
        assert_eq!(hash_of(&find("Color")), hash_of(&ValueTypeName::COLOR3D));
        assert_eq!(
            hash_of(&ValueTypeName::from("foo")),
            hash_of(&ValueTypeName::from("foo"))
        );
        assert_ne!(hash_of(&ValueTypeName::COLOR3F), hash_of(&ValueTypeName::FLOAT3));
        let set: HashSet<ValueTypeName> = [find("Color"), ValueTypeName::COLOR3D, find("Vec3d")]
            .into_iter()
            .collect();
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn array_scalar_links() {
        for row in ValueTypeName::all() {
            if row.is_array() {
                let scalar = row.scalar_type().expect("array has a scalar");
                assert!(scalar.is_scalar(), "{row}");
                assert_eq!(scalar.array_type().as_ref(), Some(row), "{row}");
                assert_eq!(format!("{scalar}[]"), row.as_str());
                assert_eq!(row.array_type().as_ref(), Some(row), "{row}");
                assert_eq!(scalar.role(), row.role(), "{row}");
                assert_eq!(scalar.dimensions(), row.dimensions(), "{row}");
            } else {
                assert!(row.is_scalar(), "{row}");
                assert_eq!(row.scalar_type().as_ref(), Some(row), "{row}");
                if let Some(array) = row.array_type() {
                    assert_eq!(array.scalar_type().as_ref(), Some(row), "{row}");
                }
            }
        }
    }

    #[test]
    fn opaque_no_array() {
        for name in [ValueTypeName::OPAQUE, ValueTypeName::GROUP] {
            assert!(name.is_scalar(), "{name}");
            assert!(!name.is_array(), "{name}");
            assert_eq!(name.scalar_type().as_ref(), Some(&name));
            assert_eq!(name.array_type(), None);
            assert_eq!(name.kind(), Some(ValueKind::Opaque));
            assert_eq!(name.default_value(), Some(Value::Opaque));
        }
        assert_eq!(ValueTypeName::GROUP.role(), Some(Role::Group));
    }

    #[test]
    fn serialization_name() {
        assert_eq!(find("Color").serialization_name(), tf::Token::new("color3d"));
        assert_eq!(find("Color[]").serialization_name(), tf::Token::new("color3d[]"));
        assert_eq!(find("Vec3f").serialization_name(), tf::Token::new("float3"));
        assert_eq!(ValueTypeName::COLOR3F.serialization_name(), tf::Token::new("color3f"));
        assert_eq!(ValueTypeName::OPAQUE.serialization_name(), tf::Token::new("opaque"));
        assert_eq!(ValueTypeName::GROUP.serialization_name(), tf::Token::new("group"));
        assert_eq!(
            ValueTypeName::from("foo[]").serialization_name(),
            tf::Token::new("foo[]")
        );
    }

    #[test]
    fn legacy_only_identities() {
        for (name, twin) in [
            ("Transform", ValueTypeName::MATRIX4D),
            ("PointIndex", ValueTypeName::INT),
            ("EdgeIndex", ValueTypeName::INT),
            ("FaceIndex", ValueTypeName::INT),
        ] {
            let scalar = find(name);
            assert_eq!(scalar.serialization_name(), tf::Token::new(name));
            assert_ne!(scalar, twin);
            assert_eq!(scalar.kind(), twin.kind());
            assert_eq!(scalar.aliases(), vec![tf::Token::new(name)]);
            let array = scalar.array_type().expect("legacy identities have arrays");
            assert_eq!(array.serialization_name(), tf::Token::from(format!("{name}[]")));
            assert_ne!(array, twin.array_type().expect("twin has an array"));
        }
    }

    #[test]
    fn aliases_in_order() {
        let aliases = ValueTypeName::COLOR3D.aliases();
        assert_eq!(aliases, vec![tf::Token::new("color3d"), tf::Token::new("Color")]);
        let aliases = ValueTypeName::FLOAT3.aliases();
        assert_eq!(aliases, vec![tf::Token::new("float3"), tf::Token::new("Vec3f")]);
        assert_eq!(
            ValueTypeName::COLOR3F_ARRAY.aliases(),
            vec![tf::Token::new("color3f[]"), tf::Token::new("ColorFloat[]")]
        );
    }

    #[test]
    fn dimensions_by_kind() {
        assert_eq!(ValueKind::Float.dimensions(), Dimensions::Scalar);
        assert_eq!(ValueKind::Token.dimensions(), Dimensions::Scalar);
        assert_eq!(ValueKind::Vec3f.dimensions(), Dimensions::Tuple(3));
        assert_eq!(ValueKind::Vec3fVec.dimensions(), Dimensions::Tuple(3));
        assert_eq!(ValueKind::Quath.dimensions(), Dimensions::Tuple(4));
        assert_eq!(ValueKind::Matrix4d.dimensions(), Dimensions::Matrix(4, 4));
        assert_eq!(ValueKind::Matrix2dVec.dimensions(), Dimensions::Matrix(2, 2));
        assert_eq!(ValueTypeName::FRAME4D.dimensions(), Some(Dimensions::Matrix(4, 4)));
        assert_eq!(ValueTypeName::FLOAT_ARRAY.dimensions(), Some(Dimensions::Scalar));
    }

    #[test]
    fn defaults_representable() {
        let mut count = 0;
        for row in ValueTypeName::all() {
            let default = row.default_value().unwrap_or_else(|| panic!("{row} has a default"));
            assert!(row.can_represent(&default), "{row}");
            count += 1;
        }
        assert_eq!(count, 172);
        for kind in ValueKind::iter() {
            assert_eq!(kind.default_value().is_some(), kind.type_name().is_some(), "{kind}");
        }
    }

    #[test]
    fn identity_defaults() {
        assert_eq!(
            ValueTypeName::QUATF.default_value(),
            Some(Value::Quatf(gf::Quatf::IDENTITY))
        );
        assert_eq!(
            ValueTypeName::QUATH.default_value(),
            Some(Value::Quath(gf::Quath::IDENTITY))
        );
        assert_eq!(
            ValueTypeName::MATRIX4D.default_value(),
            Some(Value::Matrix4d(gf::Matrix4d::IDENTITY))
        );
        assert_eq!(
            ValueTypeName::FRAME4D.default_value(),
            Some(Value::Matrix4d(gf::Matrix4d::IDENTITY))
        );
        assert_eq!(ValueTypeName::FLOAT3.default_value(), Some(Value::vec3f(0.0, 0.0, 0.0)));
        assert_eq!(
            ValueTypeName::FLOAT3_ARRAY.default_value(),
            Some(Value::Vec3fVec(Vec::new()))
        );
        assert_eq!(
            ValueTypeName::TOKEN.default_value(),
            Some(Value::Token(tf::Token::default()))
        );
        assert_eq!(
            ValueTypeName::TIME_CODE.default_value(),
            Some(Value::TimeCode(TimeCode(0.0)))
        );
    }

    #[test]
    fn can_represent_exact() {
        assert!(ValueTypeName::COLOR3F.can_represent(&Value::vec3f(1.0, 0.0, 0.0)));
        assert!(!ValueTypeName::COLOR3F.can_represent(&Value::vec3d(1.0, 0.0, 0.0)));
        assert!(!ValueTypeName::COLOR3F.can_represent(&Value::ValueBlock));
        assert!(!ValueTypeName::from("foo").can_represent(&Value::Int(1)));
        assert!(ValueTypeName::OPAQUE.can_represent(&Value::Opaque));
    }

    #[test]
    fn coerce_numeric() {
        assert_eq!(ValueTypeName::FLOAT.coerce(Value::Int(4)), Ok(Value::Float(4.0)));
        assert_eq!(ValueTypeName::FLOAT.coerce(Value::Float(4.0)), Ok(Value::Float(4.0)));
        assert_eq!(
            ValueTypeName::INT.coerce(Value::String("x".into())),
            Err(ValueTypeError::Mismatch {
                expected: tf::Token::new("int"),
                actual: ValueKind::String,
            })
        );
        assert!(matches!(
            ValueTypeName::UCHAR.coerce(Value::Int(1000)),
            Err(ValueTypeError::Cast(CastError::OutOfRange { .. }))
        ));
    }

    #[test]
    fn coerce_block_ok() {
        assert_eq!(ValueTypeName::FLOAT.coerce(Value::ValueBlock), Ok(Value::ValueBlock));
        assert_eq!(ValueTypeName::OPAQUE.coerce(Value::ValueBlock), Ok(Value::ValueBlock));
        assert_eq!(
            ValueTypeName::from("foo").coerce(Value::ValueBlock),
            Ok(Value::ValueBlock)
        );
        assert_eq!(
            ValueTypeName::from("foo").coerce(Value::Int(1)),
            Err(ValueTypeError::Unregistered {
                type_name: tf::Token::new("foo"),
            })
        );
        assert_eq!(
            ValueTypeName::from("").coerce(Value::Int(1)),
            Err(ValueTypeError::Empty)
        );
    }

    #[test]
    fn coerce_rejects_opaque() {
        assert_eq!(ValueTypeName::OPAQUE.coerce(Value::Opaque), Err(ValueTypeError::Opaque));
        assert_eq!(ValueTypeName::GROUP.coerce(Value::Int(1)), Err(ValueTypeError::Opaque));
        assert_eq!(
            ValueTypeName::OPAQUE.validate(&Value::Opaque),
            Err(ValueTypeError::Opaque)
        );
    }

    #[test]
    fn validate_no_cast() {
        assert_eq!(ValueTypeName::FLOAT.validate(&Value::Float(1.0)), Ok(()));
        assert_eq!(ValueTypeName::FLOAT.validate(&Value::ValueBlock), Ok(()));
        assert_eq!(
            ValueTypeName::FLOAT.validate(&Value::Int(1)),
            Err(ValueTypeError::Mismatch {
                expected: tf::Token::new("float"),
                actual: ValueKind::Int,
            })
        );
        assert_eq!(
            ValueTypeName::from("foo").validate(&Value::Int(1)),
            Err(ValueTypeError::Unregistered {
                type_name: tf::Token::new("foo"),
            })
        );
        assert_eq!(ValueTypeName::from("foo").validate(&Value::ValueBlock), Ok(()));
    }

    #[test]
    fn agrees_with_underlying() {
        assert!(ValueTypeName::COLOR3F.agrees_with(&ValueTypeName::FLOAT3));
        assert!(ValueTypeName::FLOAT3.agrees_with(&ValueTypeName::COLOR3F));
        assert!(ValueTypeName::COLOR3F_ARRAY.agrees_with(&ValueTypeName::FLOAT3_ARRAY));
        assert!(ValueTypeName::COLOR3F.agrees_with(&ValueTypeName::COLOR3F));
        assert!(ValueTypeName::COLOR3F.agrees_with(&find("ColorFloat")));
        assert!(!ValueTypeName::COLOR3F.agrees_with(&ValueTypeName::POINT3F));
        assert!(!ValueTypeName::COLOR3F.agrees_with(&ValueTypeName::COLOR3D));
        assert!(!ValueTypeName::COLOR3F.agrees_with(&ValueTypeName::FLOAT3_ARRAY));
        assert!(ValueTypeName::from("foo").agrees_with(&ValueTypeName::from("foo")));
        assert!(!ValueTypeName::from("foo").agrees_with(&ValueTypeName::FLOAT));
    }

    #[test]
    fn all_types_count() {
        assert_eq!(ValueTypeName::all().count(), 172);
        assert_eq!(STANDARD.len(), 110);
        assert_eq!(LEGACY.len(), 62);
        let spellings: HashSet<&str> = ValueTypeName::all().map(ValueTypeName::as_str).collect();
        assert_eq!(spellings.len(), 172, "every row has its own spelling");
    }

    #[test]
    fn constants_match_find() {
        for row in ValueTypeName::all() {
            let found = find(row.as_str());
            assert_eq!(&found, row);
            assert_eq!(found.as_str(), row.as_str());
            assert!(row.has_alias(row.as_str()));
        }
        assert_eq!(ValueTypeName::COLOR3F.as_str(), "color3f");
        assert_eq!(ValueTypeName::TEX_COORD2H_ARRAY.as_str(), "texCoord2h[]");
        assert_eq!(ValueTypeName::PATH_EXPRESSION.kind(), Some(ValueKind::PathExpression));
    }

    #[test]
    fn legacy_aliases_resolve() {
        assert_eq!(find("Color").serialization_name(), tf::Token::new("color3d"));
        assert_eq!(find("Vec3f"), ValueTypeName::FLOAT3);
        assert_eq!(find("PointFloat").role(), Some(Role::Point));
        assert_eq!(find("NormalFloat"), ValueTypeName::NORMAL3F);
        assert_eq!(find("VectorFloat"), ValueTypeName::VECTOR3F);
        assert_eq!(find("Frame"), ValueTypeName::FRAME4D);
        assert_eq!(find("Transform").role(), Some(Role::Transform));
    }

    /// The vendor conformance data for §6.2–§6.5 of the core spec.
    #[derive(serde::Deserialize)]
    struct FoundationalTypes {
        named_types: Vec<String>,
        semantic_aliases: Vec<(String, String, String)>,
    }

    fn foundational_types() -> FoundationalTypes {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/vendor/core-spec-supplemental-release_dec2025/data_types/tests/foundational_data_types.json"
        );
        let text = std::fs::read_to_string(path).expect("vendor data readable");
        serde_json::from_str(&text).expect("vendor data parses")
    }

    /// The core spec's role spellings, lowercase where C++ capitalizes.
    fn spec_role(role: Role) -> &'static str {
        match role {
            Role::Point => "point",
            Role::Normal => "normal",
            Role::Vector => "vector",
            Role::Color => "color",
            Role::Frame => "frame",
            Role::TextureCoordinate => "texCoord",
            Role::Group => "group",
            Role::Transform | Role::PointIndex | Role::EdgeIndex | Role::FaceIndex => {
                panic!("{role} is a legacy role outside the core spec")
            }
        }
    }

    #[test]
    fn spec_named_types() {
        let names: BTreeSet<String> = foundational_types().named_types.into_iter().collect();
        for name in &names {
            // `dictionary` and the list ops are metadata value types, carried by
            // `Value::Dictionary` and `ListOp`, not attribute value types.
            if name == "dictionary" || name.starts_with("listop<") {
                continue;
            }
            let found = find(name);
            assert_eq!(found.as_str(), name);
            assert_eq!(found.is_array(), name.ends_with("[]"), "{name}");
            assert_eq!(found.role(), None, "{name}");
            if found.is_array() {
                let scalar = found.scalar_type().expect("array has a scalar");
                assert_eq!(scalar.array_type(), Some(found.clone()), "{name}");
            } else if name != "opaque" {
                let array = found.array_type().unwrap_or_else(|| panic!("{name} has an array"));
                assert!(names.contains(array.as_str()), "{name}[] is listed too");
            }
        }
    }

    #[test]
    fn spec_semantic_aliases() {
        let expected: BTreeSet<(String, String, String)> = foundational_types().semantic_aliases.into_iter().collect();
        let actual: BTreeSet<(String, String, String)> = STANDARD
            .iter()
            .filter_map(|row| {
                let role = row.role()?;
                let (kind, role) = (row.kind().expect("standard rows are registered"), role);
                let underlying = preferred_spelling(kind, None).expect("every alias has an underlying type");
                Some((
                    row.as_str().to_owned(),
                    underlying.to_owned(),
                    spec_role(role).to_owned(),
                ))
            })
            .collect();
        for (alias, underlying, _) in &actual {
            assert!(
                find(alias).agrees_with(&find(underlying)),
                "{alias} agrees with {underlying}"
            );
            assert_ne!(find(alias), find(underlying), "{alias} is not {underlying}");
        }
        assert_eq!(actual, expected);
    }
}
