//! Reading and authoring a schema's token-valued enums as values.
//!
//! A schema declares a closed set of tokens for a property — an axis, a
//! subdivision scheme, an interpolation — and a family hand-writes the enum
//! that names them. This is what carries such an enum through
//! [`sdf::Value`](openusd::sdf::Value), in both directions.

/// Bidirectional conversion between a token-valued schema enum and
/// [`Value`], both delegating to the enum's `as_token` / `from_token`. `From`
/// authors a [`Value::Token`] so the enum passes straight to
/// [`Attribute::set`](openusd::usd::Attribute::set) (`attr.set(Axis::X)?`), and
/// `TryFrom` decodes one (these attributes are `token`-valued, so only a
/// `Value::Token` decodes) so [`Attribute::get`](openusd::usd::Attribute::get)
/// extracts it directly (`attr.get::<Axis>()?`). Each enum must expose
/// `fn as_token(self) -> &'static str` and
/// `fn from_token(impl Into<tf::Token>) -> Option<Self>`.
macro_rules! impl_token_value {
    ($($ty:ty),+ $(,)?) => {$(
        impl From<$ty> for $crate::openusd::sdf::Value {
            fn from(value: $ty) -> Self {
                $crate::openusd::sdf::Value::Token(value.as_token().into())
            }
        }

        impl TryFrom<$crate::openusd::sdf::Value> for $ty {
            type Error = $crate::openusd::sdf::CastError;

            fn try_from(value: $crate::openusd::sdf::Value) -> Result<Self, Self::Error> {
                match &value {
                    $crate::openusd::sdf::Value::Token(s) => <$ty>::from_token(s.as_str()),
                    _ => None,
                }
                .ok_or_else(|| $crate::openusd::sdf::CastError::TypeMismatch {
                    target: stringify!($ty),
                    actual: (&value).into(),
                })
            }
        }
    )+};
}

pub(crate) use impl_token_value;
