//! The `uiHints` dictionary a prim or property carries for user interfaces,
//! and the core fields it supersedes.

use openusd::Result;
use openusd::sdf;
use openusd::usd::{self, StageAuthoringError};

use hint_keys::{DISPLAY_GROUP, DISPLAY_NAME, HIDDEN, SHOWN_IF, UI_HINTS};

/// The UI hints of a prim, attribute or relationship, read from and written
/// to its `uiHints` dictionary (C++ `UsdUIObjectHints`,
/// `UsdUIPropertyHints`).
///
/// Each hint is a key of the dictionary. A hint the dictionary holds with a
/// value of another type reads as absent, as C++ `GetMetadataByDictKey`
/// fails on one. Where a core field carries the same hint (`displayName`,
/// `hidden`, `displayGroup`), it answers for an absent key, and a setter
/// writes it too, as C++ does under its default `USDUI_WRITE_LEGACY_UI_HINTS`.
#[derive(Debug, Clone, PartialEq)]
pub struct Hints<O> {
    object: O,
}

impl<O: usd::Object> Hints<O> {
    /// The hints of `object`.
    pub fn new(object: O) -> Self {
        Self { object }
    }

    /// The object the hints are read from (C++ `GetObject`).
    pub fn object(&self) -> &O {
        &self.object
    }

    /// The object the hints are read from, taken back.
    pub fn into_object(self) -> O {
        self.object
    }

    /// The name a user interface shows for the object, `None` where neither
    /// the hint nor the `displayName` field is authored (C++
    /// `UsdUIObjectHints::GetDisplayName`).
    pub fn display_name(&self) -> Result<Option<String>> {
        match self.hint(DISPLAY_NAME, sdf::Value::try_as_string)? {
            Some(name) => Ok(Some(name)),
            None => self.object.display_name(),
        }
    }

    /// Author the display name hint, and the `displayName` field with it
    /// (C++ `UsdUIObjectHints::SetDisplayName`). These are two layer edits,
    /// and when the second fails the first stays committed.
    pub fn set_display_name(self, name: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_with_field(
            DISPLAY_NAME,
            sdf::FieldKey::DisplayName,
            sdf::Value::String(name.into()),
        )
    }

    /// Whether the object is hidden, `false` where neither the hint nor the
    /// `hidden` field says so (C++ `UsdUIObjectHints::GetHidden`).
    pub fn is_hidden(&self) -> Result<bool> {
        match self.hint(HIDDEN, sdf::Value::try_as_bool)? {
            Some(hidden) => Ok(hidden),
            None => self.object.is_hidden(),
        }
    }

    /// Author the hidden hint, and the `hidden` field with it (C++
    /// `UsdUIObjectHints::SetHidden`). These are two layer edits, and when
    /// the second fails the first stays committed.
    pub fn set_hidden(self, hidden: bool) -> Result<Self, StageAuthoringError> {
        self.set_with_field(HIDDEN, sdf::FieldKey::Hidden, sdf::Value::Bool(hidden))
    }

    /// The hint at `key_path` decoded by `decode`, `None` where it is absent
    /// or holds a value of another type.
    fn hint<T>(&self, key_path: &str, decode: fn(sdf::Value) -> Option<T>) -> Result<Option<T>> {
        Ok(self.object.metadata_by_key(UI_HINTS, key_path)?.and_then(decode))
    }

    /// Author `value` as the hint at `key_path`.
    fn set_hint(self, key_path: &str, value: sdf::Value) -> Result<Self, StageAuthoringError> {
        let object = self.object.set_metadata_by_key(UI_HINTS, key_path, value)?;
        Ok(Self { object })
    }

    /// Author `value` as the hint at `key_path` and then as the core `field`
    /// that carries the same hint.
    fn set_with_field(
        self,
        key_path: &str,
        field: sdf::FieldKey,
        value: sdf::Value,
    ) -> Result<Self, StageAuthoringError> {
        let object = self.set_hint(key_path, value.clone())?.object;
        Ok(Self {
            object: object.set_metadata(field.as_str(), value)?,
        })
    }
}

impl<O: usd::Property> Hints<O> {
    /// The `:`-nested group the property is shown in, `None` where neither
    /// the hint nor the `displayGroup` field is authored (C++
    /// `UsdUIPropertyHints::GetDisplayGroup`).
    pub fn display_group(&self) -> Result<Option<String>> {
        match self.hint(DISPLAY_GROUP, sdf::Value::try_as_string)? {
            Some(group) => Ok(Some(group)),
            None => self.object.display_group(),
        }
    }

    /// Author the display group hint, and the `displayGroup` field with it
    /// (C++ `UsdUIPropertyHints::SetDisplayGroup`). These are two layer
    /// edits, and when the second fails the first stays committed.
    pub fn set_display_group(self, group: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_with_field(
            DISPLAY_GROUP,
            sdf::FieldKey::DisplayGroup,
            sdf::Value::String(group.into()),
        )
    }

    /// The expression that decides whether the property is shown (C++
    /// `UsdUIPropertyHints::GetShownIf`).
    pub fn shown_if(&self) -> Result<Option<String>> {
        self.hint(SHOWN_IF, sdf::Value::try_as_string)
    }

    /// Author the shown-if expression hint (C++
    /// `UsdUIPropertyHints::SetShownIf`).
    pub fn set_shown_if(self, expr: impl Into<String>) -> Result<Self, StageAuthoringError> {
        self.set_hint(SHOWN_IF, sdf::Value::String(expr.into()))
    }
}

/// The keys of the `uiHints` dictionary (C++ `UsdUIHintKeys`).
pub mod hint_keys {
    /// The dictionary metadata field the hints live in.
    pub const UI_HINTS: &str = "uiHints";
    /// The name a user interface shows for the object.
    pub const DISPLAY_NAME: &str = "displayName";
    /// The `:`-nested group a property is shown in.
    pub const DISPLAY_GROUP: &str = "displayGroup";
    /// Whether the object is hidden.
    pub const HIDDEN: &str = "hidden";
    /// The expression that decides whether a property is shown.
    pub const SHOWN_IF: &str = "shownIf";
    /// The named values an attribute offers.
    pub const VALUE_LABELS: &str = "valueLabels";
    /// The order the value labels are shown in.
    pub const VALUE_LABELS_ORDER: &str = "valueLabelsOrder";
    /// Whether each display group on a prim starts expanded.
    pub const DISPLAY_GROUPS_EXPANDED: &str = "displayGroupsExpanded";
    /// The expression that decides whether each display group is shown.
    pub const DISPLAY_GROUPS_SHOWN_IF: &str = "displayGroupsShownIf";
}
