//! Scene description foundations.

use std::fmt;

use strum::{Display, EnumCount, FromRepr};

/// An enum that specifies the type of an object.
/// Objects are entities that have fields and are addressable by path.
#[repr(u32)]
#[derive(Default, Clone, Copy, PartialEq, Eq, FromRepr, EnumCount, Display)]
pub enum SpecType {
    // The unknown type has a value of 0 so that SdfSpecType() is unknown.
    #[default]
    Unknown = 0,

    // Real concrete types
    Attribute = 1,
    Connection = 2,
    Expression = 3,
    Mapper = 4,
    MapperArg = 5,
    Prim = 6,
    PseudoRoot = 7,
    Relationship = 8,
    RelationshipTarget = 9,
    Variant = 10,
    VariantSet = 11,
}

/// Placeholder for SdfPath.
// TODO: reimplement this properly.
#[derive(Default, Clone)]
pub struct Path {
    path: String,
    props: Vec<String>,
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.path)?;
        if !self.props.is_empty() {
            write!(f, ".{}", self.props.join(","))?;
        }

        Ok(())
    }
}

impl Path {
    pub fn abs_root_path() -> Self {
        Path {
            path: "/".into(),
            props: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.path.is_empty()
    }

    pub fn append_property(&self, name: &str) -> Self {
        let mut p = self.clone();
        p.props.push(name.to_string());
        p
    }

    pub fn append_element_token(&self, name: &str) -> Self {
        let mut p = self.clone();
        p.path.push('/');
        p.path.push_str(name);

        p
    }
}
