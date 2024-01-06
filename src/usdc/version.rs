//! Version helper.

use std::fmt;

/// Helper structure to compare file versions.
#[derive(Default, Debug, Copy, Clone, Eq, PartialEq)]
pub struct Version {
    pub major: u8,
    pub minor: u8,
    pub patch: u8,
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// Make version helper.
pub const fn version(major: u8, minor: u8, patch: u8) -> Version {
    Version {
        major,
        minor,
        patch,
    }
}

impl Version {
    /// Return true if `other` has the same major version as this, and has a
    /// lesser or same minor version. Patch version irrelevant, since the
    /// versioning scheme specifies that patch level changes are forward-compatible.
    /// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.h#L547>
    #[inline]
    pub fn can_read(self, file_ver: Version) -> bool {
        file_ver.major == self.major && file_ver.minor <= self.minor
    }

    #[inline]
    pub fn as_u32(self) -> u32 {
        (self.major as u32) << 16 | (self.minor as u32) << 8 | self.patch as u32
    }

    #[inline]
    pub fn is_valid(self) -> bool {
        self.as_u32() != 0
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.as_u32().cmp(&other.as_u32()))
    }
}

use super::Bootstrap;

impl From<Bootstrap> for Version {
    fn from(boot: Bootstrap) -> Self {
        version(boot.version[0], boot.version[1], boot.version[2])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_cmp() {
        assert!(version(0, 4, 0) != version(0, 4, 1));
        assert!(version(0, 4, 0) == version(0, 4, 0));
        assert!(version(0, 4, 0) < version(0, 10, 0));
    }

    #[test]
    fn test_from_bootstrap() {
        let mut boot = Bootstrap::default();
        boot.version[0] = 1;
        boot.version[1] = 2;
        boot.version[2] = 3;

        assert_eq!(Version::from(boot), version(1, 2, 3));
    }

    #[test]
    fn test_is_valid() {
        let version = version(1, 1, 1);
        assert!(version.is_valid());

        let version = Version::default();
        assert!(!version.is_valid());
    }
}
