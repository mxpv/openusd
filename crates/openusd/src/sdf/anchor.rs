//! Anchoring an asset path at the layer that authors it (C++
//! `SdfComputeAssetPathRelativeToLayer`, `layerUtils.cpp`), and the package
//! listings its rules for search paths read.
//!
//! [`absolute_path_with`] runs the rules over a [`Listing`]. Composition
//! answers it from the packages the layer store holds ([`HeldListing`]),
//! which the store records beside each layer read from a package, so a
//! prim-index build reads no asset. Every other caller lists the packages it
//! needs from their assets ([`ReadListing`], through [`absolute_path_at`]).

use std::collections::HashMap;
use std::rc::Rc;

use super::{Layer, LayerRegistry, LayerStore, PackageFiles, PackageListings, StoreRead};
use crate::{ar, usdz};

/// What the anchoring rules read of a package: its listing.
pub(crate) trait Listing {
    /// What `package` holds, or `None` for a package that cannot be opened,
    /// which holds nothing to anchor at.
    fn files(&mut self, package: &str) -> Option<Rc<PackageFiles>>;
}

/// A [`Listing`] of the packages a layer store holds.
///
/// A layer read from a package holds the packages it lies in and those its
/// innermost package's root descends through ([`held_packages`]), the only
/// packages the anchoring rules read for a path that layer authors.
pub(crate) struct HeldListing<'a, 'r>(pub(crate) &'a StoreRead<'r>);

impl Listing for HeldListing<'_, '_> {
    fn files(&mut self, package: &str) -> Option<Rc<PackageFiles>> {
        let held = self.0.package(package);
        debug_assert!(
            held.is_some(),
            "a live layer holds every package a path it authors is anchored in: {package}"
        );
        held?.files().cloned()
    }
}

/// A [`Listing`] read from the packages' assets, each listed once, where
/// `store`, when one is given, holds no listing: a package a live layer
/// holds answers with the listing held, a failed one included.
pub(crate) struct ReadListing<'a> {
    resolver: &'a dyn ar::Resolver,
    store: Option<&'a LayerStore>,
    listed: HashMap<String, Option<Rc<PackageFiles>>>,
    /// Shares one open of each package among the listings, begun at the
    /// first that reads an asset.
    scope: Option<ar::CacheScope>,
}

impl<'a> ReadListing<'a> {
    /// A listing through `resolver`, reading what `store` holds first.
    pub(crate) fn new(resolver: &'a dyn ar::Resolver, store: Option<&'a LayerStore>) -> Self {
        Self {
            resolver,
            store,
            listed: HashMap::new(),
            scope: None,
        }
    }
}

impl Listing for ReadListing<'_> {
    fn files(&mut self, package: &str) -> Option<Rc<PackageFiles>> {
        if let Some(files) = self.listed.get(package) {
            return files.clone();
        }
        let held = self
            .store
            .and_then(|store| Some(store.read().ok()?.package(package)?.files().cloned()));
        let files = held.unwrap_or_else(|| {
            self.scope.get_or_insert_with(ar::CacheScope::begin);
            LayerRegistry::list_package(self.resolver, package).map(Rc::new)
        });
        self.listed.insert(package.to_owned(), files.clone());
        files
    }
}

/// `asset_path`, authored in a layer anchored at `anchor`, as an identifier
/// through `resolver` (C++ `SdfComputeAssetPathRelativeToLayer`), each
/// package the rules read listed from its asset. An empty path and an
/// anonymous layer identifier are returned as they are, and `anchor` is
/// `None` for an anonymous layer.
pub(crate) fn absolute_path_at(
    resolver: &dyn ar::Resolver,
    anchor: Option<&ar::ResolvedPath>,
    asset_path: &str,
) -> String {
    absolute_path_with(resolver, anchor, asset_path, &mut ReadListing::new(resolver, None))
}

/// [`absolute_path_at`] over the package listings `listing` answers.
///
/// A relative path authored in a packaged layer (`pkg.usdz[dir/layer.usda]`)
/// or in a package's root (`pkg.usdz`, anchored beside the package's root
/// layer) stays in the package. One that opens with `.` is anchored beside
/// the layer. A search path, any other relative path, is anchored there when
/// the package holds that entry, else beside the package's root layer when
/// the package holds that one, else as the resolver anchors it at the
/// package. A package's root layer here is its first entry, of any type,
/// followed into a package nested there. Every other path goes through
/// [`ar::create_identifier`].
//
// TODO: format arguments (`:SDF_FORMAT_ARGS:`) are not split from the path
// before it is anchored, nor joined back after.
//
// TODO(perf): the default resolver canonicalizes through the filesystem, so
// each call runs a `canonicalize`. Cache identifiers per `(anchor location,
// asset_path)` within an `ar::CacheScope`; `PackageFiles::files` is
// searched linearly per search path.
pub(crate) fn absolute_path_with(
    resolver: &dyn ar::Resolver,
    anchor: Option<&ar::ResolvedPath>,
    asset_path: &str,
    listing: &mut dyn Listing,
) -> String {
    if asset_path.is_empty() || Layer::is_anonymous_identifier(asset_path) {
        return asset_path.to_owned();
    }
    // An authored package-relative path anchors its package by these rules
    // and keeps the entry it names.
    if let Some((package, entry)) = ar::split_authored_package(asset_path) {
        let package = absolute_path_with(resolver, anchor, &package, listing);
        return ar::nest_packaged_path(&package, &entry);
    }
    // A URI the resolver handles names its asset whole, wherever it is
    // authored: C++ hands it that resolver once the packaged path it would
    // otherwise name fails to resolve.
    if let Some(anchor) = anchor.map(|anchor| anchor.to_string_lossy())
        && ar::is_relative_path(asset_path)
        && !ar::is_uri(resolver, asset_path)
    {
        // C++ `Sdf_IsPackageOrPackagedLayer`: the anchor is a package itself,
        // whose root layer the path is authored in, a nested one
        // (`outer.usdz[inner.usdz]`) included, or a layer inside a package.
        // A layer anchored at a package is its root layer already, so the
        // root's fallback is the same lookup.
        let (site, at_root) = if LayerRegistry::is_package(resolver.extension(&anchor)) {
            (Some(expand_root(listing, anchor.into_owned())), true)
        } else {
            (ar::split_package_relative_path_inner(&anchor), false)
        };
        if let Some((package, layer)) = site {
            let entry = ar::join_packaged_path(parent(&layer), asset_path);
            // C++ tells a search path by its first character alone.
            if asset_path.starts_with('.') || holds(listing, &package, &entry) {
                return ar::nest_packaged_path(&package, &entry);
            }
            if !at_root {
                let (package, root) = expand_root(listing, package);
                let entry = ar::join_packaged_path(parent(&root), asset_path);
                if holds(listing, &package, &entry) {
                    return ar::nest_packaged_path(&package, &entry);
                }
            }
        }
    }
    ar::create_identifier(resolver, asset_path, anchor)
}

/// The packages a layer read from `real_path` holds while it lives,
/// outermost first, each with its listing: those it lies in, the one it is
/// anchored at when that is a package, and those the innermost one's root
/// descends through. These are the packages [`absolute_path_with`] reads
/// for a path the layer authors.
pub(crate) fn held_packages(real_path: &str, listing: &mut dyn Listing) -> PackageListings {
    let innermost = if is_package(real_path) {
        real_path.to_owned()
    } else if let Some((package, _)) = ar::split_package_relative_path_inner(real_path) {
        package
    } else {
        return Vec::new();
    };
    let (innermost, _) = expand_root(listing, innermost);
    let mut packages = ar::enclosing_packages(&innermost);
    packages.push(innermost);
    packages
        .into_iter()
        .map(|package| {
            let files = listing.files(&package);
            (package, files)
        })
        .collect()
}

/// `package` paired with its root layer, its first entry followed into each
/// package nested there, the pair naming that innermost package (C++
/// `_ExpandPackagePath`). A package that holds nothing has an empty root.
fn expand_root(listing: &mut dyn Listing, mut package: String) -> (String, String) {
    let mut root = first_entry(listing, &package);
    for _ in 0..usdz::MAX_NESTING {
        if !is_package(&root) {
            break;
        }
        package = ar::nest_packaged_path(&package, &root);
        root = first_entry(listing, &package);
    }
    (package, root)
}

/// The root layer of `package` as its format names it from the package's
/// listing ([`FileFormat::package_root`](super::FileFormat::package_root)),
/// or empty.
fn first_entry(listing: &mut dyn Listing, package: &str) -> String {
    let Some(files) = listing.files(package) else {
        return String::new();
    };
    super::layer_registry::builtin_format(ar::extension(package))
        .and_then(|format| format.package_root(&files))
        .unwrap_or_default()
        .to_owned()
}

/// Whether `package` holds `entry`: whether the packaged path resolves.
fn holds(listing: &mut dyn Listing, package: &str, entry: &str) -> bool {
    listing
        .files(package)
        .is_some_and(|held| held.files.iter().any(|stored| stored == entry))
}

/// The directory part of a packaged path, empty at the package's root.
fn parent(path: &str) -> &str {
    path.rsplit_once('/').map_or("", |(dir, _)| dir)
}

/// Whether `path` names a package by its extension.
fn is_package(path: &str) -> bool {
    LayerRegistry::is_package(ar::extension(path))
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::io;

    use super::*;
    use crate::Result;
    use crate::usdz::tests::package;

    /// A package of `entries` written in a new directory, and its canonical
    /// path.
    fn package_at(entries: &[(&str, &[u8])]) -> Result<(tempfile::TempDir, String)> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("pkg.usdz");
        fs::write(&path, package(entries))?;
        let path = path.canonicalize()?.to_string_lossy().into_owned();
        Ok((dir, path))
    }

    /// A search path is anchored beside the packaged layer that authors it
    /// when the package holds that entry.
    #[test]
    fn search_path_in_layer() -> Result<()> {
        let layer: &[u8] = b"#usda 1.0
";
        let (_dir, pkg) = package_at(&[("dir/root.usda", layer), ("dir/x.usda", layer), ("x.usda", layer)])?;
        let anchor = ar::ResolvedPath::new(ar::join_package_relative_path(&pkg, "dir/root.usda"));
        let resolver = ar::DefaultResolver::new();
        assert_eq!(
            absolute_path_at(&resolver, Some(&anchor), "x.usda"),
            ar::join_package_relative_path(&pkg, "dir/x.usda")
        );
        Ok(())
    }

    /// A search path the authoring layer's directory lacks is anchored
    /// beside the package's root layer, its first entry.
    #[test]
    fn search_path_at_root() -> Result<()> {
        let layer: &[u8] = b"#usda 1.0
";
        let (_dir, pkg) = package_at(&[
            ("dir/root.usda", layer),
            ("sub/layer.usda", layer),
            ("dir/x.usda", layer),
        ])?;
        let anchor = ar::ResolvedPath::new(ar::join_package_relative_path(&pkg, "sub/layer.usda"));
        let resolver = ar::DefaultResolver::new();
        assert_eq!(
            absolute_path_at(&resolver, Some(&anchor), "x.usda"),
            ar::join_package_relative_path(&pkg, "dir/x.usda")
        );
        // A path that opens with `.` stays beside the layer, held or not.
        assert_eq!(
            absolute_path_at(&resolver, Some(&anchor), "./x.usda"),
            ar::join_package_relative_path(&pkg, "sub/x.usda")
        );
        Ok(())
    }

    /// A search path the package does not hold goes to the resolver, which
    /// finds it beside the package file.
    #[test]
    fn search_path_beside_package() -> Result<()> {
        let (dir, pkg) = package_at(&[(
            "root.usda",
            b"#usda 1.0
",
        )])?;
        fs::write(
            dir.path().join("x.usda"),
            "#usda 1.0
",
        )?;
        let anchor = ar::ResolvedPath::new(ar::join_package_relative_path(&pkg, "root.usda"));
        let resolver = ar::DefaultResolver::new();
        let beside = dir.path().join("x.usda").canonicalize()?;
        assert_eq!(
            absolute_path_at(&resolver, Some(&anchor), "x.usda"),
            beside.to_string_lossy()
        );
        Ok(())
    }

    /// A path climbing out of a packaged layer's directory names a
    /// `/`-separated, `..`-collapsed entry name, the spelling the archive is
    /// keyed by.
    #[test]
    fn in_package_anchor_crosses_dirs() {
        let anchor = ar::ResolvedPath::new("pkg.usdz[geom/scene.usda]");
        assert_eq!(
            absolute_path_at(&ar::DefaultResolver::new(), Some(&anchor), "../tex/foo.usda"),
            "pkg.usdz[tex/foo.usda]",
        );
    }

    /// The package rules apply whatever the resolver: one that knows nothing
    /// of packages still has a packaged layer's paths anchored inside its
    /// package.
    #[test]
    fn custom_resolver_nests() {
        let resolver = ar::tests::TestResolver(|| Err(io::ErrorKind::NotFound.into()));
        let packaged = ar::ResolvedPath::new("pkg.usdz[geom/scene.usda]");
        assert_eq!(
            absolute_path_at(&resolver, Some(&packaged), "./tex/a.png"),
            "pkg.usdz[geom/tex/a.png]"
        );
        let package = ar::ResolvedPath::new("pkg.usdz");
        assert_eq!(
            absolute_path_at(&resolver, Some(&package), "./tex/a.png"),
            "pkg.usdz[tex/a.png]"
        );
        // A package nested in a package is a package too, not a layer inside
        // the outer one.
        let nested = ar::ResolvedPath::new("outer.usdz[inner.usdz]");
        assert_eq!(
            absolute_path_at(&resolver, Some(&nested), "./tex/a.png"),
            "outer.usdz[inner.usdz[tex/a.png]]"
        );
    }

    /// A URI the resolver handles reaches it whole from a packaged layer,
    /// while a relative path there still anchors inside the package.
    #[test]
    fn package_uri_whole() {
        /// A resolver for `https` URIs that identifies a path as spelled and
        /// resolves only the URIs it owns.
        struct Web;
        impl ar::Resolver for Web {
            fn create_identifier(&self, asset_path: &str, _anchor: Option<&ar::ResolvedPath>) -> String {
                asset_path.to_owned()
            }
            fn resolve(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
                ar::is_uri(self, asset_path).then(|| ar::ResolvedPath::new(asset_path))
            }
            fn resolve_for_new_asset(&self, _asset_path: &str) -> Option<ar::ResolvedPath> {
                None
            }
            fn open_asset(&self, _resolved_path: &ar::ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
                Err(io::ErrorKind::NotFound.into())
            }
            fn uri_schemes(&self) -> &[&str] {
                &["https"]
            }
        }

        let packaged = ar::ResolvedPath::new("pkg.usdz[dir/root.usda]");
        let uri = absolute_path_at(&Web, Some(&packaged), "HTTPS://host/tex.png");
        assert_eq!(uri, "HTTPS://host/tex.png");
        assert!(ar::Resolver::resolve(&Web, &uri).is_some());
        assert_eq!(
            absolute_path_at(&Web, Some(&packaged), "./tex.png"),
            "pkg.usdz[dir/tex.png]"
        );
        assert!(
            !ar::is_uri(&ar::DefaultResolver::new(), "https://host/tex.png"),
            "the default resolver handles no URI scheme"
        );
    }
}
