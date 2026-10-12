//! What `UsdGeomSubset` answers beyond its own properties: the subsets of a
//! geometric prim, the families they group into, and whether a family
//! covers the prim's elements the way its type promises.
//!
//! A subset is a `GeomSubset` child of the prim whose elements it indexes.
//! Subsets that share a `familyName` form a family, and the prim says how a
//! family's subsets may share elements in a
//! `subsetFamily:<familyName>:familyType` attribute of its own.

use std::cell::OnceCell;
use std::collections::{BTreeSet, HashSet};
use std::{iter, mem};

use openusd::Result;
use openusd::usd::{self, SchemaBase};
use openusd::{sdf, tf};

use super::curves::non_negative;
use super::{BasisCurves, CurvesSchema, ElementType, ImageableSchema, Mesh, MeshSchema, PointBasedSchema};
use super::{Subset, SubsetSchema, TetMesh, TetMeshSchema, array_len, tokens};
use crate::SchemaError;

/// How the subsets of one family may share the elements of their prim (the
/// `familyType` tokens of C++ `UsdGeomSubset`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum FamilyType {
    /// `"partition"`: every element is in exactly one subset.
    Partition,
    /// `"nonOverlapping"`: an element is in at most one subset.
    NonOverlapping,
    /// `"unrestricted"`: an element may be in any number of subsets.
    #[default]
    Unrestricted,
}

impl FamilyType {
    /// The token this value is written as.
    pub const fn as_token(self) -> &'static str {
        match self {
            Self::Partition => tokens::PARTITION,
            Self::NonOverlapping => tokens::NON_OVERLAPPING,
            Self::Unrestricted => tokens::UNRESTRICTED,
        }
    }

    /// The value `token` names, or `None` where it names none.
    pub fn from_token(token: impl AsRef<str>) -> Option<Self> {
        Some(match token.as_ref() {
            tokens::PARTITION => Self::Partition,
            tokens::NON_OVERLAPPING => Self::NonOverlapping,
            tokens::UNRESTRICTED => Self::Unrestricted,
            _ => return None,
        })
    }
}

sdf::impl_token_value!(FamilyType);

impl Subset {
    /// Define the subset named `subset_name` under `geom` and author its
    /// element type, indices and family name (C++ `CreateGeomSubset`).
    ///
    /// A subset already defined under that name is the one authored on. With
    /// a non-empty `family_name` and a `family_type`, the family's type is
    /// authored on `geom` as [`set_family_type`](Self::set_family_type) does.
    /// The properties, the family type included, are one edit, which follows
    /// the edit that defines a new subset prim.
    pub fn create(
        geom: &impl ImageableSchema,
        subset_name: &str,
        element_type: ElementType,
        indices: &[i32],
        family_name: &str,
        family_type: Option<FamilyType>,
    ) -> Result<Subset> {
        let path = geom.path().append_path(subset_name)?;
        author(geom.prim(), path, element_type, indices, family_name, family_type)
    }

    /// Define a new subset under `geom` and author it as
    /// [`create`](Self::create) does (C++
    /// `CreateUniqueGeomSubset`).
    ///
    /// The subset takes `subset_name` where `geom` has no child of that name,
    /// and otherwise the first of `<subset_name>_1`, `<subset_name>_2`, … that
    /// is free.
    pub fn create_unique(
        geom: &impl ImageableSchema,
        subset_name: &str,
        element_type: ElementType,
        indices: &[i32],
        family_name: &str,
        family_type: Option<FamilyType>,
    ) -> Result<Subset> {
        let taken: BTreeSet<tf::Token> = geom.prim().child_names()?.into_iter().collect();
        let mut name = subset_name.to_string();
        let mut suffix = 0_usize;
        while taken.contains(&tf::Token::from(name.as_str())) {
            suffix += 1;
            name = format!("{subset_name}_{suffix}");
        }
        let path = geom.path().append_path(name.as_str())?;
        author(geom.prim(), path, element_type, indices, family_name, family_type)
    }

    /// Every subset of `geom`, in the order of its children (C++
    /// `GetAllGeomSubsets`).
    ///
    /// A subset is a `GeomSubset` child that is active, loaded, not abstract
    /// and itself a `def` or a `class`, whatever specifier `geom` and its
    /// ancestors have. The children of an instance are instance proxies and
    /// count as none; the subsets are those of its prototype.
    pub fn all(geom: &impl ImageableSchema) -> Result<Vec<Subset>> {
        subsets_of(geom.prim())
    }

    /// The subsets of `geom` with the element type and the family name given,
    /// where `None` admits any (C++ `GetGeomSubsets`).
    ///
    /// The subsets are the ones [`all`](Self::all)
    /// lists. A `family_name` of `Some("")` selects the subsets that name no
    /// family.
    pub fn in_family(
        geom: &impl ImageableSchema,
        element_type: Option<ElementType>,
        family_name: Option<&str>,
    ) -> Result<Vec<Subset>> {
        matching(geom.prim(), element_type.map(ElementType::as_token), family_name)
    }

    /// The names of the families the subsets of `geom` belong to (C++
    /// `GetAllGeomSubsetFamilyNames`). A subset that names no family
    /// contributes none.
    pub fn family_names(geom: &impl ImageableSchema) -> Result<BTreeSet<tf::Token>> {
        let mut names = BTreeSet::new();
        for subset in subsets_of(geom.prim())? {
            if let Some(name) = subset.family_name()?
                && !name.is_empty()
            {
                names.insert(name);
            }
        }
        Ok(names)
    }

    /// Author the type of the family `family_name` on `geom`, in its uniform
    /// `subsetFamily:<family_name>:familyType` attribute (C++
    /// `SetFamilyType`).
    pub fn set_family_type(geom: &impl ImageableSchema, family_name: &str, family_type: FamilyType) -> Result<()> {
        let builder = geom
            .prim()
            .attribute_builder(family_type_attr_name(family_name), sdf::ValueTypeName::TOKEN);
        typing(builder, family_type).build()?;
        Ok(())
    }

    /// The type of the family `family_name` on `geom` (C++ `GetFamilyType`),
    /// [`FamilyType::Unrestricted`] where none is authored or the name is
    /// empty.
    ///
    /// An authored token that names no family type is an error.
    pub fn family_type(geom: &impl ImageableSchema, family_name: &str) -> Result<FamilyType> {
        match family_type_token(geom.prim(), family_name)? {
            Some(token) => Ok(FamilyType::try_from(sdf::Value::Token(token))?),
            None => Ok(FamilyType::Unrestricted),
        }
    }

    /// The elements of `geom` that no subset of the family indexes at `time`,
    /// where `None` is the default time (C++ `GetUnassignedIndices`, whose
    /// `time` defaults to the earliest time: [`usd::TimeCode::EARLIEST`]).
    ///
    /// The family is the subsets of `element_type` named `family_name`, and
    /// an empty name takes every subset of that element type. Faces, points
    /// and tetrahedra come back as ascending indices. Edges and segments come
    /// back as ascending pairs laid end to end: the two point indices of an
    /// edge, lower first, or the curve index and segment index of a segment.
    /// Negative indices in a subset assign nothing. The answer is empty where
    /// the topology the elements are counted from reads no value.
    ///
    /// An element type `geom` has no elements of is
    /// [`SchemaError::UnsupportedSubsetElementType`]: a `Mesh` has faces,
    /// points and edges, a `TetMesh` faces and tetrahedra, a `BasisCurves`
    /// segments, and any other prim none.
    pub fn unassigned_indices(
        geom: &impl ImageableSchema,
        element_type: ElementType,
        family_name: &str,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<Vec<i32>, SchemaError> {
        let time = time.into();
        let prim = geom.prim();
        let Some(elements) = Elements::of(prim, element_type)? else {
            return Err(SchemaError::UnsupportedSubsetElementType {
                prim: prim.path().clone(),
                element_type: element_type.as_token(),
            });
        };
        let subsets = matching(prim, Some(element_type.as_token()), named(family_name))?;

        let topology = elements.at(time)?;
        if !is_paired(element_type) {
            return Ok(Self::unassigned_indices_in(&subsets, topology.count(), time)?);
        }
        let Some(possible) = topology.pairs() else {
            return Ok(Vec::new());
        };
        let ordered = element_type == ElementType::Segment;
        let mut assigned = BTreeSet::new();
        for subset in &subsets {
            assigned.extend(index_pairs(&subset.indices_at(time)?.unwrap_or_default(), ordered));
        }
        Ok(possible.difference(&assigned).flat_map(|&(a, b)| [a, b]).collect())
    }

    /// The indices below `element_count` that none of `subsets` holds at
    /// `time`, where `None` is the default time, in ascending order (C++
    /// `GetUnassignedIndices` over a vector of subsets, whose `time` defaults
    /// to the earliest time: [`usd::TimeCode::EARLIEST`]).
    ///
    /// Negative indices in a subset assign nothing.
    pub fn unassigned_indices_in(
        subsets: &[Subset],
        element_count: usize,
        time: impl Into<Option<usd::TimeCode>>,
    ) -> Result<Vec<i32>> {
        let time = time.into();
        let count = i32::try_from(element_count).unwrap_or(i32::MAX);
        let mut assigned = vec![false; non_negative(count)];
        for subset in subsets {
            for index in subset.indices_at(time)?.unwrap_or_default() {
                if let Some(slot) = usize::try_from(index).ok().and_then(|index| assigned.get_mut(index)) {
                    *slot = true;
                }
            }
        }
        Ok((0..count)
            .zip(assigned)
            .filter_map(|(index, assigned)| (!assigned).then_some(index))
            .collect())
    }

    /// Check that `subsets` hold valid indices into `element_count` elements
    /// and share them as `family_type` allows, at the default time and at
    /// every time one of them has a sample (C++ `ValidateSubsets`).
    ///
    /// The answer lists what is wrong, one sentence for each finding, and is
    /// empty for subsets that are valid; C++ returns `false` and the
    /// sentences joined as its `reason`. The findings are an index two
    /// subsets share unless the family is unrestricted, a partition whose
    /// distinct indices are not `element_count` in number, an index of
    /// `element_count` or more, and a negative index. Subsets whose element
    /// types differ are the one finding reported, without a look at their
    /// indices.
    ///
    /// A negative index is reported as negative only, where the unsigned
    /// comparison in C++ also reports it as past the element count.
    ///
    /// The indices are read as single elements, so this does not validate
    /// edges or segments; [`validate_family`](Self::validate_family) does.
    pub fn validate(subsets: &[Subset], element_count: usize, family_type: FamilyType) -> Result<Vec<String>> {
        let Some((first, rest)) = subsets.split_first() else {
            return Ok(Vec::new());
        };
        let element = element_token(first)?;
        if let Some((subset, found)) = mismatched(rest, element.as_str())? {
            return Ok(vec![format!(
                "Subset at path <{}> has elementType {found}, which does not match '{element}'.",
                subset.path()
            )]);
        }
        let indices_attrs: Vec<_> = subsets.iter().map(|subset| subset.indices_attr()).collect();

        let mut reasons = Vec::new();
        let mut in_family = Seen::new(element_count);
        for time in sampled_times(&indices_attrs)? {
            let at = time_label(time);
            in_family.clear();
            for subset in subsets {
                for index in subset.indices_at(time)?.unwrap_or_default() {
                    if !in_family.insert(index) && family_type != FamilyType::Unrestricted {
                        reasons.push(format!(
                            "Found overlapping index {index} in GeomSubset at path <{}> at time {at}.",
                            subset.path()
                        ));
                    }
                }
            }

            if family_type == FamilyType::Partition && in_family.len() != element_count {
                reasons.push(format!(
                    "Number of unique indices at time {at} does not match the element count {element_count}."
                ));
            }
            if let Some((first, last)) = in_family.bounds() {
                index_bounds(first, last, Some(element_count), &at, &mut reasons);
            }
        }
        Ok(reasons)
    }

    /// Check that the family `family_name` of `geom` holds valid
    /// `element_type` indices and shares the elements as its
    /// [`family_type`](Self::family_type) allows, at the default time and at
    /// every time one of its subsets has a sample (C++ `ValidateFamily`).
    ///
    /// The answer lists what is wrong, one sentence for each finding, and is
    /// empty for a family that is valid; C++ returns `false` and the
    /// sentences joined as its `reason`. The family is every subset named
    /// `family_name`, of any element type, and an empty name takes every
    /// subset of `geom`.
    ///
    /// Two findings are reported alone, without a look at the indices: an
    /// element type `geom` has no elements of, on the terms
    /// [`unassigned_indices`](Self::unassigned_indices) states, and a subset
    /// of the family whose element type is not `element_type`. The rest are:
    ///
    /// - geometry with no elements at the earliest time whose element count
    ///   cannot change over time, or with none at a time the family has
    ///   indices;
    /// - an element two subsets share unless the family is unrestricted, and
    ///   a partition that leaves an element out;
    /// - an index outside the elements, an edge the mesh does not have, an
    ///   odd number of indices where they pair into edges or segments;
    /// - a family with no indices at any time.
    pub fn validate_family(
        geom: &impl ImageableSchema,
        element_type: ElementType,
        family_name: &str,
    ) -> Result<Vec<String>> {
        let prim = geom.prim();
        let element = element_type.as_token();
        let Some(elements) = Elements::of(prim, element_type)? else {
            return Ok(vec![format!("Invalid geom type for elementType {element}.")]);
        };

        let subsets = matching(prim, None, named(family_name))?;
        // The token as authored: one that names no family type is itself
        // malformed data, and is held to the rule every type but
        // `unrestricted` shares, that no element is indexed twice.
        let family_type = family_type_token(prim, family_name)?;
        let family_type = family_type.as_deref().unwrap_or(FamilyType::Unrestricted.as_token());
        let restricted = family_type != FamilyType::Unrestricted.as_token();
        let partition = family_type == FamilyType::Partition.as_token();
        let paired = is_paired(element_type);
        let mut reasons = Vec::new();

        // Edges that cannot be read at the earliest time count as fixed, and
        // their absence is reported once.
        let earliest = elements.at(Some(usd::TimeCode::EARLIEST))?;
        let count_varies = !matches!(earliest, Topology::Edges(None)) && elements.might_vary()?;
        let earliest_count = earliest.count();
        if !count_varies && earliest_count == 0 {
            reasons.push(format!(
                "Unable to determine element count at earliest time for geom <{}>.",
                prim.path()
            ));
        }

        if let Some((subset, found)) = mismatched(&subsets, element)? {
            return Ok(vec![format!(
                "GeomSubset at path <{}> has elementType '{found}', which does not match '{element}'.",
                subset.path()
            )]);
        }
        let indices_attrs: Vec<_> = subsets.iter().map(|subset| subset.indices_attr()).collect();

        let mut has_indices = false;
        let mut in_family = Seen::new(earliest_count);
        // Geometry whose topology does not vary has one topology at the
        // default time and one at every sample time, each read when first
        // needed.
        let mut fixed: [Option<Topology>; 2] = [None, None];
        for time in sampled_times(&indices_attrs)? {
            let at = time_label(time);
            let mut members = Vec::with_capacity(subsets.len());
            for subset in &subsets {
                members.push((subset, subset.indices_at(time)?.unwrap_or_default()));
            }

            // An index repeats freely among pairs: one point is on several
            // edges, one curve has several segments.
            in_family.clear();
            for (subset, indices) in &members {
                if paired && indices.len() % 2 != 0 {
                    reasons.push(format!(
                        "Indices attribute has an odd number of elements in GeomSubset at path <{}> at time {at} \
                         with elementType {element}.",
                        subset.path()
                    ));
                }
                for &index in indices {
                    if !in_family.insert(index) && restricted && !paired {
                        reasons.push(format!(
                            "Found duplicate index {index} in GeomSubset at path <{}> at time {at}.",
                            subset.path()
                        ));
                    }
                }
            }

            // The topology is read at each time for the pairs it holds and,
            // where the element count may change, for that count.
            // Topologically varying geometry may have no elements at some
            // times, which only matters when the family has indices then.
            let read;
            let topology = match (count_varies, paired) {
                (true, _) => {
                    read = elements.at(time)?;
                    &read
                }
                (false, true) => {
                    let slot = &mut fixed[usize::from(time.is_some())];
                    if slot.is_none() {
                        *slot = Some(elements.at(time)?);
                    }
                    let Some(topology) = slot.as_ref() else {
                        continue;
                    };
                    topology
                }
                (false, false) => {
                    read = Topology::Count(earliest_count);
                    &read
                }
            };
            let count = match count_varies {
                true => topology.count(),
                false => earliest_count,
            };
            if in_family.len() > 0 && count_varies && count == 0 {
                reasons.push(format!(
                    "Geometry <{}> has no elements at time {at}, but the \"{family_name}\" GeomSubset family \
                     contains indices.",
                    prim.path()
                ));
            }

            let incomplete =
                || format!("Number of unique indices at time {at} does not match the element count {count}.");
            if paired {
                // An edge is the same edge in either direction, and a segment
                // is its curve and then its place on the curve.
                let ordered = element_type == ElementType::Segment;
                let mut pairs_in_family = BTreeSet::new();
                for (subset, indices) in &members {
                    for pair in index_pairs(indices, ordered) {
                        if !pairs_in_family.insert(pair) && restricted {
                            reasons.push(format!(
                                "Found duplicate {element} ({}, {}) in GeomSubset at path <{}> at time {at}.",
                                pair.0,
                                pair.1,
                                subset.path()
                            ));
                        }
                    }
                }

                topology.report_missing(&pairs_in_family, family_name, &at, &mut reasons);
                if partition
                    && topology
                        .pairs()
                        .is_some_and(|possible| !possible.is_subset(&pairs_in_family))
                {
                    reasons.push(incomplete());
                }
            } else if partition && in_family.len() != count {
                reasons.push(incomplete());
            }

            // A time without indices leaves the family as valid as it was.
            let Some((first, last)) = in_family.bounds() else {
                continue;
            };
            has_indices = true;

            // A pair's indices are bounded by the element they name, checked
            // above: an edge's are point indices and a segment's are its
            // curve and its place on it, and neither counts elements. C++
            // holds an edge's point indices to the number of edges.
            let bound = (!paired).then_some(count);
            index_bounds(first, last, bound, &at, &mut reasons);
        }

        if !has_indices {
            reasons.push("No indices in family at any time.".to_string());
        }
        Ok(reasons)
    }
}

/// The elements of one type on a prim that has them: the pairings of prim
/// type and element type a subset may index (C++ `_ValidateGeomType`), each
/// with the view its topology is read through.
enum Elements {
    /// The faces of a `Mesh`.
    MeshFaces(Mesh),
    /// The points of a `Mesh`.
    MeshPoints(Mesh),
    /// The edges of a `Mesh`'s faces.
    MeshEdges(Mesh),
    /// The surface faces of a `TetMesh`.
    TetFaces(TetMesh),
    /// The tetrahedra of a `TetMesh`.
    Tetrahedra(TetMesh),
    /// The segments of a `BasisCurves`' curves.
    Segments(BasisCurves),
}

impl Elements {
    /// The `element_type` elements of `prim`, or `None` where a prim of its
    /// type has none for a subset to index.
    fn of(prim: &usd::Prim, element_type: ElementType) -> Result<Option<Self>> {
        use ElementType::{Edge, Face, Point, Segment, Tetrahedron};

        Ok(if let Some(mesh) = Mesh::from_prim(prim.clone())? {
            match element_type {
                Face => Some(Self::MeshFaces(mesh)),
                Point => Some(Self::MeshPoints(mesh)),
                Edge => Some(Self::MeshEdges(mesh)),
                Segment | Tetrahedron => None,
            }
        } else if let Some(tets) = TetMesh::from_prim(prim.clone())? {
            match element_type {
                Face => Some(Self::TetFaces(tets)),
                Tetrahedron => Some(Self::Tetrahedra(tets)),
                Point | Edge | Segment => None,
            }
        } else if let Some(curves) = BasisCurves::from_prim(prim.clone())? {
            (element_type == Segment).then_some(Self::Segments(curves))
        } else {
            None
        })
    }

    /// The elements at `time` (C++ `_GetElementCountAtTime`,
    /// `_GetEdgesFromPrim` and `_GetAllPossibleSegments`), from one read of
    /// the topology they are counted from.
    fn at(&self, time: Option<usd::TimeCode>) -> Result<Topology> {
        Ok(match self {
            Self::MeshFaces(mesh) => Topology::Count(mesh.face_count(time)?),
            Self::MeshPoints(mesh) => Topology::Count(array_len(mesh.points_at(time)?)),
            Self::MeshEdges(mesh) => Topology::Edges(edges(mesh, time)?),
            Self::TetFaces(tets) => Topology::Count(array_len(tets.surface_face_vertex_indices_at(time)?)),
            Self::Tetrahedra(tets) => Topology::Count(array_len(tets.tet_vertex_indices_at(time)?)),
            Self::Segments(curves) => {
                let counts = match curves.curve_vertex_counts_at(time)? {
                    Some(counts) => {
                        // Curves whose type, wrap and basis answer no segment
                        // counts have no segments on any curve.
                        let mut segment_counts = curves.segment_counts_of(&counts, time)?;
                        segment_counts.resize(counts.len(), 0);
                        Some(segment_counts)
                    }
                    None => None,
                };
                Topology::Segments(counts, OnceCell::new())
            }
        })
    }

    /// Whether the number of elements may change over time: whether the
    /// topology they are counted from might be time varying.
    fn might_vary(&self) -> Result<bool> {
        let varies = |attr: usd::Attribute| attr.might_be_time_varying();
        match self {
            Self::MeshFaces(mesh) => varies(mesh.face_vertex_counts_attr()),
            Self::MeshPoints(mesh) => varies(mesh.points_attr()),
            Self::MeshEdges(mesh) => {
                Ok(varies(mesh.face_vertex_counts_attr())? || varies(mesh.face_vertex_indices_attr())?)
            }
            Self::TetFaces(tets) => varies(tets.surface_face_vertex_indices_attr()),
            Self::Tetrahedra(tets) => varies(tets.tet_vertex_indices_attr()),
            Self::Segments(curves) => varies(curves.curve_vertex_counts_attr()),
        }
    }
}

/// What the elements of one type on a prim are at one time.
enum Topology {
    /// How many faces, points or tetrahedra there are, zero where the
    /// attribute they are counted from reads no value.
    Count(usize),
    /// The edges of a mesh's faces, each as its two point indices with the
    /// lower first, or `None` where the face topology reads no value or its
    /// indices run out before its counts do.
    Edges(Option<BTreeSet<(i32, i32)>>),
    /// The segment count of each curve, or `None` where `curveVertexCounts`
    /// reads no value, and every segment those counts give once
    /// [`pairs`](Self::pairs) is asked for them.
    Segments(Option<Vec<i32>>, OnceCell<BTreeSet<(i32, i32)>>),
}

impl Topology {
    /// How many elements there are, zero where their topology reads no
    /// value. A curve with a negative segment count has none.
    fn count(&self) -> usize {
        match self {
            Self::Count(count) => *count,
            Self::Edges(edges) => edges.as_ref().map_or(0, |edges| edges.len()),
            Self::Segments(counts, _) => counts.iter().flatten().map(|&count| non_negative(count)).sum(),
        }
    }

    /// Every edge or segment as the pair of indices that names it, or `None`
    /// where their topology reads no value and for elements that one index
    /// names.
    fn pairs(&self) -> Option<&BTreeSet<(i32, i32)>> {
        match self {
            Self::Count(_) => None,
            Self::Edges(edges) => edges.as_ref(),
            Self::Segments(counts, pairs) => counts.as_deref().map(|counts| pairs.get_or_init(|| segments(counts))),
        }
    }

    /// Report the `pairs` of the family `family_name` that name no element:
    /// an edge the mesh does not have, or a segment past its curves. Nothing
    /// is reported where the topology reads no value.
    fn report_missing(&self, pairs: &BTreeSet<(i32, i32)>, family_name: &str, at: &str, reasons: &mut Vec<String>) {
        match self {
            Self::Edges(Some(edges)) if !pairs.is_subset(edges) => reasons.push(format!(
                "At least one edge in family {family_name} at time {at} does not exist on the parent prim."
            )),
            Self::Segments(Some(counts), _) => segment_bounds(counts, pairs, at, reasons),
            Self::Count(_) | Self::Edges(_) | Self::Segments(None, _) => {}
        }
    }
}

/// The distinct indices a family has been seen to hold at one time: how
/// many there are and the least and greatest of them.
struct Seen {
    /// Whether each index a family should hold, those under the element
    /// count, has been seen.
    inside: Vec<bool>,
    /// The indices seen that no element has: the negative ones and those at
    /// or past the element count.
    outside: HashSet<i32>,
    len: usize,
    bounds: Option<(i32, i32)>,
}

impl Seen {
    /// No indices, among `element_count` elements.
    fn new(element_count: usize) -> Self {
        Seen {
            inside: vec![false; element_count],
            outside: HashSet::new(),
            len: 0,
            bounds: None,
        }
    }

    /// Forget every index, for the next time.
    fn clear(&mut self) {
        self.inside.fill(false);
        self.outside.clear();
        self.len = 0;
        self.bounds = None;
    }

    /// Record `index`. Returns `false` for one already seen.
    fn insert(&mut self, index: i32) -> bool {
        let slot = usize::try_from(index).ok().and_then(|index| self.inside.get_mut(index));
        let fresh = match slot {
            Some(seen) => !mem::replace(seen, true),
            None => self.outside.insert(index),
        };
        if fresh {
            self.len += 1;
            self.bounds = Some(match self.bounds {
                Some((first, last)) => (first.min(index), last.max(index)),
                None => (index, index),
            });
        }
        fresh
    }

    /// How many distinct indices have been seen.
    fn len(&self) -> usize {
        self.len
    }

    /// The least and the greatest index seen, or `None` before any.
    fn bounds(&self) -> Option<(i32, i32)> {
        self.bounds
    }
}

/// The namespace of the attributes a prim types its subset families in.
const NS_SUBSET_FAMILY: &str = "subsetFamily";

/// The base name of the attribute typing one subset family.
const FAMILY_TYPE: &str = "familyType";

/// The name of the attribute that types the family `family_name` (C++
/// `_GetFamilyTypeAttrName`).
fn family_type_attr_name(family_name: &str) -> String {
    format!("{NS_SUBSET_FAMILY}:{family_name}:{FAMILY_TYPE}")
}

/// `builder` declaring the uniform attribute that types a family, holding
/// `family_type`.
fn typing(builder: usd::AttributeBuilder<'_>, family_type: FamilyType) -> usd::AttributeBuilder<'_> {
    builder
        .custom(false)
        .variability(sdf::Variability::Uniform)
        .set(family_type)
}

/// The family filter `family_name` stands for: an empty name admits every
/// family.
fn named(family_name: &str) -> Option<&str> {
    (!family_name.is_empty()).then_some(family_name)
}

/// The family-type token authored for the family `family_name` on `geom`,
/// or `None` where the name is empty or no token is authored.
fn family_type_token(geom: &usd::Prim, family_name: &str) -> Result<Option<tf::Token>> {
    if family_name.is_empty() {
        return Ok(None);
    }
    let token = geom.attribute(family_type_attr_name(family_name)).get::<tf::Token>()?;
    Ok(token.filter(|token| !token.is_empty()))
}

/// Whether two indices name one element of `element_type`: the points of an
/// edge, or the curve of a segment and its place on that curve.
fn is_paired(element_type: ElementType) -> bool {
    matches!(element_type, ElementType::Edge | ElementType::Segment)
}

/// Define a `GeomSubset` at `path`, where none is defined yet, and author
/// its properties and its family's type on `geom` as one edit.
///
/// A family name that makes no attribute name is refused before anything is
/// authored. When the property edit fails, a prim spec the definition added
/// to the edit target is removed again; one the target already held stays,
/// defined as a `GeomSubset`.
fn author(
    geom: &usd::Prim,
    path: sdf::Path,
    element_type: ElementType,
    indices: &[i32],
    family_name: &str,
    family_type: Option<FamilyType>,
) -> Result<Subset> {
    let stage = geom.stage();
    if family_type.is_some() && !family_name.is_empty() {
        geom.path().append_property(family_type_attr_name(family_name))?;
    }
    let existing = stage.prim(&path)?;
    let target = stage.edit_target();
    let spec_path = target.map_to_spec_path(&path);
    let held = existing
        .prim_stack()?
        .iter()
        .any(|site| site.layer == target.layer_identifier() && Some(&site.path) == spec_path.as_ref());
    // TODO: the define and the property edit are two commits because
    // `usd::StageEdit` cannot define a prim. A prim definition queued in the
    // transaction would make subset creation atomic, with no spec to look
    // for beforehand and none to remove on failure.
    let defined = existing.is_defined()? && existing.type_name()?.as_deref() == Some(tokens::GEOM_SUBSET);
    let subset = match defined {
        true => Subset::from_prim_unchecked(existing),
        false => Subset::define(stage, &path)?,
    };
    let authored = stage.edit(|edit| -> Result<()> {
        let prim = edit.prim(&path)?;
        prim.attribute_builder(tokens::ELEMENT_TYPE, sdf::ValueTypeName::TOKEN)
            .custom(false)
            .variability(sdf::Variability::Uniform)
            .set(element_type)
            .build()?;
        prim.attribute_builder(tokens::INDICES, sdf::ValueTypeName::INT_ARRAY)
            .custom(false)
            .set(indices.to_vec())
            .build()?;
        prim.attribute_builder(tokens::FAMILY_NAME, sdf::ValueTypeName::TOKEN)
            .custom(false)
            .variability(sdf::Variability::Uniform)
            .set(tf::Token::from(family_name))
            .build()?;
        if let Some(family_type) = family_type
            && !family_name.is_empty()
        {
            let builder = edit
                .prim(geom.path())?
                .attribute_builder(family_type_attr_name(family_name), sdf::ValueTypeName::TOKEN);
            typing(builder, family_type).build()?;
        }
        Ok(())
    });
    if let Err(error) = authored {
        if !held {
            stage.remove_prim(&path)?;
        }
        return Err(error);
    }
    Ok(subset)
}

/// The `GeomSubset` children of `prim` that are active, loaded, not abstract
/// and carry a defining specifier of their own (C++
/// `_GetGeomSubsetPredicate`), which admits the subsets of a prim under an
/// `over`.
fn subsets_of(prim: &usd::Prim) -> Result<Vec<Subset>> {
    let mut subsets = Vec::new();
    if prim.is_instance()? {
        return Ok(subsets);
    }
    for child in prim.children()? {
        let defining = matches!(child.specifier()?, Some(sdf::Specifier::Def | sdf::Specifier::Class));
        if defining
            && child.is_active()?
            && child.is_loaded()?
            && !child.is_abstract()?
            && let Some(subset) = Subset::from_prim(child)?
        {
            subsets.push(subset);
        }
    }
    Ok(subsets)
}

/// The subsets of `prim` whose `elementType` and `familyName` tokens are the
/// ones given, where `None` admits any.
fn matching(prim: &usd::Prim, element_type: Option<&str>, family_name: Option<&str>) -> Result<Vec<Subset>> {
    let is = |attr: usd::Attribute, wanted: Option<&str>| -> Result<bool> {
        match wanted {
            Some(wanted) => Ok(attr.get::<tf::Token>()?.as_deref() == Some(wanted)),
            None => Ok(true),
        }
    };
    let mut subsets = Vec::new();
    for subset in subsets_of(prim)? {
        if is(subset.element_type_attr(), element_type)? && is(subset.family_name_attr(), family_name)? {
            subsets.push(subset);
        }
    }
    Ok(subsets)
}

/// The `elementType` of `subset` as the token it holds, empty where it reads
/// no value. The token is compared as written: one that names no element
/// type is a value like any other.
fn element_token(subset: &Subset) -> Result<tf::Token> {
    Ok(subset.element_type_attr().get::<tf::Token>()?.unwrap_or_default())
}

/// The first of `subsets` whose `elementType` token is not `element`, with
/// the token it holds.
fn mismatched<'a>(subsets: &'a [Subset], element: &str) -> Result<Option<(&'a Subset, tf::Token)>> {
    for subset in subsets {
        let found = element_token(subset)?;
        if found.as_str() != element {
            return Ok(Some((subset, found)));
        }
    }
    Ok(None)
}

/// The edges of `mesh`'s faces at `time`, each as its two point indices with
/// the lower first, or `None` where the face topology reads no value or its
/// indices run out before its counts do (C++ `_GetEdgesFromPrim`).
fn edges(mesh: &Mesh, time: Option<usd::TimeCode>) -> Result<Option<BTreeSet<(i32, i32)>>> {
    let (Some(counts), Some(indices)) = (mesh.face_vertex_counts_at(time)?, mesh.face_vertex_indices_at(time)?) else {
        return Ok(None);
    };

    let mut edges = BTreeSet::new();
    let mut rest = indices.as_slice();
    for count in counts {
        let Some((face, after)) = rest.split_at_checked(non_negative(count)) else {
            return Ok(None);
        };
        rest = after;
        for (corner, &a) in face.iter().enumerate() {
            let b = face[(corner + 1) % face.len()];
            edges.insert((a.min(b), a.max(b)));
        }
    }
    Ok(Some(edges))
}

/// Every segment of curves with the segment `counts`, each as its curve
/// index and its index on that curve (C++ `_GetAllPossibleSegments`).
fn segments(counts: &[i32]) -> BTreeSet<(i32, i32)> {
    (0..)
        .zip(counts)
        .flat_map(|(curve, &count)| (0..count).map(move |segment| (curve, segment)))
        .collect()
}

/// Report each of `segments` whose curve index or segment index is past
/// curves with the segment `counts`. A negative curve index is passed over
/// here, where the check for negative indices reports it.
fn segment_bounds(counts: &[i32], segments: &BTreeSet<(i32, i32)>, at: &str, reasons: &mut Vec<String>) {
    for &(curve, segment) in segments {
        let Ok(curve) = usize::try_from(curve) else {
            continue;
        };
        match counts.get(curve) {
            Some(&count) if segment >= count => reasons.push(format!(
                "Found one or more indices that are greater than the segment count {count} at time {at}."
            )),
            Some(_) => {}
            None => reasons.push(format!(
                "Found one or more indices that are greater than the curve vertex count {} at time {at}.",
                counts.len()
            )),
        }
    }
}

/// Report the indices outside the elements, among indices that run from
/// `first` to `last`: one finding where `last` is at or past a `count` that
/// is not zero, and one where `first` is negative. A negative `last` is not
/// past the count, and a `count` of `None` bounds nothing from above.
fn index_bounds(first: i32, last: i32, count: Option<usize>, at: &str, reasons: &mut Vec<String>) {
    if let Some(count) = count
        && count > 0
        && usize::try_from(last).is_ok_and(|last| last >= count)
    {
        reasons.push(format!(
            "Found one or more indices that are greater than the element count {count} at time {at}."
        ));
    }
    if first < 0 {
        reasons.push(format!("Found one or more indices that are less than 0 at time {at}."));
    }
}

/// `indices` taken two at a time, dropping an odd one at the end. A pair
/// keeps its order where `ordered`, and otherwise puts its lower index first
/// (C++ `_GetIndexPairs`).
fn index_pairs(indices: &[i32], ordered: bool) -> impl Iterator<Item = (i32, i32)> + '_ {
    indices.chunks_exact(2).map(move |pair| match ordered {
        true => (pair[0], pair[1]),
        false => (pair[0].min(pair[1]), pair[0].max(pair[1])),
    })
}

/// The default time, then every time one of `attrs` has a sample, in order.
fn sampled_times(attrs: &[usd::Attribute]) -> Result<impl Iterator<Item = Option<usd::TimeCode>>> {
    let samples = usd::Attribute::unioned_time_samples(attrs)?;
    Ok(iter::once(None).chain(samples.into_iter().map(|time| Some(usd::TimeCode::new(time)))))
}

/// `time` as a finding names it: `DEFAULT`, or the time's value.
fn time_label(time: Option<usd::TimeCode>) -> String {
    match time {
        Some(time) => time.value().to_string(),
        None => "DEFAULT".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, tf};

    use super::FamilyType;
    use crate::SchemaError;
    use crate::geom::{BasisCurves, BasisCurvesSchema, CurveBasis, CurveType, CurveWrap, CurvesSchema, ElementType};
    use crate::geom::{ImageableSchema, Mesh, MeshSchema, PointBasedSchema, Scope, Subset, SubsetSchema};
    use crate::geom::{TetMesh, TetMeshSchema};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    const EARLIEST: usd::TimeCode = usd::TimeCode::EARLIEST;

    /// One subset of a family under test: its indices at the default time,
    /// where it has any, and its samples.
    type Member<'a> = (Option<&'a [i32]>, &'a [(f64, &'a [i32])]);

    /// Authors the family `name` on `geom`: its type, where it has one, and a
    /// subset `<name>_<n>` of `element_type` for each of `members`.
    fn family(
        geom: &impl ImageableSchema,
        element_type: ElementType,
        name: &str,
        family_type: Option<FamilyType>,
        members: &[Member<'_>],
    ) -> Result {
        if let Some(family_type) = family_type {
            Subset::set_family_type(geom, name, family_type)?;
        }
        for (n, (default, samples)) in members.iter().enumerate() {
            let path = geom.path().append_path(format!("{name}_{n}").as_str())?;
            let subset = Subset::define(geom.stage(), path)?;
            subset.create_element_type_attr()?.set(element_type)?;
            subset.create_family_name_attr()?.set(tf::Token::from(name))?;
            let mut indices = subset.create_indices_attr()?;
            if let Some(default) = default {
                indices = indices.set(default.to_vec())?;
            }
            for (time, sample) in *samples {
                indices = indices.set_at(sample.to_vec(), usd::TimeCode::new(*time))?;
            }
        }
        Ok(())
    }

    /// A family that validates.
    fn assert_valid(geom: &impl ImageableSchema, element_type: ElementType, name: &str) -> Result {
        let reasons = Subset::validate_family(geom, element_type, name)?;
        assert!(reasons.is_empty(), "{name}: {reasons:?}");
        Ok(())
    }

    /// A family whose findings include each of `expected`.
    fn assert_invalid(geom: &impl ImageableSchema, element_type: ElementType, name: &str, expected: &[&str]) -> Result {
        let reasons = Subset::validate_family(geom, element_type, name)?;
        assert!(!reasons.is_empty(), "{name} validates");
        for wanted in expected {
            assert!(
                reasons.iter().any(|reason| reason.contains(wanted)),
                "{name}: no {wanted:?} in {reasons:?}"
            );
        }
        Ok(())
    }

    /// A mesh of `side` by `side` quads over a grid of points.
    fn grid(stage: &usd::Stage, path: &str, side: i32) -> Result<Mesh> {
        let mesh = Mesh::define(stage, path)?;
        let row = side + 1;
        let points: Vec<_> = (0..row * row)
            .map(|n| gf::vec3f((n % row) as f32, (n / row) as f32, 0.0))
            .collect();
        let faces: Vec<i32> = (0..side * side)
            .flat_map(|n| {
                let corner = n / side * row + n % side;
                [corner, corner + 1, corner + row + 1, corner + row]
            })
            .collect();
        mesh.create_points_attr()?.set(points)?;
        mesh.create_face_vertex_counts_attr()?
            .set(vec![4; (side * side) as usize])?;
        mesh.create_face_vertex_indices_attr()?.set(faces)?;
        Ok(mesh)
    }

    /// The `/Sphere/SimpleEdges` mesh of the C++ fixture: two quads sharing
    /// the edge between points 0 and 1.
    fn simple_edges(stage: &usd::Stage, path: &str) -> Result<Mesh> {
        let mesh = Mesh::define(stage, path)?;
        mesh.create_points_attr()?.set(vec![gf::vec3f(0.0, 0.0, 0.0); 6])?;
        mesh.create_face_vertex_counts_attr()?.set(vec![4, 4])?;
        mesh.create_face_vertex_indices_attr()?
            .set(vec![0, 1, 5, 4, 0, 1, 2, 3])?;
        Ok(mesh)
    }

    /// Cubic, pinned b-spline curves.
    fn pinned_curves(stage: &usd::Stage, path: &str) -> Result<BasisCurves> {
        let curves = BasisCurves::define(stage, path)?;
        curves.create_type_attr()?.set(CurveType::Cubic)?;
        curves.create_wrap_attr()?.set(CurveWrap::Pinned)?;
        curves.create_basis_attr()?.set(CurveBasis::Bspline)?;
        Ok(curves)
    }

    /// The face families of the C++ fixture's `/Sphere/pSphere1`, on a mesh
    /// of sixteen faces (C++ `test_SubsetRetrievalAndValidity`, faces).
    #[test]
    fn face_families() -> Result {
        use ElementType::Face;
        use FamilyType::{NonOverlapping, Partition, Unrestricted};

        let stage = crate::tests::stage("anon.usda")?;
        let mesh = grid(&stage, "/Sphere", 4)?;
        let evens: &[i32] = &[0, 2, 4, 6, 8, 10, 12, 14];
        let odds: &[i32] = &[1, 3, 5, 7, 9, 11, 13, 15];

        family(
            &mesh,
            Face,
            "materialBind",
            Some(Partition),
            &[
                (
                    Some(&[12, 13, 14, 15]),
                    &[(1.0, &[0, 1, 2, 3]), (2.0, &[12, 13, 14, 15]), (3.0, &[0, 1, 2, 3])],
                ),
                (
                    Some(&[0, 1, 2, 3, 8, 9, 10, 11]),
                    &[
                        (1.0, &[4, 5, 6, 7, 8, 9, 10, 11]),
                        (2.0, &[0, 1, 2, 3, 8, 9, 10, 11]),
                        (3.0, &[4, 5, 6, 7, 8, 9, 10, 11]),
                    ],
                ),
                (
                    Some(&[4, 5, 6, 7]),
                    &[(1.0, &[12, 13, 14, 15]), (2.0, &[4, 5, 6, 7]), (3.0, &[12, 13, 14, 15])],
                ),
            ],
        )?;
        assert_eq!(Subset::in_family(&mesh, Some(Face), Some("materialBind"))?.len(), 3);
        assert_eq!(Subset::family_type(&mesh, "materialBind")?, Partition);
        assert_valid(&mesh, Face, "materialBind")?;

        family(
            &mesh,
            Face,
            "validPartition",
            Some(Partition),
            &[
                (
                    Some(&[0, 1, 2, 3, 4, 5]),
                    &[(1.0, &[11, 12, 13, 14, 15]), (3.0, &[0, 1, 2, 3, 4, 5])],
                ),
                (
                    Some(&[6, 7, 8, 9, 10]),
                    &[
                        (1.0, &[6, 7, 8, 9, 10]),
                        (2.0, &[0, 1, 2, 3, 4, 5]),
                        (3.0, &[11, 12, 13, 14, 15]),
                    ],
                ),
                (
                    Some(&[11, 12, 13, 14, 15]),
                    &[(1.0, &[0, 1, 2, 3, 4, 5]), (2.0, &[6, 7, 8, 9, 10])],
                ),
            ],
        )?;
        family(
            &mesh,
            Face,
            "validNonOverlapping",
            Some(NonOverlapping),
            &[(Some(evens), &[(1.0, odds)]), (Some(odds), &[(2.0, evens)])],
        )?;
        // Index 0 overlaps at the first sample, and 15 is left out of it.
        family(
            &mesh,
            Face,
            "validUnrestricted",
            Some(Unrestricted),
            &[
                (
                    Some(&[0, 2, 4, 6, 8, 10, 12, 14, 15]),
                    &[(1.0, &[0, 1, 3, 5, 7, 9, 11, 13])],
                ),
                (Some(odds), &[(2.0, evens)]),
            ],
        )?;
        family(
            &mesh,
            Face,
            "emptyIndicesSomeTimes",
            None,
            &[(None, &[(0.0, &[]), (1.0, &[0, 1, 2, 3]), (2.0, &[])])],
        )?;
        for name in [
            "validPartition",
            "validNonOverlapping",
            "validUnrestricted",
            "emptyIndicesSomeTimes",
        ] {
            assert_valid(&mesh, Face, name)?;
        }

        // Index 16 at the second sample and -1 at the third are invalid.
        family(
            &mesh,
            Face,
            "invalidIndices",
            None,
            &[(
                Some(&[4, 5, 6, 7]),
                &[
                    (1.0, &[12, 13, 14, 15]),
                    (2.0, &[4, 5, 6, 7, 16]),
                    (3.0, &[-1, 12, 13, 14, 15]),
                ],
            )],
        )?;
        family(
            &mesh,
            Face,
            "badPartition1",
            Some(Partition),
            &[
                (Some(&[4, 5, 6, 7]), &[(1.0, &[12, 13, 14, 15])]),
                (
                    Some(&[0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 16]),
                    &[(2.0, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])],
                ),
            ],
        )?;
        family(
            &mesh,
            Face,
            "badPartition2",
            Some(Partition),
            &[(Some(&[0, 1, 2, 3, 4, 5, 6, 7]), &[])],
        )?;
        family(
            &mesh,
            Face,
            "badPartition3",
            Some(Partition),
            &[(Some(&[0, 1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 5, 15]), &[])],
        )?;
        family(
            &mesh,
            Face,
            "invalidNonOverlapping",
            Some(NonOverlapping),
            &[
                (Some(evens), &[(1.0, odds)]),
                (Some(odds), &[(2.0, &[0, 1, 2, 4, 6, 8, 10, 12, 14])]),
            ],
        )?;
        family(
            &mesh,
            Face,
            "invalidUnrestricted",
            Some(Unrestricted),
            &[
                (
                    Some(&[0, 2, 4, 6, 8, 10, 12, 14, 16]),
                    &[(1.0, &[-1, 1, 3, 5, 7, 9, 11, 13, 15])],
                ),
                (Some(odds), &[(2.0, &[0, 1, 2, 4, 6, 8, 10, 12, 14])]),
            ],
        )?;
        family(
            &mesh,
            Face,
            "onlyNegativeIndices",
            None,
            &[(Some(&[-1, -2, -3, -4, -5]), &[])],
        )?;
        family(&mesh, Face, "emptyIndicesAtAllTimes", None, &[(None, &[])])?;

        let above = "Found one or more indices that are greater than the element count";
        let below = "Found one or more indices that are less than 0";
        let count = "does not match the element count";
        for (name, expected) in [
            ("invalidIndices", &[above, below][..]),
            ("badPartition1", &[count, above]),
            ("badPartition2", &[count]),
            ("badPartition3", &["Found duplicate index"]),
            ("invalidNonOverlapping", &["Found duplicate index"]),
            ("invalidUnrestricted", &[above, below]),
            ("onlyNegativeIndices", &[below]),
            ("emptyIndicesAtAllTimes", &["No indices in family at any time"]),
        ] {
            assert_invalid(&mesh, Face, name, expected)?;
        }
        // Negative indices alone are not also reported as too large.
        let negative = Subset::validate_family(&mesh, Face, "onlyNegativeIndices")?;
        assert!(!negative.iter().any(|reason| reason.contains(above)), "{negative:?}");
        Ok(())
    }

    /// Geometry whose face count changes over time, and geometry with no
    /// faces at all (the `VaryingMesh` and `NullMesh` cases of the C++
    /// fixture).
    #[test]
    fn varying_and_null_faces() -> Result {
        use ElementType::Face;

        let stage = crate::tests::stage("anon.usda")?;
        let varying = Mesh::define(&stage, "/Varying")?;
        varying
            .create_face_vertex_counts_attr()?
            .set_at(vec![3], usd::TimeCode::new(1.0))?
            .set_at(vec![3, 3], usd::TimeCode::new(2.0))?
            .set_at(vec![3, 3, 3], usd::TimeCode::new(3.0))?;
        family(
            &varying,
            Face,
            "validPartition",
            Some(FamilyType::Partition),
            &[
                (None, &[(1.0, &[0]), (2.0, &[]), (3.0, &[0, 1])]),
                (None, &[(1.0, &[]), (2.0, &[0, 1]), (3.0, &[2])]),
            ],
        )?;
        assert_valid(&varying, Face, "validPartition")?;

        // The default indices index faces the mesh only has at its samples.
        family(
            &varying,
            Face,
            "invalidNoDefaultTimeElements",
            None,
            &[(Some(&[0]), &[(1.0, &[0]), (2.0, &[0, 1]), (3.0, &[0, 1, 2])])],
        )?;
        assert_invalid(&varying, Face, "invalidNoDefaultTimeElements", &["has no elements"])?;

        let null = Mesh::define(&stage, "/Null")?;
        family(&null, Face, "emptyIndicesAtAllTimes", None, &[(None, &[])])?;
        family(
            &null,
            Face,
            "invalidPartition",
            Some(FamilyType::Partition),
            &[(Some(&[0, 1]), &[])],
        )?;
        assert_invalid(
            &null,
            Face,
            "emptyIndicesAtAllTimes",
            &["No indices in family at any time"],
        )?;
        assert_invalid(
            &null,
            Face,
            "invalidPartition",
            &["Unable to determine element count at earliest time"],
        )?;
        Ok(())
    }

    /// Point and edge families on the two-quad mesh: six points, seven
    /// edges.
    #[test]
    fn point_and_edge_families() -> Result {
        use ElementType::{Edge, Point};
        use FamilyType::{NonOverlapping, Partition};

        let stage = crate::tests::stage("anon.usda")?;
        let mesh = simple_edges(&stage, "/Mesh")?;

        family(
            &mesh,
            Point,
            "points",
            Some(Partition),
            &[
                (Some(&[0, 1, 2]), &[(1.0, &[3, 4, 5])]),
                (Some(&[3, 4, 5]), &[(1.0, &[0, 1, 2])]),
            ],
        )?;
        assert_valid(&mesh, Point, "points")?;
        family(
            &mesh,
            Point,
            "badPoints",
            Some(Partition),
            &[(Some(&[0, 1, 1, 6]), &[(1.0, &[-1])])],
        )?;
        assert_invalid(
            &mesh,
            Point,
            "badPoints",
            &[
                "Found duplicate index 1",
                "does not match the element count 6",
                "greater than the element count 6 at time DEFAULT",
                "less than 0 at time 1",
            ],
        )?;

        // Every edge once, in either direction, split over two subsets.
        family(
            &mesh,
            Edge,
            "edges",
            Some(Partition),
            &[(Some(&[0, 1, 3, 0, 0, 4, 1, 2]), &[]), (Some(&[5, 1, 2, 3, 4, 5]), &[])],
        )?;
        assert_valid(&mesh, Edge, "edges")?;

        family(
            &mesh,
            Edge,
            "invalidIndices",
            None,
            &[(Some(&[0, 1, 0, 2]), &[(1.0, &[0, 1, 4]), (2.0, &[-1, 0])])],
        )?;
        assert_invalid(
            &mesh,
            Edge,
            "invalidIndices",
            &[
                "does not exist on the parent prim",
                "Indices attribute has an odd number of elements",
                "Found one or more indices that are less than 0",
            ],
        )?;
        family(
            &mesh,
            Edge,
            "badPartition",
            Some(Partition),
            &[(Some(&[0, 1, 0, 3]), &[])],
        )?;
        assert_invalid(&mesh, Edge, "badPartition", &["does not match the element count 7"])?;
        // The same edge named from either end is one edge.
        family(
            &mesh,
            Edge,
            "duplicate",
            Some(NonOverlapping),
            &[(Some(&[0, 1]), &[]), (Some(&[1, 0]), &[])],
        )?;
        assert_invalid(&mesh, Edge, "duplicate", &["Found duplicate edge (0, 1)"])?;

        // A mesh has no segments or tetrahedra.
        for element_type in [ElementType::Segment, ElementType::Tetrahedron] {
            assert_eq!(
                Subset::validate_family(&mesh, element_type, "edges")?,
                [format!(
                    "Invalid geom type for elementType {}.",
                    element_type.as_token()
                )]
            );
            assert!(matches!(
                Subset::unassigned_indices(&mesh, element_type, "edges", None),
                Err(SchemaError::UnsupportedSubsetElementType { .. })
            ));
        }
        Ok(())
    }

    /// The segment families of the C++ fixture's `/Sphere/BasisCurves`,
    /// `VaryingBasisCurves` and `NullBasisCurves` (C++
    /// `test_SubsetRetrievalAndValidity`, segments).
    #[test]
    fn segment_families() -> Result {
        use ElementType::Segment;
        use FamilyType::{NonOverlapping, Partition, Unrestricted};

        let stage = crate::tests::stage("anon.usda")?;
        // Segment counts 4, 3 and 2.
        let curves = pinned_curves(&stage, "/Curves")?;
        curves.create_curve_vertex_counts_attr()?.set(vec![5, 4, 3])?;
        let a: &[i32] = &[0, 0, 0, 1, 0, 2];
        let b: &[i32] = &[0, 3, 1, 0, 1, 1];
        let c: &[i32] = &[1, 2, 2, 0, 2, 1];

        family(
            &curves,
            Segment,
            "physicsAttachment",
            Some(Partition),
            &[
                (Some(a), &[(1.0, a), (2.0, b), (3.0, a)]),
                (Some(c), &[(1.0, c), (2.0, a), (3.0, c)]),
                (Some(b), &[(1.0, b), (2.0, c), (3.0, b)]),
            ],
        )?;
        assert_eq!(
            Subset::in_family(&curves, Some(Segment), Some("physicsAttachment"))?.len(),
            3
        );
        assert_eq!(Subset::family_type(&curves, "physicsAttachment")?, Partition);

        family(
            &curves,
            Segment,
            "validPartition",
            Some(Partition),
            &[
                (Some(a), &[(1.0, c), (3.0, a)]),
                (Some(b), &[(1.0, b), (2.0, a), (3.0, c)]),
                (Some(c), &[(1.0, a), (2.0, b)]),
            ],
        )?;
        family(
            &curves,
            Segment,
            "validNonOverlapping",
            Some(NonOverlapping),
            &[(Some(a), &[(1.0, b)]), (Some(b), &[(2.0, a)])],
        )?;
        family(
            &curves,
            Segment,
            "validUnrestricted",
            Some(Unrestricted),
            &[
                (
                    Some(&[0, 3, 1, 0, 1, 1, 0, 1]),
                    &[(1.0, &[0, 0, 0, 1, 0, 2, 1, 2, 2, 0])],
                ),
                (Some(b), &[(2.0, a)]),
            ],
        )?;
        family(
            &curves,
            Segment,
            "emptyIndicesSomeTimes",
            None,
            &[(None, &[(0.0, &[]), (1.0, b), (2.0, &[])])],
        )?;
        for name in [
            "physicsAttachment",
            "validPartition",
            "validNonOverlapping",
            "validUnrestricted",
            "emptyIndicesSomeTimes",
        ] {
            assert_valid(&curves, Segment, name)?;
        }

        // (0, 4) and (5, 0) at the default time and (-1, 2) at the third
        // sample are invalid, and the second sample is odd.
        family(
            &curves,
            Segment,
            "invalidIndices",
            None,
            &[(
                Some(&[0, 4, 5, 0, 1, 1]),
                &[(1.0, a), (2.0, &[0, 3, 1, 0, 1]), (3.0, &[-1, 2, 2, 0, 2, 1])],
            )],
        )?;
        family(
            &curves,
            Segment,
            "badPartition1",
            Some(Partition),
            &[
                (Some(a), &[(1.0, a)]),
                (
                    Some(&[0, 3, 1, 0, 1, 1, 1, 2, 2, 0, 2, 1, 5, 6]),
                    &[(2.0, &[0, 3, 1, 0, 1, 1, 1, 2, 2, 0, 2, 1])],
                ),
            ],
        )?;
        family(
            &curves,
            Segment,
            "badPartition2",
            Some(Partition),
            &[(Some(&[0, 2, 0, 3, 1, 0, 1, 1, 1, 2, 2, 0, 2, 1]), &[])],
        )?;
        family(
            &curves,
            Segment,
            "badPartition3",
            Some(Partition),
            &[(Some(&[0, 0, 0, 1, 0, 2, 0, 3, 1, 0, 1, 1, 1, 2, 2, 0, 2, 1, 0, 0]), &[])],
        )?;
        family(
            &curves,
            Segment,
            "invalidNonOverlapping",
            Some(NonOverlapping),
            &[(Some(a), &[(1.0, b)]), (Some(b), &[(2.0, &[0, 0, 0, 1, 0, 2, 0, 3])])],
        )?;
        family(
            &curves,
            Segment,
            "invalidUnrestricted",
            Some(Unrestricted),
            &[
                (
                    Some(&[0, 4, 1, 0, 1, 1, 0, 1]),
                    &[(1.0, &[0, 0, 0, -1, 0, 2, 1, 2, 2, 0])],
                ),
                (Some(b), &[(2.0, a)]),
            ],
        )?;
        family(
            &curves,
            Segment,
            "onlyNegativeIndices",
            None,
            &[(Some(&[-1, -2, -1, -1]), &[])],
        )?;
        family(&curves, Segment, "emptyIndicesAtAllTimes", None, &[(None, &[])])?;

        let curve = "greater than the curve vertex count";
        let segment = "greater than the segment count";
        let below = "Found one or more indices that are less than 0";
        for (name, expected) in [
            (
                "invalidIndices",
                &[curve, segment, "Indices attribute has an odd number of elements", below][..],
            ),
            ("badPartition1", &[curve]),
            ("badPartition2", &["does not match the element count"]),
            ("badPartition3", &["Found duplicate segment"]),
            ("invalidNonOverlapping", &["Found duplicate segment"]),
            ("invalidUnrestricted", &[segment, below]),
            ("onlyNegativeIndices", &[below]),
            ("emptyIndicesAtAllTimes", &["No indices in family at any time"]),
        ] {
            assert_invalid(&curves, Segment, name, expected)?;
        }

        let varying = pinned_curves(&stage, "/Varying")?;
        varying
            .create_curve_vertex_counts_attr()?
            .set_at(vec![5], usd::TimeCode::new(1.0))?
            .set_at(vec![5, 4], usd::TimeCode::new(2.0))?
            .set_at(vec![5, 4, 3], usd::TimeCode::new(3.0))?;
        let first: &[i32] = &[0, 0, 0, 1, 0, 2, 0, 3];
        let both: &[i32] = &[0, 0, 0, 1, 0, 2, 0, 3, 1, 0, 1, 1, 1, 2];
        family(
            &varying,
            Segment,
            "validPartition",
            Some(Partition),
            &[
                (None, &[(1.0, first), (2.0, &[]), (3.0, first)]),
                (None, &[(1.0, &[]), (2.0, both), (3.0, &[1, 0, 1, 1, 1, 2])]),
                (None, &[(1.0, &[]), (2.0, &[]), (3.0, &[2, 0, 2, 1])]),
            ],
        )?;
        assert_valid(&varying, Segment, "validPartition")?;
        family(
            &varying,
            Segment,
            "invalidNoDefaultTimeElements",
            None,
            &[(
                Some(&[0, 1]),
                &[
                    (1.0, first),
                    (2.0, both),
                    (3.0, &[0, 0, 0, 1, 0, 2, 0, 3, 1, 0, 1, 1, 1, 2, 2, 0, 2, 1]),
                ],
            )],
        )?;
        assert_invalid(&varying, Segment, "invalidNoDefaultTimeElements", &["has no elements"])?;

        let null = BasisCurves::define(&stage, "/Null")?;
        family(&null, Segment, "emptyIndicesAtAllTimes", None, &[(None, &[])])?;
        family(
            &null,
            Segment,
            "invalidPartition",
            Some(Partition),
            &[(Some(&[0, 1, 1, 2]), &[])],
        )?;
        assert_invalid(
            &null,
            Segment,
            "emptyIndicesAtAllTimes",
            &["No indices in family at any time"],
        )?;
        assert_invalid(
            &null,
            Segment,
            "invalidPartition",
            &["Unable to determine element count at earliest time"],
        )?;
        Ok(())
    }

    /// Tetrahedron and surface-face families on a `TetMesh`, which has no
    /// points or edges for a subset to index.
    #[test]
    fn tet_mesh_families() -> Result {
        use ElementType::{Face, Tetrahedron};

        let stage = crate::tests::stage("anon.usda")?;
        let tets = TetMesh::define(&stage, "/Tets")?;
        tets.create_points_attr()?.set(vec![gf::vec3f(0.0, 0.0, 0.0); 5])?;
        tets.create_tet_vertex_indices_attr()?
            .set(vec![gf::Vec4i::from([0, 1, 2, 3]), gf::Vec4i::from([1, 2, 3, 4])])?;
        tets.create_surface_face_vertex_indices_attr()?.set(vec![
            gf::Vec3i::from([0, 1, 2]),
            gf::Vec3i::from([0, 1, 3]),
            gf::Vec3i::from([0, 2, 3]),
        ])?;

        family(
            &tets,
            Tetrahedron,
            "tets",
            Some(FamilyType::Partition),
            &[(Some(&[0]), &[]), (Some(&[1]), &[])],
        )?;
        assert_valid(&tets, Tetrahedron, "tets")?;
        assert_eq!(Subset::unassigned_indices(&tets, Tetrahedron, "none", None)?, [0, 1]);

        family(
            &tets,
            Face,
            "faces",
            Some(FamilyType::Partition),
            &[(Some(&[0, 2]), &[])],
        )?;
        assert_invalid(&tets, Face, "faces", &["does not match the element count 3"])?;
        assert_eq!(Subset::unassigned_indices(&tets, Face, "faces", None)?, [1]);

        // The family holds tetrahedra, so it is no family of faces.
        let reasons = Subset::validate_family(&tets, Face, "tets")?;
        assert_eq!(reasons.len(), 1, "{reasons:?}");
        assert!(reasons[0].contains("has elementType 'tetrahedron', which does not match 'face'"));

        assert_eq!(
            Subset::validate_family(&tets, ElementType::Point, "tets")?,
            ["Invalid geom type for elementType point."]
        );
        Ok(())
    }

    /// C++ `test_GetUnassignedIndicesForEdges`.
    #[test]
    fn unassigned_edges() -> Result {
        use ElementType::Edge;

        let stage = crate::tests::stage("anon.usda")?;
        let mesh = simple_edges(&stage, "/SimpleEdges")?;
        let unassigned = || Subset::unassigned_indices(&mesh, Edge, "testEdgeFamily", EARLIEST);

        let subset = Subset::create(&mesh, "testEdge", Edge, &[], "testEdgeFamily", None)?;
        assert_eq!(subset.indices()?, Some(vec![]));
        assert_eq!(unassigned()?, [0, 1, 0, 3, 0, 4, 1, 2, 1, 5, 2, 3, 4, 5]);

        subset.indices_attr().set(vec![0, 1, 5, 4])?;
        assert_eq!(unassigned()?, [0, 3, 0, 4, 1, 2, 1, 5, 2, 3]);

        subset
            .indices_attr()
            .set(vec![0, 1, 0, 3, 0, 4, 1, 2, 1, 5, 2, 3, 4, 5])?;
        assert!(unassigned()?.is_empty());

        // Invalid indices assign nothing.
        let invalid = [0, 1, 0, 3, 0, 4, 1, 2, 2, 3, 4, 5, 7, -1];
        let again = Subset::create(&mesh, "testEdge", Edge, &invalid, "testEdgeFamily", None)?;
        assert_eq!(again.path(), subset.path());
        assert_eq!(again.indices()?.as_deref(), Some(&invalid[..]));
        assert_eq!(unassigned()?, [1, 5]);
        Ok(())
    }

    /// C++ `test_GetUnassignedIndicesForSegments`.
    #[test]
    fn unassigned_segments() -> Result {
        use ElementType::Segment;

        let stage = crate::tests::stage("anon.usda")?;
        // Segment counts 3 and 2.
        let curves = BasisCurves::define(&stage, "/SimpleSegments")?;
        curves.create_type_attr()?.set(CurveType::Linear)?;
        curves.create_wrap_attr()?.set(CurveWrap::Periodic)?;
        curves.create_curve_vertex_counts_attr()?.set(vec![3, 2])?;
        let unassigned = || Subset::unassigned_indices(&curves, Segment, "testSegmentFamily", EARLIEST);

        let subset = Subset::create(&curves, "testSegment", Segment, &[], "testSegmentFamily", None)?;
        assert_eq!(unassigned()?, [0, 0, 0, 1, 0, 2, 1, 0, 1, 1]);

        subset.indices_attr().set(vec![0, 0, 1, 0])?;
        assert_eq!(unassigned()?, [0, 1, 0, 2, 1, 1]);

        subset.indices_attr().set(vec![0, 0, 0, 1, 0, 2, 1, 0, 1, 1])?;
        assert!(unassigned()?.is_empty());

        // Invalid indices assign nothing.
        Subset::create(
            &curves,
            "testSegment",
            Segment,
            &[0, 0, 1, 0, -1, 0, 5, 2],
            "testSegmentFamily",
            None,
        )?;
        assert_eq!(unassigned()?, [0, 1, 0, 2, 1, 1]);
        Ok(())
    }

    /// C++ `test_CreateGeomSubset`, on a mesh of sixteen faces.
    #[test]
    fn create_geom_subset() -> Result {
        use ElementType::Face;

        let stage = crate::tests::stage("anon.usda")?;
        let mesh = grid(&stage, "/Sphere", 4)?;
        let unassigned = |name: &str| Subset::unassigned_indices(&mesh, Face, name, EARLIEST);
        let in_family = || Subset::in_family(&mesh, Some(Face), Some("testFamily"));

        // A new subset is its definition and then its properties.
        let commits = crate::tests::commits(&stage);
        let subset = Subset::create(&mesh, "testSubset", Face, &[], "", None)?;
        assert_eq!(commits.get(), 2);
        assert_eq!(subset.element_type()?, Some(Face));
        assert_eq!(subset.family_name()?.as_deref(), Some(""));
        subset.family_name_attr().set(tf::Token::from("testFamily"))?;
        assert_eq!(subset.family_name()?.as_deref(), Some("testFamily"));

        assert_eq!(subset.indices()?, Some(vec![]));
        assert_eq!(unassigned("testFamily")?, (0..16).collect::<Vec<_>>());
        subset.indices_attr().set(vec![1, 2, 3, 4, 5])?;

        // A family is not a partition until it is said to be one.
        assert_eq!(Subset::family_type(&mesh, "testFamily")?, FamilyType::Unrestricted);
        assert_eq!(in_family()?.len(), 1);

        // Creating under the same name authors on the subset that is there,
        // and the family type goes in the same edit.
        let commits = crate::tests::commits(&stage);
        let partition = Some(FamilyType::Partition);
        let same = Subset::create(&mesh, "testSubset", Face, &[0, 1, 2], "testFamily", partition)?;
        assert_eq!(commits.get(), 1);
        assert_eq!(same.path(), subset.path());
        assert_eq!(in_family()?.len(), 1);
        assert_eq!(Subset::family_type(&mesh, "testFamily")?, FamilyType::Partition);
        assert_invalid(&mesh, Face, "testFamily", &["does not match the element count"])?;
        let rest = unassigned("testFamily")?;
        assert_eq!(rest, (3..16).collect::<Vec<_>>());

        // A unique subset is always a new one, and indices past the faces
        // leave nothing unassigned.
        let beyond: Vec<i32> = (3..20).collect();
        let another = Subset::create_unique(&mesh, "testSubset", Face, &beyond, "testFamily", partition)?;
        assert_eq!(another.path().name(), Some("testSubset_1"));
        assert_eq!(another.indices()?, Some(beyond));
        assert!(unassigned("testFamily")?.is_empty());
        assert_eq!(in_family()?.len(), 2);

        Subset::create(&mesh, "testSubset_1", Face, &rest, "testFamily", partition)?;
        assert_eq!(in_family()?.len(), 2);
        assert_valid(&mesh, Face, "testFamily")?;
        assert_eq!(Subset::all(&mesh)?.len(), 2);

        // Negative indices assign nothing.
        let invalid = Subset::create_unique(&mesh, "testSubset", Face, &[-3, -2, 0, 1, 2], "testInvalid", partition)?;
        assert_eq!(invalid.path().name(), Some("testSubset_2"));
        assert_eq!(unassigned("testInvalid")?, (3..16).collect::<Vec<_>>());

        let names = Subset::family_names(&mesh)?;
        assert_eq!(
            names.iter().map(|name| name.as_str()).collect::<Vec<_>>(),
            ["testFamily", "testInvalid"]
        );
        Ok(())
    }

    /// The subsets of a prim under an `over` are still its subsets (C++
    /// `test_PointInstancer`), while a subset that is itself an `over`, a
    /// `class` descendant or inactive is not one.
    #[test]
    fn subsets_under_over() -> Result {
        use ElementType::Face;

        let stage = crate::tests::stage("anon.usda")?;
        Scope::define(&stage, "/Sphere")?;
        stage.override_prim("/Sphere/Prototypes")?;
        let mesh = grid(&stage, "/Sphere/Prototypes/pSphere1", 2)?;
        assert!(!mesh.prim().is_defined()?);

        family(
            &mesh,
            Face,
            "materialBind",
            Some(FamilyType::Partition),
            &[(Some(&[0]), &[]), (Some(&[1, 2]), &[]), (Some(&[3]), &[])],
        )?;
        assert_eq!(Subset::in_family(&mesh, Some(Face), Some("materialBind"))?.len(), 3);
        assert_eq!(Subset::family_type(&mesh, "materialBind")?, FamilyType::Partition);
        assert_valid(&mesh, Face, "materialBind")?;

        // Neither filter admits the family under another element type or
        // another name.
        assert!(Subset::in_family(&mesh, Some(ElementType::Point), None)?.is_empty());
        assert!(Subset::in_family(&mesh, None, Some("other"))?.is_empty());
        assert!(Subset::in_family(&mesh, None, Some(""))?.is_empty());

        stage
            .override_prim("/Sphere/Prototypes/pSphere1/undefined")?
            .set_type_name("GeomSubset")?;
        stage
            .prim("/Sphere/Prototypes/pSphere1/materialBind_0")?
            .set_active(false)?;
        assert_eq!(Subset::all(&mesh)?.len(), 2);
        Ok(())
    }

    /// A family type is `unrestricted` until authored, and a token that
    /// names none is an error.
    #[test]
    fn family_type_tokens() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = grid(&stage, "/Mesh", 1)?;
        assert_eq!(Subset::family_type(&mesh, "fam")?, FamilyType::Unrestricted);
        assert_eq!(Subset::family_type(&mesh, "")?, FamilyType::Unrestricted);

        Subset::set_family_type(&mesh, "fam", FamilyType::NonOverlapping)?;
        let attr = mesh.prim().attribute("subsetFamily:fam:familyType");
        assert_eq!(attr.get::<tf::Token>()?.as_deref(), Some("nonOverlapping"));
        assert_eq!(attr.variability()?, Some(openusd::sdf::Variability::Uniform));
        assert!(!attr.is_custom()?);
        assert_eq!(Subset::family_type(&mesh, "fam")?, FamilyType::NonOverlapping);

        attr.set(tf::Token::from("bogus"))?;
        assert!(Subset::family_type(&mesh, "fam").is_err());

        for family_type in [
            FamilyType::Partition,
            FamilyType::NonOverlapping,
            FamilyType::Unrestricted,
        ] {
            assert_eq!(FamilyType::from_token(family_type.as_token()), Some(family_type));
        }
        Ok(())
    }

    /// An edge names its two points, which may be numbered past the number
    /// of edges the mesh has.
    #[test]
    fn validate_edge_point_indices() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = Mesh::define(&stage, "/Mesh")?;
        mesh.create_points_attr()?.set(vec![gf::vec3f(0.0, 0.0, 0.0); 6])?;
        mesh.create_face_vertex_counts_attr()?.set(vec![3])?;
        mesh.create_face_vertex_indices_attr()?.set(vec![3, 4, 5])?;
        Subset::create(&mesh, "edge", ElementType::Edge, &[3, 4], "fam", None)?;
        assert_valid(&mesh, ElementType::Edge, "fam")?;

        // An edge the mesh does not have is still a finding.
        Subset::create(&mesh, "missing", ElementType::Edge, &[0, 1], "fam", None)?;
        assert_invalid(&mesh, ElementType::Edge, "fam", &["does not exist on the parent prim"])
    }

    /// A family name that makes no attribute name fails before the subset is
    /// defined, so a prim already at the subset's path keeps its type and its
    /// children.
    #[test]
    fn create_keeps_existing_prim() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = grid(&stage, "/Mesh", 1)?;
        stage.define_typed_prim("/Mesh/taken", "Xform")?;
        stage.define_prim("/Mesh/taken/child")?;

        let partition = Some(FamilyType::Partition);
        let commits = crate::tests::commits(&stage);
        assert!(Subset::create(&mesh, "taken", ElementType::Face, &[0], "bad name", partition).is_err());
        assert!(Subset::create(&mesh, "fresh", ElementType::Face, &[0], "bad name", partition).is_err());
        assert_eq!(commits.get(), 0);
        assert_eq!(stage.prim("/Mesh/taken")?.type_name()?.as_deref(), Some("Xform"));
        assert!(stage.prim("/Mesh/taken/child")?.is_valid()?);
        assert!(!stage.prim("/Mesh/fresh")?.is_valid()?);
        Ok(())
    }

    /// A property edit that fails takes back the prim spec the call added,
    /// and leaves a prim the edit target already held, which the definition
    /// has typed a `GeomSubset` by then.
    #[test]
    fn create_failure_rollback() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = grid(&stage, "/Mesh", 1)?;
        // A relationship where the family type goes, and one where a
        // subset's indices go, each refuse the attribute.
        mesh.prim()
            .relationship_builder("subsetFamily:fam:familyType")
            .build()?;
        let taken = stage.define_typed_prim("/Mesh/taken", "Xform")?;
        taken.relationship_builder("indices").build()?;
        stage.define_prim("/Mesh/taken/child")?;

        let partition = Some(FamilyType::Partition);
        assert!(Subset::create(&mesh, "fresh", ElementType::Face, &[0], "fam", partition).is_err());
        assert!(!stage.prim("/Mesh/fresh")?.is_valid()?);

        assert!(Subset::create(&mesh, "taken", ElementType::Face, &[0], "", None).is_err());
        assert_eq!(taken.type_name()?.as_deref(), Some("GeomSubset"));
        assert!(stage.prim("/Mesh/taken/child")?.is_valid()?);
        Ok(())
    }

    /// A family whose type token names no family type is validated as a
    /// restricted family, so a repeated index is a finding and the call does
    /// not fail.
    #[test]
    fn validate_unknown_family_type() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let mesh = grid(&stage, "/Mesh", 1)?;
        Subset::create(
            &mesh,
            "a",
            ElementType::Face,
            &[0],
            "fam",
            Some(FamilyType::NonOverlapping),
        )?;
        Subset::create(&mesh, "b", ElementType::Face, &[0], "fam", None)?;
        mesh.prim()
            .attribute("subsetFamily:fam:familyType")
            .set(tf::Token::from("bogus"))?;

        let reasons = Subset::validate_family(&mesh, ElementType::Face, "fam")?;
        assert_eq!(reasons.len(), 1, "{reasons:?}");
        assert!(reasons[0].contains("duplicate index 0"), "{reasons:?}");
        Ok(())
    }

    /// Subsets validated against a count of the caller's own.
    #[test]
    fn validate_subsets() -> Result {
        use ElementType::Face;
        use FamilyType::{NonOverlapping, Partition, Unrestricted};

        let stage = crate::tests::stage("anon.usda")?;
        let mesh = grid(&stage, "/Mesh", 2)?;
        family(
            &mesh,
            Face,
            "halves",
            None,
            &[(Some(&[0, 1]), &[(1.0, &[2, 3])]), (Some(&[2, 3]), &[(1.0, &[0, 1])])],
        )?;
        let halves = Subset::in_family(&mesh, None, Some("halves"))?;
        assert!(Subset::validate(&halves, 4, Partition)?.is_empty());
        assert!(Subset::validate(&[], 4, Partition)?.is_empty());
        assert_eq!(Subset::unassigned_indices_in(&halves, 6, None)?, [4, 5]);

        let short = Subset::validate(&halves, 5, Partition)?;
        assert_eq!(short.len(), 2, "{short:?}");
        assert!(short[0].contains("at time DEFAULT does not match the element count 5"));
        assert!(short[1].contains("at time 1 does not match the element count 5"));

        let long = Subset::validate(&halves, 3, NonOverlapping)?;
        assert!(
            long.iter()
                .all(|reason| reason.contains("greater than the element count 3"))
        );
        assert_eq!(long.len(), 2, "{long:?}");

        family(
            &mesh,
            Face,
            "overlap",
            None,
            &[(Some(&[0, 1]), &[]), (Some(&[1, -1]), &[])],
        )?;
        let overlap = Subset::in_family(&mesh, None, Some("overlap"))?;
        let reasons = Subset::validate(&overlap, 4, NonOverlapping)?;
        assert_eq!(reasons.len(), 2, "{reasons:?}");
        assert!(reasons[0].contains("Found overlapping index 1 in GeomSubset at path </Mesh/overlap_1>"));
        assert!(reasons[1].contains("less than 0 at time DEFAULT"));
        assert_eq!(Subset::validate(&overlap, 4, Unrestricted)?.len(), 1);

        // Subsets with nothing in them have nothing out of bounds.
        family(&mesh, Face, "empty", None, &[(None, &[])])?;
        let empty = Subset::in_family(&mesh, None, Some("empty"))?;
        assert!(Subset::validate(&empty, 4, Unrestricted)?.is_empty());

        // Subsets of different element types are no family.
        family(&mesh, ElementType::Point, "points", None, &[(Some(&[0]), &[])])?;
        let mut mixed = empty;
        mixed.extend(Subset::in_family(&mesh, None, Some("points"))?);
        let reasons = Subset::validate(&mixed, 4, Unrestricted)?;
        assert_eq!(
            reasons,
            ["Subset at path </Mesh/points_0> has elementType point, which does not match 'face'."]
        );
        Ok(())
    }
}
