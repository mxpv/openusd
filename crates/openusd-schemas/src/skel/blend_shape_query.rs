//! The blend shapes a skinnable prim binds, and the weights and offsets that
//! deform it through them (C++ `UsdSkelBlendShapeQuery`).
//!
//! The query reads the prim's `skel:blendShapeTargets` once and lays out
//! each target's sub-shapes: its primary shape at weight 1, an implicit rest
//! shape at weight 0, and its inbetweens, sorted by weight. The layout is a
//! snapshot: after an edit to the targets, a target's activation, or an
//! inbetween's weight, build a new query. Offsets and point indices are read
//! when asked for, at the default time.

use std::ops::Range;

use openusd::Result;
use openusd::gf;
use openusd::usd::{Prim, SchemaBase};
use openusd::vt::Value;

use super::inbetween::InbetweenShape;
use super::skinning::{BlendShapeWeighted, SubShape, apply_blend_shapes, interpolate_run, is_close, sub_shape_run};
use super::{BindingAPI, BlendShape, BlendShapeSchema};

/// The blend shapes bound to one prim, laid out as sub-shapes.
///
/// Build with [`BlendShapeQuery::new`]. A blend shape is indexed by its
/// position in `skel:blendShapeTargets`; a sub-shape by its position in the
/// query's layout, where each blend shape's sub-shapes are contiguous.
#[derive(Debug, Clone)]
pub struct BlendShapeQuery {
    prim: Prim,
    /// One entry per `skel:blendShapeTargets` target, in target order.
    blend_shapes: Vec<Shape>,
    /// Every blend shape's sub-shapes, each blend shape's sorted by weight.
    sub_shapes: Vec<Slot>,
    /// The inbetween shapes the sub-shapes name.
    inbetweens: Vec<InbetweenShape>,
}

/// One `skel:blendShapeTargets` target.
#[derive(Debug, Clone)]
struct Shape {
    /// The target, where it is a `BlendShape`.
    shape: Option<BlendShape>,
    /// The target's sub-shapes in the layout: none for a target that is not a
    /// `BlendShape` or is inactive.
    sub_shapes: Range<usize>,
}

/// One sub-shape in the layout.
#[derive(Debug, Clone, Copy)]
struct Slot {
    /// The blend shape the sub-shape belongs to.
    blend_shape: usize,
    /// The sub-shape, `None` for the rest shape; an inbetween indexes the
    /// query's inbetweens.
    shape: Option<SubShape>,
    /// The weight the sub-shape applies at.
    weight: f32,
}

/// One sub-shape a set of blend-shape weights applies (an entry of C++
/// `ComputeSubShapeWeights`' three parallel outputs).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SubShapeWeight {
    /// The weight the sub-shape's offsets are scaled by.
    pub weight: f32,
    /// The blend shape the sub-shape belongs to.
    pub blend_shape: usize,
    /// The sub-shape's index in the query's layout.
    pub sub_shape: usize,
}

impl BlendShapeQuery {
    /// The query over the blend shapes `binding`'s prim targets through
    /// `skel:blendShapeTargets` (C++ `UsdSkelBlendShapeQuery`'s constructor).
    /// A target that is another relationship is replaced by that
    /// relationship's forwarded targets, where C++ reads the targets as
    /// authored. A target that is not a `BlendShape` prim, or is inactive,
    /// keeps its place with no sub-shapes. An inbetween without a weight, or with one
    /// within `1e-6` of 0 or 1, is left out.
    pub fn new(binding: &BindingAPI) -> Result<Self> {
        let mut blend_shapes = Vec::new();
        let mut sub_shapes = Vec::new();
        let mut inbetweens = Vec::new();
        for (index, target) in binding
            .blend_shape_targets_rel()
            .forwarded_targets()?
            .into_iter()
            .enumerate()
        {
            let first = sub_shapes.len();
            let shape = BlendShape::get(binding.stage(), target)?;
            if let Some(shape) = &shape
                && shape.is_active()?
            {
                let mut weights = Vec::new();
                for inbetween in shape.inbetweens()? {
                    if let Some(weight) = inbetween.weight()?
                        && !is_close(weight, 0.0)
                        && !is_close(weight, 1.0)
                    {
                        weights.push((SubShape::Inbetween(inbetweens.len()), weight));
                        inbetweens.push(inbetween);
                    }
                }
                sub_shapes.extend(
                    sub_shape_run(SubShape::Primary, weights)
                        .into_iter()
                        .map(|(shape, weight)| Slot {
                            blend_shape: index,
                            shape,
                            weight,
                        }),
                );
            }
            blend_shapes.push(Shape {
                shape,
                sub_shapes: first..sub_shapes.len(),
            });
        }
        Ok(Self {
            prim: binding.prim().clone(),
            blend_shapes,
            sub_shapes,
            inbetweens,
        })
    }

    /// The prim whose blend shapes the query lays out.
    pub fn prim(&self) -> &Prim {
        &self.prim
    }

    /// The blend shape at `index` in `skel:blendShapeTargets`, where that
    /// target is a `BlendShape` (C++ `GetBlendShape`).
    pub fn blend_shape(&self, index: usize) -> Option<&BlendShape> {
        self.blend_shapes.get(index)?.shape.as_ref()
    }

    /// The inbetween the sub-shape at `index` is, where it is one (C++
    /// `GetInbetween`).
    pub fn inbetween(&self, index: usize) -> Option<&InbetweenShape> {
        match self.sub_shapes.get(index)?.shape? {
            SubShape::Inbetween(inbetween) => self.inbetweens.get(inbetween),
            SubShape::Primary => None,
        }
    }

    /// The blend shape the sub-shape at `index` belongs to, `0` for an index
    /// past the layout, as C++ answers (C++ `GetBlendShapeIndex`).
    pub fn blend_shape_index(&self, index: usize) -> usize {
        self.sub_shapes.get(index).map_or(0, |slot| slot.blend_shape)
    }

    /// The number of `skel:blendShapeTargets` targets (C++
    /// `GetNumBlendShapes`).
    pub fn num_blend_shapes(&self) -> usize {
        self.blend_shapes.len()
    }

    /// The number of sub-shapes in the layout, rest shapes included (C++
    /// `GetNumSubShapes`).
    pub fn num_sub_shapes(&self) -> usize {
        self.sub_shapes.len()
    }

    /// The sub-shapes `weights` apply, one weight per blend shape in target
    /// order (C++ `ComputeSubShapeWeights`). Each blend shape's weight
    /// interpolates between its two nearest sub-shapes, as
    /// [`skinning::sub_shape_weights`](super::skinning::sub_shape_weights)
    /// describes. `None` unless `weights` holds one weight per blend shape.
    ///
    /// A blend shape with no sub-shapes applies nothing, where C++ reads past
    /// the end of its layout.
    pub fn sub_shape_weights(&self, weights: &[f32]) -> Option<Vec<SubShapeWeight>> {
        if weights.len() != self.blend_shapes.len() {
            return None;
        }
        let mut applied = Vec::with_capacity(weights.len() * 2);
        for (blend_shape, (shape, &weight)) in self.blend_shapes.iter().zip(weights).enumerate() {
            // TODO(perf): the run could be kept in the layout's own form, and
            // read as a slice.
            let run: Vec<(Option<usize>, f32)> = shape
                .sub_shapes
                .clone()
                .map(|index| {
                    let slot = self.sub_shapes[index];
                    (slot.shape.map(|_| index), slot.weight)
                })
                .collect();
            applied.extend(
                interpolate_run(weight, &run)
                    .into_iter()
                    .map(|(sub_shape, weight)| SubShapeWeight {
                        weight,
                        blend_shape,
                        sub_shape,
                    }),
            );
        }
        Some(applied)
    }

    /// The weight of every sub-shape in the layout, zero for the ones
    /// `weights` do not apply (C++ `ComputeFlattenedSubShapeWeights`). `None`
    /// unless `weights` holds one weight per blend shape.
    pub fn flattened_sub_shape_weights(&self, weights: &[f32]) -> Option<Vec<f32>> {
        let mut flattened = vec![0.0; self.sub_shapes.len()];
        for applied in self.sub_shape_weights(weights)? {
            flattened[applied.sub_shape] = applied.weight;
        }
        Some(flattened)
    }

    /// Each blend shape's `pointIndices`, empty for a dense shape or a target
    /// that is not a `BlendShape` (C++ `ComputeBlendShapePointIndices`).
    /// Indices authored as `uint[]`, the type the attribute had before, are
    /// read too.
    pub fn blend_shape_point_indices(&self) -> Result<Vec<Vec<i32>>> {
        // TODO(rayon): each blend shape's indices are read independently.
        self.blend_shapes
            .iter()
            .map(|shape| {
                let Some(shape) = &shape.shape else {
                    return Ok(Vec::new());
                };
                Ok(match shape.point_indices_attr().get::<Value>()? {
                    Some(Value::IntVec(indices)) => indices,
                    Some(Value::UintVec(indices)) => indices
                        .into_iter()
                        .map(|index| i32::try_from(index).unwrap_or(0))
                        .collect(),
                    _ => Vec::new(),
                })
            })
            .collect()
    }

    /// Each sub-shape's point offsets: the blend shape's `offsets` for its
    /// primary shape, the inbetween's for an inbetween, and none for the rest
    /// shape (C++ `ComputeSubShapePointOffsets`).
    pub fn sub_shape_point_offsets(&self) -> Result<Vec<Vec<gf::Vec3f>>> {
        self.sub_shape_offsets(BlendShape::offsets, InbetweenShape::offsets)
    }

    /// Each sub-shape's normal offsets, laid out as
    /// [`sub_shape_point_offsets`](Self::sub_shape_point_offsets) (C++
    /// `ComputeSubShapeNormalOffsets`).
    pub fn sub_shape_normal_offsets(&self) -> Result<Vec<Vec<gf::Vec3f>>> {
        self.sub_shape_offsets(BlendShape::normal_offsets, InbetweenShape::normal_offsets)
    }

    /// `points` deformed by the sub-shapes `weights` apply (C++
    /// `ComputeDeformedPoints`). `point_indices` holds each blend shape's
    /// point indices and `offsets` each sub-shape's offsets, as
    /// [`blend_shape_point_indices`](Self::blend_shape_point_indices) and
    /// [`sub_shape_point_offsets`](Self::sub_shape_point_offsets) answer
    /// them. A sub-shape with no offsets is skipped. `None` when an index
    /// names no blend shape or sub-shape, or a shape's offsets do not fit
    /// `points`, as [`apply_blend_shapes`] requires.
    pub fn deformed_points(
        weights: &[SubShapeWeight],
        point_indices: &[Vec<i32>],
        offsets: &[Vec<gf::Vec3f>],
        points: &[gf::Vec3f],
    ) -> Option<Vec<gf::Vec3f>> {
        let mut shapes = Vec::with_capacity(weights.len());
        for applied in weights {
            let offsets = offsets.get(applied.sub_shape)?;
            let indices = point_indices.get(applied.blend_shape)?;
            if !offsets.is_empty() {
                shapes.push(BlendShapeWeighted {
                    weight: applied.weight,
                    offsets,
                    point_indices: indices,
                });
            }
        }
        apply_blend_shapes(points, &shapes)
    }

    /// `normals` deformed as [`deformed_points`](Self::deformed_points)
    /// deforms points, with `offsets` the sub-shapes' normal offsets, then
    /// each normalized (C++ `ComputeDeformedNormals`).
    pub fn deformed_normals(
        weights: &[SubShapeWeight],
        point_indices: &[Vec<i32>],
        offsets: &[Vec<gf::Vec3f>],
        normals: &[gf::Vec3f],
    ) -> Option<Vec<gf::Vec3f>> {
        let mut deformed = Self::deformed_points(weights, point_indices, offsets, normals)?;
        // TODO(rayon): each normal normalizes independently.
        for normal in &mut deformed {
            *normal = normal.normalize();
        }
        Some(deformed)
    }

    /// Every sub-shape's offsets packed by point, for applying the blend
    /// shapes on a GPU (C++ `ComputePackedShapeTable`). Each point's entry in
    /// the second array is the `[start, end)` range of the first that holds
    /// its offsets, each `(x, y, z, sub-shape index)`. The table covers one
    /// point more than the largest point index or offset count, as C++ lays
    /// it out; a dense shape's offsets run from point 0. Both are empty when
    /// no shape has offsets or indices.
    ///
    /// `None` for a negative point index, or a sparse shape with fewer
    /// offsets than point indices, where C++ reads out of bounds.
    pub fn packed_shape_table(&self) -> Result<Option<(Vec<gf::Vec4f>, Vec<gf::Vec2i>)>> {
        let point_indices = self.blend_shape_point_indices()?;
        let offsets = self.sub_shape_point_offsets()?;
        // TODO(rayon): the largest index reduces over the blend shapes
        // independently.
        let mut largest = offsets.iter().map(Vec::len).max().unwrap_or(0);
        for &index in point_indices.iter().flatten() {
            let Ok(index) = usize::try_from(index) else {
                return Ok(None);
            };
            largest = largest.max(index);
        }
        if largest == 0 {
            return Ok(Some((Vec::new(), Vec::new())));
        }
        let num_points = largest + 1;

        // Each blend shape's sub-shapes other than its rest shape hold offsets
        // for each point the shape names, or every point for a dense shape.
        let mut per_point = vec![0u32; num_points];
        let mut dense = 0u32;
        for (indices, shape) in point_indices.iter().zip(&self.blend_shapes) {
            let count = shape.sub_shapes.len().saturating_sub(1) as u32;
            if indices.is_empty() {
                dense += count;
            } else {
                for &index in indices {
                    per_point[index as usize] += count;
                }
            }
        }
        let mut ranges = Vec::with_capacity(num_points);
        let mut start = 0i32;
        for count in per_point {
            let end = start + (count + dense) as i32;
            ranges.push(gf::vec2i(start, end));
            start = end;
        }

        let mut next: Vec<usize> = ranges.iter().map(|range| range.x as usize).collect();
        let mut table = vec![gf::Vec4f::default(); start as usize];
        for (index, slot) in self.sub_shapes.iter().enumerate() {
            let offsets = &offsets[index];
            if slot.shape.is_none() || offsets.is_empty() {
                continue;
            }
            let indices = &point_indices[slot.blend_shape];
            let count = if indices.is_empty() {
                offsets.len()
            } else {
                indices.len()
            };
            if offsets.len() < count {
                return Ok(None);
            }
            for (position, offset) in offsets[..count].iter().enumerate() {
                let point = indices.get(position).map_or(position, |&point| point as usize);
                table[next[point]] = gf::vec4f(offset.x, offset.y, offset.z, index as f32);
                next[point] += 1;
            }
        }
        Ok(Some((table, ranges)))
    }

    /// Each sub-shape's offsets: `primary` of its blend shape for the primary
    /// shape, `inbetween` of its inbetween, and none for the rest shape.
    fn sub_shape_offsets(
        &self,
        primary: impl Fn(&BlendShape) -> Result<Option<Vec<gf::Vec3f>>>,
        inbetween: impl Fn(&InbetweenShape) -> Result<Option<Vec<gf::Vec3f>>>,
    ) -> Result<Vec<Vec<gf::Vec3f>>> {
        // TODO(rayon): each sub-shape's offsets are read independently.
        self.sub_shapes
            .iter()
            .map(|slot| {
                let offsets = match slot.shape {
                    None => None,
                    Some(SubShape::Inbetween(index)) => inbetween(&self.inbetweens[index])?,
                    Some(SubShape::Primary) => match &self.blend_shapes[slot.blend_shape].shape {
                        Some(shape) => primary(shape)?,
                        None => None,
                    },
                };
                Ok(offsets.unwrap_or_default())
            })
            .collect()
    }
}
