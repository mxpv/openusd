//! What `UsdGeomPointInstancer` answers beyond its own properties: how many
//! instances it holds, which of them `inactiveIds` and `invisibleIds` mask
//! out, and how those two are authored.

use std::borrow::Cow;
use std::collections::{BTreeSet, HashSet};
use std::iter;

use openusd::Result;
use openusd::sdf;
use openusd::usd::{self, SchemaBase};

use super::{PointInstancer, PointInstancerSchema, PrimMetadata, array_len, tokens};
use crate::SchemaError;

/// Instance counting and masking (C++ `UsdGeomPointInstancer`).
///
/// An instance is named by its id: the element of `ids` at its index, or the
/// index itself where `ids` holds no value. Two sets of ids prune instances.
/// `inactiveIds` is prim metadata, list-edited across layers and the same at
/// every time. `invisibleIds` is an attribute: it can be animated, and a
/// stronger layer's value replaces a weaker one's whole.
///
/// # Example
///
/// ```
/// use openusd::usd;
/// use openusd_schemas::geom::{self, PointInstancerSchema};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// let instancer = geom::PointInstancer::define(&stage, "/Instancer")?;
/// instancer.create_proto_indices_attr()?.set(vec![0, 0, 1, 1])?;
/// assert_eq!(instancer.instance_count(None)?, 4);
///
/// // Nothing is pruned yet, which an empty mask says.
/// assert!(instancer.compute_mask_at_time(None, None)?.is_empty());
///
/// instancer.deactivate_id(1)?;
/// instancer.invis_id(3, None)?;
/// let mask = instancer.compute_mask_at_time(None, None)?;
/// assert_eq!(mask, [true, false, true, false]);
///
/// // The mask contracts any per-instance array.
/// let mut indices = instancer.proto_indices()?.expect("authored above");
/// geom::PointInstancer::apply_mask_to_array(&mask, &mut indices, 1)?;
/// assert_eq!(indices, [0, 1]);
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
impl PointInstancer {
    /// The number of instances at `time`, where `None` is the default time
    /// (C++ `GetInstanceCount`): the length of `protoIndices` there, and zero
    /// where it holds no value.
    pub fn instance_count(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<usize> {
        Ok(array_len(self.proto_indices_at(time)?))
    }

    /// Which instances survive `inactiveIds` and the `invisibleIds` of
    /// `time`, where `None` is the default time (C++ `ComputeMaskAtTime`).
    ///
    /// The mask holds one entry for each of `ids`, `true` for an instance to
    /// keep. With no `ids` given it covers the `ids` attribute's value at
    /// `time`, or the indices of `protoIndices` where `ids` holds none. An
    /// empty mask says every instance survives: it is what comes back where
    /// nothing is pruned, and where the prim has neither `ids` nor
    /// `protoIndices` to cover.
    pub fn compute_mask_at_time(
        &self,
        time: impl Into<Option<usd::TimeCode>>,
        ids: Option<&[i64]>,
    ) -> Result<Vec<bool>> {
        let time = time.into();
        let mut masked: HashSet<i64> = self.composed_inactive_ids()?.into_iter().collect();
        masked.extend(self.invisible_ids_at(time)?.unwrap_or_default());
        if masked.is_empty() {
            return Ok(Vec::new());
        }

        let named = match ids {
            Some(ids) => Some(Cow::Borrowed(ids)),
            None => self.ids_at(time)?.map(Cow::Owned),
        };
        let mask: Vec<bool> = if let Some(ids) = named {
            ids.iter().map(|id| !masked.contains(id)).collect()
        } else {
            // An instance's id is its index.
            let mut mask = vec![true; self.instance_count(time)?];
            for id in masked {
                if let Some(keep) = usize::try_from(id).ok().and_then(|index| mask.get_mut(index)) {
                    *keep = false;
                }
            }
            mask
        };
        Ok(match mask.contains(&false) {
            true => mask,
            false => Vec::new(),
        })
    }

    /// Contract `data` to the elements `mask` keeps, each element being
    /// `element_size` consecutive values (C++ `ApplyMaskToArray`).
    ///
    /// An empty mask keeps everything. So does any mask over an array that
    /// holds exactly one element, which stands for every instance at once.
    /// Otherwise the mask must have one entry for each element of `data`,
    /// and one that does not is [`SchemaError::MaskSizeMismatch`], where C++
    /// warns and returns `false`.
    pub fn apply_mask_to_array<T>(mask: &[bool], data: &mut Vec<T>, element_size: usize) -> Result<(), SchemaError> {
        if mask.is_empty() || data.len() == element_size {
            return Ok(());
        }
        if mask.len() * element_size != data.len() {
            return Err(SchemaError::MaskSizeMismatch {
                mask: mask.len(),
                len: data.len(),
                element_size,
            });
        }
        let mut kept = mask.iter().flat_map(|keep| iter::repeat_n(*keep, element_size));
        data.retain(|_| kept.next().unwrap_or(false));
        Ok(())
    }

    /// Make the instance `id` active again (C++ `ActivateId`); see
    /// [`activate_ids`](Self::activate_ids).
    pub fn activate_id(&self, id: i64) -> Result<()> {
        self.activate_ids(&[id])
    }

    /// Make the instances `ids` active again by removing them from
    /// `inactiveIds` on the edit target (C++ `ActivateIds`).
    ///
    /// The edit target's own opinion is edited as a list op, so an id a
    /// weaker layer deactivates is deleted there, and the rest of that
    /// layer's opinion still composes.
    pub fn activate_ids(&self, ids: &[i64]) -> Result<()> {
        merge_inactive_ids(self.prim(), sdf::Int64ListOp::deleted(ids.iter().copied()))
    }

    /// Make every instance active by authoring an explicit, empty
    /// `inactiveIds` on the edit target, which hides every weaker opinion
    /// (C++ `ActivateAllIds`).
    pub fn activate_all_ids(&self) -> Result<()> {
        let none = sdf::Int64ListOp::explicit([]);
        self.prim().clone().set_inactive_ids(sdf::Value::Int64ListOp(none))?;
        Ok(())
    }

    /// Prune the instance `id` at every time (C++ `DeactivateId`); see
    /// [`deactivate_ids`](Self::deactivate_ids).
    pub fn deactivate_id(&self, id: i64) -> Result<()> {
        self.deactivate_ids(&[id])
    }

    /// Prune the instances `ids` at every time by appending them to
    /// `inactiveIds` on the edit target (C++ `DeactivateIds`).
    ///
    /// The edit target's own opinion is edited as a list op, so the ids
    /// weaker layers deactivate stay deactivated.
    pub fn deactivate_ids(&self, ids: &[i64]) -> Result<()> {
        merge_inactive_ids(self.prim(), sdf::Int64ListOp::appended(ids.iter().copied()))
    }

    /// Show the instance `id` at `time`, where `None` is the default time
    /// (C++ `VisId`); see [`vis_ids`](Self::vis_ids).
    pub fn vis_id(&self, id: i64, time: impl Into<Option<usd::TimeCode>>) -> Result<()> {
        self.vis_ids(&[id], time)
    }

    /// Show the instances `ids` at `time`, where `None` is the default time,
    /// by removing them from `invisibleIds` there (C++ `VisIds`).
    ///
    /// The value `invisibleIds` resolves to at `time` is authored back at
    /// `time` on the edit target, even where none of `ids` was in it. Where
    /// one was, what remains is authored sorted and without duplicates.
    /// Nothing is authored where `invisibleIds` reads no value at `time`, as
    /// at a blocked time sample.
    pub fn vis_ids(&self, ids: &[i64], time: impl Into<Option<usd::TimeCode>>) -> Result<()> {
        let time = time.into();
        let Some(mut invised) = self.invisible_ids_at(time)? else {
            return Ok(());
        };
        let shown: HashSet<i64> = ids.iter().copied().collect();
        if invised.iter().any(|id| shown.contains(id)) {
            invised.retain(|id| !shown.contains(id));
            invised.sort_unstable();
            invised.dedup();
        }
        self.set_invisible_ids(invised, time)
    }

    /// Show every instance at `time`, where `None` is the default time, by
    /// authoring an empty `invisibleIds` there (C++ `VisAllIds`). Nothing is
    /// authored where no layer gives `invisibleIds` a value.
    pub fn vis_all_ids(&self, time: impl Into<Option<usd::TimeCode>>) -> Result<()> {
        match self.invisible_ids_attr().has_authored_value()? {
            true => self.set_invisible_ids(Vec::new(), time.into()),
            false => Ok(()),
        }
    }

    /// Hide the instance `id` at `time`, where `None` is the default time
    /// (C++ `InvisId`); see [`invis_ids`](Self::invis_ids).
    pub fn invis_id(&self, id: i64, time: impl Into<Option<usd::TimeCode>>) -> Result<()> {
        self.invis_ids(&[id], time)
    }

    /// Hide the instances `ids` at `time`, where `None` is the default time,
    /// by adding them to `invisibleIds` there (C++ `InvisIds`).
    ///
    /// The value `invisibleIds` resolves to at `time` is authored back at
    /// `time` on the edit target, followed by each of `ids` it does not
    /// hold yet, once. Nothing is authored where `invisibleIds` reads no
    /// value at `time`, as at a blocked time sample.
    pub fn invis_ids(&self, ids: &[i64], time: impl Into<Option<usd::TimeCode>>) -> Result<()> {
        let time = time.into();
        let Some(mut invised) = self.invisible_ids_at(time)? else {
            return Ok(());
        };
        let mut held: HashSet<i64> = invised.iter().copied().collect();
        invised.extend(ids.iter().copied().filter(|id| held.insert(*id)));
        self.set_invisible_ids(invised, time)
    }

    /// Whether the instancer rotates its instances by `orientationsf`, and
    /// the attribute it rotates them by (C++ `UsesOrientationsf`).
    ///
    /// `orientationsf` is in use where its earliest time sample, or its
    /// default where it has no samples, is a non-empty array. Otherwise the
    /// answer is `false` with `orientations`.
    pub fn uses_orientationsf(&self) -> Result<(bool, usd::Attribute)> {
        let earliest = self.orientationsf_at(usd::TimeCode::EARLIEST)?;
        Ok(match earliest.is_some_and(|orientations| !orientations.is_empty()) {
            true => (true, self.orientationsf_attr()),
            false => (false, self.orientations_attr()),
        })
    }

    /// The ids every layer's `inactiveIds` opinion composes to.
    fn composed_inactive_ids(&self) -> Result<Vec<i64>> {
        let composed = self.prim().inactive_ids()?;
        Ok(composed
            .and_then(|value| value.try_as_int_64_list_op())
            .map(|op| op.flatten())
            .unwrap_or_default())
    }

    /// Author `ids` as the value of `invisibleIds` at `time`, declaring the
    /// attribute where the edit target lacks it, as one edit.
    fn set_invisible_ids(&self, ids: Vec<i64>, time: Option<usd::TimeCode>) -> Result<()> {
        self.invisible_ids_attr_builder()
            .set_at(sdf::Value::Int64Vec(ids), time)
            .build()?;
        Ok(())
    }
}

/// Apply `proposed` over the `inactiveIds` opinion the edit target holds for
/// `prim`, and author the result there (C++
/// `UsdGeomPointInstancerSetOrMergeOverOp`, as it runs with
/// `USDGEOM_POINTINSTANCER_NEW_APPLYOPS` at its default). The two compose
/// into one list op, the held opinion in its [`canonical`] form (C++
/// `SdfListOp::ApplyOperations`).
fn merge_inactive_ids(prim: &usd::Prim, proposed: sdf::Int64ListOp) -> Result<()> {
    prim.clone().update_metadata(tokens::INACTIVE_IDS, |local| {
        let current = local
            .and_then(|value| value.try_as_int_64_list_op())
            .unwrap_or_default();
        Some(sdf::Value::Int64ListOp(proposed.combined_with(&canonical(current))))
    })?;
    Ok(())
}

/// `op` as an edit of a set (C++ `_CanonicalizeListOp`): the ids it adds by
/// any means, prepended in ascending order, and the ids it deletes. An id
/// it both adds and deletes is in both, as C++ deletes before it adds. An
/// explicit op is canonical as it is.
fn canonical(op: sdf::Int64ListOp) -> sdf::Int64ListOp {
    if op.is_explicit() {
        return op;
    }
    let added: BTreeSet<i64> = op.iter().copied().collect();
    sdf::Int64ListOp::prepended(added).with(sdf::ListOpType::Deleted, op.deleted_items().iter().copied())
}

#[cfg(test)]
mod tests {
    use openusd::usd::{SchemaBase, Stage, TimeCode};
    use openusd::{gf, sdf};

    use super::canonical;
    use crate::SchemaError;
    use crate::geom::{PointInstancer, PointInstancerSchema};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    /// The instancer `/Instance` of a new stage, holding `count` instances.
    fn instancer(count: usize) -> Result<PointInstancer> {
        let stage = crate::tests::stage("anon.usda")?;
        let instancer = PointInstancer::define(&stage, "/Instance")?;
        if count > 0 {
            instancer.create_proto_indices_attr()?.set(vec![0; count])?;
        }
        Ok(instancer)
    }

    /// The ids the prim at `path` composes as inactive.
    fn inactive(stage: &Stage, path: &str) -> Result<Vec<i64>> {
        let instancer = PointInstancer::get(stage, path)?.expect("a PointInstancer");
        Ok(instancer.composed_inactive_ids()?)
    }

    /// A stage whose `/Ref` references the instancer `/Source`, which
    /// deactivates the ids 1 and 2.
    fn referencing() -> Result<(tempfile::TempDir, Stage)> {
        Ok(crate::tests::from_usda(
            r#"#usda 1.0
def PointInstancer "Source" (
    inactiveIds = [1, 2]
)
{
    int[] protoIndices = [0, 0, 0, 0]
}

def "Ref" (
    references = </Source>
)
{
}
"#,
        )?)
    }

    /// The count is the length of `protoIndices` at the time asked for, and
    /// zero where it is unset, blocked or empty (C++
    /// `test_ComputeInstancerCount`).
    #[test]
    fn instance_count() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0
def PointInstancer "UnsetIndices"
{
}

def PointInstancer "BlockedIndices"
{
    int[] protoIndices = None
}

def PointInstancer "EmptyIndices"
{
    int[] protoIndices = []
}

def PointInstancer "TimeSampledIndices"
{
    int[] protoIndices.timeSamples = {
        1: [4, 4, 4]
    }
}

def PointInstancer "TimeSampledAndDefaultIndices"
{
    int[] protoIndices = [4, 4, 4, 4]
    int[] protoIndices.timeSamples = {
        1: [4, 4, 4, 4, 4]
    }
}
"#,
        )?;
        for (path, earliest, default) in [
            ("/UnsetIndices", 0, 0),
            ("/BlockedIndices", 0, 0),
            ("/EmptyIndices", 0, 0),
            ("/TimeSampledIndices", 3, 0),
            ("/TimeSampledAndDefaultIndices", 5, 4),
        ] {
            let instancer = PointInstancer::get(&stage, path)?.expect("a PointInstancer");
            assert_eq!(instancer.instance_count(TimeCode::EARLIEST)?, earliest, "{path}");
            assert_eq!(instancer.instance_count(None)?, default, "{path}");
        }
        Ok(())
    }

    /// Hiding an id authors `invisibleIds` at the default time, as one edit
    /// (C++ `test_InstancerInVis`).
    #[test]
    fn invis_authors_default() -> Result {
        let instancer = instancer(0)?;
        let commits = crate::tests::commits(instancer.stage());
        instancer.invis_id(1, None)?;

        assert_eq!(commits.get(), 1);
        assert!(instancer.invisible_ids_attr().has_authored_value()?);
        assert_eq!(instancer.invisible_ids()?, Some(vec![1]));
        Ok(())
    }

    /// Ids are added after the ones already hidden, each once.
    #[test]
    fn invis_appends_once() -> Result {
        let instancer = instancer(0)?;
        instancer.invis_ids(&[3, 1], None)?;
        instancer.invis_ids(&[1, 5, 5, 2], None)?;
        assert_eq!(instancer.invisible_ids()?, Some(vec![3, 1, 5, 2]));
        Ok(())
    }

    /// Showing an id that was hidden leaves the rest sorted.
    #[test]
    fn vis_removes_sorted() -> Result {
        let instancer = instancer(0)?;
        instancer.invis_ids(&[3, 1, 5, 2], None)?;
        instancer.vis_id(5, None)?;
        assert_eq!(instancer.invisible_ids()?, Some(vec![1, 2, 3]));
        Ok(())
    }

    /// Showing an id that was not hidden authors the value as it resolves,
    /// order kept, and an unauthored attribute comes to hold its fallback.
    #[test]
    fn vis_absent_reauthors() -> Result {
        let instancer = instancer(0)?;
        instancer.vis_id(7, None)?;
        assert!(instancer.invisible_ids_attr().has_authored_value()?);
        assert_eq!(instancer.invisible_ids()?, Some(Vec::new()));

        instancer.invis_ids(&[3, 1], None)?;
        instancer.vis_id(7, None)?;
        assert_eq!(instancer.invisible_ids()?, Some(vec![3, 1]));
        Ok(())
    }

    /// A blocked sample reads no value, so nothing is authored over it. A
    /// blocked default reads the fallback, which is authored over the block.
    #[test]
    fn blocked_sample_untouched() -> Result {
        let instancer = instancer(0)?;
        let one = TimeCode::new(1.0);
        instancer
            .create_invisible_ids_attr()?
            .set_at(sdf::Value::ValueBlock, one)?;
        let commits = crate::tests::commits(instancer.stage());
        instancer.invis_id(1, one)?;
        instancer.vis_id(1, one)?;
        assert_eq!(commits.get(), 0);
        assert_eq!(instancer.invisible_ids_at(one)?, None);

        instancer.invisible_ids_attr().block()?;
        instancer.invis_id(1, None)?;
        assert_eq!(instancer.invisible_ids()?, Some(vec![1]));
        Ok(())
    }

    /// Hiding an id at a time starts from what `invisibleIds` resolves to
    /// there, which past the last sample is that sample's value, and
    /// authors the result at that time alone.
    #[test]
    fn invis_per_time() -> Result {
        let instancer = instancer(0)?;
        let (one, two) = (TimeCode::new(1.0), TimeCode::new(2.0));
        instancer.invis_id(1, one)?;
        instancer.invis_id(2, two)?;
        assert_eq!(instancer.invisible_ids_at(two)?, Some(vec![1, 2]));

        instancer.vis_id(1, two)?;
        assert_eq!(instancer.invisible_ids_at(one)?, Some(vec![1]));
        assert_eq!(instancer.invisible_ids_at(two)?, Some(vec![2]));
        Ok(())
    }

    /// Showing everything authors an empty array over an authored value,
    /// and nothing where no value is authored.
    #[test]
    fn vis_all_needs_authored() -> Result {
        let instancer = instancer(0)?;
        let commits = crate::tests::commits(instancer.stage());
        instancer.vis_all_ids(None)?;
        assert_eq!(commits.get(), 0);
        assert!(!instancer.invisible_ids_attr().has_authored_value()?);

        instancer.invis_ids(&[1, 2], None)?;
        instancer.vis_all_ids(None)?;
        assert_eq!(instancer.invisible_ids()?, Some(Vec::new()));
        Ok(())
    }

    /// Deactivating and activating edit the composed `inactiveIds`, one
    /// edit a call.
    #[test]
    fn deactivate_then_activate() -> Result {
        let instancer = instancer(4)?;
        let stage = instancer.stage().clone();
        let commits = crate::tests::commits(&stage);
        instancer.deactivate_ids(&[1, 2])?;
        assert_eq!(commits.get(), 1);
        assert_eq!(inactive(&stage, "/Instance")?, [1, 2]);

        instancer.activate_id(1)?;
        assert_eq!(inactive(&stage, "/Instance")?, [2]);
        instancer.deactivate_id(3)?;
        assert_eq!(inactive(&stage, "/Instance")?, [2, 3]);
        instancer.activate_ids(&[2, 3, 9])?;
        assert!(inactive(&stage, "/Instance")?.is_empty());
        Ok(())
    }

    /// An id a referenced prim deactivates is deleted across the arc, and
    /// the rest of the referenced opinion still composes.
    #[test]
    fn activate_over_reference() -> Result {
        let (_dir, stage) = referencing()?;
        let referencing = PointInstancer::get(&stage, "/Ref")?.expect("a PointInstancer");
        assert_eq!(inactive(&stage, "/Ref")?, [1, 2]);

        referencing.activate_id(1)?;
        referencing.deactivate_id(7)?;
        assert_eq!(inactive(&stage, "/Ref")?, [2, 7]);
        assert_eq!(inactive(&stage, "/Source")?, [1, 2]);

        // The local opinion is a list edit, so a later change to the
        // referenced prim still reaches the referencing one.
        PointInstancer::get(&stage, "/Source")?
            .expect("a PointInstancer")
            .deactivate_id(4)?;
        assert_eq!(inactive(&stage, "/Ref")?, [2, 4, 7]);
        Ok(())
    }

    /// Activating everything hides the referenced opinion, and what is
    /// deactivated afterwards is all there is.
    #[test]
    fn activate_all_explicit() -> Result {
        let (_dir, stage) = referencing()?;
        let referencing = PointInstancer::get(&stage, "/Ref")?.expect("a PointInstancer");
        referencing.activate_all_ids()?;
        assert!(inactive(&stage, "/Ref")?.is_empty());
        assert!(referencing.compute_mask_at_time(None, None)?.is_empty());

        referencing.deactivate_id(3)?;
        assert_eq!(inactive(&stage, "/Ref")?, [3]);
        Ok(())
    }

    /// The list op each edit leaves on the edit target (C++
    /// `SdfListOp::ApplyOperations` over a canonical op).
    #[test]
    fn merged_list_ops() {
        let deactivate = |ids: &[i64]| sdf::Int64ListOp::appended(ids.to_vec());
        let activate = |ids: &[i64]| sdf::Int64ListOp::deleted(ids.to_vec());
        let merged =
            |proposed: &sdf::Int64ListOp, current: sdf::Int64ListOp| proposed.combined_with(&canonical(current));

        // Over nothing, the edit is the opinion.
        assert_eq!(
            merged(&deactivate(&[2, 1]), sdf::Int64ListOp::default()),
            deactivate(&[2, 1])
        );

        // An activation takes the id out of what the layer adds and deletes
        // it from what weaker layers add.
        let after = merged(&activate(&[2]), deactivate(&[2, 1]));
        assert_eq!(after.prepended_items(), [1]);
        assert_eq!(after.deleted_items(), [2]);
        assert!(after.appended_items().is_empty());

        // A deactivation takes the id out of the deletes.
        let after = merged(&deactivate(&[2]), after);
        assert_eq!(after.prepended_items(), [1]);
        assert_eq!(after.appended_items(), [2]);
        assert!(after.deleted_items().is_empty());

        // An explicit opinion stays explicit.
        let explicit = sdf::Int64ListOp::explicit([5, 3, 4]);
        assert_eq!(
            merged(&activate(&[3]), explicit.clone()),
            sdf::Int64ListOp::explicit([5, 4])
        );
        assert_eq!(
            merged(&deactivate(&[5, 9]), explicit),
            sdf::Int64ListOp::explicit([3, 4, 5, 9])
        );
    }

    /// Every id an op adds is prepended in ascending order, whatever it
    /// deletes, and the result holds no `add` or `reorder` items.
    #[test]
    fn canonical_sorts_added() {
        let op = sdf::Int64ListOp::added([9, 2])
            .with(sdf::ListOpType::Prepended, [7])
            .with(sdf::ListOpType::Appended, [3, 7])
            .with(sdf::ListOpType::Deleted, [2, 8, 8])
            .with(sdf::ListOpType::Ordered, [9, 3]);
        let expected = sdf::Int64ListOp::prepended([2, 3, 7, 9]).with(sdf::ListOpType::Deleted, [2, 8]);
        assert_eq!(canonical(op), expected);

        let explicit = sdf::Int64ListOp::explicit([3, 1]);
        assert_eq!(canonical(explicit.clone()), explicit);
    }

    /// With no `ids` attribute an instance's id is its index.
    #[test]
    fn mask_by_index() -> Result {
        let instancer = instancer(4)?;
        assert!(instancer.compute_mask_at_time(None, None)?.is_empty());

        instancer.deactivate_id(1)?;
        instancer.invis_id(3, None)?;
        assert_eq!(instancer.compute_mask_at_time(None, None)?, [true, false, true, false]);
        Ok(())
    }

    /// The `ids` attribute names the instances, and ids given by the caller
    /// take its place.
    #[test]
    fn mask_by_ids() -> Result {
        let instancer = instancer(3)?;
        instancer.create_ids_attr()?.set(vec![10_i64, 11, 12])?;
        instancer.deactivate_ids(&[1, 12])?;

        assert_eq!(instancer.compute_mask_at_time(None, None)?, [true, true, false]);
        assert_eq!(instancer.compute_mask_at_time(None, Some(&[1, 2]))?, [false, true]);
        Ok(())
    }

    /// A pruned id that names no instance leaves the mask empty.
    #[test]
    fn mask_empty_unpruned() -> Result {
        let instancer = instancer(3)?;
        instancer.deactivate_id(8)?;
        assert!(instancer.compute_mask_at_time(None, None)?.is_empty());
        assert!(instancer.compute_mask_at_time(None, Some(&[1, 2]))?.is_empty());
        Ok(())
    }

    /// A prim with neither `ids` nor `protoIndices` has nothing to mask.
    #[test]
    fn mask_without_instances() -> Result {
        let instancer = instancer(0)?;
        instancer.deactivate_id(0)?;
        assert!(instancer.compute_mask_at_time(None, None)?.is_empty());
        Ok(())
    }

    /// The invisible ids are the ones of the time asked for, and the
    /// inactive ones hold at every time. The second sample starts from the
    /// first one's value, so the id hidden there is shown again.
    #[test]
    fn mask_at_time() -> Result {
        let instancer = instancer(3)?;
        let (one, two) = (TimeCode::new(1.0), TimeCode::new(2.0));
        instancer.deactivate_id(0)?;
        instancer.invis_id(1, one)?;
        instancer.invis_id(2, two)?;
        instancer.vis_id(1, two)?;

        assert_eq!(instancer.compute_mask_at_time(one, None)?, [false, false, true]);
        assert_eq!(instancer.compute_mask_at_time(two, None)?, [false, true, false]);
        Ok(())
    }

    #[test]
    fn apply_mask_contracts() -> Result {
        let mask = [true, false, true];
        let mut scalars = vec![10, 11, 12];
        PointInstancer::apply_mask_to_array(&mask, &mut scalars, 1)?;
        assert_eq!(scalars, [10, 12]);

        let mut pairs = vec![0, 1, 10, 11, 20, 21];
        PointInstancer::apply_mask_to_array(&mask, &mut pairs, 2)?;
        assert_eq!(pairs, [0, 1, 20, 21]);
        Ok(())
    }

    /// An empty mask keeps everything, and an array of one element is left
    /// as it is.
    #[test]
    fn apply_mask_passes() -> Result {
        let mut data = vec![1, 2, 3];
        PointInstancer::apply_mask_to_array(&[], &mut data, 1)?;
        assert_eq!(data, [1, 2, 3]);

        let mut constant = vec![4, 5];
        PointInstancer::apply_mask_to_array(&[false, true, false], &mut constant, 2)?;
        assert_eq!(constant, [4, 5]);
        Ok(())
    }

    #[test]
    fn apply_mask_mismatch() {
        let mut data = vec![1, 2, 3];
        let error =
            PointInstancer::apply_mask_to_array(&[true, false], &mut data, 1).expect_err("two entries for three");
        assert!(matches!(
            error,
            SchemaError::MaskSizeMismatch {
                mask: 2,
                len: 3,
                element_size: 1
            }
        ));
        assert_eq!(data, [1, 2, 3]);
    }

    /// `orientationsf` is in use once its earliest value is a non-empty
    /// array, whether that is a sample or the default.
    #[test]
    fn orientationsf_in_use() -> Result {
        let instancer = instancer(1)?;
        let (uses, attr) = instancer.uses_orientationsf()?;
        assert!(!uses);
        assert_eq!(attr, instancer.orientations_attr());

        let orientationsf = instancer.create_orientationsf_attr()?;
        let orientationsf = orientationsf.set(sdf::Value::QuatfVec(Vec::new()))?;
        assert!(!instancer.uses_orientationsf()?.0);

        orientationsf.set_at(sdf::Value::QuatfVec(vec![gf::Quatf::IDENTITY]), TimeCode::new(5.0))?;
        let (uses, attr) = instancer.uses_orientationsf()?;
        assert!(uses);
        assert_eq!(attr, instancer.orientationsf_attr());
        Ok(())
    }
}
