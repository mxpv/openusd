import functools
import unittest

from pxr import Sdf

from data_types.tests import harness


class TestReduceChain(harness.TestReduceChain):
    def _make_sdf_list_op(self, list_op_data):
        if "explicit_items" in list_op_data:
            return Sdf.IntListOp.CreateExplicit(list_op_data["explicit_items"])
        return Sdf.IntListOp.Create(
            prependedItems=list_op_data.get("prepended_items", []),
            appendedItems=list_op_data.get("appended_items", []),
            deletedItems=list_op_data.get("deleted_items", []),
        )

    def combine_and_reduce(self, chain):
        def apply(stronger, weaker):
            return stronger.ApplyOperations(weaker)

        combined = functools.reduce(apply, (self._make_sdf_list_op(v) for v in chain))
        if combined.isExplicit:
            return {"explicit_items": (combined.explicitItems)}
        else:
            result = {}
            if combined.prependedItems:
                result["prepended_items"] = [i for i in combined.prependedItems if i not in combined.appendedItems]
            if combined.appendedItems:
                result["appended_items"] = list(combined.appendedItems)
            if combined.deletedItems:
                result["deleted_items"] = [
                    i
                    for i in combined.deletedItems
                    if (i not in combined.prependedItems and i not in combined.appendedItems)
                ]
            return result


if __name__ == "__main__":
    unittest.main()
