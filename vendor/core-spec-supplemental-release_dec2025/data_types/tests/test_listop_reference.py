import dataclasses
import functools
import unittest

from data_types import listop
from data_types.tests import harness


class TestReduceChain(harness.TestReduceChain):
    def _make_reference_list_op(self, list_op_data):
        if "explicit_items" in list_op_data:
            return listop.ListOp[int](explicit_items=listop.UniqueList[int](list_op_data["explicit_items"]))
        return listop.ListOp[int](
            prepended_items=listop.UniqueList[int](list_op_data.get("prepended_items", [])),
            appended_items=listop.UniqueList[int](list_op_data.get("appended_items", [])),
            deleted_items=listop.UniqueList[int](list_op_data.get("deleted_items", [])),
        )

    def combine_and_reduce(self, chain):
        combined = functools.reduce(
            lambda s, w: s.combined_with(w) if s is not None else w, (self._make_reference_list_op(v) for v in chain)
        )
        result = dataclasses.asdict(combined.reduced())
        if not combined.is_explicit:
            assert result["explicit_items"] is None
            del result["explicit_items"]
        if not result["prepended_items"]:
            del result["prepended_items"]
        if not result["appended_items"]:
            del result["appended_items"]
        if not result["deleted_items"]:
            del result["deleted_items"]
        # print(result)
        return {k: list(v) for k, v in result.items()}


if __name__ == "__main__":
    unittest.main()
