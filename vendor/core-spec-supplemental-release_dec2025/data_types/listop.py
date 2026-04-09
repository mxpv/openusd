from __future__ import annotations

import collections
import collections.abc
import dataclasses
import itertools
import typing
import warnings

ElementType = typing.TypeVar("ElementType", bound=collections.abc.Hashable)


class UniqueList(collections.abc.Sequence[ElementType]):
    """Sequence that preserves the order and uniqueness of elements.

    Each property of a list operation is required to be an ordered unique
    sequence of elements.
    """

    def __init__(self, elements: collections.abc.Iterable[ElementType] = ()):
        self._elements = list(elements)
        self._elementsAsSet = set(self._elements)
        if len(self._elements) != len(self._elementsAsSet):
            counter = collections.Counter(self._elements)
            counter.subtract(self._elementsAsSet)
            raise ValueError(f"UniqueList initialized with repeated elements: {set(counter.elements())}")

    def __eq__(self, other: collections.abc.Sequence[ElementType]):
        return len(other) == len(self) and all(s == o for s, o in zip(self, other))

    def __repr__(self):
        return f"{type(self).__qualname__}({repr(self._elements)})"

    def __getitem__(self, index: int):
        return self._elements[index]

    def __contains__(self, value: ElementType):
        return value in self._elementsAsSet

    def __len__(self):
        return len(self._elements)

    def count(self, value: ElementType) -> int:
        return 1 if value in self else 0


@dataclasses.dataclass(frozen=True, kw_only=True)
class ListOp(typing.Generic[ElementType]):
    """Operations that may be composed to produce an ordered sequence of
    elements

    A ListOp may be explicit or composable."""

    explicit_items: UniqueList[ElementType] | None = None
    deleted_items: UniqueList[ElementType] = dataclasses.field(default_factory=UniqueList[ElementType])
    prepended_items: UniqueList[ElementType] = dataclasses.field(default_factory=UniqueList[ElementType])
    appended_items: UniqueList[ElementType] = dataclasses.field(default_factory=UniqueList[ElementType])

    def __post_init__(self):
        if self.explicit_items is not None and (self.deleted_items or self.prepended_items or self.appended_items):
            warnings.warn(
                "ListOp authored with both an explicit item list "
                "and composable operations. The composable "
                "operations will be ignored."
            )

    def __bool__(self):
        """Return True if the list operation may produce a side effect when
        composed

        Inert list operations may be dropped from a chain or stack of list ops
        as if they had been applied."""
        return (
            self.explicit_items is not None
            or bool(self.deleted_items)
            or bool(self.prepended_items)
            or bool(self.appended_items)
        )

    @property
    def is_explicit(self) -> bool:
        """Returns true if the explicit item sequence has been authored

        An explicit list op
        """
        return self.explicit_items is not None

    def _compose_over_explicit(self, weaker_list_op: ListOp[ElementType]) -> ListOp[ElementType]:
        """Applies composable operations to an explicit weaker list op.

        Always produces a new explicit list op."""
        assert not self.is_explicit
        assert weaker_list_op.is_explicit

        explicit_items = UniqueList[ElementType](
            itertools.chain(
                (e for e in self.prepended_items if e not in self.appended_items),
                (
                    e
                    for e in (weaker_list_op.explicit_items)
                    if e not in itertools.chain(self.deleted_items, self.prepended_items, self.appended_items)
                ),
                self.appended_items,
            )
        )

        result = ListOp[ElementType](explicit_items=explicit_items)
        assert result.is_explicit
        return result

    def _compose_deleted_items(self, weaker_list_op: ListOp[ElementType]) -> UniqueList[ElementType]:
        items_from_weaker = (
            e
            for e in (weaker_list_op.deleted_items)
            if e not in itertools.chain(self.prepended_items, self.appended_items)
        )
        items_from_stronger = (
            e
            for e in self.deleted_items
            if e not in itertools.chain(weaker_list_op.deleted_items, self.prepended_items, self.appended_items)
        )
        # Note that the weaker items appear before the stronger items in the
        # normative ordering but the ordering of deleted items should not
        # affect downstream usage since deleted items don't affect
        # 'ordered_elements'.
        return UniqueList[ElementType](itertools.chain(items_from_weaker, items_from_stronger))

    def _compose_prepended_items(self, weaker_list_op: ListOp[ElementType]) -> UniqueList[ElementType]:
        items_from_weaker = (
            e
            for e in weaker_list_op.prepended_items
            if e not in itertools.chain(self.deleted_items, self.prepended_items, self.appended_items)
        )
        items_from_stronger = (e for e in self.prepended_items if e not in self.appended_items)
        return UniqueList[ElementType](itertools.chain(items_from_stronger, items_from_weaker))

    def _compose_appended_items(self, weaker_list_op: ListOp[ElementType]) -> UniqueList[ElementType]:
        items_form_weaker = (
            e
            for e in weaker_list_op.appended_items
            if e not in itertools.chain(self.deleted_items, self.prepended_items, self.appended_items)
        )
        # Stronger items intentionally are ordered after weaker items as they
        # are modeling "appending" to a list.
        return UniqueList[ElementType](itertools.chain(items_form_weaker, self.appended_items))

    def _compose_over_appliable(self, weaker_list_op: ListOp[ElementType]) -> ListOp[ElementType]:
        """Applies composable operations to an composable weaker list op.

        Always produces a new composable list op."""
        assert not self.is_explicit
        assert not weaker_list_op.is_explicit
        result = ListOp[ElementType](
            deleted_items=self._compose_deleted_items(weaker_list_op),
            prepended_items=self._compose_prepended_items(weaker_list_op),
            appended_items=self._compose_appended_items(weaker_list_op),
        )
        assert not result.is_explicit
        return result

    def combined_with(self, weaker_list_op: ListOp[ElementType]) -> ListOp[ElementType]:
        """Produce a new ListOp through either explicit replacement or
        applying composable operations."""

        # As an optimization, if both are inert, return a new inert list op as
        # this is equivalent to composing an inert over an inert.
        if not self and not weaker_list_op:
            return ListOp[ElementType]()
        # As an optimization, if self is inert, return a copy of weaker as this
        # is equivalent to composing an inert over a weaker.
        if not self:
            return (
                ListOp[ElementType](explicit_items=weaker_list_op.explicit_items)
                if weaker_list_op.is_explicit
                else ListOp[ElementType](
                    appended_items=weaker_list_op.appended_items,
                    deleted_items=weaker_list_op.deleted_items,
                    prepended_items=weaker_list_op.prepended_items,
                )
            )
        # If self is explicit, weaker_list_op does not affect the composed
        # result.
        if self.is_explicit:
            # Note that spurious appended, prepended, and deleted items are
            # dropped
            return ListOp[ElementType](explicit_items=UniqueList[ElementType](self.explicit_items))
        # As an optimization, if weaker is inert return a copy of self.
        # Since the explicit case is handled above, we don't need to consider
        # it here.
        if not weaker_list_op:
            return ListOp[ElementType](
                appended_items=self.appended_items,
                deleted_items=self.deleted_items,
                prepended_items=self.prepended_items,
            )
        if weaker_list_op.is_explicit:
            return self._compose_over_explicit(weaker_list_op)
        return self._compose_over_appliable(weaker_list_op)

    def reduced(self) -> ListOp[ElementType]:
        """Removes a copy of the list op with all spurious elements removed"""
        if self.is_explicit:
            return ListOp[ElementType](explicit_items=self.explicit_items)
        else:
            return ListOp[ElementType](
                appended_items=self.appended_items,
                deleted_items=UniqueList[int](
                    [i for i in self.deleted_items if (i not in self.appended_items and i not in self.prepended_items)]
                ),
                prepended_items=UniqueList[int]([i for i in self.prepended_items if i not in self.appended_items]),
            )

    def ordered_elements(self) -> typing.Sequence[ElementType]:
        """Yields normative ordering of unique elements derived from either the
        explicit or appended/prepended items sequences.

        This is generally used once a chain or stack of list operations have
        been reduced through "compose_over" to a single list operation.

        Note that deleted items do not affect the normative ordering of a
        single list operation."""
        return (
            self.explicit_items
            if self.is_explicit
            else itertools.chain((e for e in self.prepended_items if e not in self.appended_items), self.appended_items)
        )
