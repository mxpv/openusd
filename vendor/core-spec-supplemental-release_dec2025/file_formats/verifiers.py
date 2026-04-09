import collections
import enum
import re
import typing
import unicodedata

import data_types


class RegexVerifier:
    """Verfies that a Utf8TextType matches a regular expression pattern"""

    def __init__(self, pattern: str):
        self._pattern = re.compile(pattern)

    def __repr__(self):
        return f"{type(self).__qualname__}({self._pattern.pattern})"

    def __str__(self):
        return str(self._pattern.pattern)

    def __call__(self, value: data_types.Utf8TextType) -> bool:
        return self._pattern.match(str(value))


class IntervalVerifier:
    """Verifies that an numeric type is within an interval"""

    class Boundary(enum.Flag):
        ClosedLeft = enum.auto()
        ClosedRight = enum.auto()
        Closed = ClosedLeft | ClosedRight
        Open = ~(Closed)

    def __init__(
        self, left: int | float = float("-inf"), right: int | float = float("inf"), boundary: Boundary = Boundary.Open
    ):
        self._left = left
        self._right = right
        self._boundary = boundary

        if self._left == float("nan") or self._right == float("nan"):
            raise ValueError("'nan' not allowed in interval")
        if self._left in (float("inf"), float("-inf")) and (self._boundary & self.Boundary.ClosedLeft):
            raise ValueError("Interval cannot be closed at 'inf' or '-inf'")
        if self._right in (float("inf"), float("-inf")) and (self._boundary & self.Boundary.ClosedRight):
            raise ValueError("Interval cannot be closed at 'inf' or '-inf'")

    def __repr__(self):
        return f"{type(self).__qualname__}({self._left}, {self._right}, {self._boundary})"

    @classmethod
    def _value_to_str(self, value: float | int) -> str:
        match value:
            case float("inf"):
                return "∞"
            case float("-inf"):
                return "-∞"
            case _:
                return str(value)

    def __str__(self):
        return (
            f"{'[' if self._boundary & self.Boundary.ClosedLeft else '('}{self._value_to_str(self._left)}, "
            f"{self._value_to_str(self._right)}{']' if self._boundary & self.Boundary.ClosedRight else ')'}"
        )

    def __call__(self, value):
        return (((self._boundary & self.Boundary.ClosedLeft) and value >= self._left) or value > self._left) and (
            ((self._boundary & self.Boundary.ClosedRight) and value <= self._right) or value < self._right
        )


class UnicodeIdentifierVerifier:
    """Ensures that a string matches the Unicode Identifier Pattern.

    The 'start' and 'continue_' fields are expected to be explicit unicode characters (strings of length 1) or unicode
    categories (strings of length 2). The medial field currently only supports explicit unicode characters
    (strings of length 1).

    There are two variations to the standard unicode identifier pattern which are specified via 'flags'. Optional
    allows an empty string to match. MedialRestart requires the first character after a medial character to be a
    character in Start."""

    class Flags(enum.Flag):
        Optional = enum.auto()
        MedialRestart = enum.auto()

    def __init__(
        self,
        start: collections.abc.Iterable[str],
        continue_: collections.abc.Iterable[str],
        medial: collections.abc.Iterable[str] = None,
        flags=(~Flags.Optional & ~Flags.MedialRestart),
    ):
        if any(len(s) not in (1, 2) for s in start):
            raise ValueError("Start element must be either explicit characters or unicode categories.")
        if any(len(c) not in (1, 2) for c in continue_):
            raise ValueError("Continue element must be either explicit characters or unicode categories.")
        self._medial_values = tuple(medial) if medial else tuple()
        if any(len(m) != 1 for m in self._medial_values):
            raise ValueError("Medial element must be explicit characters.")
        self._start_categories = tuple(s for s in start if len(s) == 2)
        self._start_values = tuple(s for s in start if len(s) == 1)
        self._continue_categories = tuple(c for c in continue_ if len(c) == 2)
        self._continue_values = tuple(c for c in continue_ if len(c) == 1)
        self._medial = tuple(medial) if medial else tuple()
        self._flags = flags

    @property
    def start(self):
        return (*self._start_values, *self._start_categories)

    @property
    def continue_(self):
        return (*self._continue_values, *self._continue_categories)

    @property
    def medial(self):
        return self._medial

    @property
    def flags(self):
        return self._flags

    def __repr__(self):
        return (
            f"{type(self).__qualname__}(start={repr(self.start)}, continue_={repr(self.continue_)}, "
            f"flags={repr(self.flags)})"
        )

    def __str__(self):
        """Outputs a PEG expression that represents the rule"""
        start_category_strings = (f"[{c}]" for c in self._start_categories)
        start_value_strings = (f"'{v}'" for v in self._start_values)
        continue_category_strings = (f"[{c}]" for c in self._continue_categories)
        continue_value_strings = (f"'{v}'" for v in self._continue_values)
        medial_value_strings = (f"'{v}'" for v in self._medial)

        start = f"({'/'.join((*start_category_strings, *start_value_strings))})"
        continue_ = f"({'/'.join((*continue_category_strings, *continue_value_strings))})"
        medial = f"({'/'.join(medial_value_strings)})" if self._medial else None

        if medial is None:
            expression = f"{start}+ {continue_}*"
        elif self.flags & self.Flags.MedialRestart:
            expression = f"{start}+ {continue_}* ({medial} {start}+ {continue_}*)*"
        else:
            expression = f"{start}+ {continue_}* ({medial} {continue_}+)*"
        return f"({expression})?" if self.flags & self.Flags.Optional else expression

    def _verify_start_continue(self, value: str):
        return value and (
            (value[0] in self._start_values or unicodedata.category(value[0]) in self._start_categories)
            and all(
                v in self._continue_values or unicodedata.category(v) in self._continue_categories for v in value[1:]
            )
        )

    def _verify_continue(self, value: str):
        return value and all(
            v in self._continue_values or unicodedata.category(v) in self._continue_categories for v in value
        )

    def __call__(self, value: data_types.Utf8TextType) -> bool:
        value = str(value)
        if not value:
            return bool(self.flags & self.Flags.Optional)
        if self.medial:
            split_value = re.split("|".join(re.escape(m) for m in self.medial), value)
        else:
            split_value = (value,)
        return (
            all(self._verify_start_continue(v) for v in split_value)
            if (self.flags & self.Flags.MedialRestart)
            else self._verify_start_continue(split_value[0]) and all(self._verify_continue(v) for v in split_value[1:])
        )


IdentifierVerifier = UnicodeIdentifierVerifier(
    start=("_", "Lu", "Ll", "Lt", "Lm", "Lo", "Nl"),
    continue_=("Lu", "Ll", "Lt", "Lm", "Lo", "Nl", "Nd", "Mn", "Mc", "Pc"),
)

VariantNameVerifier = UnicodeIdentifierVerifier(
    start=(".", "|", "-", *IdentifierVerifier.start), continue_=("|", "-", "Lu", *IdentifierVerifier.continue_)
)

VariantSelectionVerifier = UnicodeIdentifierVerifier(
    start=VariantNameVerifier.start,
    continue_=VariantNameVerifier.continue_,
    flags=UnicodeIdentifierVerifier.Flags.Optional,
)

PropertyNameVerifier = UnicodeIdentifierVerifier(
    start=IdentifierVerifier.start,
    continue_=IdentifierVerifier.continue_,
    medial=(":",),
    flags=UnicodeIdentifierVerifier.Flags.MedialRestart,
)

TypeNameVerifier = RegexVerifier(r"^[A-Za-z_][A-Za-z0-9_]*(\[\])?$")


class ElementVerifier:
    """Applies a verifier to every element in a sequence"""

    def __init__(self, verifier: typing.Callable[str, bool]):
        self._verifier = verifier

    def __repr__(self):
        return f"{type(self).__qualname__}({repr(self._verifier)})"

    def __str__(self):
        return f"⋀ₑ{{{self._verifier}}}"

    def __call__(self, value) -> bool:
        match value:
            case data_types.listop.ListOp():
                return all(
                    self._verifier(i)
                    for i in (
                        value.explicit_items
                        if value.is_explicit
                        else (*value.prepended_items, *value.appended_items, *value.deleted_items)
                    )
                )
            case collections.abc.Iterable():
                return all(self._verifier(i) for i in value)
            case _:
                raise TypeError("ElementVerifier only applies to ListOp or Iterable types")


class DictionaryVerifier:
    """Applies a key and value verifier to each element in a dictionary"""

    def __init__(self, key_verifier: typing.Callable[str, bool], value_verifier: typing.Callable[str, bool]):
        self._key_verifier = key_verifier
        self._value_verifier = value_verifier

    def __str__(self):
        return f"⋀ₖ{{{self._key_verifier}}} ∧ ⋀ᵥ{{{self._value_verifier}}}"

    def __repr__(self):
        return f"{type(self).__qualname__}({repr(self._key_verifier)}, {repr(self._value_verifier)})"

    def __call__(self, value) -> bool:
        return all(self._key_verifier(k) and self._value_verifier(v) for k, v in value.items())


class PropertyVerifier:
    """Verify that a property takes on a particular value"""

    def __init__(self, name: str, value):
        self._property_name = name
        self._property_value = value

    def __repr__(self):
        return f"{type(self).__qualname__}({repr(self._property_name)}, {repr(self._property_value)})"

    def __str__(self):
        return f".{self._property_name} == {self._property_value}"

    def __call__(self, value) -> bool:
        return getattr(value, self._property_name) == self._property_value


if __name__ == "__main__":
    print("identifier: ", IdentifierVerifier)
    print("variant: ", VariantNameVerifier)
    print("property: ", PropertyNameVerifier)
    print("variantSelection: ", VariantSelectionVerifier)
    print("type: ", TypeNameVerifier)
