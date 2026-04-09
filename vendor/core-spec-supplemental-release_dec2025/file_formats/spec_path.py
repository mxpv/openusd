import collections.abc
import copy
import dataclasses
import enum
import itertools
import typing

import data_types
from file_formats import verifiers


class SpecFormFlags(enum.Flag):
    Layer = enum.auto()
    Prim = enum.auto()
    VariantSet = enum.auto()
    Variant = enum.auto()
    Relationship = enum.auto()
    Attribute = enum.auto()
    Property = Relationship | Attribute


@dataclasses.dataclass(frozen=True)
class SpecPathElement:
    form: SpecFormFlags
    name: data_types.Token

    def __post_init__(self):
        match self.form:
            case SpecFormFlags.Layer:
                if self.name is not data_types.Token():
                    raise ValueError(f"LayerSpec was provided a name '{self.name}' but should be empty.")
            case SpecFormFlags.Prim:
                if not verifiers.IdentifierVerifier(str(self.name)):
                    raise ValueError(f"PrimSpec name '{self.name}' does match '{verifiers.IdentifierVerifier}'")
            case SpecFormFlags.VariantSet:
                if not verifiers.IdentifierVerifier(str(self.name)):
                    raise ValueError(f"VariantSet name '{self.name}' does match '{verifiers.IdentifierVerifier}'")
            case SpecFormFlags.VariantSet:
                if not verifiers.VariantNameVerifier(str(self.name)):
                    raise ValueError(f"Variant name '{self.name}' does match '{verifiers.VariantNameVerifier}'")
            case SpecFormFlags.Property:
                if not verifiers.PropertyNameVerifier(str(self.name)):
                    raise ValueError(f"PropertySpec name '{self.name}' does match '{verifiers.PropertyNameVerifier}'")
            case SpecFormFlags.Attribute | SpecFormFlags.Relationship:
                raise ValueError(
                    "SpecPath elements should be assigned SpecFormFlags.Property not SpecFormFlags.Relationship or SpecFormFlags.Attribute"
                )

    @classmethod
    def Layer(cls):
        return cls(SpecFormFlags.Layer, data_types.Token())

    @classmethod
    def Prim(cls, name: str | data_types.Token):
        return cls(
            SpecFormFlags.Prim, name if isinstance(name, data_types.Token.__origin__) else data_types.Token(name)
        )

    @classmethod
    def VariantSet(cls, name: str | data_types.Token):
        return cls(
            SpecFormFlags.VariantSet, name if isinstance(name, data_types.Token.__origin__) else data_types.Token(name)
        )

    @classmethod
    def Variant(cls, name: str | data_types.Token):
        return cls(
            SpecFormFlags.Variant, name if isinstance(name, data_types.Token.__origin__) else data_types.Token(name)
        )

    @classmethod
    def Property(cls, name: str | data_types.Token):
        return cls(
            SpecFormFlags.Property, name if isinstance(name, data_types.Token.__origin__) else data_types.Token(name)
        )


class SpecPath(collections.abc.Sequence[SpecPathElement]):
    """Absolute identifier for a spec in a layer"""

    AllowedChildren = {
        SpecFormFlags.Layer: SpecFormFlags.Prim,
        SpecFormFlags.Prim: SpecFormFlags.Prim | SpecFormFlags.VariantSet | SpecFormFlags.Property,
        SpecFormFlags.VariantSet: SpecFormFlags.Variant,
        SpecFormFlags.Variant: SpecFormFlags.Prim | SpecFormFlags.VariantSet | SpecFormFlags.Property,
        SpecFormFlags.Property: ~(
            SpecFormFlags.Layer
            | SpecFormFlags.Prim
            | SpecFormFlags.VariantSet
            | SpecFormFlags.Variant
            | SpecFormFlags.Property
        ),
    }

    def __init__(self, elements: typing.Sequence[SpecPathElement]):
        if elements[0] != SpecPathElement.Layer():
            raise ValueError("The first element must be a layer.")
        for parent, child in itertools.pairwise(elements):
            self._verify_parent_accepts_child(parent, child)
        self._elements = tuple(elements)

    @property
    def parent(self) -> typing.Self | None:
        if len(self._elements) == 1:
            return None
        parent = copy.copy(self)
        parent._elements = parent._elements[:-1]
        return parent

    @property
    def form(self) -> SpecFormFlags:
        return self._elements[-1].form

    @property
    def name(self) -> data_types.Token:
        return self._elements[-1].name

    def _verify_parent_accepts_child(self, parent: SpecPathElement, child: SpecPathElement):
        if child.form not in self.AllowedChildren[parent.form]:
            raise ValueError(f"Child of form {child.form} must match {self.AllowedChildren[parent.form]}")

    def __repr__(self):
        return f"{type(self).__qualname__}(elements={repr(self._elements[1:])})"

    def __hash__(self) -> int:
        return hash(self._elements)

    def __eq__(self, other: typing.Self) -> bool:
        return self._elements == other._elements

    def __getitem__(self, index: int) -> SpecPathElement:
        return self._elements[index]

    def __len__(self) -> int:
        return len(self._elements)

    def _element_to_string(self, element) -> str:
        match element:
            case SpecPathElement(SpecFormFlags.Prim, name):
                return f"/{name}"
            case SpecPathElement(SpecFormFlags.VariantSet, name):
                return f"{{{name}="
            case SpecPathElement(SpecFormFlags.Variant, name):
                return f"{name}}}"
            case SpecPathElement(SpecFormFlags.Property, name):
                return f".{name}"

    @classmethod
    def absolute_root(self) -> typing.Self:
        return SpecPath(elements=(SpecPathElement.Layer(),))

    def __add__(self, elements: collections.abc.Sequence[SpecPathElement]) -> typing.Self:
        # Only validatation against the tail element is required
        for parent, child in itertools.pairwise((self._elements[-1], *elements)):
            self._verify_parent_accepts_child(parent, child)
        concatenated = copy.copy(self)
        concatenated._elements = (*self._elements, *elements)
        return concatenated

    def __str__(self) -> str:
        if len(self._elements) == 1:
            return "/"
        return (
            result := "".join(self._element_to_string(element) for element in self._elements[1:])
            if self._elements[-1].form != SpecFormFlags.VariantSet
            else f"{result}"
        )


if __name__ == "__main__":
    print(
        str(SpecPath(elements=[SpecPathElement.Layer(), SpecPathElement.Prim("hello"), SpecPathElement.Prim("world")]))
    )
    print(
        str(
            SpecPath(
                elements=[
                    SpecPathElement.Layer(),
                    SpecPathElement.Prim("hello"),
                    SpecPathElement.VariantSet("world"),
                    SpecPathElement.Variant("earth"),
                    SpecPathElement.Property("x"),
                ]
            )
        )
    )
    print(
        SpecPath(
            elements=[SpecPathElement.Layer(), SpecPathElement.Prim("hello"), SpecPathElement.Prim("world")]
        ).parent
        == SpecPath.absolute_root() + [SpecPathElement.Prim("hello")]
    )
    print(
        hash(
            SpecPath(
                elements=[SpecPathElement.Layer(), SpecPathElement.Prim("hello"), SpecPathElement.Prim("world")]
            ).parent
        )
        == hash(SpecPath.absolute_root() + [SpecPathElement.Prim("hello")])
    )
