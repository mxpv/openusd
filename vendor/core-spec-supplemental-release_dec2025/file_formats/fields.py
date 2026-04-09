import collections.abc
import functools
import typing

import data_types
from file_formats import spec_path, specialized_types, verifiers

ExtensionTypes = (
    data_types.ScalarType
    | data_types.DimensionedType
    | data_types.Utf8TextType
    | data_types.ScalarArrayType
    | data_types.DimensionedArrayType
    | data_types.Utf8TextArrayType
    | data_types.Dictionary
    | data_types.StringListOp
    | data_types.TokenListOp
    | data_types.IntListOp
    | data_types.Int64ListOp
    | data_types.UIntListOp
    | data_types.UInt64ListOp
)

CoreTypes = (
    ExtensionTypes
    | specialized_types.Variability
    | specialized_types.Specifier
    | specialized_types.DefaultValue
    | specialized_types.TimeSampleMap
    | data_types.listop.ListOp[specialized_types.ObjectPath]
    | data_types.listop.ListOp[specialized_types.Reference]
    | data_types.listop.ListOp[specialized_types.Payload]
    | list[specialized_types.Retiming]
    | list[specialized_types.Relocate]
)


ObjectPathTargetsPrimVerifier = verifiers.PropertyVerifier("targets_prim", True)
FieldDefinitionType = typing.TypeVar("FieldDefinitionType", bound=CoreTypes)


class InitializeSentinel:
    """Sentinel indicating fallback aquisition will initialize a new value of the field's type without arguments"""

    __instance = None

    def __new__(cls, *args, **kwargs):
        if cls.__instance is None:
            cls.__instance = super().__new__(cls)
        return cls.__instance

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}()"


# This was originally a dataclass but there were issues accessing the FieldDefinitionType at runtime
class FieldDefinition(typing.Generic[FieldDefinitionType]):
    def __init__(
        self,
        name: data_types.Token,
        forms: spec_path.SpecFormFlags,
        required_forms: spec_path.SpecFormFlags = spec_path.SpecFormFlags(0),
        fallback: FieldDefinitionType | InitializeSentinel = InitializeSentinel(),
        verifier: typing.Callable[FieldDefinitionType, bool] | None = None,
    ):
        self.__name = name
        self.__forms = forms
        self.__required_forms = required_forms
        self.__fallback = fallback
        self.__verifier = verifier

        if not self.forms:
            raise ValueError("FieldDefinition requires at least one supported form flag.")
        if missing_required := (self.required_forms & ~self.forms):
            raise ValueError(
                f"{missing_required} are specified as required but not included in the field definition's allowed forms"
            )

    @property
    def name(self) -> data_types.Token:
        return self.__name

    @property
    def forms(self) -> spec_path.SpecFormFlags:
        return self.__forms

    @property
    def required_forms(self) -> spec_path.SpecFormFlags:
        return self.__required_forms

    @property
    def verifier(self) -> typing.Callable[FieldDefinitionType, bool] | None:
        return self.__verifier

    def __str__(self) -> str:
        # The string representations of DefaultType and TimeSampleMap are quite large, so they're special cased here.
        type_name = data_types.type_name(self.data_type) or str(self.data_type)
        fallback = self.acquire_fallback()
        return (
            f"{self.name}:\n"
            f"    {type_name}\n"
            f"    forms: {self.forms}\n"
            f"    fallback: {fallback if not isinstance(fallback, (str, data_types.Token.__origin__)) else repr(fallback)}\n"
            f"    verifier: {str(self.verifier)}"
        )

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}({repr(self.__name)}, {repr(self.__forms)}, required_forms={repr(self.__required_forms)}, fallback={repr(self.__fallback)}, verifier={repr(self.__verifier)})"

    @property
    def data_type(self) -> type:
        return typing.get_args(self.__orig_class__)[0]

    def acquire_fallback(self) -> FieldDefinitionType:
        return self.data_type() if self.__fallback is InitializeSentinel() else self.__fallback


class FieldRegistry(collections.abc.Mapping[data_types.Token, FieldDefinition]):
    __instance = None

    def __new__(cls, *args, **kwargs):
        if cls.__instance is None:
            cls.__instance = super().__new__(cls)
        return cls.__instance

    def __init__(self):
        core_fields = [
            # Layer Fields
            FieldDefinition[data_types.AssetArray](
                name=data_types.Token("subLayers"),
                forms=spec_path.SpecFormFlags.Layer,
                verifier=verifiers.ElementVerifier(verifiers.RegexVerifier(".+")),
            ),
            FieldDefinition[list[specialized_types.Retiming]](
                name=data_types.Token("subLayerOffsets"), forms=spec_path.SpecFormFlags.Layer
            ),
            FieldDefinition[data_types.Token](
                name=data_types.Token("defaultPrim"), forms=spec_path.SpecFormFlags.Layer
            ),
            FieldDefinition[list[specialized_types.Relocate]](
                name=data_types.Token("layerRelocates"), forms=spec_path.SpecFormFlags.Layer
            ),
            # Timing Fields
            FieldDefinition[data_types.Double](
                name=data_types.Token("timeCodesPerSecond"),
                fallback=data_types.Double(24),
                forms=spec_path.SpecFormFlags.Layer,
            ),
            FieldDefinition[data_types.Double](
                name=data_types.Token("framesPerSecond"),
                fallback=data_types.Double(24),
                forms=spec_path.SpecFormFlags.Layer,
                verifier=verifiers.IntervalVerifier(left=0.0, boundary=verifiers.IntervalVerifier.Boundary.Open),
            ),
            FieldDefinition[data_types.Double](
                name=data_types.Token("startTimeCode"),
                fallback=data_types.Double(0),
                forms=spec_path.SpecFormFlags.Layer,
            ),
            FieldDefinition[data_types.Double](
                name=data_types.Token("endTimeCode"),
                fallback=data_types.Double(0),
                forms=spec_path.SpecFormFlags.Layer,
            ),
            # Hierarchy Fields
            FieldDefinition[data_types.TokenArray](
                name=data_types.Token("primChildren"),
                forms=(spec_path.SpecFormFlags.Layer | spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant),
                verifier=verifiers.ElementVerifier(verifiers.IdentifierVerifier),
            ),
            FieldDefinition[data_types.TokenArray](
                name=data_types.Token("propertyChildren"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.ElementVerifier(verifiers.PropertyNameVerifier),
            ),
            FieldDefinition[data_types.TokenArray](
                name=data_types.Token("variantSetChildren"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.ElementVerifier(verifiers.IdentifierVerifier),
            ),
            FieldDefinition[data_types.TokenArray](
                name=data_types.Token("variantChildren"),
                forms=spec_path.SpecFormFlags.VariantSet,
                verifier=verifiers.ElementVerifier(verifiers.VariantNameVerifier),
            ),
            # Composition Arc Fields
            FieldDefinition[data_types.listop.ListOp[specialized_types.Reference]](
                name=data_types.Token("references"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
            ),
            FieldDefinition[data_types.listop.ListOp[specialized_types.Payload]](
                name=data_types.Token("payload"), forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant
            ),
            FieldDefinition[data_types.listop.ListOp[specialized_types.ObjectPath]](
                name=data_types.Token("inheritPaths"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.ElementVerifier(ObjectPathTargetsPrimVerifier),
            ),
            FieldDefinition[data_types.listop.ListOp[specialized_types.ObjectPath]](
                name=data_types.Token("specializes"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.ElementVerifier(ObjectPathTargetsPrimVerifier),
            ),
            FieldDefinition[data_types.StringListOp](
                name=data_types.Token("variantSetNames"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.ElementVerifier(verifiers.IdentifierVerifier),
            ),
            FieldDefinition[specialized_types.VariantSelectionMap](
                name=data_types.Token("variantSelection"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.DictionaryVerifier(verifiers.IdentifierVerifier, verifiers.VariantSelectionVerifier),
            ),
            # Ordering Fields
            FieldDefinition[data_types.TokenArray](
                name=data_types.Token("primOrder"),
                forms=spec_path.SpecFormFlags.Layer | spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.ElementVerifier(verifiers.IdentifierVerifier),
            ),
            FieldDefinition[data_types.TokenArray](
                name=data_types.Token("propertyOrder"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                verifier=verifiers.ElementVerifier(verifiers.PropertyNameVerifier),
            ),
            # User Interface Fields
            FieldDefinition[data_types.String](
                name=data_types.Token("displayName"),
                forms=spec_path.SpecFormFlags.Property | spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
            ),
            FieldDefinition[data_types.String](
                name=data_types.Token("displayGroup"), forms=spec_path.SpecFormFlags.Property
            ),
            FieldDefinition[data_types.StringArray](
                name=data_types.Token("displayGroupOrder"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
            ),
            FieldDefinition[data_types.Bool](
                name=data_types.Token("hidden"),
                forms=spec_path.SpecFormFlags.Property | spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                fallback=data_types.Bool(False),
            ),
            # User Fields
            FieldDefinition[data_types.String](
                name=data_types.Token("documentation"),
                forms=spec_path.SpecFormFlags.Layer
                | spec_path.SpecFormFlags.Prim
                | spec_path.SpecFormFlags.Variant
                | spec_path.SpecFormFlags.Property,
            ),
            FieldDefinition[data_types.String](
                name=data_types.Token("comment"),
                forms=spec_path.SpecFormFlags.Layer
                | spec_path.SpecFormFlags.Prim
                | spec_path.SpecFormFlags.Variant
                | spec_path.SpecFormFlags.Property,
            ),
            FieldDefinition[data_types.Dictionary](
                name=data_types.Token("customLayerData"), forms=spec_path.SpecFormFlags.Layer
            ),
            FieldDefinition[data_types.Dictionary](
                name=data_types.Token("customData"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant | spec_path.SpecFormFlags.Property,
            ),
            FieldDefinition[data_types.Dictionary](
                name=data_types.Token("assetInfo"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant | spec_path.SpecFormFlags.Property,
            ),
            # typeName is shared between attribute and prim/variant specs even though their
            # functions and rules are different
            FieldDefinition[data_types.Token](
                name=data_types.Token("typeName"),
                forms=spec_path.SpecFormFlags.Attribute
                | spec_path.SpecFormFlags.Prim
                | spec_path.SpecFormFlags.Variant,
                required_forms=spec_path.SpecFormFlags.Attribute,
                verifier=verifiers.TypeNameVerifier,
            ),
            # Prim Fields
            FieldDefinition[specialized_types.Specifier](
                name=data_types.Token("specifier"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                fallback=specialized_types.Specifier.Over,
                required_forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
            ),
            FieldDefinition[data_types.Bool](
                name=data_types.Token("active"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                fallback=data_types.Bool(True),
            ),
            FieldDefinition[data_types.Bool](
                name=data_types.Token("instanceable"),
                forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant,
                fallback=data_types.Bool(False),
            ),
            FieldDefinition[data_types.Bool](
                name=data_types.Token("kind"), forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Variant
            ),
            # Property Field
            FieldDefinition[data_types.Bool](
                name=data_types.Token("custom"),
                forms=spec_path.SpecFormFlags.Property,
                required_forms=spec_path.SpecFormFlags.Property,
                fallback=data_types.Bool(False),
            ),
            # Attribute Fields
            # TODO: Spline
            FieldDefinition[specialized_types.Variability](
                name=data_types.Token("variability"),
                forms=spec_path.SpecFormFlags.Attribute,
                fallback=specialized_types.Variability.Varying,
            ),
            FieldDefinition[data_types.TokenArray](
                name=data_types.Token("allowedTokens"), forms=spec_path.SpecFormFlags.Attribute
            ),
            FieldDefinition[data_types.listop.ListOp[specialized_types.ObjectPath]](
                name=data_types.Token("connectionPaths"), forms=spec_path.SpecFormFlags.Attribute
            ),
            FieldDefinition[specialized_types.DefaultValue](
                name=data_types.Token("default"),
                fallback=InitializeSentinel(),
                forms=spec_path.SpecFormFlags.Attribute,
                # Note that the verifier will fail the fallback value. This allows the `DefaultValue` to take on
                # an empty state but it should never author that state.
                verifier=verifiers.PropertyVerifier("empty", False),
            ),
            FieldDefinition[specialized_types.TimeSampleMap](
                name=data_types.Token("timeSamples"), forms=spec_path.SpecFormFlags.Attribute
            ),
            # Relationship Fields
            FieldDefinition[data_types.listop.ListOp[specialized_types.ObjectPath]](
                name=data_types.Token("targetPaths"), forms=spec_path.SpecFormFlags.Relationship
            ),
        ]

        self._fields_by_name = {field.name: field for field in core_fields}

    def __hash__(self) -> int:
        return 0

    def __eq__(self) -> bool:
        return self is FieldRegistry()

    def __getitem__(self, name: data_types.Token) -> FieldDefinitionType:
        return self._fields_by_name[name]

    def __iter__(self):
        for key in self._fields_by_name:
            yield key

    def __len__(self):
        return len(self._fields_by_name)

    def __str__(self) -> str:
        return "\n".join(str(self[key]) for key in sorted(self._fields_by_name.keys()))

    @functools.cache
    def fields_by_form(self, form: spec_path.SpecFormFlags) -> frozenset[FieldDefinition]:
        return frozenset(field for field in self._fields_by_name.values() if form in field.forms)

    @functools.cache
    def required_fields_by_form(self, form: spec_path.SpecFormFlags) -> frozenset[FieldDefinition]:
        return frozenset(field for field in self._fields_by_name.values() if form in field.required_forms)

    def extend(self, extension_fields: typing.Sequence[FieldDefinition[ExtensionTypes]]):
        if invalid_field := next(
            (field for field in extension_fields if field.data_type not in typing.get_args(ExtensionTypes)), None
        ):
            raise TypeError(f"Extension field {invalid_field} did not match {ExtensionTypes}")
        if reregistered_name := next((field for field in extension_fields if field.name in self._fields_by_name), None):
            raise ValueError(f"Extension field {invalid_field} uses name already registered")
        self._fields_by_name |= {field.name: field for field in extension_fields}

        self.fields_by_form.clear_cache()
        self.required_fields_by_form.clear_cache()


if __name__ == "__main__":
    print(FieldRegistry())
    print("")
    print(
        f"Layer Fields: {', '.join(str(field.name) for field in FieldRegistry().fields_by_form(spec_path.SpecFormFlags.Layer))}"
    )
    print(
        f"Prim Fields: {', '.join(str(field.name) for field in FieldRegistry().fields_by_form(spec_path.SpecFormFlags.Prim))}"
    )
    print(
        f"Variant Set Fields: {', '.join(str(field.name) for field in FieldRegistry().fields_by_form(spec_path.SpecFormFlags.VariantSet))}"
    )
    print(
        f"Variant Fields: {', '.join(str(field.name) for field in FieldRegistry().fields_by_form(spec_path.SpecFormFlags.Variant))}"
    )
    print(
        f"Property Fields: {', '.join(str(field.name) for field in FieldRegistry().fields_by_form(spec_path.SpecFormFlags.Property))}"
    )
    print(
        f"Relationship Fields: {', '.join(str(field.name) for field in FieldRegistry().fields_by_form(spec_path.SpecFormFlags.Relationship))}"
    )
    print(
        f"Attribute Fields: {', '.join(str(field.name) for field in FieldRegistry().fields_by_form(spec_path.SpecFormFlags.Attribute))}"
    )
