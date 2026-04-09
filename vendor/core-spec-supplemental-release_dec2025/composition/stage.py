import os
from collections import deque
from dataclasses import dataclass, field
from enum import IntEnum
from functools import total_ordering
from pprint import pprint
from typing import *

from data_types import Asset
from data_types.listop import ListOp, UniqueList
from file_formats.parsers.binary.binary_parser import BinaryParser, Scene
from file_formats.parsers.binary.types import SpecForm
from file_formats.parsers.binary.values import ValueRep
from file_formats.specialized_types import ObjectPath, Reference, Retiming


class Tokens:
    "A series of constant tokens for use in this algorithm"

    primChildren = "primChildren"
    inheritPaths = "inheritPaths"
    variantSetNames = "variantSetNames"
    variantSetChildren = "variantSetChildren"
    variantChildren = "variantChildren"
    variantSelection = "variantSelection"
    references = "references"
    payload = "payload"
    specializes = "specializes"
    defaultPrim = "defaultPrim"
    pathSeparator = "/"
    root = "/"
    active = "active"
    properties = "properties"
    timeSamples = "timeSamples"
    layerRelocates = "layerRelocates"
    subLayers = "subLayers"
    subLayerOffsets = "subLayerOffsets"


class Arc(IntEnum):
    "The ordered list of the arcs themselves"

    Local = 0
    Inherit = 1
    Variant = 2
    Relocate = 3
    Reference = 4
    Payload = 5
    Specialize = 6

    def __repr__(self):
        return self.name


@total_ordering
@dataclass
class Spec:
    form: SpecForm
    fields: Dict[str, ValueRep]
    source_path: str
    layer: Optional["Layer"] = None
    arc: List[Arc] = field(default_factory=list)
    offset: Retiming = field(default_factory=Retiming)

    def __repr__(self):
        return f"Spec <{self.source_path} - {self.layer} - {self.arc[0].name}>"

    def get_name(self):
        return os.path.basename(self.source_path)

    def copy(self, arc=None, offset=None):
        inst = Spec(**self.__dict__)
        arc = arc or []
        inst.arc = arc + self.arc.copy()
        if offset:
            inst.offset += offset
        return inst

    def child_prim_path(self, name):
        if self.source_path in ("/", None):
            return f"/{name}"

        return "/".join((self.source_path, name))

    def get_prim_children_paths(self):
        children = self.fields.get(Tokens.primChildren, None)
        children = children.value if children else []
        for child in children:
            child_path = self.child_prim_path(child)
            yield (child_path)

    def __eq__(self, other: "Spec"):
        if not isinstance(other, Spec):
            return False
        return all(
            (
                self.form == other.form,
                self.fields == other.fields,
                self.source_path == other.source_path,
                self.layer.file_path == other.layer.file_path,
                self.arc == other.arc,
                self.offset == other.offset,
            )
        )

    def __lt__(self, other: "Spec"):
        if Tokens.specializes in self.fields and Tokens.specializes not in other.fields:
            return True

        for my_arc, other_arc in zip(self.arc, other.arc):
            if my_arc == other_arc:
                continue
            return my_arc < other_arc

        return False

    def get_variant_set_path(self, variant_set_name):
        path = "/".join((self.source_path, f"{{{variant_set_name}=}}"))
        return path

    def get_variant_set_name(self):
        assert self.form == SpecForm.VariantSet
        name = self.get_name()[1:-2]
        return name

    def get_variant_path(self, variant_name):
        path = f"{self.source_path[:-1]}{variant_name}}}"
        return path


@dataclass
class Prim:
    """A collection of specs to flatten down a representation of a prim"""

    path: str
    specs: List[Spec] = field(default_factory=list)
    is_dirty: bool = False
    visit_count: int = 0
    children: Set[str] = field(default_factory=set)

    def add_spec(self, spec: Spec):
        if spec in self.specs:
            return

        self.is_dirty = True
        self.specs.append(spec)

    def add_specs(self, specs):
        for spec in specs:
            self.add_spec(spec)

    def sort_specs(self):
        self.specs = sorted(self.specs)

    def add_child(self, child):
        self.children.add(child)

    def resolve_metadata(self, name):
        values = []
        for spec in sorted(self.specs):
            if value := spec.fields.get(name):
                values.append(value)

        if not values:
            return

        # Make sure our type is consistent and filter any that don't match
        primary = values.pop(0)

        result = primary.value
        # Some types join together
        if isinstance(primary.value, ListOp):
            result = primary.value
            for vtvalue in values:
                result = result.combined_with(vtvalue.value)

            result = list(result.reduced().ordered_elements())
            result = ListOp(explicit_items=UniqueList(result))

        elif isinstance(primary.value, Dict):
            result = merge_vtdictionary_with_values(primary.value, values)

        elif isinstance(primary.value, list):
            result = primary.value.copy()
            for vtvalue in values:
                for v in vtvalue.value:
                    if v not in result:
                        result.append(v)

        value_rep = ValueRep()
        value_rep.type = primary.type
        value_rep.value = result
        value_rep._is_processed = True
        return value_rep

    def get_variant_configuration(self) -> Dict[str, str]:
        result = {}

        # The names give us ordering and is required
        variant_set_names = self.resolve_metadata(Tokens.variantSetNames)
        if not variant_set_names:
            return result

        variant_set_names = variant_set_names.value.explicit_items

        # The selection gives us the value
        variant_selection = self.resolve_metadata(Tokens.variantSelection)
        if not variant_selection:
            return result

        for name in variant_set_names:
            value = variant_selection.value.get(name)
            if not value:
                continue

            result[name] = value[0]

        return result

    def reduced_fields(self):
        fields = {}

        field_keys = []
        for spec in self.specs:
            field_keys.extend(spec.fields.keys())

        for key in field_keys:
            value = self.resolve_metadata(key)
            fields[key] = value
        return fields

    def get_type(self):
        for spec in self.specs:
            return spec.form

    def get_property(self, name) -> Tuple[SpecForm, Dict[str, ValueRep]]:
        property_type = SpecForm.Unknown
        fields = {}

        found = []
        for spec in self.specs:
            properties = spec.fields.get(Tokens.properties)
            if not properties:
                continue

            properties = properties.value
            if name not in properties:
                continue

            prop_spec_path = ".".join((spec.source_path, name))
            prop_spec = spec.layer._scene.get(prop_spec_path)

            prop_spec = Spec(
                prop_spec.form,
                prop_spec.fields,
                prop_spec_path,
                spec.layer,
                spec.arc,
                spec.offset,
            )
            if prop_spec not in found:
                found.append(prop_spec)

        if not found:
            return property_type, fields

        property_type = found[0].form

        field_keys = []
        for spec in found:
            field_keys.extend(spec.fields.keys())

        # TODO: Implement merging of property data if applicable
        primary = found[0]
        fields = primary.fields

        if timeSamples := fields.get(Tokens.timeSamples):
            timecodes = timeSamples.value
            offsets = []
            for frame, value in timecodes:
                frame = primary.offset.apply(frame)
                offsets.append((frame, value))

            val = ValueRep()
            val.type = timeSamples.type
            val.value = offsets
            val._is_processed = True
            fields[Tokens.timeSamples] = val

        return property_type, fields

    def get_name(self):
        return os.path.basename(self.path)


class Layer:
    CACHE = {}

    def __init__(self, file_path):
        self.file_path = file_path
        # TODO: Crate file should be closed. This will be addressed when moved to a shared layer reader.
        self._crate_file = open(self.file_path, mode="rb")
        self._scene = BinaryParser(self._crate_file).build_scene()
        self.prims = {}
        self.relocates = {}

    def __hash__(self):
        return self.filepath.__hash__()

    def __repr__(self):
        return f"Layer<{os.path.basename(self.file_path)}>"

    @classmethod
    def Open(cls, filepath, *args, **kwargs):
        if not os.path.exists(filepath):
            filepath = os.path.abspath(os.path.join(os.path.dirname(__file__), filepath))
        if not os.path.exists(filepath):
            raise OSError(f"Could not find {filepath}")
        inst = cls.CACHE.get(filepath)
        if not inst:
            inst = cls.CACHE[filepath] = cls(filepath, *args, **kwargs)
            inst.build_hierarchy()

        return inst

    def build_hierarchy(self):
        stack = deque()
        pseudoroot = self.build_prim(Tokens.root)

        # Pseudoroots have some specific composition attributes
        self.get_relocates(pseudoroot)
        self.get_sublayers(pseudoroot)

        # We can process the prims breadth first
        # so that we can collect as many opinions up front that might
        # affect the hierarchy below
        stack.append(pseudoroot)
        while stack:
            prim: Prim = stack.popleft()
            prim.visit_count += 1
            if prim.visit_count > 10:
                raise RuntimeError(f"Cannot resolve {prim.path} in {self.file_path}")
            self.compose_prim(prim)

            if prim.is_dirty:
                stack.append(prim)
            else:
                prim.sort_specs()

            for child in self.populate_prim_children(prim):
                prim.add_child(child.get_name())
                stack.append(child)

    def build_prim(self, path, arc=None, offset=None) -> Prim:
        prim = self.prims.get(path)
        if not prim:
            prim = Prim(path, self.get_specs(path, arc=arc, offset=offset))
            self.prims[path] = prim

        return prim

    def get_specs(self, path, arc=None, offset: Retiming = None):
        specs = []
        if prim := self.prims.get(path):
            specs: List[Spec] = [s.copy(arc=arc, offset=offset) for s in prim.specs]

        elif spec := self._scene.get(path):
            spec = self._make_spec(path, spec, arc=arc)
            specs = [spec]

        return specs

    def _make_spec(
        self,
        path,
        spec,
        arc=None,
        offset=None,
    ):
        offset = offset or Retiming()
        arc = arc or [Arc.Local]
        return Spec(spec.form, spec.fields, layer=self, source_path=path, offset=offset, arc=arc)

    def get_relocates(self, pseudoroot):
        if layerRelocates := pseudoroot.specs[0].fields.get(Tokens.layerRelocates):
            self.relocates = layerRelocates.value

    def get_sublayers(self, pseudoroot):
        primary = pseudoroot.specs[0]
        if subLayers := primary.fields.get(Tokens.subLayers):
            subLayers = subLayers.value
        else:
            return

        if offsets := primary.fields.get(Tokens.subLayerOffsets, None):
            offsets = offsets.value
        else:
            offsets = []

        assert len(offsets) == len(subLayers)
        for file_path, offset in zip(subLayers, offsets):
            file_path = self.resolve_path(file_path)
            layer = Layer.Open(file_path)

            specs = layer.get_specs(pseudoroot.path, offset=offset)
            pseudoroot.specs.extend(specs)

    def resolve_path(self, file_path):
        path = os.path.abspath(os.path.join(os.path.dirname(self.file_path), file_path))
        return path

    def populate_prim_children(self, prim):
        child_spec_map = {}

        for spec in prim.specs:
            for child_path in spec.get_prim_children_paths():
                arc = spec.arc
                insertion_path, did_relocate = self.make_target_path(child_path, prim, spec)
                if not insertion_path:
                    continue
                if did_relocate:
                    arc = [Arc.Relocate] + arc
                child_specs = spec.layer.get_specs(child_path, arc=arc, offset=spec.offset)
                child_spec_map.setdefault(insertion_path, []).extend(child_specs)

        for path, specs in child_spec_map.items():
            if path in self.prims:
                continue

            prim = self.build_prim(path)
            prim.add_specs(specs)
            yield prim

    def make_target_path(self, child_path, prim, spec):
        name = os.path.basename(child_path)
        if prim.path == Tokens.root:
            return f"/{name}", False

        result = Tokens.pathSeparator.join((prim.path, name))

        if result in self.relocates and spec.arc[0] == Arc.Local and spec.source_path == prim.path:
            return None, False

        did_relocate = False
        for original, remap in self.relocates.items():
            if result == original:
                result = remap
                did_relocate = True
                break

        return result, did_relocate

    def compose_prim(self, prim: Prim):
        variant_configuration = prim.get_variant_configuration()

        prim.is_dirty = False
        # Copy the specs list because we'll be modifying it
        spec: Spec
        for spec in prim.specs.copy():
            # Inheritance
            if inherits := spec.fields.get(Tokens.inheritPaths):
                inherits = self._flattened_from_spec(inherits.value)
                self.process_inherits(prim, spec, inherits)

            # Variants
            if variantSetChildren := spec.fields.get(Tokens.variantSetChildren):
                variantSetChildren = variantSetChildren.value
                self.process_variants_sets(prim, spec, variantSetChildren)

            if variant_configuration and (variant_children := spec.fields.get(Tokens.variantChildren)):
                variant_children = variant_children.value
                self.process_variants(prim, spec, variant_children, variant_configuration)

            # References
            if references := spec.fields.get(Tokens.references):
                references = self._flattened_from_spec(references.value)
                self.process_references(prim, spec, references)

            # Payloads
            if payloads := spec.fields.get(Tokens.payload):
                payloads = self._flattened_from_spec(payloads.value)
                self.process_payloads(prim, spec, payloads)

            # Specialized
            if specializes := spec.fields.get(Tokens.specializes):
                specializes = self._flattened_from_spec(specializes.value)
                self.process_specializes(prim, spec, specializes)

    def get_default_prim(self):
        prim_path = self.prims[Tokens.root].specs[0].fields.get(Tokens.defaultPrim).value
        if not prim_path.startswith(Tokens.root):
            prim_path = Tokens.root + prim_path

        return prim_path

    def process_inherits(self, prim: Prim, spec: Spec, inherits: List[str], mode=Arc.Inherit):
        arc = [mode] + spec.arc
        for inherit_path in inherits:
            relpath = os.path.relpath(inherit_path, spec.source_path)
            inherit_path = os.path.abspath(os.path.join(prim.path, relpath))
            if os.name == "nt":
                # I need to use abspath to resolve all the relative paths
                # But windows has reverse slash pathing and puts the drive letter in
                inherit_path = inherit_path.replace("\\", "/")[2:]
            exists_in_layer = inherit_path in self.prims
            if not exists_in_layer:
                continue

            # Make sure we record the arc of how we got here
            specs = self.get_specs(inherit_path, arc=arc, offset=spec.offset)
            prim.add_specs(specs)

    def process_variants_sets(self, prim: Prim, spec: Spec, variantSetChildren: List[str]):
        for variant_set_name in variantSetChildren:
            variant_set = spec.get_variant_set_path(variant_set_name)
            variant_set_specs = spec.layer.get_specs(variant_set, arc=spec.arc, offset=spec.offset)
            prim.add_specs(variant_set_specs)

    def process_variants(
        self,
        prim: Prim,
        spec: Spec,
        variant_children: List[str],
        variant_configuration: Dict[str, str],
    ):
        variant_set_name = spec.get_variant_set_name()
        variant_name = variant_configuration.get(variant_set_name)
        if variant_name not in variant_children:
            return

        variant_path = spec.get_variant_path(variant_name)

        arc = [Arc.Variant] + spec.arc

        variant_specs = self.get_specs(variant_path, arc=arc, offset=spec.offset)
        prim.add_specs(variant_specs)

    def process_references(self, prim, spec, references, mode=Arc.Reference):
        arc = [mode] + spec.arc
        reference: Reference
        for reference in references:
            # Extract asset_path and prim_path from target
            asset_path: str | None = None
            prim_path: str | None = None
            match reference.target:
                case (Asset.__origin__() as asset_obj, ObjectPath() as object_path):
                    asset_path = str(asset_obj)
                    prim_path = str(object_path)
                case Asset.__origin__() as asset_obj:
                    asset_path = str(asset_obj)
                case ObjectPath() as object_path:
                    prim_path = str(object_path)
                case _:
                    raise ValueError(f"Invalid target: {reference.target}")

            if asset_path:
                layer = Layer.Open(self.resolve_path(asset_path))
            else:
                layer = spec.layer

            prim_path = prim_path or layer.get_default_prim()
            reference_specs = layer.get_specs(prim_path, arc=arc, offset=spec.offset + reference.retiming)
            prim.add_specs(reference_specs)

    def process_payloads(self, prim, spec, payloads):
        return self.process_references(prim, spec, payloads, mode=Arc.Payload)

    def process_specializes(self, prim, spec, specializes):
        # TODO: Need to figure out how to apply specializations, but being lazy for now
        self.process_inherits(prim, spec, specializes, mode=Arc.Specialize)

    @classmethod
    def _flattened_from_spec(cls, value: ListOp) -> list:
        return list(value.ordered_elements())


class Stage:
    def __init__(self, root_layer):
        assert isinstance(root_layer, Layer)
        self.root_layer = root_layer
        self.scene = Scene()

    @classmethod
    def Open(cls, *args, **kwargs):
        root_layer = Layer.Open(*args, **kwargs)
        inst = cls(root_layer)

        inst.build_hierarchy()
        return inst

    def get(self, path):
        return self.scene.get(path)

    def __contains__(self, item):
        return item in self.scene

    def build_hierarchy(self, path=None):
        path = path or Tokens.root

        prim: Prim = self.root_layer.prims[path]
        prim.specs.sort()

        prim_fields = prim.reduced_fields()
        self.scene.add_spec(path, prim.get_type(), prim_fields)

        # Only build out the hierarchy for prims that are active
        if active := prim_fields.get(Tokens.active):
            active = active.value
            if not active:
                return

        if properties := prim_fields.get(Tokens.properties):
            properties = properties.value
            for prop in properties:
                prop_type, prop_fields = prim.get_property(prop)
                prop_path = ".".join((path, prop))

                self.scene.add_spec(prop_path, prop_type, prop_fields)

        for child in prim.children:
            if path == Tokens.root:
                child_path = f"/{child}"
            else:
                child_path = f"{path}/{child}"
            self.build_hierarchy(child_path)


def merge_vtdictionary_with_values(source, values):
    result = {}
    # TODO: Implement a more recursive implementation
    #       A simple deepcopy is not sufficient due to VtValues being backed by IoBuffers
    for key, value in source.items():
        result[key] = value

    # TODO: Implement a more recursive implementation
    for vtvalue in values:
        for k, v in vtvalue.value.items():
            if k not in result:
                result[k] = v

    return source


if __name__ == "__main__":
    stage = Stage.Open("./composition/tests/assets/inheritance/entry.usd")
    prim = stage.root_layer.prims.get("/Root")
    pprint(stage.root_layer.prims)

    print(stage.get("/Root.first").fields["default"].value)
