import os.path
from pprint import pformat

from file_formats.parsers.binary.types import ListOp, SpecForm, ValueType, Variability


class USDADisplayPrinter:
    """This is a work in progress way to convert the input Binary parser scene into a USDA compatible output"""

    def __init__(self, scene: dict):
        self.text = "#usda 1.0\n"
        self.previous_block_depth = -1

        self.construct(scene)

    def traverse_layer(self, scene, path, spec):
        if properties := spec.fields.get("properties", []):
            for prop in properties.value:
                prop_path = ".".join((path, prop))
                prop_spec = scene[prop_path]

                yield prop_path, prop_spec

        if children := spec.fields.get("primChildren", []):
            for child in children.value:
                if path == "/":
                    child_path = f"/{child}"
                else:
                    child_path = "/".join((path, child))
                child_spec = scene[child_path]

                yield child_path, child_spec

                yield from self.traverse_layer(scene, child_path, child_spec)

    def construct(self, scene):
        pseudoroot_path = "/"
        pseudoroot = scene[pseudoroot_path]

        assert pseudoroot.form == SpecForm.PseudoRoot
        self.text += self.construct_metadata(pseudoroot.fields)
        self.text += "\n"

        for path, spec in self.traverse_layer(scene, pseudoroot_path, pseudoroot):
            match spec.type:
                case SpecForm.Prim:
                    self.text += self.construct_prim(path, spec.fields)
                case SpecForm.Attribute:
                    self.text += self.construct_attribute(path, spec.fields)
                case _:
                    continue
                    raise NotImplementedError(f"Unsupported spec type: {spec.type}")

        while self.previous_block_depth >= 0:
            self.text += f"{self.previous_block_depth * ' '}}}\n"
            self.previous_block_depth -= 4

    def __str__(self):
        return self.text

    def construct_vtvalue(self, vtvalue, indent=0):
        if not vtvalue.is_array:
            match vtvalue.type:
                case ValueType.Bool:
                    return str(int(vtvalue.value))
                case (
                    ValueType.Int
                    | ValueType.UInt
                    | ValueType.Int64
                    | ValueType.UInt64
                    | ValueType.Half
                    | ValueType.Float
                    | ValueType.Double
                    | ValueType.Matrix2d
                    | ValueType.Matrix3d
                    | ValueType.Matrix4d
                    | ValueType.Vec2d
                    | ValueType.Vec3d
                    | ValueType.Vec4d
                    | ValueType.Vec2f
                    | ValueType.Vec3f
                    | ValueType.Vec4f
                    | ValueType.Vec2h
                    | ValueType.Vec3h
                    | ValueType.Vec4h
                    | ValueType.Vec2i
                    | ValueType.Vec3i
                    | ValueType.Vec4i
                    | ValueType.StringVector
                ):
                    return str(vtvalue.value)
                case ValueType.UChar | ValueType.Token | ValueType.String | ValueType.PathExpression:
                    if "\n" in vtvalue.value:
                        return f"'''{vtvalue.value}{indent * ' '}'''"
                    else:
                        return f'"{vtvalue.value}"'
                case ValueType.Dictionary:
                    return self.construct_dictionary(vtvalue.value, indent=indent)
                case ValueType.AssetPath:
                    return f"@{vtvalue.value}@"
                case ValueType.Quath | ValueType.Quatf | ValueType.Quatd:
                    return str(self.process_quats(vtvalue.value))
                case ValueType.Relocates:
                    return pformat(vtvalue.value)
                case ValueType.LayerOffsetVector:
                    # TODO: Not critical
                    pass
                case _:
                    raise NotImplementedError(f"Unsupported value type:{vtvalue.type}")
        else:
            match vtvalue.type:
                case ValueType.Bool:
                    return str([int(v) for v in vtvalue.value])
                case ValueType.AssetPath:
                    vals = [f"@{v}@" for v in vtvalue.value]
                    return "[" + (", ".join(vals)) + "]"
                case (
                    ValueType.Int
                    | ValueType.UInt
                    | ValueType.Int64
                    | ValueType.UInt64
                    | ValueType.Half
                    | ValueType.Float
                    | ValueType.Double
                    | ValueType.Matrix2d
                    | ValueType.Matrix3d
                    | ValueType.Matrix4d
                    | ValueType.Vec2d
                    | ValueType.Vec3d
                    | ValueType.Vec4d
                    | ValueType.Vec2f
                    | ValueType.Vec3f
                    | ValueType.Vec4f
                    | ValueType.Vec2h
                    | ValueType.Vec3h
                    | ValueType.Vec4h
                    | ValueType.Vec2i
                    | ValueType.Vec3i
                    | ValueType.Vec4i
                ):
                    return str(vtvalue.value)
                case ValueType.Quath | ValueType.Quatf | ValueType.Quatd:
                    return str([self.process_quats(v) for v in vtvalue.value])
                case ValueType.Token:
                    return str(vtvalue.value)
                case _:
                    raise NotImplementedError(f"Arrays aren't implemented for {vtvalue.type}")

    def construct_metadata(self, fields, indent=0):
        text = ""
        indent = indent + 4
        for field, vtvalue in fields.items():
            if field in ("primChildren", "properties"):
                continue

            if vtvalue.type.name.endswith("ListOp"):
                text += self.construct_listop(field, vtvalue, indent)
                continue

            value_text = self.construct_vtvalue(vtvalue, indent=indent)
            text += f"{indent * ' '}{field}"
            if value_text:
                text += f" = {value_text}"
            text += "\n"

        indent -= 4
        if not text:
            return text

        text = f"(\n{text}{indent * ' '})\n"

        return text

    def construct_dictionary(self, data, indent=0):
        text = "{\n"
        indent = indent + 4
        for key, value in data.items():
            text += f"{indent * ' '}{value.type.name.lower()} {key}"

            value_text = self.construct_vtvalue(value, indent=indent)
            if value_text:
                text += f" = {value_text}"
            text += "\n"

        indent -= 4
        text += f"{indent * ' '}}}"
        return text

    def construct_prim(self, path, fields):
        text = ""
        indent = (path.count("/") - 1) * 4
        while indent <= self.previous_block_depth:
            text += f"{self.previous_block_depth * ' '}}}\n\n"
            self.previous_block_depth -= 4

        self.previous_block_depth = indent

        fields = fields.copy()  # Copy so we can pop
        text += f"{indent * ' '}{fields.pop('specifier').value.name.lower()}"
        if typeName := fields.pop("typeName", None):
            text += f" {typeName.value}"

        name = os.path.basename(path)
        text += f' "{name}" '

        _ = fields.pop("properties", None)
        _ = fields.pop("primChildren", None)

        if metadata := self.construct_metadata(fields, indent=indent):
            text += metadata
            text += f"{indent * ' '}{{\n"
        else:
            text += "{\n"

        return text

    def construct_listop(self, field: str, vtvalue, indent):
        text = ""
        listop: ListOp = vtvalue.value
        for key, value in listop.to_dict().items():
            if not value:
                continue

            if key == "is_explicit":
                continue

            text += indent * " "
            operation = key.replace("ed_items", "").split("_")[0]
            if operation:
                text += f" {operation} "

            match vtvalue.type:
                case ValueType.StringListOp | ValueType.TokenListOp:
                    strings = [f'"{v}"' for v in value]
                case ValueType.PathListOp:
                    strings = [f"<{v}>" for v in value]
                case ValueType.ReferenceListOp:
                    strings = []
                    for v in value:
                        string = ""
                        if v.asset_path:
                            string += f"@{v.asset_path}@"
                        if v.prim_path:
                            string += f"<{v.prim_path}>"

                        strings.append(string)
                case _:
                    raise NotImplementedError(f"Unsupported value type: {vtvalue.type}")

            if len(value) > 1:
                text += f"{field} = [{', '.join(strings)}]\n"
            else:
                text += f"{field} = {strings[0]}\n"

        return text

    def construct_attribute(self, path, fields):
        indent = (path.count("/")) * 4
        name = os.path.basename(path).split(".", 1)[-1]

        tokens = []
        if custom := fields.get("custom"):
            if custom.value:
                tokens.append("custom")

        if variability := fields.get("variability"):
            if variability.value == Variability.Uniform:
                tokens.append("uniform")

        tokens.append(fields["typeName"].value)
        tokens.append(name)

        text = ""
        if default := fields.get("default"):
            text += f"{indent * ' '}{' '.join(tokens)} = {self.construct_vtvalue(default)}\n"

        if not text:
            text += f"{indent * ' '}{' '.join(tokens)}\n"

        return text

    def process_quats(self, val):
        # Quats need to have the last element up front
        return val[3], val[0], val[1], val[2]
