import math
import os

from pxr import Gf, Sdf, Ts, Usd, Vt

print(f"Using USD {Usd.GetVersion()} from {os.path.dirname(os.path.dirname(Usd.__file__))}")

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets"))


def int_range(width, signed):
    raise_to = width
    if signed:
        raise_to -= 1

    maximum = (2**raise_to) - 1
    minimum = -maximum if signed else 0

    return minimum, maximum


class CreateBinaryTests:
    def _create_layer(self, name, string):
        filename = os.path.join(f"gen_{name}.usda")
        layer = Sdf.Layer.CreateAnonymous(filename)
        layer.ImportFromString(string)
        return layer

    def _save_layer(self, layer, name, ext="usdc"):
        filepath = os.path.join(ROOT, "binary", f"gen_{name}.{ext}")
        layer.Export(filepath)

    def _create_stage(self, name, ext="usdc"):
        filepath = os.path.join(ROOT, "binary", f"gen_{name}.{ext}")
        stage = Usd.Stage.CreateNew(filepath)
        return stage

    def run(self):
        print("Starting generator...")
        ver = Usd.GetVersion()

        self.create_vectors()
        self.create_listops()
        self.create_variants()
        self.create_permissions()
        self.create_timesamples()
        self.create_timecodes()
        self.create_relocates()
        self.create_dict()
        self.create_bool()
        self.create_integers()
        self.create_floats()
        self.create_strings()
        self.create_matrices()
        self.create_mathematic_vectors()

        if ver[1] > 24 or (ver[1] == 24 and ver[2] == 11):
            self.create_splines()

        if ver[1] > 23 or (ver[1] == 23 and ver[2] >= 8):
            self.create_path_expression()

        print("Done!")

    def create_bool(self):
        print("\tCreating Boolean Samples...")

        stage = self._create_stage("bool")

        prim = stage.DefinePrim("/root")
        prim.CreateAttribute("unset", Sdf.ValueTypeNames.Bool, custom=False)
        single = prim.CreateAttribute("single", Sdf.ValueTypeNames.Bool, custom=False)
        single.Set(True)

        prim.CreateAttribute("array:unset", Sdf.ValueTypeNames.BoolArray, custom=False)
        array = prim.CreateAttribute("array", Sdf.ValueTypeNames.BoolArray, custom=False)
        array.SetVariability(Sdf.VariabilityUniform)
        array.Set([False, False, True, False, False])

        stage.Save()

    def create_integers(self):
        print("\tCreating Integer Samples...")

        integers = (
            ("uchar", 8, Sdf.ValueTypeNames.UChar, Sdf.ValueTypeNames.UCharArray),
            ("int", 32, Sdf.ValueTypeNames.Int, Sdf.ValueTypeNames.IntArray),
            ("uint", 32, Sdf.ValueTypeNames.UInt, Sdf.ValueTypeNames.UIntArray),
            ("int64", 64, Sdf.ValueTypeNames.Int64, Sdf.ValueTypeNames.Int64Array),
            ("uint64", 64, Sdf.ValueTypeNames.UInt64, Sdf.ValueTypeNames.UInt64Array),
        )

        for file_name, width, single_name, array_name in integers:
            signed = not file_name.startswith("u")
            stage = self._create_stage(file_name)
            minimum, maximum = int_range(width, signed)
            prim = stage.DefinePrim("/root")
            single = prim.CreateAttribute("single", single_name, custom=False)
            single.Set(minimum if signed else maximum)

            array = prim.CreateAttribute("array", array_name, custom=False)
            values = [0, 1, 2, 3, 4, maximum]
            if signed:
                values.insert(0, minimum)
            array.Set(values)

            stage.Save()

    def create_floats(self):
        print("\tCreating Floating Point Samples...")

        precisions = (
            ("half", Sdf.ValueTypeNames.Half, Sdf.ValueTypeNames.HalfArray),
            ("float", Sdf.ValueTypeNames.Float, Sdf.ValueTypeNames.FloatArray),
            ("double", Sdf.ValueTypeNames.Double, Sdf.ValueTypeNames.DoubleArray),
        )
        for file_name, single_name, array_name in precisions:
            stage = self._create_stage(file_name)
            prim = stage.DefinePrim("/root")
            single = prim.CreateAttribute("single", single_name, custom=False)
            single.Set(3.1415)

            array = prim.CreateAttribute("array:lut", array_name, custom=False)
            array.Set([-3.1415, 2.7182, 1.6180])

            array = prim.CreateAttribute("array:ints", array_name, custom=False)
            array.Set([-1, 0, 1])

            stage.Save()

    def create_strings(self):
        print("\tCreating String Samples...")

        stringy_types = (
            ["string", Sdf.ValueTypeNames.String, Sdf.ValueTypeNames.StringArray],
            ["token", Sdf.ValueTypeNames.Token, Sdf.ValueTypeNames.TokenArray],
            ["assetpath", Sdf.ValueTypeNames.Asset, Sdf.ValueTypeNames.AssetArray],
        )
        for file_name, single_name, array_name in stringy_types:
            stage = self._create_stage(file_name)

            prim = stage.DefinePrim("/root")
            single = prim.CreateAttribute("single", single_name, custom=False)
            single.Set("Hello/World")

            array = prim.CreateAttribute("array", array_name, custom=False)
            array.Set(["Hello/World", "Good/Bye"])

            stage.Save()

    def create_path_expression(self):
        print("\tCreating Path Expression Samples...")

        # OpenUSD doesn't have a Python API for path expression arrays
        sourceData = """#usda 1.0

def "root"
{
    pathExpression single = "/root/Foo"
    pathExpression[] array = ["/root/Spam", "/root/Eggs"] 
}
"""
        layer = self._create_layer("pathexpression", sourceData)
        self._save_layer(layer, "pathexpression")

    def create_matrices(self):
        print("\tCreating Matrices Samples...")

        matrices = (
            (
                "matrix2d",
                Sdf.ValueTypeNames.Matrix2d,
                Sdf.ValueTypeNames.Matrix2dArray,
                Vt.Matrix2dArray,
                Gf.Matrix2d,
                2,
            ),
            (
                "matrix3d",
                Sdf.ValueTypeNames.Matrix3d,
                Sdf.ValueTypeNames.Matrix3dArray,
                Vt.Matrix3dArray,
                Gf.Matrix3d,
                3,
            ),
            (
                "matrix4d",
                Sdf.ValueTypeNames.Matrix4d,
                Sdf.ValueTypeNames.Matrix4dArray,
                Vt.Matrix4dArray,
                Gf.Matrix4d,
                4,
            ),
        )
        for (
            file_name,
            single_name,
            array_name,
            vt_array_type,
            gf_type,
            dimension,
        ) in matrices:
            stage = self._create_stage(file_name)
            prim = stage.DefinePrim("/root")
            single = prim.CreateAttribute("single", single_name, custom=False)
            single_mat = []
            for i in range(dimension):
                r = []
                for x in range(dimension):
                    r.append((i + 1) * (x + 1))
                single_mat.append(r)

            single.Set(gf_type(single_mat))

            inlined = prim.CreateAttribute("inlined", single_name, custom=False)
            inlined.Set(gf_type())

            array = prim.CreateAttribute("array", array_name, custom=False)
            val = vt_array_type((gf_type(single_mat), gf_type(single_mat)))
            array.Set(val)

            stage.Save()

    def create_mathematic_vectors(self):
        print("\tCreating Mathematic Vector Samples...")

        vectors = (
            ("quatd", Sdf.ValueTypeNames.Quatd, Sdf.ValueTypeNames.QuatdArray, 4),
            ("quatf", Sdf.ValueTypeNames.Quatf, Sdf.ValueTypeNames.QuatfArray, 4),
            ("quath", Sdf.ValueTypeNames.Quath, Sdf.ValueTypeNames.QuathArray, 4),
            ("vec2d", Sdf.ValueTypeNames.Double2, Sdf.ValueTypeNames.Double2Array, 2),
            ("vec2f", Sdf.ValueTypeNames.Float2, Sdf.ValueTypeNames.Float2Array, 2),
            ("vec2h", Sdf.ValueTypeNames.Half2, Sdf.ValueTypeNames.Half2Array, 2),
            ("vec2i", Sdf.ValueTypeNames.Int2, Sdf.ValueTypeNames.Int2Array, 2),
            ("vec3d", Sdf.ValueTypeNames.Double3, Sdf.ValueTypeNames.Double3Array, 3),
            ("vec3f", Sdf.ValueTypeNames.Float3, Sdf.ValueTypeNames.Float3Array, 3),
            ("vec3h", Sdf.ValueTypeNames.Half3, Sdf.ValueTypeNames.Half3Array, 3),
            ("vec3i", Sdf.ValueTypeNames.Int3, Sdf.ValueTypeNames.Int3Array, 3),
            ("vec4d", Sdf.ValueTypeNames.Double4, Sdf.ValueTypeNames.Double4Array, 4),
            ("vec4f", Sdf.ValueTypeNames.Float4, Sdf.ValueTypeNames.Float4Array, 4),
            ("vec4h", Sdf.ValueTypeNames.Half4, Sdf.ValueTypeNames.Half4Array, 4),
            ("vec4i", Sdf.ValueTypeNames.Int4, Sdf.ValueTypeNames.Int4Array, 4),
        )

        for file_name, single_name, array_name, dimension in vectors:
            stage = self._create_stage(file_name)
            integer = file_name.endswith("i")
            gf_type = getattr(Gf, file_name[0].upper() + file_name[1:])
            prim = stage.DefinePrim("/root")

            single = prim.CreateAttribute("single", single_name, custom=False)
            inline = prim.CreateAttribute("inlined", single_name, custom=False)
            array = prim.CreateAttribute("array", array_name, custom=False)

            single_value = [3.14, 4.824, 1.225, 5.247][:dimension]
            inline_value = [0, 1, 2, 3][:dimension]

            if integer:
                single_value = [math.ceil(i) for i in single_value]
                inline_value = [math.ceil(i) for i in inline_value]

            single_value = gf_type(*single_value)
            inline_value = gf_type(*inline_value)

            single.Set(single_value)
            inline.Set(inline_value)

            array.Set([single_value, inline_value, single_value])

            stage.Save()

    def create_splines(self):
        print("\tCreating Spline Samples...")

        a = dir(Ts.Spline)
        attr_type = Sdf.ValueTypeNames.Double

        # Create Sample Spline
        typeName = str(attr_type)
        spline = Ts.Spline(typeName)

        spline.SetKnot(
            Ts.Knot(
                typeName=typeName,
                time=1,
                value=8,
                nextInterp=Ts.InterpCurve,
                postTanWidth=1.3,
                postTanSlope=0.125,
            )
        )
        spline.SetKnot(
            Ts.Knot(
                typeName=typeName,
                time=6,
                value=20,
                nextInterp=Ts.InterpCurve,
                preTanWidth=1.3,
                preTanSlope=-0.2,
                postTanWidth=2,
                postTanSlope=0.3,
            )
        )

        for format in ["usda", "usdc"]:
            stage = self._create_stage("splines", ext=format)
            prim = stage.DefinePrim(Sdf.Path("/MyPrim"))
            attr = prim.CreateAttribute("myAttr", Sdf.ValueTypeNames.Double)
            attr.SetSpline(spline)
            stage.Save()

    def create_dict(self):
        print("\tCreating Dictionary Samples...")
        stage = self._create_stage("dict")

        root = stage.GetRootLayer()
        custom_data = root.customLayerData
        custom_data.setdefault("Apple", {})["preferredIblVersion"] = 2
        root.customLayerData = custom_data

        stage.Save()

    def create_relocates(self):
        print("\tCreating Relocate Samples...")
        stage = self._create_stage("relocates")

        layer = stage.GetRootLayer()
        layer.relocates = [("/Egg/Foo", "/Egg/Bar")]
        stage.Save()

    def create_timecodes(self):
        print("\tCreating timecodes")
        stage = self._create_stage("timecodes")

        prim = stage.DefinePrim("/root")
        single = prim.CreateAttribute("single", Sdf.ValueTypeNames.TimeCode, custom=False)
        single.Set(Sdf.TimeCode(11.0))

        array = prim.CreateAttribute("array", Sdf.ValueTypeNames.TimeCodeArray, custom=False)
        array.Set([Sdf.TimeCode(100.1), Sdf.TimeCode(13.1234)])

        stage.Save()

    def create_timesamples(self):
        print("\tCreating timesamples")
        stage = self._create_stage("timesamples")

        prim = stage.DefinePrim("/root")
        animated = prim.CreateAttribute("animated", Sdf.ValueTypeNames.Float, custom=False)
        for i in range(0, 10):
            animated.Set(i, i)

        animated.Set(Sdf.ValueBlock(), 11)
        stage.Save()

    def create_permissions(self):
        print("\tCreating permissions")
        # AFAIK there's no permissions API, so we create it with a string
        sourceData = """#usda 1.0
def "Specialize" (
    permission = private
) { }
        """
        layer = self._create_layer("permissions", sourceData)
        self._save_layer(layer, "permissions")

    def create_variants(self):
        print("\tCreating variants")
        stage = self._create_stage("variants")

        root = stage.DefinePrim("/root")
        vset = root.GetVariantSets().AddVariantSet("foo")

        vset.AddVariant("eggs")
        vset.AddVariant("spam")

        vset.SetVariantSelection("eggs")

        stage.Save()

    def create_listops(self):
        print("\tCreating ListOps")
        sourceData = """#usda 1.0
def "root" (
    apiSchemas = ["MaterialBindingAPI"]
    prepend references = [@./ref.usda@</Model>(offset = 10)]
    append payload = [@eggs.usda@]
) {
    rel foo = [</eggs>, </spam>]
}

        
        """
        layer = self._create_layer("listops", sourceData)
        self._save_layer(layer, "listops")

    def create_vectors(self):
        print("\tCreating Vectors")
        sourceData = """#usda 1.0
(
    subLayers = [
        @foo.usda@,
        @bar.usda@ (
            offset = 4.5
        ),@baz.usda@ (
            offset = 2.4;
            scale = 6
            offset = 1.2
        )
    ]
)
"""
        layer = self._create_layer("vectors", sourceData)
        self._save_layer(layer, "vectors")


if __name__ == "__main__":
    CreateBinaryTests().run()
