import math
import os
import unittest

from data_types import Asset
from data_types.listop import ListOp
from file_formats import specialized_types
from file_formats.parsers.binary import splines, types
from file_formats.parsers.binary.binary_parser import BinaryParser
from file_formats.parsers.binary.values import ValueRep
from file_formats.tests.utils import ParserTestBase


class BinaryParserTests(ParserTestBase):
    def setUp(self):
        self.assertTrue(os.path.exists(self.TEST_ASSETS_ROOT))
        self.binary_root = os.path.join(self.TEST_ASSETS_ROOT, "binary")

    def read_scene(self, name):
        with open(os.path.join(self.binary_root, f"gen_{name}.usdc"), mode="rb") as reader:
            parser = BinaryParser(reader)
            scene = parser.build_scene()

        return scene

    def __test_string(self, name):
        scene = self.read_scene(name)

        self.assertEqual(scene["/root.single"]["default"].value, "Hello/World")
        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, ["Hello/World", "Good/Bye"])

    def __test_floats(self, precision, places=None):
        scene = self.read_scene(precision)

        self.assertAlmostEqual(scene["/root.single"]["default"].value, 3.1415, places=places)
        array = scene["/root.array:lut"]["default"].value
        target = [-3.1415, 2.7182, 1.6180]
        for i, val in enumerate(array):
            self.assertAlmostEqual(val, target[i], places=places)

        array = scene["/root.array:ints"]["default"].value
        self.assertListEqual(array, [-1, 0, 1])

    def __test_matrices(self, dimension):
        scene = self.read_scene(f"matrix{dimension}d")

        single_mat = []
        inlined_mat = []
        for i in range(dimension):
            r_single = []
            r_inline = []
            for x in range(dimension):
                r_single.append(float((i + 1) * (x + 1)))
                r_inline.append(0.0 if x != i else 1.0)
            single_mat.append(r_single)
            inlined_mat.append(r_inline)

        single = scene["/root.single"]["default"].value
        self.assertListEqual(single, single_mat)

        inlined = scene["/root.inlined"]["default"]
        self.assertTrue(inlined.is_inlined)
        self.assertListEqual(inlined.value, inlined_mat)

        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, [single_mat, single_mat])

    def __test_complex_mathematical(self, name, dimension, integer=False, places=4):
        scene = self.read_scene(name)
        quat = name.startswith("quat")
        single_value = [3.14, 4.824, 1.225, 5.247][:dimension]
        inline_value = [0, 1, 2, 3][:dimension]

        if integer:
            single_value = [math.ceil(i) for i in single_value]
            inline_value = [math.ceil(i) for i in inline_value]

        if quat:
            # Quat actually stores the first element last.
            single_value = [
                single_value[1],
                single_value[2],
                single_value[3],
                single_value[0],
            ]
            inline_value = [
                inline_value[1],
                inline_value[2],
                inline_value[3],
                inline_value[0],
            ]

        single = scene["/root.single"]["default"].value
        for i, v in enumerate(single):
            self.assertAlmostEqual(v, single_value[i], places=places)

        inline = scene["/root.inlined"]["default"]
        if not quat:
            self.assertTrue(inline.is_inlined)
        for i, v in enumerate(inline.value):
            self.assertAlmostEqual(v, inline_value[i], places=places)

        array = scene["/root.array"]["default"].value

        for i, item in enumerate(array):
            value = inline_value if i == 1 else single_value
            for i, v in enumerate(item):
                self.assertAlmostEqual(v, value[i], places=places)

    def test_scene_strat(self):
        with open(os.path.join(self.binary_root, "fender_stratocaster.usdc"), mode="rb") as reader:
            parser = BinaryParser(reader)
            scene = parser.build_scene()

        self.assertEqual(len(scene), 432)
        self.assertEqual("fender_stratocaster", scene["/"]["defaultPrim"].value)

    def test_scene_plane(self):
        with open(os.path.join(self.binary_root, "toy_biplane_idle.usdc"), mode="rb") as reader:
            parser = BinaryParser(reader)
            scene = parser.build_scene()

        self.assertEqual(len(scene), 425)
        self.assertEqual("toy_biplane_idle", scene["/"]["defaultPrim"].value)

    def test_bool(self):
        scene = self.read_scene("bool")
        self.assertFalse("default" in scene["/root.unset"])
        self.assertFalse("default" in scene["/root.array:unset"])

        self.assertTrue(scene["/root.single"]["default"].value)
        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, [False, False, True, False, False])

        # Test Variability
        self.assertEqual(scene["/root.array"]["variability"].value, types.Variability.Uniform)

    def test_uchar(self):
        scene = self.read_scene("uchar")

        self.assertEqual(scene["/root.single"]["default"].value, 255)
        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, [0, 1, 2, 3, 4, 255])

    def test_int(self):
        scene = self.read_scene("int")

        self.assertEqual(scene["/root.single"]["default"].value, -2147483647)
        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, [-2147483647, 0, 1, 2, 3, 4, 2147483647])

    def test_uint(self):
        scene = self.read_scene("uint")

        self.assertEqual(scene["/root.single"]["default"].value, 4294967295)
        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, [0, 1, 2, 3, 4, 4294967295])

    def test_int64(self):
        scene = self.read_scene("int64")

        self.assertEqual(scene["/root.single"]["default"].value, -9223372036854775807)
        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, [-9223372036854775807, 0, 1, 2, 3, 4, 9223372036854775807])

    def test_uint64(self):
        scene = self.read_scene("uint64")

        self.assertEqual(scene["/root.single"]["default"].value, 18446744073709551615)
        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, [0, 1, 2, 3, 4, 18446744073709551615])

    def test_half(self):
        self.__test_floats("half", places=2)

    def test_float(self):
        self.__test_floats("float")

    def test_double(self):
        self.__test_floats("double")

    def test_string(self):
        self.__test_string("string")

    def test_token(self):
        self.__test_string("token")

    def test_assetpath(self):
        self.__test_string("assetpath")

    def test_path_expression(self):
        scene = self.read_scene("pathexpression")
        self.assertEqual(scene["/root.single"]["default"].value, "/root/Foo")

        array = scene["/root.array"]["default"].value
        self.assertListEqual(array, ["/root/Spam", "/root/Eggs"])

    def test_matrix2d(self):
        self.__test_matrices(2)

    def test_matrix3d(self):
        self.__test_matrices(3)

    def test_matrix4d(self):
        self.__test_matrices(4)

    def test_quatd(self):
        self.__test_complex_mathematical("quatd", 4)

    def test_quatf(self):
        self.__test_complex_mathematical("quatf", 4)

    def test_quath(self):
        self.__test_complex_mathematical("quath", 4, places=2)

    def test_vec2d(self):
        self.__test_complex_mathematical("vec2d", 2)

    def test_vec2f(self):
        self.__test_complex_mathematical("vec2f", 2)

    def test_roundtrip_float_half(self):
        single_value = [3.14, 4.824, 1.225, 5.247]
        for i, v in enumerate(single_value):
            h = ValueRep.convert_float_to_half(single_value[i])
            self.assertAlmostEqual(v, ValueRep.convert_half_to_float(h), places=2)

        inline_value = [0, 1, 2, 3]
        for i, v in enumerate(inline_value):
            h = ValueRep.convert_float_to_half(inline_value[i])
            self.assertAlmostEqual(v, ValueRep.convert_half_to_float(h), places=2)

    def test_vec2h(self):
        self.__test_complex_mathematical("vec2h", 2, places=2)

    def test_vec2i(self):
        self.__test_complex_mathematical("vec2i", 2, integer=True)

    def test_vec3d(self):
        self.__test_complex_mathematical("vec3d", 3)

    def test_vec3f(self):
        self.__test_complex_mathematical("vec3f", 3)

    def test_vec3h(self):
        self.__test_complex_mathematical("vec3h", 3, places=2)

    def test_vec3i(self):
        self.__test_complex_mathematical("vec3i", 3, integer=True)

    def test_vec4d(self):
        self.__test_complex_mathematical("vec4d", 4)

    def test_vec4f(self):
        self.__test_complex_mathematical("vec4f", 4)

    def test_vec4h(self):
        self.__test_complex_mathematical("vec4h", 4, places=2)

    def test_vec4i(self):
        self.__test_complex_mathematical("vec4i", 4, integer=True)

    def test_relocates(self):
        pass

    def test_dictionary(self):
        scene = self.read_scene("dict")
        self.assertEqual(
            scene["/"]["customLayerData"].value["Apple"].value["preferredIblVersion"].value,
            2,
        )

    def test_spline_simple(self):
        scene = self.read_scene("splines")
        spline = scene["/MyPrim.myAttr"]["spline"].value

        self.assertFalse(spline.custom_data)
        self.assertEqual(spline.data_type, splines.CurveDataType.Double)
        self.assertFalse(spline.loop_parameters.looping)
        knots = sorted(spline.knots, key=lambda k: k.time)

        self.assertEqual(len(knots), 2)

        first = knots[0]
        self.assertEqual(first.time, 1.0)
        self.assertEqual(first.post_tan_width, 1.3)
        self.assertEqual(first.post_tan_slope, 0.125)
        self.assertEqual(first.value, 8.0)

        second = knots[1]
        self.assertEqual(second.time, 6.0)
        self.assertEqual(second.post_tan_width, 2.0)
        self.assertEqual(second.post_tan_slope, 0.3)
        self.assertEqual(second.value, 20.0)

    def test_relocates(self):
        scene = self.read_scene("relocates")

        relocates = scene["/"].fields["layerRelocates"].value
        self.assertEqual(len(relocates), 1)

        self.assertDictEqual(relocates, {"/Egg/Foo": "/Egg/Bar"})

    def test_timecodes(self):
        scene = self.read_scene("timecodes")
        single = scene["/root.single"].fields["default"].value
        self.assertAlmostEqual(single, 11.0)

        array = scene["/root.array"].fields["default"].value
        self.assertEqual(len(array), 2)
        self.assertAlmostEqual(array[0], 100.1)
        self.assertAlmostEqual(array[1], 13.1234)

    def test_timesamples(self):
        scene = self.read_scene("timesamples")
        timesamples = scene["/root.animated"]["timeSamples"].value

        for time, value in timesamples[:-1]:
            self.assertAlmostEqual(time, value.value)

        self.assertEqual(timesamples[-1][1].type, types.ValueType.ValueBlock)

    def test_permissions(self):
        scene = self.read_scene("permissions")

        permission = scene["/Specialize"]["permission"].value
        self.assertEqual(permission, types.Permission.Private)

    def test_variants(self):
        # Also a good oppurtunity to test a few other data types
        scene = self.read_scene("variants")

        # Test Variant Selection
        variantSelection = scene["/root"]["variantSelection"].value
        self.assertDictEqual(variantSelection, {"foo": ["eggs"]})

        # Test token vector
        primChildren = scene["/"]["primChildren"].value
        self.assertListEqual(primChildren, ["root"])

        # Test Specifier
        self.assertEqual(scene["/root"]["specifier"].value, types.Specifier.Def)

        # Test String List Op
        variantSetNames: ListOp = scene["/root"]["variantSetNames"].value
        self.assertFalse(variantSetNames.is_explicit)
        self.assertSequenceEqual(variantSetNames.prepended_items, ["foo"])

    def test_listops(self):
        scene = self.read_scene("listops")

        root = scene["/root"]

        # Test TokenListOp
        apiSchemas: ListOp = root["apiSchemas"].value
        self.assertTrue(apiSchemas.is_explicit)
        self.assertSequenceEqual(apiSchemas.explicit_items, ["MaterialBindingAPI"])

        # Test reference list op
        references: ListOp = root["references"].value
        self.assertFalse(references.is_explicit)

        matchingRef = specialized_types.Reference(
            target=(Asset("./ref.usda"), specialized_types.ObjectPath.from_str("/Model")),
            retiming=specialized_types.Retiming(offset=10.0, scale=1.0),
        )
        self.assertSequenceEqual(references.prepended_items, [matchingRef])

        # Test Payload List Op
        payloads: ListOp = root["payload"].value
        self.assertFalse(payloads.is_explicit)

        matchingPayload = specialized_types.Payload(
            target=Asset("eggs.usda"),
            retiming=specialized_types.Retiming(offset=0.0, scale=1.0),
        )
        self.assertSequenceEqual(payloads.appended_items, [matchingPayload])

        # Test Path List Op
        targetPaths: ListOp = scene["/root.foo"]["targetPaths"].value
        self.assertTrue(targetPaths.is_explicit)
        self.assertSequenceEqual(targetPaths.explicit_items, ["/eggs", "/spam"])

    def test_vectors(self):
        scene = self.read_scene("vectors")

        # Test StringVector
        subLayers = scene["/"]["subLayers"].value
        self.assertListEqual(subLayers, ["foo.usda", "bar.usda", "baz.usda"])

        # Test Layer Offset Vector
        layerOffsets = scene["/"]["subLayerOffsets"].value
        self.assertListEqual(
            layerOffsets,
            [
                specialized_types.Retiming(offset=0.0, scale=1.0),
                specialized_types.Retiming(offset=4.5, scale=1.0),
                specialized_types.Retiming(offset=1.2, scale=6.0),
            ],
        )

    def test_path_vector(self):
        with open(os.path.join(self.binary_root, "ball.maya.usdc"), mode="rb") as reader:
            parser = BinaryParser(reader)
            scene = parser.build_scene()

        baseColor = scene["/Ball/Looks/BallMaterial/Base.inputs:baseColor"]["connectionChildren"].value
        self.assertListEqual(baseColor, ["/Ball/Looks/BallMaterial/BallTexture.outputs:resultRGB"])


if __name__ == "__main__":
    unittest.main()
