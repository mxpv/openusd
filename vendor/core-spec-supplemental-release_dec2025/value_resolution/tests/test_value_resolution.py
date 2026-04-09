import pathlib
import unittest

import value_resolution.value_clips as value_clips
from composition.stage import Stage
from value_resolution import InterpolationType, ValueResolution, ValueResolutionProcess
from value_resolution.time_code import timeCode


class ValueResolutionTests(unittest.TestCase):
    def setUp(self):
        self.assets_root = pathlib.Path(__file__).resolve().parent / "assets"

    def tearDown(self):
        pass

    def get_test_filename(self, name=None) -> pathlib.Path:
        if not name:
            name = self.id().split(".test_")[-1]

        entry = self.assets_root / name / "entry.usd"
        if not entry.is_file():
            raise OSError(f"Could not find {entry}")

        return entry

    def test_interpolationType(self):
        value_resolution = ValueResolution(None, None)
        # default type is linear
        self.assertEqual(value_resolution.interpolation_type, InterpolationType.Linear)
        value_resolution.interpolation_type = InterpolationType.Held
        self.assertEqual(value_resolution.interpolation_type, InterpolationType.Held)

    def test_default(self):
        stage = Stage.Open(str(self.get_test_filename()))
        root = stage.get("/Root")
        attribute = stage.get("/Root.root")
        value_resolution = ValueResolution(stage, root)
        val = value_resolution.get_value(attribute, timeCode.default())
        self.assertEqual(val[0], 2.0)

    def test_timesamples(self):
        stage = Stage.Open(str(self.get_test_filename()))
        root = stage.get("/Root")
        attribute = stage.get("/Root.root")
        value_resolution = ValueResolution(stage, root)
        val = value_resolution.get_value(attribute, timeCode(1.0))
        self.assertEqual(val[0], 5.0)
        val = value_resolution.get_value(attribute, timeCode(40.0))
        self.assertEqual(val[0], 15.0)
        val = value_resolution.get_value(attribute, timeCode(15.0))
        self.assertGreater(val[0], 5.0)
        self.assertLess(val[0], 10.0)

        # test out of range
        val = value_resolution.get_value(attribute, timeCode(60.0))
        self.assertEqual(val[0], 15.0)
        val = value_resolution.get_value(attribute, timeCode(0.5))
        self.assertEqual(val[0], 5.0)

        # test fallback by requesting default when not authored
        val = value_resolution.get_value(attribute, timeCode.default())
        self.assertEqual(val[1], ValueResolutionProcess.Fallback)

        # test Held
        value_resolution.interpolation_type = InterpolationType.Held
        val = value_resolution.get_value(attribute, timeCode(15.0))
        self.assertEqual(val[0], 5.0)
        val = value_resolution.get_value(attribute, timeCode(30.0))
        self.assertEqual(val[0], 10.0)

    # Test direct access through ValueCLip
    def test_clip_timings(self):
        print("Direct ValueCLip test using 'active' and 'times' directives")
        stage = Stage.Open(self.get_test_filename())
        root = stage.get("/Model")
        attribute = "/Model.size"
        clips = value_clips.setup_value_clip(stage, root)
        if clips and clips.is_valid():
            val = round(clips.get_value_at_stagetime(timeCode(0.0), attribute), 1)
            self.assertEqual(val, 10.0)
            val = round(clips.get_value_at_stagetime(timeCode(15.0), attribute), 1)
            self.assertEqual(val, 17.5)
            val = round(clips.get_value_at_stagetime(timeCode(30.0), attribute), 1)
            self.assertEqual(val, 15.0)
            val = round(clips.get_value_at_stagetime(timeCode(40.0), attribute), 1)
            self.assertEqual(val, 20.0)

            # Test out of range
            val = round(clips.get_value_at_stagetime(timeCode(50.0), attribute), 1)
            self.assertEqual(val, 25.0)
            val = round(clips.get_value_at_stagetime(timeCode(-1.0), attribute), 1)
            self.assertEqual(val, 0.0)

    def test_clip_basic(self):
        print("Test basic test from 'active' and 'Manifest' using full Value Resolution")

        stage = Stage.Open(self.get_test_filename())
        root = stage.get("/Model")
        attribute = stage.get("/Model.size")
        value_resolution = ValueResolution(stage, root)
        val = value_resolution.get_value(attribute, timeCode(0.0))
        self.assertEqual(val[0], 0.0)
        val = value_resolution.get_value(attribute, timeCode(5.0))
        self.assertEqual(val[0], 5.0)

    def test_clip_advanced(self):
        print("Test basic LVRPS and Clips")
        stage = Stage.Open(self.get_test_filename())
        root = stage.get("/Model")
        attribute = stage.get("/Model.local")

        # Local has a stronger opinion, so values need to come from the root layer and not clips
        value_resolution = ValueResolution(stage, root)
        val = value_resolution.get_value(attribute, timeCode(0.0))
        self.assertEqual(val[0], 0.0)
        val = value_resolution.get_value(attribute, timeCode(5.0))
        self.assertEqual(val[0], 5.0)
        val = value_resolution.get_value(attribute, timeCode(10.0))
        self.assertEqual(val[0], 10.0)
        val = value_resolution.get_value(attribute, timeCode(15.0))
        self.assertEqual(val[0], 15.0)
        val = value_resolution.get_value(attribute, timeCode(20.0))
        self.assertEqual(val[0], 20.0)
        val = value_resolution.get_value(attribute, timeCode(25.0))
        self.assertEqual(val[0], 20.0)

        # Attribute Ref is on a weaker layer, so Clips will be used
        # in this case, clips have negative values
        attribute = stage.get("/Model.ref")
        value_resolution = ValueResolution(stage, root)
        val = value_resolution.get_value(attribute, timeCode(0.0))
        self.assertEqual(val[0], 0.0)
        val = value_resolution.get_value(attribute, timeCode(5.0))
        self.assertEqual(val[0], -5.0)
        val = value_resolution.get_value(attribute, timeCode(10.0))
        self.assertEqual(val[0], -10.0)
        val = value_resolution.get_value(attribute, timeCode(20.0))
        self.assertEqual(val[0], -20.0)
        val = value_resolution.get_value(attribute, timeCode(25.0))
        self.assertEqual(val[0], -25.0)
        # test out of bounds for clip
        val = value_resolution.get_value(attribute, timeCode(30.0))
        self.assertEqual(val[0], -25.0)

    def test_clip_sets(self):
        print("Test basic clips sets")
        stage = Stage.Open(self.get_test_filename())
        root = stage.get("/DefaultOrderTest")
        attribute = stage.get("/DefaultOrderTest.attr")
        value_resolution = ValueResolution(stage, root)

        # Test the ordering - Even though Clip_b is defined first, clip_a should be used by default
        val = value_resolution.get_value(attribute, timeCode(0.0))
        self.assertEqual(val[0], 10.0)
        val = value_resolution.get_value(attribute, timeCode(1.0))
        self.assertEqual(val[0], 20.0)
        val = value_resolution.get_value(attribute, timeCode(2.0))
        self.assertEqual(val[0], 30.0)

    def test_clip_multi(self):
        print("Test basic clips sets")
        stage = Stage.Open(self.get_test_filename())
        root = stage.get("/Model_1")
        attribute = stage.get("/Model_1.size")
        value_resolution = ValueResolution(stage, root)
        val = value_resolution.get_value(attribute, timeCode(5.0))
        self.assertEqual(round(val[0], 1), -5.0)
        val = value_resolution.get_value(attribute, timeCode(10.0))
        self.assertEqual(round(val[0], 1), -10.0)
        # we are at a clip boundary at time=16 15 is clip1 and 16 is clip2
        # using time step will mean that clip1 is sampled
        val = value_resolution.get_value(attribute, timeCode.safe_step(16.0))
        self.assertEqual(round(val[0], 1), -15.0)
        # time code 16 maps to time 0 in clip2
        val = value_resolution.get_value(attribute, timeCode(16.0))
        self.assertEqual(round(val[0], 1), -23.0)
        val = value_resolution.get_value(attribute, timeCode(19.0))
        self.assertEqual(round(val[0], 1), -23.0)
        val = value_resolution.get_value(attribute, timeCode(22.0))
        self.assertEqual(round(val[0], 1), -26.0)
        val = value_resolution.get_value(attribute, timeCode(25.0))
        self.assertEqual(round(val[0], 1), -29.0)


if __name__ == "__main__":
    unittest.main()
