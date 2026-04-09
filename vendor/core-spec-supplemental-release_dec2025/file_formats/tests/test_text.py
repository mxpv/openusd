import json
import os
import pprint
import unittest

import jsondiff
from parameterized import parameterized

from file_formats.parsers.text.text_parser import TextParser

base_path = os.path.dirname(os.path.abspath(__file__))


class TextParserTests(unittest.TestCase):
    @parameterized.expand(
        [entry for entry in os.scandir(os.path.join(base_path, "assets/text/usda")) if entry.is_file()]
    )
    def test_parsing(self, file_name):
        """
        Tests that the parsing of the given usda file
        in file_name creates the same layer data as
        that present in the baseline json file with
        the same name.
        """
        test_output = {}
        text_parser = TextParser()
        layer_data = text_parser.parse(file_name)
        for path, spec in layer_data._spec_data.items():
            spec_data = json.loads(spec.json_encode())
            test_output.update(spec_data)

        baseline_path = os.path.join(
            base_path, "assets/text/baseline", os.path.basename(os.path.splitext(file_name)[0]) + ".json"
        )
        with open(baseline_path, "r", encoding="utf-8") as file:
            baseline = json.load(file)

        result = jsondiff.diff(test_output, baseline, syntax="compact")
        try:
            self.assertTrue(len(result) == 0)
        except AssertionError as e:
            print(result)
            print("Parsed output:")
            pprint.pp(test_output)
            print("Baseline: ")
            pprint.pp(baseline)
            raise e


if __name__ == "__main__":
    unittest.main()
