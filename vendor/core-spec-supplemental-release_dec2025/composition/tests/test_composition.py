import json
import os
import unittest
from pathlib import Path

from composition.stage import Stage


def get_assets_root() -> Path:
    return Path(os.path.join(os.path.dirname(os.path.abspath(__file__)), "assets"))


class PCPTestCase:
    def __init__(self, test_dir, test_runner):
        self.test_dir = test_dir
        self.test_runner: unittest.TestCase = test_runner
        self.data = {}

    def run_test(self):
        pcp_results = self.test_dir / "pcp.json"
        with open(pcp_results) as fp:
            self.data = json.load(fp)

        entry = self.data["Entry"]
        entry_path = self.test_dir / entry
        if not entry_path.exists():
            if self.data.get("Errors"):
                self.test_runner.skipTest(
                    f"Skipping {self.test_dir.name} because the source files had {len(self.data['Errors'])} error(s)"
                )
            else:
                self.test_runner.fail(f"Could not find {entry_path}")

        try:
            stage = Stage.Open(entry_path)
        except Exception as e:
            raise AssertionError(f"Could not open {entry_path}: {e}") from e

        composing = self.data["Composing"]
        for prim_path in composing:
            self.test_runner.assertIn(prim_path, stage, f"Could not find {prim_path}.")
            if "Child names" in composing[prim_path]:
                for child_name in composing[prim_path]["Child names"]:
                    self.test_runner.assertIn(
                        f"{prim_path}/{child_name}", stage, f"Could not find {prim_path}/{child_name}"
                    )
            if "Property names" in composing[prim_path]:
                for property_name in composing[prim_path]["Property names"]:
                    self.test_runner.assertIn(
                        f"{prim_path}.{property_name}", stage, f"Could not find {prim_path}.{property_name}"
                    )
            # TODO: Implement stacks


class ComposerTests(unittest.TestCase):
    ASSET_TESTS_TO_SKIP = [
        "BasicAncestralReference_root",
        "BasicInstancingAndVariants_root",
        "BasicInstancing_root",
        "BasicListEditingWithInherits_root",
        "BasicNestedPayload_root",
        "BasicNestedVariants_root",
        "BasicPayloadDiamond_root",
        "BasicPayload_root",
        "BasicReferenceAndClass_root",
        "BasicReferenceDiamond_root",
        "BasicRelocateToAnimInterfaceAsNewRootPrim_root",
        "BasicRelocateToAnimInterface_root",
        "BasicTimeOffset_root",
        "BasicVariantWithConnections_root",
        "BasicVariantWithReference_root",
        "bug69932_root",
        "bug74847_root",
        "bug92827_root",
        "case1_root",
        "ElidedAncestralRelocates_root",
        "ErrorArcCycle_root",
        "ErrorConnectionPermissionDenied_root",
        "ErrorInvalidAuthoredRelocates_root",
        "ErrorInvalidConflictingRelocates_root",
        "ErrorInvalidInstanceTargetPath_root",
        "ErrorInvalidPayload_root",
        "ErrorInvalidPreRelocateTargetPath_root",
        "ErrorInvalidReferenceToRelocationSource_root",
        "ErrorInvalidTargetPath_root",
        "ErrorOpinionAtRelocationSource_root",
        "ErrorPermissionDenied_root",
        "ExpressionsInPayloads_root",
        "ExpressionsInReferences_root",
        "ImpliedAndAncestralInherits_ComplexEvaluation_root",
        "PayloadsAndAncestralArcs3_root",
        "PayloadsAndAncestralArcs_root",
        "RelativePathPayloads_root",
        "RelativePathReferences_root",
        "RelocatePrimsWithSameName_root",
        "SpecializesAndAncestralArcs3_root",
        "SpecializesAndAncestralArcs5_root",
        "SpecializesAndVariants4_root",
        "SubrootReferenceNonCycle_root",
        "TrickyClassHierarchy_root",
        "TrickyConnectionToRelocatedAttribute_root",
        "TrickyInheritsAndRelocates2_root",
        "TrickyInheritsAndRelocates3_root",
        "TrickyInheritsAndRelocates4_root",
        "TrickyInheritsAndRelocates5_root",
        "TrickyInheritsAndRelocatesToNewRootPrim_root",
        "TrickyInheritsAndRelocates_root",
        "TrickyInheritsInVariants2_root",
        "TrickyInheritsInVariants_root",
        "TrickyLocalClassHierarchyWithRelocates_root",
        "TrickyMultipleRelocations2_root",
        "TrickyMultipleRelocations4_root",
        "TrickyMultipleRelocationsAndClasses2_root",
        "TrickyMultipleRelocationsAndClasses_root",
        "TrickyMultipleRelocations_root",
        "TrickyNestedClasses3_root",
        "TrickyNonLocalVariantSelection_root",
        "TrickyRelocatedTargetInVariant_root",
        "TrickyRelocationOfPrimFromPayload_root",
        "TrickyRelocationOfPrimFromVariant_root",
        "TrickySpookyInheritsInSymmetricArmRig_root",
        "TrickySpookyVariantSelectionInClass_root",
        "TrickySpookyVariantSelection_root",
        "TrickyVariantIndependentSelection_root",
        "TrickyVariantInPayload_root",
        "TrickyVariantOverrideOfLocalClass_root",
        "TrickyVariantOverrideOfRelocatedPrim_root",
        "TrickyVariantSelectionInVariant_root",
        "TrickyVariantSelectionInVariant2_root",
        "TrickyVariantWeakerSelection2_root",
        "TrickyVariantWeakerSelection4_root",
        "TypicalReferenceToChargroup_root",
        "TypicalReferenceToRiggedModel_root",
        "VariantSpecializesAndReferenceSurprisingBehavior_root",
        "VariantSpecializesAndReference_root",
    ]

    def setUp(self):
        self.assets_root = get_assets_root()

    def tearDown(self):
        pass

    def get_test_entry_layer(self, name=None):
        if not name:
            name = self.id().split(".test_")[-1]

        entry = os.path.join(self.assets_root, name, "entry.usd")
        if not os.path.exists(entry):
            raise OSError(f"Could not find {entry}")

        return entry

    def get_test_output_layer_name(self, name=None):
        if not name:
            name = self.id().split(".test_")[-1]

        return f"{name}.usd"

    def test_simple_sublayer(self):
        stage = Stage.Open(self.get_test_entry_layer())

        for path in (
            "/",
            "/RootBaseClass",
            "/RootBaseClass/FirstChild",
            "/RootBaseClass/FirstChild.fromFirstChild:RootBaseClass",
            "/RootBaseClass/InheritedChild",
            "/RootBaseClass.fromRootBaseClass",
            "/RootBaseClass.name",
            "/Root",
            "/Root/FirstChild",
            "/Root/FirstChild.fromFirstChild",
            "/Root/FirstChild.fromFirstChild:RootBaseClass",
            "/Root/FromSecondLayer",
            "/Root/FromSecondLayer.secondLayerAttr",
            "/Root/InheritedChild",
            "/Root/FromReference",
            "/Root.name",
            "/Root.fromRootBaseClass",
            "/WithVariants",
            "/WithVariants/Short",
            "/WithVariants.blue",
            "/WithVariants.red",
            "/Sleeping",
            "/FromSecond",
        ):
            self.assertIn(path, stage, f"Could not find {path}. Valid paths are {stage.scene.keys()}")

        self.assertNotIn("/Sleeping/SleepingChild", stage)

    def test_relocates(self):
        stage = Stage.Open(self.get_test_entry_layer())
        for path in ("/", "/Foo", "/Foo/Foo", "/Root", "/Root/ChildB", "/Root/Spam"):
            self.assertIn(path, stage, f"Could not find {path}. Valid paths are {stage.scene.keys()}")

        for path in ("/Root/Foo", "/Root/ChildA"):
            self.assertNotIn(path, stage)

    def test_layer_offsets(self):
        stage = Stage.Open(self.get_test_entry_layer())
        for path in ("/", "/Root.root", "/Root.second", "/Root.third"):
            self.assertIn(path, stage, f"Could not find {path}. Valid paths are {stage.scene.keys()}")

        root = [v[0] for v in stage.get("/Root.root").fields["timeSamples"].value]
        second = [v[0] for v in stage.get("/Root.second").fields["timeSamples"].value]
        third = [v[0] for v in stage.get("/Root.third").fields["timeSamples"].value]

        self.assertListEqual(root, [-10, 0, 15])
        self.assertListEqual(second, [5, 10, 17.5])
        self.assertListEqual(third, [-5, 5, 20])

    def test_inheritance(self):
        stage = Stage.Open(self.get_test_entry_layer())
        for path in ("/", "/Root.first", "/Root.second", "/Inherit", "/Inherit.first"):
            self.assertIn(path, stage, f"Could not find {path}. Valid paths are {stage.scene.keys()}")

        first = stage.get("/Root.first").fields["default"].value
        second = stage.get("/Root.second").fields["default"].value

        self.assertEqual(first, 99)
        self.assertEqual(second, 24)

    def test_specializes(self):
        stage = Stage.Open(self.get_test_entry_layer())
        for path in (
            "/",
            "/Root",
            "/Root/Container",
            "/Root/Container/Base",
            "/Root/Container/Base.standard",
            "/Root/Container/Base.arc",
            "/Root/Container/Specialized",
            "/Root/Container/Specialized.arc",
            "/Root/Container/Specialized.standard",
            "/Root/Container/Inherits",
            "/Root/Container/Inherits.arc",
            "/Root/Container/Inherits.standard",
        ):
            self.assertIn(path, stage, f"Could not find {path}. Valid paths are {stage.scene.keys()}")

        base = stage.get("/Root/Container/Base.arc").fields["default"].value
        specialized = stage.get("/Root/Container/Specialized.arc").fields["default"].value
        inherits = stage.get("/Root/Container/Inherits.arc").fields["default"].value

        self.assertEqual(base, "FromRoot")
        self.assertEqual(specialized, "FromSpecialized")
        self.assertEqual(inherits, "FromRoot")

    def test_listop_ordering(self):
        stage = Stage.Open(self.get_test_entry_layer())
        append_path = "/append"
        explicit_order_path = "/explicit_order"
        explicit_remove_path = "/explicit_remove"

        identifier_key = ".identifier"
        for path in (append_path, explicit_order_path, explicit_remove_path):
            self.assertIn(path, stage, f"Could not find {path}. Valid paths are {stage.scene.keys()}")
            self.assertIn(
                path + identifier_key,
                stage,
                f"Could not find {path + identifier_key}. Valid paths are {stage.scene.keys()}",
            )

        append_identifier = stage.get(append_path + identifier_key).fields["default"].value
        explicit_order_identifier = stage.get(explicit_order_path + identifier_key).fields["default"].value
        explicit_remove_identifier = stage.get(explicit_remove_path + identifier_key).fields["default"].value

        self.assertEqual(append_identifier, "B_from_Entry")
        self.assertEqual(explicit_order_identifier, "A_from_Entry")
        self.assertEqual(explicit_remove_identifier, "B_from_Entry")

    @classmethod
    def add_asset_test(cls, test_dir: Path) -> None:
        test_name = test_dir.name

        @unittest.skipIf(test_name in cls.ASSET_TESTS_TO_SKIP, "Skipping asset test: {test_name}")
        def test_asset_function(self):
            pcp_test = PCPTestCase(test_dir, self)
            pcp_test.run_test()

        test_asset_function.__name__ = f"test_asset_{test_name}"
        setattr(cls, test_asset_function.__name__, test_asset_function)


def add_asset_tests():
    assets_root = get_assets_root()
    for assets_entry in os.scandir(assets_root):
        if not assets_entry.is_dir():
            continue

        test_dir = Path(assets_entry.path)
        pcp_results = test_dir / "pcp.json"
        if not pcp_results.exists():
            continue
        ComposerTests.add_asset_test(test_dir)


add_asset_tests()


if __name__ == "__main__":
    unittest.main()
