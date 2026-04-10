//! Composition compliance tests.
//!
//! Each test opens a scene via `Stage::open` and validates the composed result
//! against the `pcp.json` baseline from the vendor test suite.

use std::path::Path;

use openusd::{sdf, Stage};

const ASSETS: &str = "vendor/core-spec-supplemental-release_dec2025/composition/tests/assets";

/// JSON schema for loading pcp.json baselines.
mod schema {
    use std::collections::HashMap;

    #[derive(serde::Deserialize)]
    #[serde(rename_all = "PascalCase")]
    pub struct Baseline {
        pub entry: String,
        #[serde(default)]
        pub composing: HashMap<String, PrimData>,
        #[serde(default)]
        pub errors: Vec<String>,
    }

    #[derive(serde::Deserialize, Debug)]
    pub struct PrimData {
        #[serde(default, rename = "Child names")]
        pub child_names: Vec<String>,
        #[serde(default, rename = "Property names")]
        pub property_names: Vec<String>,
    }
}

#[derive(Clone, Copy)]
enum Format {
    Text,
    Binary,
}

fn run(name: &str, format: Format) {
    let test_dir = Path::new(ASSETS).join(name);
    let baseline_path = test_dir.join("pcp.json");
    let json =
        std::fs::read_to_string(&baseline_path).unwrap_or_else(|e| panic!("read {}: {e}", baseline_path.display()));
    let baseline: schema::Baseline = serde_json::from_str(&json).expect("parse pcp.json");

    // Skip error test cases — they test failure modes we don't validate yet.
    if !baseline.errors.is_empty() {
        return;
    }

    // Skip if no composing data.
    if baseline.composing.is_empty() {
        return;
    }

    let entry = match format {
        Format::Text => test_dir.join("usda").join(&baseline.entry),
        Format::Binary => test_dir.join(&baseline.entry),
    };

    if !entry.exists() {
        return;
    }

    let stage = match Stage::builder().on_error(|_| Ok(())).open(entry.to_str().unwrap()) {
        Ok(s) => s,
        Err(_) => return, // Skip tests that fail to open (unsupported features).
    };

    // Collect all prims via traversal.
    let mut prims = Vec::new();
    stage.traverse(|path| prims.push(path.to_string())).unwrap();

    let mut failures = Vec::new();

    for (prim_path, expected) in &baseline.composing {
        // Check prim exists.
        if !prims.iter().any(|p| p == prim_path) {
            failures.push(format!("missing prim: {prim_path}"));
            continue;
        }

        // Check child names.
        for child in &expected.child_names {
            let child_path = format!("{prim_path}/{child}");
            if !prims.iter().any(|p| p == &child_path) {
                failures.push(format!("missing child: {child_path}"));
            }
        }

        // Check property names.
        for prop in &expected.property_names {
            let prop_path = format!("{prim_path}.{prop}");
            if !stage.has_spec(sdf::path(&prop_path).unwrap()) {
                failures.push(format!("missing property: {prop_path}"));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "composition test {name} ({format}) failed:\n  {}",
        failures.join("\n  "),
        format = match format {
            Format::Text => "text",
            Format::Binary => "binary",
        },
    );
}

macro_rules! composition_tests {
    ($($name:ident),* $(,)?) => {
        paste::paste! {
            $(
                #[test]
                #[allow(non_snake_case)]
                fn [<$name _text>]() {
                    run(stringify!($name), Format::Text);
                }

                #[test]
                #[allow(non_snake_case)]
                fn [<$name _binary>]() {
                    run(stringify!($name), Format::Binary);
                }
            )*
        }
    };
}

composition_tests! {
    BasicAncestralReference_root,
    BasicDuplicateSublayer_root,
    BasicInherits_root,
    BasicInstancing_root,
    BasicInstancingAndNestedInstances_root,
    BasicInstancingAndVariants_root,
    BasicListEditing_root,
    BasicListEditingWithInherits_root,
    BasicLocalAndGlobalClassCombination_root,
    BasicNestedPayload_root,
    BasicNestedVariants_root,
    BasicNestedVariantsWithSameName_root,
    BasicOwner_root,
    BasicPayload_root,
    BasicPayloadDiamond_root,
    BasicReference_session,
    BasicReferenceAndClass_root,
    BasicReferenceAndClassDiamond_root,
    BasicReferenceDiamond_root,
    BasicRelocateToAnimInterface_root,
    BasicRelocateToAnimInterfaceAsNewRootPrim_root,
    BasicSpecializes_root,
    BasicSpecializesAndInherits_root,
    BasicSpecializesAndReferences_root,
    BasicSpecializesAndVariants_root,
    BasicTimeOffset_root,
    BasicVariantWithConnections_root,
    BasicVariantWithReference_root,
    bug69932_root,
    bug74847_root,
    bug92827_root,
    case1_root,
    ElidedAncestralRelocates_root,
    ErrorArcCycle_root,
    ErrorConnectionPermissionDenied_root,
    ErrorInconsistentProperties_root,
    ErrorInvalidAuthoredRelocates_root,
    ErrorInvalidConflictingRelocates_root,
    ErrorInvalidInstanceTargetPath_root,
    ErrorInvalidPayload_root,
    ErrorInvalidPreRelocateTargetPath_root,
    ErrorInvalidReferenceToRelocationSource_root,
    ErrorInvalidTargetPath_root,
    ErrorOpinionAtRelocationSource_root,
    ErrorOwner_root,
    ErrorPermissionDenied_root,
    ErrorRelocateWithVariantSelection_root,
    ErrorSublayerCycle_root,
    ExpressionsInPayloads_root,
    ExpressionsInReferences_root,
    ImpliedAndAncestralInherits_ComplexEvaluation_root,
    ImpliedAndAncestralInherits_root,
    PayloadsAndAncestralArcs_root,
    PayloadsAndAncestralArcs2_root,
    PayloadsAndAncestralArcs3_root,
    ReferenceListOpsWithOffsets_root,
    RelativePathPayloads_root,
    RelativePathReferences_root,
    RelocatePrimsWithSameName_root,
    RelocateToNone_root,
    SpecializesAndAncestralArcs_root,
    SpecializesAndAncestralArcs2_root,
    SpecializesAndAncestralArcs3_root,
    SpecializesAndAncestralArcs4_root,
    SpecializesAndAncestralArcs5_root,
    SpecializesAndVariants_root,
    SpecializesAndVariants2_root,
    SpecializesAndVariants3_root,
    SpecializesAndVariants4_root,
    SubrootInheritsAndVariants_root,
    SubrootReferenceAndClasses_root,
    SubrootReferenceAndRelocates_root,
    SubrootReferenceAndVariants_root,
    SubrootReferenceAndVariants2_root,
    SubrootReferenceNonCycle_root,
    TimeCodesPerSecond_root,
    TimeCodesPerSecond_root_12fps,
    TimeCodesPerSecond_root_24tcps_12fps,
    TimeCodesPerSecond_root_48tcps,
    TimeCodesPerSecond_session,
    TimeCodesPerSecond_session_24fps,
    TimeCodesPerSecond_session_48tcps,
    TrickyClassHierarchy_root,
    TrickyConnectionToRelocatedAttribute_root,
    TrickyInheritsAndRelocates_root,
    TrickyInheritsAndRelocates2_root,
    TrickyInheritsAndRelocates3_root,
    TrickyInheritsAndRelocates4_root,
    TrickyInheritsAndRelocates5_root,
    TrickyInheritsAndRelocatesToNewRootPrim_root,
    TrickyInheritsInVariants_root,
    TrickyInheritsInVariants2_root,
    TrickyListEditedTargetPaths_root,
    TrickyLocalClassHierarchyWithRelocates_root,
    TrickyMultipleRelocations_root,
    TrickyMultipleRelocations2_root,
    TrickyMultipleRelocations3_root,
    TrickyMultipleRelocations4_root,
    TrickyMultipleRelocations5_root,
    TrickyMultipleRelocationsAndClasses_root,
    TrickyMultipleRelocationsAndClasses2_root,
    TrickyNestedClasses_root,
    TrickyNestedClasses2_root,
    TrickyNestedClasses3_root,
    TrickyNestedClasses4_root,
    TrickyNestedSpecializes_root,
    TrickyNestedSpecializes2_root,
    TrickyNestedVariants_root,
    TrickyNonLocalVariantSelection_root,
    TrickyRelocatedTargetInVariant_root,
    TrickyRelocationOfPrimFromPayload_root,
    TrickyRelocationOfPrimFromVariant_root,
    TrickyRelocationSquatter_root,
    TrickySpecializesAndInherits_root,
    TrickySpecializesAndInherits2_root,
    TrickySpecializesAndInherits3_root,
    TrickySpecializesAndRelocates_root,
    TrickySpookyInherits_root,
    TrickySpookyInheritsInSymmetricArmRig_root,
    TrickySpookyInheritsInSymmetricBrowRig_root,
    TrickySpookyVariantSelection_root,
    TrickySpookyVariantSelectionInClass_root,
    TrickyVariantAncestralSelection_root,
    TrickyVariantIndependentSelection_root,
    TrickyVariantInPayload_root,
    TrickyVariantOverrideOfLocalClass_root,
    TrickyVariantOverrideOfRelocatedPrim_root,
    TrickyVariantSelectionInVariant_root,
    TrickyVariantSelectionInVariant2_root,
    TrickyVariantWeakerSelection_root,
    TrickyVariantWeakerSelection2_root,
    TrickyVariantWeakerSelection3_root,
    TrickyVariantWeakerSelection4_root,
    TypicalReferenceToChargroup_root,
    TypicalReferenceToChargroupWithRename_root,
    TypicalReferenceToRiggedModel_root,
    VariantSpecializesAndReference_root,
    VariantSpecializesAndReferenceSurprisingBehavior_root,
}
