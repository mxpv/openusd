use std::collections::HashMap;

use openusd::sdf::{self, ChildrenKey, FieldKey, LayerOffset, ListOp, Reference, SpecType, Specifier, Value};

fn main() -> anyhow::Result<()> {
    write_spheres("sphere.usda")?;
    write_scene("scene.usda")?;
    Ok(())
}

fn write_spheres(path: &str) -> anyhow::Result<()> {
    let mut data = sdf::Data::new();

    let root = sdf::Path::abs_root();
    let root_spec = data.create_spec(root.clone(), SpecType::PseudoRoot);
    root_spec.add(FieldKey::DefaultPrim, Value::Token("BlueSphere".into()));
    root_spec.add(
        ChildrenKey::PrimChildren,
        Value::TokenVec(vec!["BlueSphere".into(), "GreenSphere".into(), "RedSphere".into()]),
    );

    add_sphere(&mut data, "/BlueSphere", [0.0, 0.0, 1.0])?;
    add_sphere(&mut data, "/GreenSphere", [0.0, 1.0, 0.0])?;
    add_sphere(&mut data, "/RedSphere", [1.0, 0.0, 0.0])?;

    data.write_usda(path)?;
    println!("Wrote {} spec(s) to {path}", data.len());
    Ok(())
}

fn add_sphere(data: &mut sdf::Data, prim_path: &str, color: [f32; 3]) -> anyhow::Result<()> {
    let prim = sdf::path(prim_path)?;
    let prim_spec = data.create_spec(prim.clone(), SpecType::Prim);
    prim_spec.add(FieldKey::Specifier, Value::Specifier(Specifier::Def));
    prim_spec.add(FieldKey::TypeName, Value::Token("Sphere".into()));
    prim_spec.add(
        ChildrenKey::PropertyChildren,
        Value::TokenVec(vec!["primvars:displayColor".into()]),
    );

    let color_prop = prim.append_property("primvars:displayColor")?;
    let attr_spec = data.create_spec(color_prop, SpecType::Attribute);
    attr_spec.add(FieldKey::TypeName, Value::Token("color3f[]".into()));
    attr_spec.add(FieldKey::Default, Value::Vec3fVec(vec![color]));

    Ok(())
}

/// Write `scene.usda` — a single prim with a `color` variant set that references
/// one of the three spheres from `sphere.usda` depending on the selected variant.
fn write_scene(path: &str) -> anyhow::Result<()> {
    let mut data = sdf::Data::new();

    let root = sdf::Path::abs_root();
    let root_spec = data.create_spec(root.clone(), SpecType::PseudoRoot);
    root_spec.add(FieldKey::DefaultPrim, Value::Token("ColoredSphere".into()));
    root_spec.add(ChildrenKey::PrimChildren, Value::TokenVec(vec!["ColoredSphere".into()]));

    // /ColoredSphere — owns the variant set.
    let sphere = sdf::path("/ColoredSphere")?;
    let sphere_spec = data.create_spec(sphere.clone(), SpecType::Prim);
    sphere_spec.add(FieldKey::Specifier, Value::Specifier(Specifier::Def));

    // Declare the "color" variant set and choose "blue" as the default selection.
    sphere_spec.add(
        FieldKey::VariantSetNames,
        Value::TokenListOp(ListOp {
            prepended_items: vec!["color".into()],
            ..Default::default()
        }),
    );
    sphere_spec.add(
        FieldKey::VariantSelection,
        Value::VariantSelectionMap({
            let mut map = HashMap::new();
            map.insert("color".into(), "blue".into());
            map
        }),
    );
    sphere_spec.add(ChildrenKey::VariantSetChildren, Value::TokenVec(vec!["color".into()]));

    // /ColoredSphere{color=} — the variant set spec.
    let vset_path = sdf::Path::new("/ColoredSphere{color=}")?;
    let vset_spec = data.create_spec(vset_path, SpecType::VariantSet);
    vset_spec.add(
        ChildrenKey::VariantChildren,
        Value::TokenVec(vec!["blue".into(), "green".into(), "red".into()]),
    );

    // Individual variant specs, each referencing a different sphere prim.
    add_variant(&mut data, "/ColoredSphere", "color", "blue", None)?;
    add_variant(&mut data, "/ColoredSphere", "color", "green", Some("/GreenSphere"))?;
    add_variant(&mut data, "/ColoredSphere", "color", "red", Some("/RedSphere"))?;

    data.write_usda(path)?;
    println!("Wrote {} spec(s) to {path}", data.len());
    Ok(())
}

/// Insert a variant spec that references `target_prim` inside `sphere.usda`.
/// When `target_prim` is `None` the reference omits an explicit prim path,
/// so USD resolves to the layer's `defaultPrim`.
fn add_variant(
    data: &mut sdf::Data,
    prim_path: &str,
    set_name: &str,
    variant_name: &str,
    target_prim: Option<&str>,
) -> anyhow::Result<()> {
    let variant_path = sdf::Path::new(&format!("{prim_path}{{{set_name}={variant_name}}}"))?;
    let variant_spec = data.create_spec(variant_path, SpecType::Variant);

    let prim_path = match target_prim {
        Some(p) => sdf::path(p)?,
        None => sdf::Path::default(),
    };

    let ref_list = ListOp::<Reference> {
        prepended_items: vec![Reference {
            asset_path: "./sphere.usda".into(),
            prim_path,
            layer_offset: LayerOffset::IDENTITY,
            custom_data: HashMap::new(),
        }],
        ..Default::default()
    };
    variant_spec.add(FieldKey::References, Value::ReferenceListOp(ref_list));

    Ok(())
}
