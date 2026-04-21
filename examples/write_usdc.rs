//! Build a minimal USD scene programmatically and write it as `.usdc`.
//!
//! Usage: `cargo run --example write_usdc -- out.usdc`

use openusd::sdf::{self, ChildrenKey, FieldKey, SpecType, Specifier, Value};

fn main() -> anyhow::Result<()> {
    let out = std::env::args().nth(1).unwrap_or_else(|| "out.usdc".to_string());

    let mut data = sdf::Data::new();

    let root = sdf::Path::abs_root();
    let root_spec = data.create_spec(root.clone(), SpecType::PseudoRoot);
    root_spec.add(ChildrenKey::PrimChildren, Value::TokenVec(vec!["World".into()]));
    root_spec.add(FieldKey::DefaultPrim, Value::Token("World".into()));

    let world = sdf::path("/World")?;
    let world_spec = data.create_spec(world.clone(), SpecType::Prim);
    world_spec.add(FieldKey::Specifier, Value::Specifier(Specifier::Def));
    world_spec.add(FieldKey::TypeName, Value::Token("Xform".into()));
    world_spec.add(ChildrenKey::PrimChildren, Value::TokenVec(vec!["Cube".into()]));

    let cube = sdf::path("/World/Cube")?;
    let cube_spec = data.create_spec(cube.clone(), SpecType::Prim);
    cube_spec.add(FieldKey::Specifier, Value::Specifier(Specifier::Def));
    cube_spec.add(FieldKey::TypeName, Value::Token("Cube".into()));
    cube_spec.add(ChildrenKey::PropertyChildren, Value::TokenVec(vec!["size".into()]));

    let size = cube.append_property("size")?;
    let attr_spec = data.create_spec(size, SpecType::Attribute);
    attr_spec.add(FieldKey::TypeName, Value::Token("double".into()));
    attr_spec.add(FieldKey::Default, Value::Double(1.0));

    data.write_usdc(&out)?;
    println!("Wrote {} spec(s) to {out}", data.len());
    Ok(())
}
