//! Text file format (`usda`) reader.

use std::borrow::Cow;
use std::{collections::{HashMap, HashSet}, fs, path::{Path, PathBuf}};

use anyhow::{bail, Context, Result};

pub mod parser;
pub mod token;

use parser::Parser;

use crate::sdf::{self, schema::{FieldKey, ChildrenKey}, AbstractData, Value};

/// High level interface to text data.
#[derive(Clone)]
pub struct TextReader {
    pub data: HashMap<sdf::Path, sdf::Spec>,
}

impl TextReader {
    /// Read a file on disk.
    pub fn read(path: impl AsRef<Path>) -> Result<Self> {
        let path = path.as_ref();
        let data = fs::read_to_string(path).with_context(|| format!("Unable to read file: {}", path.display()))?;

        let mut parser = Parser::new(&data);
        let data = parser.parse().context("Unable to parse text file")?;

        Ok(Self { data })
    }

    /// Create from parsed data.
    pub fn from_data(data: HashMap<sdf::Path, sdf::Spec>) -> Self {
        Self { data }
    }

    /// Returns a list of child paths for a given prim path.
    pub fn get_name_children(&self, path: &sdf::Path) -> Vec<sdf::Path> {
        if let Some(spec) = self.data.get(path) {
            if let Some(sdf::Value::TokenVec(children)) = spec.fields.get(ChildrenKey::PrimChildren.as_str()) {
                return children.iter()
                    .filter_map(|name| path.append_path(name.as_str()).ok())
                    .collect();
            }
        }
        Vec::new()
    }

    /// Returns the value of an attribute if it exists and matches the requested type.
    /// This looks for the 'default' field on the property spec at the given path.
    pub fn get_attribute_value<T: sdf::FromValue>(&mut self, path: &sdf::Path) -> Option<T> {
        if let Ok(val) = self.get(path, "default") {
            T::from_value(&val)
        } else {
            None
        }
    }

    /// Helper to get an attribute value directly from a prim path and attribute name.
    pub fn get_prim_attribute_value<T: sdf::FromValue>(
        &mut self,
        prim_path: &sdf::Path,
        attr_name: &str,
    ) -> Option<T> {
        let prop_path = prim_path.append_property(attr_name).ok()?;
        self.get_attribute_value(&prop_path)
    }

    /// Returns the default prim path for this stage if defined.
    pub fn get_default_prim(&self) -> Option<sdf::Path> {
        let root_path = sdf::Path::abs_root();
        if let Some(spec) = self.data.get(&root_path) {
            if let Some(Value::Token(name)) = spec.fields.get(FieldKey::DefaultPrim.as_str()) {
                return sdf::Path::new(&format!("/{}", name)).ok();
            }
        }
        None
    }

    /// Resolves all references in the stage recursively and merges them.
    /// This is a "Basic Composition" that flattens the stage.
    pub fn flatten(&mut self, base_dir: &Path) -> Result<()> {
        let mut processed_references = HashSet::new();
        self.flatten_recursive(base_dir, &mut processed_references)
    }

    fn flatten_recursive(&mut self, base_dir: &Path, processed: &mut HashSet<PathBuf>) -> Result<()> {
        let prim_paths: Vec<sdf::Path> = self.data.keys().cloned().collect();
        let mut pending_merges = Vec::new();

        for path in prim_paths {
            let spec = self.data.get(&path).unwrap();
            if let Some(Value::ReferenceListOp(list_op)) = spec.fields.get(FieldKey::References.as_str()) {
                let mut refs = list_op.explicit_items.clone();
                refs.extend(list_op.added_items.clone());
                refs.extend(list_op.prepended_items.clone());
                refs.extend(list_op.appended_items.clone());

                for reference in refs {
                    let ref_path = if Path::new(&reference.asset_path).is_absolute() {
                        PathBuf::from(&reference.asset_path)
                    } else {
                        base_dir.join(&reference.asset_path)
                    };

                    if processed.contains(&ref_path) {
                        continue; 
                    }
                    processed.insert(ref_path.clone());

                    let mut ref_reader = Self::read(&ref_path)?;
                    let ref_base_dir = ref_path.parent().unwrap_or(Path::new("."));
                    ref_reader.flatten_recursive(ref_base_dir, processed)?;

                    let source_root = if reference.prim_path.is_empty() {
                        ref_reader.get_default_prim().ok_or_else(|| anyhow::anyhow!("No defaultPrim in referenced file {}", reference.asset_path))?
                    } else {
                        reference.prim_path.clone()
                    };

                    pending_merges.push((path.clone(), source_root, ref_reader));
                }
            }
        }

        for (target_root, source_root, ref_reader) in pending_merges {
            let child_key = ChildrenKey::PrimChildren.as_str();
            for (source_path, source_spec) in ref_reader.data {
                if let Ok(remapped_path) = self.remap_path(&source_root, &target_root, &source_path) {
                    let target_spec = self.data.entry(remapped_path).or_insert_with(|| sdf::Spec::new(source_spec.ty));
                    for (field_name, field_value) in source_spec.fields {
                        if field_name == child_key {
                            if let Value::TokenVec(source_children) = &field_value {
                                let mut children = if let Some(Value::TokenVec(existing)) = target_spec.fields.get(child_key) {
                                    existing.clone()
                                } else {
                                    Vec::new()
                                };
                                for child in source_children {
                                    if !children.contains(child) {
                                        children.push(child.clone());
                                    }
                                }
                                target_spec.fields.insert(child_key.to_string(), Value::TokenVec(children));
                                continue;
                            }
                        }
                        target_spec.fields.entry(field_name).or_insert(field_value);
                    }
                }
            }
        }

        Ok(())
    }

    fn remap_path(&self, source_root: &sdf::Path, target_root: &sdf::Path, source_path: &sdf::Path) -> Result<sdf::Path> {
        let source_str = source_path.as_str();
        let root_str = source_root.as_str();
        
        if source_str == root_str {
            return Ok(target_root.clone());
        }

        if source_str.starts_with(root_str) {
            let mut relative = &source_str[root_str.len()..];
            if relative.starts_with('/') {
                relative = &relative[1..];
            }
            
            let target_str = target_root.as_str();
            let new_path_str = if target_str == "/" {
                format!("/{}", relative)
            } else {
                format!("{}/{}", target_str, relative)
            };
            sdf::Path::new(&new_path_str)
        } else {
            bail!("Path {} not under root {}", source_str, root_str)
        }
    }
}

impl sdf::AbstractData for TextReader {
    fn has_spec(&self, path: &sdf::Path) -> bool {
        self.data.contains_key(path)
    }

    fn has_field(&self, path: &sdf::Path, field: &str) -> bool {
        self.data.get(path).is_some_and(|spec| spec.fields.contains_key(field))
    }

    fn spec_type(&self, path: &sdf::Path) -> Option<sdf::SpecType> {
        self.data.get(path).map(|spec| spec.ty)
    }

    fn get(&mut self, path: &sdf::Path, field: &str) -> Result<Cow<'_, sdf::Value>> {
        let Some(spec) = self.data.get(path) else {
            bail!("No spec found for path: {path}")
        };

        let Some(field) = spec.fields.get(field) else {
            bail!("No field found for path '{path}' and field '{field}'")
        };

        Ok(Cow::Borrowed(field))
    }

    fn list(&self, path: &sdf::Path) -> Option<Vec<String>> {
        self.data.get(path).map(|spec| spec.fields.keys().cloned().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{Path, Spec, SpecType, Value};
    use crate::sdf::schema::ChildrenKey;

    #[test]
    fn test_get_name_children() {
        let mut data = HashMap::new();
        let root_path = Path::new("/World").unwrap();
        let child_name = "Capsule".to_string();
        
        let mut world_spec = Spec::new(SpecType::Prim);
        world_spec.fields.insert(
            ChildrenKey::PrimChildren.as_str().to_string(),
            Value::TokenVec(vec![child_name.clone()])
        );
        
        data.insert(root_path.clone(), world_spec);
        data.insert(Path::new("/World/Capsule").unwrap(), Spec::new(SpecType::Prim));
        
        let reader = TextReader::from_data(data);
        let children = reader.get_name_children(&root_path);
        
        assert_eq!(children.len(), 1);
        assert_eq!(children[0].as_str(), "/World/Capsule");
    }
}
