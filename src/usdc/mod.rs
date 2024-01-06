//! `usdc` file format support.

mod coding;
mod file;
mod reader;
mod types;
mod version;

pub use file::*;
use reader::CrateReader;
pub use types::*;
pub use version::{version, Version};
