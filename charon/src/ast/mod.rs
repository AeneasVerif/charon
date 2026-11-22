pub mod bodies;
pub mod from_rustc;
pub mod items;
pub mod krate;
pub mod meta;
pub mod type_level;
pub mod visitor;

pub mod llbc_ast {
    pub use crate::ast::bodies::structured::*;
    pub use crate::ast::*;
}
pub mod ullbc_ast {
    pub use crate::ast::bodies::unstructured::*;
    pub use crate::ast::*;
}

// Re-export everything except llbc/ullbc.
pub use derive_generic_visitor::Visitor;
pub use index_vec::Idx;
pub use std::ops::ControlFlow;

/// Insertion-ordered hash map.
pub type SeqHashMap<K, V> = indexmap::IndexMap<K, V, rustc_hash::FxBuildHasher>;
/// Insertion-ordered hash set.
pub type SeqHashSet<T> = indexmap::IndexSet<T, rustc_hash::FxBuildHasher>;

pub use crate::errors::Error;
pub use crate::ids::{IndexMap, IndexVec};
pub use crate::utils::dedup::*;
pub use crate::utils::hash_cons::*;

pub use bodies::*;
pub use items::*;
pub use krate::*;
pub use meta::*;
pub use type_level::*;
pub use visitor::*;
