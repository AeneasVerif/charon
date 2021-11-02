use crate::cfim_ast::*;
use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::reorder_decls::*;
use crate::types::*;
use crate::values::*;
use hashlink::linked_hash_map::LinkedHashMap;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::collections::HashMap;

/*/// An auxiliary type used for serialization
pub enum DeclarationSerializer {
    Type(DefId),
    Fun(DefId),
    RecTypes(Vec<DefId>),
    RecFuns(Vec<DefId>),
}*/

/// Export the translated definitions to a JSON file.
pub fn export(
    ordered_decls: &Declarations,
    type_rid_to_id: &HashMap<rustc_hir::def_id::DefId, TypeDefId::Id>,
    type_defs: &TypeDefs,
    fun_rid_to_id: &HashMap<rustc_hir::def_id::DefId, DefId::Id>,
    fun_defs: &FunDefs,
) -> Result<()> {
    unimplemented!();
}
