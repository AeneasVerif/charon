use crate::common::*;
use crate::expressions::SharedExprVisitor;
use crate::gast::{FunDeclId, GlobalDeclId};
use crate::graphs::*;
use crate::translate_ctx::TransCtx;
use crate::types::{SharedTypeVisitor, TypeDeclId, TypeDeclKind};
use crate::ullbc_ast::{ExprBody, SharedAstVisitor};
use hashlink::linked_hash_map::LinkedHashMap;
use linked_hash_set::LinkedHashSet;
use macros::EnumAsGetters;
use macros::EnumIsA;
use macros::{VariantIndexArity, VariantName};
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::collections::HashMap;
use std::fmt::{Debug, Display, Error, Formatter};
use std::vec::Vec;

/// All kind of supported Rust top-level declarations.
/// const and static variables are merged together in the global kind.
/// TODO: remove?
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Type,
    Fun,
    Global,
}

/// A (group of) top-level declaration(s), properly reordered.
/// "G" stands for "generic"
#[derive(Debug, VariantIndexArity, VariantName)]
pub enum GDeclarationGroup<Id: Copy> {
    /// A non-recursive declaration
    NonRec(Id),
    /// A (group of mutually) recursive declaration(s)
    Rec(Vec<Id>),
}

/// A (group of) top-level declaration(s), properly reordered.
#[derive(Debug, VariantIndexArity, VariantName)]
pub enum DeclarationGroup<TypeId: Copy, FunId: Copy, GlobalId: Copy> {
    /// A type declaration group
    Type(GDeclarationGroup<TypeId>),
    /// A function declaration group
    Fun(GDeclarationGroup<FunId>),
    /// A global declaration group
    Global(GDeclarationGroup<GlobalId>),
}

impl<TypeId: Copy, FunId: Copy, GlobalId: Copy> DeclarationGroup<TypeId, FunId, GlobalId> {
    fn make_type_group<'a>(is_rec: bool, gr: impl Iterator<Item = TypeId>) -> Self {
        let gr: Vec<TypeId> = gr.collect();
        if is_rec {
            DeclarationGroup::Type(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Type(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_fun_group<'a>(is_rec: bool, gr: impl Iterator<Item = FunId>) -> Self {
        let gr: Vec<FunId> = gr.collect();
        if is_rec {
            DeclarationGroup::Fun(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_global_group<'a>(is_rec: bool, gr: impl Iterator<Item = GlobalId>) -> Self {
        let gr: Vec<GlobalId> = gr.collect();
        if is_rec {
            DeclarationGroup::Global(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Global(GDeclarationGroup::NonRec(gr[0]))
        }
    }
}

#[derive(
    PartialEq,
    Eq,
    Hash,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Copy,
    Clone,
    Debug,
    PartialOrd,
    Ord,
)]
pub enum AnyDeclId<TypeId: Copy, FunId: Copy, GlobalId: Copy> {
    Type(TypeId),
    Fun(FunId),
    Global(GlobalId),
}

#[derive(Clone, Copy)]
pub struct DeclInfo {
    pub is_transparent: bool,
}

/// The top-level declarations in a module and their external dependencies.
/// External declarations are recognizable with `DefId::is_local()`:
/// See [rust_to_local_ids.rs].
pub struct DeclarationsGroups<TypeId: Copy, FunId: Copy, GlobalId: Copy> {
    /// The properly grouped and ordered declarations
    pub decls: Vec<DeclarationGroup<TypeId, FunId, GlobalId>>,
    /// All the type ids
    pub type_ids: Vec<TypeId>,
    /// All the function ids
    pub fun_ids: Vec<FunId>,
    /// All the global ids
    pub global_ids: Vec<GlobalId>,
    /// Additional information on declarations
    pub decls_info: HashMap<AnyDeclId<TypeId, FunId, GlobalId>, DeclInfo>,
}

pub type Decls = DeclarationsGroups<TypeDeclId::Id, FunDeclId::Id, GlobalDeclId::Id>;

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<Id: Copy + Debug> Display for GDeclarationGroup<Id> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            GDeclarationGroup::NonRec(id) => write!(f, "non-rec: {id:?}"),
            GDeclarationGroup::Rec(ids) => write!(
                f,
                "rec: {}",
                vec_to_string(&|id| format!("    {id:?}"), ids)
            ),
        }
    }
}

/// This is a bit annoying: because [DefId] and [Vec] doe't implement the
/// [Serialize] trait, we can't automatically derive the serializing trait...
impl<Id: Copy + Serialize> Serialize for GDeclarationGroup<Id> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "GDeclarationGroup";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        assert!(variant_arity > 0);
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            GDeclarationGroup::NonRec(id) => {
                vs.serialize_field(id)?;
            }
            GDeclarationGroup::Rec(ids) => {
                let ids = VecSerializer::new(ids);
                vs.serialize_field(&ids)?;
            }
        }
        vs.end()
    }
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<TypeId: Copy + Debug, FunId: Copy + Debug, GlobalId: Copy + Debug> Display
    for DeclarationGroup<TypeId, FunId, GlobalId>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            DeclarationGroup::Type(decl) => write!(f, "{{ Type(s): {decl} }}"),
            DeclarationGroup::Fun(decl) => write!(f, "{{ Fun(s): {decl} }}"),
            DeclarationGroup::Global(decl) => write!(f, "{{ Global(s): {decl} }}"),
        }
    }
}

/// This is a bit annoying: because [DefId] and [Vec] doe't implement the
/// [Serialize] trait, we can't automatically derive the serializing trait...
impl<TypeId: Copy + Serialize, FunId: Copy + Serialize, GlobalId: Copy + Serialize> Serialize
    for DeclarationGroup<TypeId, FunId, GlobalId>
{
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "DeclarationGroup";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        assert!(variant_arity > 0);
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            DeclarationGroup::Type(decl) => {
                vs.serialize_field(decl)?;
            }
            DeclarationGroup::Fun(decl) => {
                vs.serialize_field(decl)?;
            }
            DeclarationGroup::Global(decl) => {
                vs.serialize_field(decl)?;
            }
        }
        vs.end()
    }
}

impl<TypeId: Copy, FunId: Copy, GlobalId: Copy> DeclarationsGroups<TypeId, FunId, GlobalId> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> DeclarationsGroups<TypeId, FunId, GlobalId> {
        DeclarationsGroups {
            decls: vec![],
            type_ids: vec![],
            fun_ids: vec![],
            global_ids: vec![],
            decls_info: HashMap::new(),
        }
    }

    fn push(&mut self, decl: DeclarationGroup<TypeId, FunId, GlobalId>) {
        match &decl {
            DeclarationGroup::Type(GDeclarationGroup::NonRec(id)) => {
                self.type_ids.push(*id);
            }
            DeclarationGroup::Type(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.type_ids.push(*id);
                }
            }
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)) => {
                self.fun_ids.push(*id);
            }
            DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.fun_ids.push(*id);
                }
            }
            DeclarationGroup::Global(GDeclarationGroup::NonRec(id)) => {
                self.global_ids.push(*id);
            }
            DeclarationGroup::Global(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.global_ids.push(*id);
                }
            }
        }
        self.decls.push(decl);
    }
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<TypeId: Copy + Debug, FunId: Copy + Debug, GlobalId: Copy + Debug> Display
    for DeclarationsGroups<TypeId, FunId, GlobalId>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        write!(
            f,
            "{}",
            vec_to_string(
                &|d: &DeclarationGroup<TypeId, FunId, GlobalId>| d.to_string(),
                &self.decls,
            )
        )
    }
}

impl<'a, TypeId: Copy, FunId: Copy, GlobalId: Copy> std::iter::IntoIterator
    for &'a DeclarationsGroups<TypeId, FunId, GlobalId>
{
    type Item = &'a DeclarationGroup<TypeId, FunId, GlobalId>;
    type IntoIter = std::slice::Iter<'a, DeclarationGroup<TypeId, FunId, GlobalId>>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.decls.iter()
    }
}

pub type AnyId = AnyDeclId<TypeDeclId::Id, FunDeclId::Id, GlobalDeclId::Id>;

pub struct Deps {
    dgraph: DiGraphMap<AnyId, ()>,
    /// Want to make sure we remember the order of insertion
    graph: LinkedHashMap<AnyId, LinkedHashSet<AnyId>>,
    /// We use this when exploring the graph
    current_id: Option<AnyId>,
}

impl Deps {
    fn new() -> Self {
        Deps {
            dgraph: DiGraphMap::new(),
            graph: LinkedHashMap::new(),
            current_id: Option::None,
        }
    }

    fn set_current_id(&mut self, id: AnyId) {
        self.insert_node(id);
        self.current_id = Option::Some(id);
    }

    fn unset_current_id(&mut self) {
        self.current_id = Option::None;
    }

    fn insert_node(&mut self, id: AnyId) {
        // We have to be careful about duplicate nodes
        if !self.dgraph.contains_node(id) {
            self.dgraph.add_node(id);
            assert!(!self.graph.contains_key(&id));
            self.graph.insert(id, LinkedHashSet::new());
        }
    }

    fn insert_edge(&mut self, id1: AnyId) {
        let id0 = self.current_id.unwrap();
        self.insert_node(id1);
        if !self.dgraph.contains_edge(id0, id1) {
            self.dgraph.add_edge(id0, id1, ());
            self.graph.get_mut(&id0).unwrap().insert(id1);
        }
    }
}

impl SharedTypeVisitor for Deps {
    fn visit_type_decl_id(&mut self, id: &TypeDeclId::Id) {
        let id = AnyDeclId::Type(*id);
        self.insert_edge(id);
    }

    fn visit_global_decl_id(&mut self, id: &GlobalDeclId::Id) {
        let id = AnyDeclId::Global(*id);
        self.insert_edge(id);
    }
}

impl SharedExprVisitor for Deps {
    fn visit_fun_decl_id(&mut self, id: &FunDeclId::Id) {
        let id = AnyDeclId::Fun(*id);
        self.insert_edge(id);
    }
}

impl SharedAstVisitor for Deps {}

impl Deps {
    fn visit_body(&mut self, body: &Option<ExprBody>) {
        match &body {
            Option::None => (),
            Option::Some(body) => {
                for v in &body.locals {
                    self.visit_ty(&v.ty);
                }
                for block in &body.body {
                    self.visit_block_data(block);
                }
            }
        }
    }
}

pub fn reorder_declarations(ctx: &TransCtx) -> Result<Decls> {
    trace!();

    // Step 1: explore the declarations to build the graph
    let mut graph = Deps::new();
    for id in &ctx.all_ids {
        graph.set_current_id(*id);
        match id {
            AnyId::Type(id) => {
                let d = ctx.type_defs.get(*id).unwrap();
                use TypeDeclKind::*;
                match &d.kind {
                    Struct(fields) => {
                        for f in fields {
                            graph.visit_ty(&f.ty)
                        }
                    }
                    Enum(vl) => {
                        for v in vl {
                            for f in &v.fields {
                                graph.visit_ty(&f.ty);
                            }
                        }
                    }
                    Opaque => (),
                }
            }
            AnyId::Fun(id) => {
                let d = ctx.fun_defs.get(*id).unwrap();

                // Explore the signature
                for ty in &d.signature.inputs {
                    graph.visit_ty(ty);
                }
                graph.visit_ty(&d.signature.output);

                // Explore the body
                graph.visit_body(&d.body);
            }
            AnyId::Global(id) => {
                let d = ctx.global_defs.get(*id).unwrap();

                // Explore the body
                graph.visit_body(&d.body);
            }
        }
        graph.unset_current_id();
    }

    trace!("Graph: {:?}", &graph.dgraph);

    // Step 2: Apply Tarjan's SCC (Strongly Connected Components) algorithm
    let sccs = tarjan_scc(&graph.dgraph);

    // Step 3: Reorder the declarations in an order as close as possible to the one
    // given by the user. To be more precise, if we don't need to move
    // definitions, the order in which we generate the declarations should
    // be the same as the one in which the user wrote them.
    // Remark: the [get_id_dependencies] function will be called once per id, meaning
    // it is ok if it is not very efficient and clones values.
    let get_id_dependencies = &|id| graph.graph.get(&id).unwrap().iter().copied().collect();
    let all_ids: Vec<AnyId> = graph.graph.keys().copied().collect();
    let SCCs {
        sccs: reordered_sccs,
        scc_deps: _,
    } = reorder_sccs::<AnyId>(get_id_dependencies, &all_ids, &sccs);

    // Finally, generate the list of declarations
    let mut reordered_decls = DeclarationsGroups::new();

    // Iterate over the SCC ids in the proper order
    for scc in reordered_sccs.iter() {
        // Retrieve the SCC
        assert!(!scc.is_empty());

        // Note that the length of an SCC should be at least 1.
        let mut it = scc.iter();
        let id0 = *it.next().unwrap();
        let decl = graph.graph.get(&id0).unwrap();

        // The group should consist of only functions, only types or only one global.
        for id in scc {
            assert!(id0.variant_index_arity() == id.variant_index_arity());
        }
        if let AnyDeclId::Global(_) = id0 {
            assert!(scc.len() == 1);
        }

        // If an SCC has length one, the declaration may be simply recursive:
        // we determine whether it is the case by checking if the def id is in
        // its own set of dependencies.
        let is_mutually_recursive = scc.len() > 1;
        let is_simply_recursive = !is_mutually_recursive && decl.contains(&id0);

        // Add the declaration.
        // Note that we clone the vectors: it is not optimal, but they should
        // be pretty small.
        let is_rec = is_mutually_recursive || is_simply_recursive;
        let group: DeclarationGroup<TypeDeclId::Id, FunDeclId::Id, GlobalDeclId::Id> = match id0 {
            AnyDeclId::Type(_) => DeclarationGroup::make_type_group(
                is_rec,
                scc.iter().map(AnyDeclId::as_type).copied(),
            ),
            AnyDeclId::Fun(_) => {
                DeclarationGroup::make_fun_group(is_rec, scc.iter().map(AnyDeclId::as_fun).copied())
            }
            AnyDeclId::Global(_) => DeclarationGroup::make_global_group(
                is_rec,
                scc.iter().map(AnyDeclId::as_global).copied(),
            ),
        };

        reordered_decls.push(group);
    }

    trace!("{}", reordered_decls.to_string());

    Ok(reordered_decls)
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_reorder_sccs1() {
        let sccs = vec![vec![0], vec![1, 2], vec![3, 4, 5]];
        let ids = vec![0, 1, 2, 3, 4, 5];

        let get_deps = &|x| match x {
            0 => vec![3],
            1 => vec![0, 3],
            _ => vec![],
        };
        let reordered = crate::reorder_decls::reorder_sccs(get_deps, &ids, &sccs);

        assert!(reordered.sccs == vec![vec![3, 4, 5], vec![0], vec![1, 2],]);
        assert!(reordered.scc_deps[0] == im::OrdSet::from(vec![]));
        assert!(reordered.scc_deps[1] == im::OrdSet::from(vec![0]));
        assert!(reordered.scc_deps[2] == im::OrdSet::from(vec![0, 1]));
    }
}
