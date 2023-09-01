use crate::common::*;
use crate::expressions::*;
use crate::gast::*;
use crate::graphs::*;
use crate::translate_ctx::TransCtx;
use crate::types::*;
use crate::ullbc_ast::*;
use hashlink::linked_hash_map::LinkedHashMap;
use linked_hash_set::LinkedHashSet;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use serde::Serialize;
use std::fmt::{Debug, Display, Error, Formatter};
use std::vec::Vec;

/// A (group of) top-level declaration(s), properly reordered.
/// "G" stands for "generic"
#[derive(Debug, VariantIndexArity, VariantName, Serialize)]
pub enum GDeclarationGroup<Id> {
    /// A non-recursive declaration
    NonRec(Id),
    /// A (group of mutually) recursive declaration(s)
    Rec(Vec<Id>),
}

/// A (group of) top-level declaration(s), properly reordered.
#[derive(Debug, VariantIndexArity, VariantName, Serialize)]
pub enum DeclarationGroup {
    /// A type declaration group
    Type(GDeclarationGroup<TypeDeclId::Id>),
    /// A function declaration group
    Fun(GDeclarationGroup<FunDeclId::Id>),
    /// A global declaration group
    Global(GDeclarationGroup<GlobalDeclId::Id>),
    ///
    TraitDecl(GDeclarationGroup<TraitDeclId::Id>),
    ///
    TraitImpl(GDeclarationGroup<TraitImplId::Id>),
}

impl DeclarationGroup {
    fn make_type_group(is_rec: bool, gr: impl Iterator<Item = TypeDeclId::Id>) -> Self {
        let gr: Vec<_> = gr.collect();
        if is_rec {
            DeclarationGroup::Type(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Type(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_fun_group(is_rec: bool, gr: impl Iterator<Item = FunDeclId::Id>) -> Self {
        let gr: Vec<_> = gr.collect();
        if is_rec {
            DeclarationGroup::Fun(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_global_group(is_rec: bool, gr: impl Iterator<Item = GlobalDeclId::Id>) -> Self {
        let gr: Vec<_> = gr.collect();
        if is_rec {
            DeclarationGroup::Global(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Global(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_trait_decl_group(is_rec: bool, gr: impl Iterator<Item = TraitDeclId::Id>) -> Self {
        let gr: Vec<_> = gr.collect();
        assert!(!is_rec && gr.len() == 1);
        DeclarationGroup::TraitDecl(GDeclarationGroup::NonRec(gr[0]))
    }

    fn make_trait_impl_group(is_rec: bool, gr: impl Iterator<Item = TraitImplId::Id>) -> Self {
        let gr: Vec<_> = gr.collect();
        assert!(!is_rec && gr.len() == 1);
        DeclarationGroup::TraitImpl(GDeclarationGroup::NonRec(gr[0]))
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
pub enum AnyDeclId<TypeId, FunId, GlobalId, TraitDeclId, TraitImplId> {
    Type(TypeId),
    Fun(FunId),
    Global(GlobalId),
    TraitDecl(TraitDeclId),
    TraitImpl(TraitImplId),
}

#[derive(Clone, Copy)]
pub struct DeclInfo {
    pub is_transparent: bool,
}

pub type DeclarationsGroups = Vec<DeclarationGroup>;

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<Id: Debug> Display for GDeclarationGroup<Id> {
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

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl Display for DeclarationGroup {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            DeclarationGroup::Type(decl) => write!(f, "{{ Type(s): {decl} }}"),
            DeclarationGroup::Fun(decl) => write!(f, "{{ Fun(s): {decl} }}"),
            DeclarationGroup::Global(decl) => write!(f, "{{ Global(s): {decl} }}"),
            DeclarationGroup::TraitDecl(decl) => write!(f, "{{ Trait decls(s): {decl} }}"),
            DeclarationGroup::TraitImpl(decl) => write!(f, "{{ Trait impl(s): {decl} }}"),
        }
    }
}

pub type AnyTransId =
    AnyDeclId<TypeDeclId::Id, FunDeclId::Id, GlobalDeclId::Id, TraitDeclId::Id, TraitImplId::Id>;

pub struct Deps {
    dgraph: DiGraphMap<AnyTransId, ()>,
    /// Want to make sure we remember the order of insertion
    graph: LinkedHashMap<AnyTransId, LinkedHashSet<AnyTransId>>,
    /// We use this when exploring the graph
    current_id: Option<AnyTransId>,
}

impl Deps {
    fn new() -> Self {
        Deps {
            dgraph: DiGraphMap::new(),
            graph: LinkedHashMap::new(),
            current_id: Option::None,
        }
    }

    fn set_current_id(&mut self, id: AnyTransId) {
        self.insert_node(id);
        self.current_id = Option::Some(id);
    }

    fn unset_current_id(&mut self) {
        self.current_id = Option::None;
    }

    fn insert_node(&mut self, id: AnyTransId) {
        // We have to be careful about duplicate nodes
        if !self.dgraph.contains_node(id) {
            self.dgraph.add_node(id);
            assert!(!self.graph.contains_key(&id));
            self.graph.insert(id, LinkedHashSet::new());
        }
    }

    fn insert_edge(&mut self, id1: AnyTransId) {
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

    fn visit_generics_and_preds(&mut self, generics: &GenericParams, preds: &Predicates) {
        // Visit the traits referenced in the generics
        for clause in &generics.trait_clauses {
            self.visit_trait_clause(clause);
        }

        // Visit the predicates
        self.visit_predicates(preds);
    }
}

pub fn reorder_declarations(ctx: &TransCtx) -> Result<DeclarationsGroups> {
    trace!();

    // Step 1: explore the declarations to build the graph
    let mut graph = Deps::new();
    for id in &ctx.all_ids {
        graph.set_current_id(*id);
        match id {
            AnyTransId::Type(id) => {
                let d = ctx.type_defs.get(*id).unwrap();
                use TypeDeclKind::*;

                // Visit the generics and the predicates
                graph.visit_generics_and_preds(&d.generics, &d.preds);

                // Visit the body
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
            AnyTransId::Fun(id) => {
                let d = ctx.fun_defs.get(*id).unwrap();

                // Explore the signature
                let sig = &d.signature;
                graph.visit_generics_and_preds(&sig.generics, &sig.preds);
                for ty in &sig.inputs {
                    graph.visit_ty(ty);
                }
                graph.visit_ty(&sig.output);

                // Explore the body
                graph.visit_body(&d.body);
            }
            AnyTransId::Global(id) => {
                let d = ctx.global_defs.get(*id).unwrap();

                // Explore the body
                graph.visit_body(&d.body);
            }
            AnyTransId::TraitDecl(id) => {
                let d = ctx.trait_decls.get(*id).unwrap();

                // Visit the generics and the predicates
                graph.visit_generics_and_preds(&d.generics, &d.preds);

                // Visit the items
                for (_, (ty, c)) in &d.consts {
                    graph.visit_ty(ty);
                    if let Some(id) = c {
                        graph.visit_global_decl_id(id);
                    }
                }

                for (_, (clauses, ty)) in &d.types {
                    for c in clauses {
                        graph.visit_trait_clause(c);
                    }
                    if let Some(ty) = ty {
                        graph.visit_ty(ty);
                    }
                }

                for (_, id) in &d.required_methods {
                    graph.visit_fun_decl_id(id);
                }
            }
            AnyTransId::TraitImpl(id) => {
                let d = ctx.trait_impls.get(*id).unwrap();

                // Visit the generics and the predicates
                graph.visit_generics_and_preds(&d.generics, &d.preds);

                // Visit the implemented trait
                graph.visit_trait_decl_id(&d.impl_trait.trait_id);
                graph.visit_generic_args(&d.impl_trait.generics);

                // Visit the items
                for (_, (ty, id)) in &d.consts {
                    graph.visit_ty(ty);
                    graph.visit_global_decl_id(id);
                }

                for (_, (trait_refs, ty)) in &d.types {
                    graph.visit_ty(ty);
                    for trait_ref in trait_refs {
                        graph.visit_trait_ref(trait_ref);
                    }
                }

                for (_, id) in d.required_methods.iter().chain(d.provided_methods.iter()) {
                    graph.visit_fun_decl_id(id);
                }
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
    let all_ids: Vec<AnyTransId> = graph.graph.keys().copied().collect();
    let SCCs {
        sccs: reordered_sccs,
        scc_deps: _,
    } = reorder_sccs::<AnyTransId>(get_id_dependencies, &all_ids, &sccs);

    // Finally, generate the list of declarations
    let mut reordered_decls: DeclarationsGroups = Vec::new();

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
        let group: DeclarationGroup = match id0 {
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
            AnyDeclId::TraitDecl(_) => DeclarationGroup::make_trait_decl_group(
                is_rec,
                scc.iter().map(AnyDeclId::as_trait_decl).copied(),
            ),
            AnyDeclId::TraitImpl(_) => DeclarationGroup::make_trait_impl_group(
                is_rec,
                scc.iter().map(AnyDeclId::as_trait_impl).copied(),
            ),
        };

        reordered_decls.push(group);
    }

    trace!("{:?}", reordered_decls);

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
