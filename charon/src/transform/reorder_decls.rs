use crate::common::*;
use crate::formatter::{AstFormatter, IntoFormatter};
use crate::graphs::*;
use crate::transform::TransformCtx;
pub use crate::translate_ctx::AnyTransId;
use crate::types::*;
use crate::ullbc_ast::*;
use derive_visitor::{Drive, Visitor};
use hashlink::linked_hash_map::LinkedHashMap;
use linked_hash_set::LinkedHashSet;
use macros::{VariantIndexArity, VariantName};
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use serde::{Deserialize, Serialize};
use std::fmt::{Debug, Display, Error};
use std::vec::Vec;

/// A (group of) top-level declaration(s), properly reordered.
/// "G" stands for "generic"
#[derive(Debug, Clone, VariantIndexArity, VariantName, Serialize, Deserialize)]
pub enum GDeclarationGroup<Id> {
    /// A non-recursive declaration
    NonRec(Id),
    /// A (group of mutually) recursive declaration(s)
    Rec(Vec<Id>),
}

/// A (group of) top-level declaration(s), properly reordered.
#[derive(Debug, Clone, VariantIndexArity, VariantName, Serialize, Deserialize)]
pub enum DeclarationGroup {
    /// A type declaration group
    Type(GDeclarationGroup<TypeDeclId>),
    /// A function declaration group
    Fun(GDeclarationGroup<FunDeclId>),
    /// A global declaration group
    Global(GDeclarationGroup<GlobalDeclId>),
    ///
    TraitDecl(GDeclarationGroup<TraitDeclId>),
    ///
    TraitImpl(GDeclarationGroup<TraitImplId>),
}

impl<Id: Copy> GDeclarationGroup<Id> {
    pub fn get_ids(&self) -> Vec<Id> {
        use GDeclarationGroup::*;
        match self {
            NonRec(id) => vec![*id],
            Rec(ids) => ids.clone(),
        }
    }
}

impl DeclarationGroup {
    fn make_type_group(is_rec: bool, gr: impl Iterator<Item = TypeDeclId>) -> Self {
        let gr: Vec<_> = gr.collect();
        if is_rec {
            DeclarationGroup::Type(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Type(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_fun_group(is_rec: bool, gr: impl Iterator<Item = FunDeclId>) -> Self {
        let gr: Vec<_> = gr.collect();
        if is_rec {
            DeclarationGroup::Fun(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_global_group(is_rec: bool, gr: impl Iterator<Item = GlobalDeclId>) -> Self {
        let gr: Vec<_> = gr.collect();
        if is_rec {
            DeclarationGroup::Global(GDeclarationGroup::Rec(gr))
        } else {
            assert!(gr.len() == 1);
            DeclarationGroup::Global(GDeclarationGroup::NonRec(gr[0]))
        }
    }

    fn make_trait_decl_group(
        _ctx: &TransformCtx,
        _is_rec: bool,
        gr: impl Iterator<Item = TraitDeclId>,
    ) -> Self {
        let gr: Vec<_> = gr.collect();
        // Trait declarations often refer to `Self`, like below,
        // which means they are often considered as recursive by our
        // analysis. TODO: do something more precise. What is important
        // is that we never use the "whole" self clause as argument,
        // but rather projections over the self clause (like `<Self as Foo>::u`,
        // in the declaration for `Foo`).
        if gr.len() == 1 {
            DeclarationGroup::TraitDecl(GDeclarationGroup::NonRec(gr[0]))
        } else {
            DeclarationGroup::TraitDecl(GDeclarationGroup::Rec(gr))
        }
    }

    fn make_trait_impl_group(
        ctx: &TransformCtx,
        is_rec: bool,
        gr: impl Iterator<Item = TraitImplId>,
    ) -> Self {
        let gr: Vec<_> = gr.collect();
        let ctx = ctx.into_fmt();
        assert!(
            !is_rec && gr.len() == 1,
            "Invalid trait impl group:\n{}",
            gr.iter()
                .map(|id| ctx.format_object(*id))
                .collect::<Vec<String>>()
                .join("\n")
        );
        DeclarationGroup::TraitImpl(GDeclarationGroup::NonRec(gr[0]))
    }
}

#[derive(Clone, Copy)]
pub struct DeclInfo {
    pub is_transparent: bool,
}

pub type DeclarationsGroups = Vec<DeclarationGroup>;

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<Id: Debug> Display for GDeclarationGroup<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), Error> {
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            DeclarationGroup::Type(decl) => write!(f, "{{ Type(s): {decl} }}"),
            DeclarationGroup::Fun(decl) => write!(f, "{{ Fun(s): {decl} }}"),
            DeclarationGroup::Global(decl) => write!(f, "{{ Global(s): {decl} }}"),
            DeclarationGroup::TraitDecl(decl) => write!(f, "{{ Trait decls(s): {decl} }}"),
            DeclarationGroup::TraitImpl(decl) => write!(f, "{{ Trait impl(s): {decl} }}"),
        }
    }
}

#[derive(Visitor)]
#[visitor(
    TypeDeclId(enter),
    FunDeclId(enter),
    GlobalDeclId(enter),
    TraitImplId(enter),
    TraitDeclId(enter),
    BodyId(enter)
)]
pub struct Deps<'tcx, 'ctx> {
    ctx: &'tcx TransformCtx<'ctx>,
    dgraph: DiGraphMap<AnyTransId, ()>,
    // Want to make sure we remember the order of insertion
    graph: LinkedHashMap<AnyTransId, LinkedHashSet<AnyTransId>>,
    // We use this when computing the graph
    current_id: Option<AnyTransId>,
    // We use this to track the trait impl block the current item belongs to
    // (if relevant).
    //
    // We use this to ignore the references to the parent impl block.
    //
    // If we don't do so, when computing our dependency graph we end up with
    // mutually recursive trait impl blocks/trait method impls in the presence
    // of associated types (the deepest reason is that we don't normalize the
    // types we query from rustc when translating the types from function
    // signatures - we avoid doing so because as of now it makes resolving
    // the trait params harder: if we get normalized types, we have to
    // implement a normalizer on our side to make sure we correctly match
    // types...).
    //
    //
    // For instance, the problem happens if in Rust we have:
    // ```text
    // pub trait WithConstTy {
    //     type W;
    //     fn f(x: &mut Self::W);
    // }
    //
    // impl WithConstTy for bool {
    //     type W = u64;
    //     fn f(_: &mut Self::W) {}
    // }
    // ```
    //
    // In LLBC we get:
    //
    // ```text
    // impl traits::Bool::0 : traits::WithConstTy<bool>
    // {
    //     type W = u64 with []
    //     fn f = traits::Bool::0::f
    // }
    //
    // fn traits::Bool::0::f<@R0>(@1: &@R0 mut (traits::Bool::0::W)) { .. }
    // //                                       ^^^^^^^^^^^^^^^
    // //                                    refers to the trait impl
    // ```
    impl_trait_id: Option<TraitImplId>,
}

impl<'tcx, 'ctx> Deps<'tcx, 'ctx> {
    fn new(ctx: &'tcx TransformCtx<'ctx>) -> Self {
        Deps {
            ctx,
            dgraph: DiGraphMap::new(),
            graph: LinkedHashMap::new(),
            current_id: None,
            impl_trait_id: None,
        }
    }

    fn set_current_id(&mut self, ctx: &TransformCtx, id: AnyTransId) {
        self.insert_node(id);
        self.current_id = Some(id);

        // Add the id of the trait impl trait this item belongs to, if necessary
        use AnyTransId::*;
        match id {
            TraitDecl(_) | TraitImpl(_) => (),
            Type(_) | Global(_) => {
                // TODO
            }
            Fun(id) => {
                // Lookup the function declaration.
                //
                // The declaration may not be present if we encountered errors.
                if let Some(decl) = ctx.translated.fun_decls.get(id) {
                    if let ItemKind::TraitItemImpl {
                        impl_id,
                        trait_id: _,
                        item_name: _,
                        provided: _,
                    } = &decl.kind
                    {
                        // Register the trait decl id
                        self.impl_trait_id = Some(*impl_id)
                    }
                } else {
                    // Sanity check
                    assert!(ctx.has_errors());
                }
            }
        }
    }

    fn unset_current_id(&mut self) {
        self.current_id = None;
        self.impl_trait_id = None;
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

impl Deps<'_, '_> {
    fn enter_type_decl_id(&mut self, id: &TypeDeclId) {
        let id = AnyTransId::Type(*id);
        self.insert_edge(id);
    }

    fn enter_global_decl_id(&mut self, id: &GlobalDeclId) {
        let id = AnyTransId::Global(*id);
        self.insert_edge(id);
    }

    fn enter_trait_impl_id(&mut self, id: &TraitImplId) {
        // If the impl is the impl this item belongs to, we ignore it
        // TODO: this is not very satisfying but this is the only way
        // we have of preventing mutually recursive groups between
        // method impls and trait impls in the presence of associated types...
        if let Some(impl_id) = &self.impl_trait_id && impl_id == id {
            // Ignore
        }
        else {
            let id = AnyTransId::TraitImpl(*id);
            self.insert_edge(id);
        }
    }

    fn enter_trait_decl_id(&mut self, id: &TraitDeclId) {
        let id = AnyTransId::TraitDecl(*id);
        self.insert_edge(id);
    }

    fn enter_fun_decl_id(&mut self, id: &FunDeclId) {
        let id = AnyTransId::Fun(*id);
        self.insert_edge(id);
    }

    fn enter_body_id(&mut self, id: &BodyId) {
        if let Some(body) = self.ctx.translated.bodies.get(*id) {
            body.drive(self);
        }
    }
}

impl AnyTransId {
    fn fmt_with_ctx(&self, ctx: &TransformCtx) -> String {
        use AnyTransId::*;
        let ctx = ctx.into_fmt();
        match self {
            Type(id) => ctx.format_object(*id),
            Fun(id) => ctx.format_object(*id),
            Global(id) => ctx.format_object(*id),
            TraitDecl(id) => ctx.format_object(*id),
            TraitImpl(id) => ctx.format_object(*id),
        }
    }
}

impl Deps<'_, '_> {
    fn fmt_with_ctx(&self, ctx: &TransformCtx) -> String {
        self.dgraph
            .nodes()
            .map(|node| {
                let edges = self
                    .dgraph
                    .edges(node)
                    .map(|e| format!("\n  {}", e.1.fmt_with_ctx(ctx)))
                    .collect::<Vec<String>>()
                    .join(",");

                format!("{} -> [{}\n]", node.fmt_with_ctx(ctx), edges)
            })
            .collect::<Vec<String>>()
            .join(",\n")
    }
}

fn compute_declarations_graph<'tcx, 'ctx>(ctx: &'tcx TransformCtx<'ctx>) -> Deps<'tcx, 'ctx> {
    let mut graph = Deps::new(ctx);
    for id in &ctx.translated.all_ids {
        graph.set_current_id(ctx, *id);
        match id {
            AnyTransId::Type(id) => {
                if let Some(d) = ctx.translated.type_decls.get(*id) {
                    d.drive(&mut graph);
                } else {
                    // There may have been errors
                    assert!(ctx.has_errors());
                }
            }
            AnyTransId::Fun(id) => {
                if let Some(d) = ctx.translated.fun_decls.get(*id) {
                    // Explore the signature
                    d.signature.drive(&mut graph);
                    // Skip `d.kind`: we don't want to record a dependency to the impl block this
                    // belongs to.
                    d.body.drive(&mut graph);
                } else {
                    // There may have been errors
                    assert!(ctx.has_errors());
                }
            }
            AnyTransId::Global(id) => {
                if let Some(d) = ctx.translated.global_decls.get(*id) {
                    // FIXME: shouldn't we visit the generics etc?
                    d.body.drive(&mut graph);
                } else {
                    // There may have been errors
                    assert!(ctx.has_errors());
                }
            }
            AnyTransId::TraitDecl(id) => {
                if let Some(d) = ctx.translated.trait_decls.get(*id) {
                    // Visit the traits referenced in the generics
                    d.generics.drive(&mut graph);

                    // Visit the predicates
                    d.preds.drive(&mut graph);

                    // Visit the parent clauses
                    d.parent_clauses.drive(&mut graph);

                    // Visit the items
                    d.consts.drive(&mut graph);
                    d.types.drive(&mut graph);

                    let method_ids = d
                        .required_methods
                        .iter()
                        .map(|(_, id)| id)
                        .chain(d.provided_methods.iter().filter_map(|(_, id)| id.as_ref()))
                        .copied();
                    for id in method_ids {
                        // Important: we must ignore the function id, because
                        // otherwise in the presence of associated types we may
                        // get a mutual recursion between the function and the
                        // trait.
                        // Ex:
                        // ```
                        // trait Trait {
                        //   type X;
                        //   fn f(x : Trait::X);
                        // }
                        // ```
                        let decl = ctx.translated.fun_decls.get(id).unwrap();
                        decl.signature.drive(&mut graph);
                    }
                } else {
                    // There may have been errors
                    assert!(ctx.has_errors());
                }
            }
            AnyTransId::TraitImpl(id) => {
                if let Some(d) = ctx.translated.trait_impls.get(*id) {
                    d.drive(&mut graph);
                } else {
                    // There may have been errors
                    assert!(ctx.has_errors());
                }
            }
        }
        graph.unset_current_id();
    }
    graph
}

fn group_declarations_from_scc(
    ctx: &TransformCtx,
    graph: Deps<'_, '_>,
    reordered_sccs: SCCs<AnyTransId>,
) -> DeclarationsGroups {
    let reordered_sccs = &reordered_sccs.sccs;
    let mut reordered_decls: DeclarationsGroups = Vec::new();

    // Iterate over the SCC ids in the proper order
    for scc in reordered_sccs.iter() {
        assert!(!scc.is_empty());

        // Note that the length of an SCC should be at least 1.
        let mut it = scc.iter();
        let id0 = *it.next().unwrap();
        let decl = graph.graph.get(&id0).unwrap();

        // The group should consist of only functions, only types or only one global.
        for id in scc {
            assert!(
                id0.variant_index_arity() == id.variant_index_arity(),
                "Invalid scc:\n{}",
                scc.iter()
                    .map(|x| x.fmt_with_ctx(ctx))
                    .collect::<Vec<String>>()
                    .join("\n")
            );
        }
        if let AnyTransId::Global(_) = id0 {
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
            AnyTransId::Type(_) => DeclarationGroup::make_type_group(
                is_rec,
                scc.iter().map(AnyTransId::as_type).copied(),
            ),
            AnyTransId::Fun(_) => DeclarationGroup::make_fun_group(
                is_rec,
                scc.iter().map(AnyTransId::as_fun).copied(),
            ),
            AnyTransId::Global(_) => DeclarationGroup::make_global_group(
                is_rec,
                scc.iter().map(AnyTransId::as_global).copied(),
            ),
            AnyTransId::TraitDecl(_) => DeclarationGroup::make_trait_decl_group(
                ctx,
                is_rec,
                scc.iter().map(AnyTransId::as_trait_decl).copied(),
            ),
            AnyTransId::TraitImpl(_) => DeclarationGroup::make_trait_impl_group(
                ctx,
                is_rec,
                scc.iter().map(AnyTransId::as_trait_impl).copied(),
            ),
        };

        reordered_decls.push(group);
    }
    reordered_decls
}

pub fn compute_reordered_decls(ctx: &TransformCtx) -> DeclarationsGroups {
    trace!();

    // Step 1: explore the declarations to build the graph
    let graph = compute_declarations_graph(ctx);
    trace!("Graph:\n{}\n", graph.fmt_with_ctx(ctx));

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
    let reordered_sccs = reorder_sccs::<AnyTransId>(get_id_dependencies, &all_ids, &sccs);

    // Finally, generate the list of declarations
    let reordered_decls = group_declarations_from_scc(ctx, graph, reordered_sccs);

    trace!("{:?}", reordered_decls);
    reordered_decls
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
