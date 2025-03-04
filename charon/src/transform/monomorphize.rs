//! # Micro-pass: monomorphize all functions and types; at the end of this pass, all functions and types are monomorphic.
use derive_generic_visitor::*;
use std::collections::{HashMap, HashSet};
use std::ops::ControlFlow::Continue;

use crate::transform::TransformCtx;
use crate::ullbc_ast::*;
use std::fmt::Debug;

use super::ctx::UllbcPass;

struct PassData {
    // Map of (poly item, generic args) -> mono item
    // None indicates the item hasn't been monomorphized yet
    items: HashMap<(AnyTransId, GenericArgs), Option<AnyTransId>>,
    worklist: Vec<AnyTransId>,
    visited: HashSet<AnyTransId>,
}

impl PassData {
    fn new() -> Self {
        PassData {
            items: HashMap::new(),
            worklist: Vec::new(),
            visited: HashSet::new(),
        }
    }
}

#[derive(Visitor)]
struct UsageVisitor<'a> {
    data: &'a mut PassData,
}
impl UsageVisitor<'_> {
    fn found_use(&mut self, id: &AnyTransId, gargs: &GenericArgs) {
        self.data.items.entry((*id, gargs.clone())).or_insert(None);
    }
    fn found_use_ty(&mut self, id: &TypeDeclId, gargs: &GenericArgs) {
        self.found_use(&AnyTransId::Type(*id), gargs);
    }
    fn found_use_fn(&mut self, id: &FunDeclId, gargs: &GenericArgs) {
        self.found_use(&AnyTransId::Fun(*id), gargs);
    }
}
impl VisitAst for UsageVisitor<'_> {
    fn visit_aggregate_kind(&mut self, kind: &AggregateKind) -> ControlFlow<Infallible> {
        match kind {
            AggregateKind::Adt(TypeId::Adt(id), _, _, gargs) => self.found_use_ty(id, gargs),
            AggregateKind::Closure(fun_id, gargs) => self.found_use_fn(fun_id, gargs),
            _ => {}
        }

        Continue(())
    }

    fn visit_ty_kind(&mut self, kind: &TyKind) -> ControlFlow<Infallible> {
        match kind {
            TyKind::Adt(TypeId::Adt(id), gargs) => self.found_use_ty(id, gargs),
            TyKind::Adt(TypeId::Tuple, garg) => {
                garg.drive(self);
            }
            TyKind::Literal(_) => {}
            TyKind::Ref(_, ty, _) => {
                ty.drive(self);
            }
            ty => warn!("Unhandled type kind {:?}", ty),
        }
        Continue(())
    }

    fn visit_fn_ptr(&mut self, fn_ptr: &FnPtr) -> ControlFlow<Infallible> {
        match &fn_ptr.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(id)) => {
                self.found_use_fn(id, &fn_ptr.generics)
            }
            FunIdOrTraitMethodRef::Trait(..) => {
                warn!("Monomorphization doesn't reach traits yet.")
            }
            // These can't be monomorphized, since they're builtins
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(..)) => {}
        }
        Continue(())
    }
}

fn find_uses(data: &mut PassData, item: &AnyTransItem) {
    let mut visitor = UsageVisitor { data };
    item.drive(&mut visitor);
}

// Akin to find_uses_in_*, but substitutes all uses of generics with the monomorphized versions
// This is a two-step process, because we can't mutate the translation context with new definitions
// while also mutating the existing definitions.
#[derive(Visitor)]
struct SubstVisitor<'a> {
    data: &'a PassData,
}
impl VisitAstMut for SubstVisitor<'_> {
    fn visit_ullbc_statement(&mut self, stt: &mut Statement) -> ControlFlow<Infallible> {
        stt.content.drive_mut(self);
        match &mut stt.content {
            RawStatement::Assign(_, Rvalue::Discriminant(Place { ty, .. }, id)) => {
                match ty.as_adt() {
                    Some((TypeId::Adt(new_enum_id), _)) => {
                        // Small trick; the discriminant doesn't carry the information on the
                        // generics of the enum, since it's irrelevant, but we need it to do
                        // the substitution, so we look at the type of the place we read from
                        *id = new_enum_id;
                    }
                    _ => {}
                }
                ()
            }
            _ => (),
        }

        Continue(())
    }

    fn visit_aggregate_kind(&mut self, kind: &mut AggregateKind) -> ControlFlow<Infallible> {
        match kind {
            AggregateKind::Adt(TypeId::Adt(id), _, _, gargs) => {
                let key = (AnyTransId::Type(*id), gargs.clone());
                let subst = self.data.items.get(&key).unwrap();
                let Some(AnyTransId::Type(subst_id)) = subst else {
                    panic!("Substitution missing for {:?}", key);
                };
                *id = *subst_id;
                *gargs = GenericArgs::empty(GenericsSource::Builtin);
            }
            AggregateKind::Closure(fun_id, gargs) => {
                let key = (AnyTransId::Fun(*fun_id), gargs.clone());
                let subst = self.data.items.get(&key).unwrap();
                let Some(AnyTransId::Fun(subst_id)) = subst else {
                    panic!("Substitution missing for {:?}", key);
                };
                *fun_id = *subst_id;
                *gargs = GenericArgs::empty(GenericsSource::Builtin);
            }
            _ => {}
        }

        Continue(())
    }

    fn visit_ty_kind(&mut self, kind: &mut TyKind) -> ControlFlow<Infallible> {
        match kind {
            TyKind::Adt(TypeId::Adt(id), gargs) => {
                let key = (AnyTransId::Type(*id), gargs.clone());
                let subst = self.data.items.get(&key).unwrap();
                let Some(AnyTransId::Type(subst_id)) = subst else {
                    panic!("Substitution missing for {:?}", key);
                };
                *id = *subst_id;
                *gargs = GenericArgs::empty(GenericsSource::Builtin);
            }
            TyKind::Adt(TypeId::Tuple, garg) => {
                garg.drive_mut(self);
            }
            TyKind::Literal(_) => {}
            TyKind::Ref(_, ty, _) => {
                ty.drive_mut(self);
            }
            ty => warn!("Unhandled type kind {:?}", ty),
        }
        Continue(())
    }

    fn visit_fn_ptr(&mut self, fn_ptr: &mut FnPtr) -> ControlFlow<Infallible> {
        match &mut fn_ptr.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id)) => {
                let key = (AnyTransId::Fun(*fun_id), fn_ptr.generics.clone());
                let subst = self.data.items.get(&key).unwrap();
                let Some(AnyTransId::Fun(subst_id)) = subst else {
                    panic!("Substitution missing for {:?}", key);
                };
                *fun_id = *subst_id;
                fn_ptr.generics = GenericArgs::empty(GenericsSource::Builtin);
            }
            FunIdOrTraitMethodRef::Trait(..) => {
                warn!("Monomorphization doesn't reach traits yet.")
            }
            // These can't be monomorphized, since they're builtins
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(..)) => {}
        }
        Continue(())
    }

    fn visit_place(&mut self, place: &mut Place) -> ControlFlow<Infallible> {
        place.ty.drive_mut(self);
        match &mut place.kind {
            PlaceKind::Projection(inner, ProjectionElem::Field(FieldProjKind::Adt(id, _), _)) => {
                // Trick, we don't know the generics but the projected place does, so
                // we substitute it there, then update our current id.
                inner.drive_mut(self);
                let (inner_id, _) = inner.ty.as_adt().unwrap();
                *id = *inner_id.as_adt().unwrap()
            }
            _ => {}
        }
        Continue(())
    }
}

fn subst_uses<T: AstVisitable + Debug>(data: &PassData, item: &mut T) {
    let mut visitor = SubstVisitor { data };
    item.drive_mut(&mut visitor);
}

fn path_for_generics(gargs: &GenericArgs) -> PathElem {
    PathElem::Ident(gargs.to_string(), Disambiguator::ZERO)
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Check the option which instructs to ignore this pass
        if !ctx.options.monomorphize {
            return;
        }

        // From https://doc.rust-lang.org/nightly/nightly-rustc/rustc_monomorphize/collector/index.html#general-algorithm
        //
        // The purpose of the algorithm implemented in this module is to build the mono item
        // graph for the current crate. It runs in two phases:
        // 1. Discover the roots of the graph by traversing the HIR of the crate.
        // 2. Starting from the roots, find uses by inspecting the MIR representation of the
        //    item corresponding to a given node, until no more new nodes are found.
        //
        // The roots of the mono item graph correspond to the public non-generic syntactic
        // items in the source code. We find them by walking the HIR of the crate, and whenever
        // we hit upon a public function, method, or static item, we create a mono item
        // consisting of the items DefId and, since we only consider non-generic items, an
        // empty type-parameters set.
        //
        // Given a mono item node, we can discover uses by inspecting its MIR. We walk the MIR
        // to find other mono items used by each mono item. Since the mono item we are
        // currently at is always monomorphic, we also know the concrete type arguments of its
        // used mono items. The specific forms a use can take in MIR are quite diverse: it
        // includes calling functions/methods, taking a reference to a function/method, drop
        // glue, and unsizing casts.

        // In our version of the algorithm, we do the following:
        // 1. Find all the roots, adding them to the worklist.
        // 2. For each item in the worklist:
        //    a. Find all the items it uses, adding them to the worklist and the generic
        //      arguments to the item.
        //    b. Mark the item as visited

        // Final list of monomorphized items: { (poly item, generic args) -> mono item }
        let mut data = PassData::new();

        let empty_gargs = GenericArgs::empty(GenericsSource::Builtin);

        // Find the roots of the mono item graph
        for (id, item) in ctx.translated.all_items_with_ids() {
            match item {
                AnyTransItem::Fun(f) if f.signature.generics.is_empty() => {
                    data.items.insert((id, empty_gargs.clone()), Some(id));
                    data.worklist.push(id);
                }
                _ => {}
            }
        }

        // Iterate over worklist -- these items are always monomorphic!
        while let Some(id) = data.worklist.pop() {
            if data.visited.contains(&id) {
                continue;
            }
            data.visited.insert(id);

            // 1. Find new uses
            let Some(item) = ctx.translated.get_item(id) else {
                panic!("Couldn't find item {:} in translated items.", id)
            };
            find_uses(&mut data, &item);

            // 2. Iterate through all newly discovered uses
            for ((id, gargs), mono) in data.items.iter_mut() {
                if mono.is_some() {
                    continue;
                }

                // a. Monomorphize the items if they're polymorphic, add them to the worklist
                let new_mono = match id {
                    AnyTransId::Fun(fun_id) => 'id_match: {
                        let fun = ctx.translated.fun_decls.get(*fun_id).unwrap();

                        if gargs.is_empty() {
                            break 'id_match AnyTransId::Fun(*fun_id);
                        }

                        let mut fun_sub = fun.clone().substitute(gargs);
                        fun_sub.signature.generics = GenericParams::empty();

                        let fun_id_sub = ctx.translated.fun_decls.reserve_slot();
                        fun_sub.def_id = fun_id_sub;
                        ctx.translated.fun_decls.set_slot(fun_id_sub, fun_sub);

                        AnyTransId::Fun(fun_id_sub)
                    }
                    AnyTransId::Type(typ_id) => 'id_match: {
                        let typ = ctx.translated.type_decls.get(*typ_id).unwrap();

                        if gargs.is_empty() {
                            break 'id_match AnyTransId::Type(*typ_id);
                        }

                        let mut typ_sub = typ.clone().substitute(gargs);
                        typ_sub.generics = GenericParams::empty();
                        typ_sub.item_meta.name.name.push(path_for_generics(gargs));

                        let typ_id_sub = ctx.translated.type_decls.reserve_slot();
                        typ_sub.def_id = typ_id_sub;
                        ctx.translated.type_decls.set_slot(typ_id_sub, typ_sub);

                        AnyTransId::Type(typ_id_sub)
                    }
                    _ => todo!("Unhandled monomorphization target ID {:?}", id),
                };
                *mono = Some(new_mono);
                data.worklist.push(new_mono);
            }

            // 3. Substitute all generics with the monomorphized versions
            let Some(item) = ctx.translated.get_item_mut(id) else {
                panic!("Couldn't find item {:} in translated items.", id)
            };
            match item {
                AnyTransItemMut::Fun(f) => subst_uses(&data, f),
                AnyTransItemMut::Type(t) => subst_uses(&data, t),
                AnyTransItemMut::TraitImpl(t) => subst_uses(&data, t),
                AnyTransItemMut::Global(g) => subst_uses(&data, g),
                AnyTransItemMut::TraitDecl(t) => subst_uses(&data, t),
            };
        }

        // Now, remove all polymorphic items from the translation context, as all their
        // uses have been monomorphized and substituted
        ctx.translated
            .fun_decls
            .retain(|f| f.signature.generics.is_empty());
        ctx.translated.type_decls.retain(|t| t.generics.is_empty());
    }

    fn name(&self) -> &str {
        "monomorphize"
    }
}
