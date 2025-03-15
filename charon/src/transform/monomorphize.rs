//! # Micro-pass: monomorphize all functions and types; at the end of this pass, all functions and types are monomorphic.
use derive_generic_visitor::*;
use std::collections::{HashMap, HashSet};
use std::ops::ControlFlow::Continue;

use crate::transform::TransformCtx;
use crate::ullbc_ast::*;
use std::fmt::Debug;

use super::ctx::UllbcPass;

enum OptionHint<T, H> {
    Some(T),
    None,
    Hint(H),
}

impl<T, H> OptionHint<T, H> {
    fn is_some(&self) -> bool {
        match self {
            OptionHint::Some(_) => true,
            OptionHint::None => false,
            OptionHint::Hint(_) => false,
        }
    }

    fn hint_or<'a>(&'a self, hint: &'a H) -> &'a H {
        match self {
            OptionHint::Some(_) => hint,
            OptionHint::None => hint,
            OptionHint::Hint(h) => h,
        }
    }
}

struct PassData {
    // Map of (poly item, generic args) -> mono item
    // None indicates the item hasn't been monomorphized yet
    items: HashMap<(AnyTransId, GenericArgs), OptionHint<AnyTransId, (AnyTransId, GenericArgs)>>,
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

impl TranslatedCrate {
    fn find_trait_impl_and_gargs(self: &Self, kind: &TraitRefKind) -> (&TraitImpl, GenericArgs) {
        match kind {
            TraitRefKind::TraitImpl(impl_id, gargs) => {
                let trait_impl = self.trait_impls.get(*impl_id).unwrap();
                (trait_impl, gargs.clone())
            }
            TraitRefKind::ParentClause(p, _, clause) => {
                let (trait_impl, _) = self.find_trait_impl_and_gargs(p);
                let t_ref = trait_impl.parent_trait_refs.get(*clause).unwrap();
                self.find_trait_impl_and_gargs(&t_ref.kind)
            }
            _ => panic!("Unexpected trait reference kind"),
        }
    }
}

#[derive(Visitor)]
struct UsageVisitor<'a> {
    data: &'a mut PassData,
    krate: &'a TranslatedCrate,
}
impl UsageVisitor<'_> {
    fn found_use(
        &mut self,
        id: &AnyTransId,
        gargs: &GenericArgs,
        default: OptionHint<AnyTransId, (AnyTransId, GenericArgs)>,
    ) {
        trace!("Mono: Found use: {:?} / {:?}", id, gargs);
        self.data
            .items
            .entry((*id, gargs.clone()))
            .or_insert(default);
    }
    fn found_use_ty(&mut self, id: &TypeDeclId, gargs: &GenericArgs) {
        self.found_use(&AnyTransId::Type(*id), gargs, OptionHint::None);
    }
    fn found_use_fn(&mut self, id: &FunDeclId, gargs: &GenericArgs) {
        self.found_use(&AnyTransId::Fun(*id), gargs, OptionHint::None);
    }
    fn found_use_fn_hinted(
        &mut self,
        id: &FunDeclId,
        gargs: &GenericArgs,
        (h_id, h_args): (FunDeclId, GenericArgs),
    ) {
        self.found_use(
            &AnyTransId::Fun(*id),
            gargs,
            OptionHint::Hint((AnyTransId::Fun(h_id), h_args)),
        );
    }
}
impl VisitAst for UsageVisitor<'_> {
    fn enter_aggregate_kind(&mut self, kind: &AggregateKind) {
        match kind {
            AggregateKind::Adt(TypeId::Adt(id), _, _, gargs) => self.found_use_ty(id, gargs),
            AggregateKind::Closure(fun_id, gargs) => self.found_use_fn(fun_id, gargs),
            _ => {}
        }
    }

    fn enter_ty_kind(&mut self, kind: &TyKind) {
        match kind {
            TyKind::Adt(TypeId::Adt(id), gargs) => {
                self.found_use_ty(id, gargs);
            }
            _ => {}
        }
    }

    fn enter_fn_ptr(&mut self, fn_ptr: &FnPtr) {
        match &fn_ptr.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(id)) => {
                self.found_use_fn(id, &fn_ptr.generics)
            }
            FunIdOrTraitMethodRef::Trait(t_ref, name, id) => {
                let (trait_impl, impl_gargs) = self.krate.find_trait_impl_and_gargs(&t_ref.kind);
                let (_, bound_fn) = trait_impl.methods().find(|(n, _)| n == name).unwrap();
                let fn_ref: Binder<Binder<FunDeclRef>> = Binder::new(
                    BinderKind::Other,
                    trait_impl.generics.clone(),
                    bound_fn.clone(),
                );
                // This is the actual function we need to call!
                // Whereas id is the trait method reference(?)
                let fn_ref = fn_ref.apply(&impl_gargs).apply(&fn_ptr.generics);
                let gargs_key = fn_ptr.generics.clone().concat(
                    GenericsSource::Builtin,
                    &t_ref.trait_decl_ref.skip_binder.generics,
                );
                self.found_use_fn_hinted(id, &gargs_key, (fn_ref.id, fn_ref.generics))
            }
            // These can't be monomorphized, since they're builtins
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(..)) => {}
        }
    }
}

// Akin to UsageVisitor, but substitutes all uses of generics with the monomorphized versions
// This is a two-step process, because we can't mutate the translation context with new definitions
// while also mutating the existing definitions.
#[derive(Visitor)]
struct SubstVisitor<'a> {
    data: &'a PassData,
}
impl SubstVisitor<'_> {
    fn subst_use_ty(&mut self, id: &mut TypeDeclId, gargs: &mut GenericArgs) {
        trace!("Mono: Subst use: {:?} / {:?}", id, gargs);
        let key = (AnyTransId::Type(*id), gargs.clone());
        let subst = self.data.items.get(&key);
        let Some(OptionHint::Some(AnyTransId::Type(subst_id))) = subst else {
            panic!("Substitution missing for {:?}", key);
        };
        *id = *subst_id;
        *gargs = GenericArgs::empty(GenericsSource::Builtin);
    }
    fn subst_use_fun(&mut self, id: &mut FunDeclId, gargs: &mut GenericArgs) {
        trace!("Mono: Subst use: {:?} / {:?}", id, gargs);
        let key = (AnyTransId::Fun(*id), gargs.clone());
        let subst = self.data.items.get(&key);
        let Some(OptionHint::Some(AnyTransId::Fun(subst_id))) = subst else {
            panic!("Substitution missing for {:?}", key);
        };
        *id = *subst_id;
        *gargs = GenericArgs::empty(GenericsSource::Builtin);
    }
}

impl VisitAstMut for SubstVisitor<'_> {
    fn exit_ullbc_statement(&mut self, stt: &mut Statement) {
        match &mut stt.content {
            RawStatement::Assign(_, Rvalue::Discriminant(Place { ty, .. }, id)) => {
                match ty.as_adt() {
                    Some((TypeId::Adt(new_enum_id), _)) => {
                        // Small trick; the discriminant doesn't carry the information on the
                        // generics of the enum, since it's irrelevant, but we need it to do
                        // the substitution, so we look at the type of the place we read from
                        println!(
                            "Substituted in discriminant: {:?} -> {:?}",
                            *id, new_enum_id
                        );
                        *id = new_enum_id;
                    }
                    _ => {}
                }
                ()
            }
            _ => (),
        }
    }

    fn enter_aggregate_kind(&mut self, kind: &mut AggregateKind) {
        match kind {
            AggregateKind::Adt(TypeId::Adt(id), _, _, gargs) => self.subst_use_ty(id, gargs),
            AggregateKind::Closure(fun_id, gargs) => self.subst_use_fun(fun_id, gargs),
            _ => {}
        }
    }

    fn enter_ty_kind(&mut self, kind: &mut TyKind) {
        match kind {
            TyKind::Adt(TypeId::Adt(id), gargs) => {
                self.subst_use_ty(id, gargs);
            }
            _ => {}
        }
    }

    fn enter_fn_ptr(&mut self, fn_ptr: &mut FnPtr) {
        match &mut fn_ptr.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id)) => {
                self.subst_use_fun(fun_id, &mut fn_ptr.generics)
            }
            FunIdOrTraitMethodRef::Trait(t_ref, _, fun_id) => {
                let mut gargs_key = fn_ptr.generics.clone().concat(
                    GenericsSource::Builtin,
                    &t_ref.trait_decl_ref.skip_binder.generics,
                );
                self.subst_use_fun(fun_id, &mut gargs_key);
                fn_ptr.generics = gargs_key;
            }
            // These can't be monomorphized, since they're builtins
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(..)) => {}
        }
    }

    fn exit_place(&mut self, place: &mut Place) {
        match &mut place.kind {
            PlaceKind::Projection(inner, ProjectionElem::Field(FieldProjKind::Adt(id, _), _)) => {
                // Trick, we don't know the generics but the projected place does, so
                // we substitute it there, then update our current id.
                let (inner_id, _) = inner.ty.as_adt().unwrap();
                *id = *inner_id.as_adt().unwrap()
            }
            _ => {}
        }
    }
}

#[derive(Visitor)]
#[allow(dead_code)]
struct MissingIndexChecker<'a> {
    krate: &'a TranslatedCrate,
    current_item: Option<AnyTransItem<'a>>,
}
impl VisitAst for MissingIndexChecker<'_> {
    fn enter_fun_decl_id(&mut self, id: &FunDeclId) {
        if self.krate.fun_decls.get(*id).is_none() {
            panic!(
                "Missing function declaration for id: {:?}, in {:?}",
                id, self.current_item
            );
        }
    }

    fn enter_trait_impl_id(&mut self, id: &TraitImplId) {
        if self.krate.trait_impls.get(*id).is_none() {
            panic!(
                "Missing trait implementation for id: {:?}, in {:?}",
                id, self.current_item
            );
        }
    }

    fn enter_trait_decl_id(&mut self, id: &TraitDeclId) {
        if self.krate.trait_decls.get(*id).is_none() {
            panic!(
                "Missing trait declaration for id: {:?}, in {:?}",
                id, self.current_item
            );
        }
    }

    fn enter_type_decl_id(&mut self, id: &TypeDeclId) {
        if self.krate.type_decls.get(*id).is_none() {
            panic!(
                "Missing type declaration for id: {:?}, in {:?}",
                id, self.current_item
            );
        }
    }
}

fn find_uses(data: &mut PassData, krate: &TranslatedCrate, item: &AnyTransItem) {
    let mut visitor = UsageVisitor { data, krate };
    item.drive(&mut visitor);
}

fn subst_uses<T: AstVisitable + Debug>(data: &PassData, item: &mut T) {
    let mut visitor = SubstVisitor { data };
    item.drive_mut(&mut visitor);
}

fn check_missing_indices(krate: &TranslatedCrate) {
    let mut visitor = MissingIndexChecker {
        krate,
        current_item: None,
    };
    for item in krate.all_items() {
        visitor.current_item = Some(item);
        item.drive(&mut visitor);
    }
}

fn path_for_generics(gargs: &GenericArgs) -> PathElem {
    PathElem::Ident(gargs.to_string(), Disambiguator::ZERO)
}

impl GenericArgs {
    fn is_empty_ignoring_regions(&self) -> bool {
        let GenericArgs {
            types,
            const_generics,
            trait_refs,
            regions: _,
            target: _,
        } = self;
        let len = types.elem_count() + const_generics.elem_count() + trait_refs.elem_count();
        len == 0
    }
}

impl GenericParams {
    fn is_empty_ignoring_regions(&self) -> bool {
        let GenericParams {
            regions: _,
            types,
            const_generics,
            trait_clauses,
            regions_outlive: _,
            types_outlive,
            trait_type_constraints,
        } = self;
        let len = types.elem_count()
            + const_generics.elem_count()
            + trait_clauses.elem_count()
            + trait_type_constraints.elem_count()
            + types_outlive.len();
        len == 0
    }
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
                    data.items
                        .insert((id, empty_gargs.clone()), OptionHint::Some(id));
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
            find_uses(&mut data, &ctx.translated, &item);

            // 2. Iterate through all newly discovered uses
            for ((id, gargs), mono) in data.items.iter_mut() {
                if mono.is_some() {
                    continue;
                }

                // a. Monomorphize the items if they're polymorphic, add them to the worklist
                let new_mono = if gargs.is_empty_ignoring_regions() {
                    *id
                } else {
                    match id {
                        AnyTransId::Fun(_) => {
                            let key_pair = (id.clone(), gargs.clone());
                            let (AnyTransId::Fun(fun_id), gargs) = mono.hint_or(&key_pair) else {
                                panic!("Unexpected ID type in hint_or");
                            };
                            let fun = ctx.translated.fun_decls.get(*fun_id).unwrap();
                            let mut fun_sub = fun.clone().substitute(gargs);
                            fun_sub.signature.generics = GenericParams::empty();

                            let fun_id_sub = ctx.translated.fun_decls.reserve_slot();
                            fun_sub.def_id = fun_id_sub;
                            ctx.translated.fun_decls.set_slot(fun_id_sub, fun_sub);

                            AnyTransId::Fun(fun_id_sub)
                        }
                        AnyTransId::Type(typ_id) => {
                            let typ = ctx.translated.type_decls.get(*typ_id).unwrap();
                            let mut typ_sub = typ.clone().substitute(gargs);
                            typ_sub.generics = GenericParams::empty();
                            // typ_sub.item_meta.name.name.push(path_for_generics(gargs));

                            let typ_id_sub = ctx.translated.type_decls.reserve_slot();
                            typ_sub.def_id = typ_id_sub;
                            ctx.translated.type_decls.set_slot(typ_id_sub, typ_sub);

                            AnyTransId::Type(typ_id_sub)
                        }
                        _ => todo!("Unhandled monomorphization target ID {:?}", id),
                    }
                };
                trace!(
                    "Mono: Monomorphized {:?} with {:?} to {:?}",
                    id,
                    gargs,
                    new_mono
                );
                if id != &new_mono {
                    trace!(" - From {:?}", ctx.translated.get_item(id.clone()));
                    trace!(" - To {:?}", ctx.translated.get_item(new_mono.clone()));
                }
                *mono = OptionHint::Some(new_mono);
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
            .retain(|f| f.signature.generics.is_empty_ignoring_regions());
        ctx.translated
            .type_decls
            .retain(|t| t.generics.is_empty_ignoring_regions());
        // ctx.translated.trait_impls.retain(|t| t.generics.is_empty());

        // TODO: Currently we don't update all TraitImpls/TraitDecls with the monomorphized versions
        //       and removing the polymorphic ones, so this fails.
        // Finally, ensure we didn't leave any IDs un-replaced
        // check_missing_indices(&ctx.translated);
    }

    fn name(&self) -> &str {
        "monomorphize"
    }
}
