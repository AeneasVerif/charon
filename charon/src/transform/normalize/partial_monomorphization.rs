//! This module implements partial monomorphization, which allows specializing generic items on
//! some specific instanciation patterns. This is used by Aeneas to avoid nested mutable borrows:
//! we transform `Iter<'a, &'b mut T>` to `{Iter::<_, &mut U>}<'a, 'b, T>`, where
//! ```ignore
//! struct {Iter::<'a, &'b mut U>}<'a, 'b, U> {
//!   // the field of `Iter` but instantiated with `T -> &'b mut U`.
//! }
//! ```
//!
//! Note: We may need to partial-mono the same item multiple times: `Foo::<&mut A, B>`, `Foo::<A,
//! &mut B>`. Note also that partial-mono is infectious: `Foo<Bar<&mut A>>` generates `Bar::<&mut
//! A>` then `Foo::<Bar::<&mut A>>``.
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::mem;

use derive_generic_visitor::Visitor;
use index_vec::Idx;
use indexmap::IndexMap;

use crate::ast::types_utils::TyVisitable;
use crate::ast::visitor::{VisitWithBinderDepth, VisitorWithBinderDepth};
use crate::transform::ctx::TransformPass;
use crate::{transform::TransformCtx, ullbc_ast::*};

type MutabilityShape = Binder<GenericArgs>;

/// See the docs of `MutabilityShapeBuilder::compute_shape`.
#[derive(Visitor)]
struct MutabilityShapeBuilder<'pm, 'ctx> {
    pm: &'pm PartialMonomorphizer<'ctx>,
    /// The parameters that will constitute the final binder.
    params: GenericParams,
    /// The arguments to pass to the final binder to recover the input arguments.
    extracted: GenericArgs,
    /// Current depth under which we're visiting.
    binder_depth: DeBruijnId,
}

impl<'pm, 'ctx> MutabilityShapeBuilder<'pm, 'ctx> {
    /// Compute the mutability "shape" of a set of generic arguments by factoring out the minimal
    /// amount of information that still allows reconstructing the original arguments while keeping the
    /// "shape arguments" free of mutable borrows.
    ///
    /// For example, for input:
    ///   <u32, &'a mut &'b A, Option::<&'a mut bool>>
    /// we want to build:
    ///   binder<'a, 'b, A, B, C> <A, &'a mut B, Option::<&'b mut C>>
    /// from which we can recover the original arguments by instantiating it with:
    ///   <'a, 'a, u32, &'b A, bool>
    ///
    /// Formally, given `let (shape, shape_args) = get_mutability_shape(args);`, we have the following:
    /// - `shape.substitute(shape_args) == args`;
    /// - `shape_args` contains no infected types;
    /// - `shape` is as shallow as possible (i.e. takes just enough to get all the infected types
    ///     and not more).
    ///
    /// Note: the input arguments are assumed to have been already partially monomorphized, in the
    /// sense that we won't recurse inside ADT args because we assume any ADT applied to infected
    /// args to have been replaced with a fresh infected ADT.
    fn compute_shape(
        pm: &'pm PartialMonomorphizer<'ctx>,
        target_params: &GenericParams,
        args: &GenericArgs,
    ) -> (MutabilityShape, GenericArgs) {
        // We start with the implicit parameters from the original item. We'll need to substitute
        // them once we've figured out the mapping of explicit parameters, but we'll also be adding
        // new trait clauses potentially so we can't leave the vector empty (the ids would be
        // wrong).
        let mut shape_contents = args.clone();
        let mut builder = Self {
            pm,
            params: GenericParams {
                regions: Vector::new(),
                types: Vector::new(),
                const_generics: Vector::new(),
                ..target_params.clone()
            },
            extracted: GenericArgs {
                regions: Vector::new(),
                types: Vector::new(),
                const_generics: Vector::new(),
                trait_refs: mem::take(&mut shape_contents.trait_refs),
            },
            binder_depth: DeBruijnId::zero(),
        };

        // Traverse the generics and replace any non-infected type, region or const generic with a
        // fresh variable.
        let _ = VisitWithBinderDepth::new(&mut builder).visit(&mut shape_contents);

        let shape_params = {
            let mut shape_params = builder.params;
            // Now the explicit params in `shape_params` are correct, and the implicit params are a mix
            // of the old params and new trait clauses. The old params may refer to the old explicit
            // params which is wrong and must be fixed up.
            shape_params.trait_clauses = shape_params.trait_clauses.map(|clause| {
                if clause.clause_id.index() < target_params.trait_clauses.slot_count() {
                    clause.substitute_explicits(&shape_contents)
                } else {
                    clause
                }
            });
            shape_params.trait_type_constraints =
                shape_params.trait_type_constraints.map_indexed(|i, x| {
                    if i.index() < target_params.trait_type_constraints.slot_count() {
                        x.substitute_explicits(&shape_contents)
                    } else {
                        x
                    }
                });
            shape_params.regions_outlive = shape_params
                .regions_outlive
                .into_iter()
                .enumerate()
                .map(|(i, x)| {
                    if i < target_params.regions_outlive.len() {
                        x.substitute_explicits(&shape_contents)
                    } else {
                        x
                    }
                })
                .collect();
            shape_params.types_outlive = shape_params
                .types_outlive
                .into_iter()
                .enumerate()
                .map(|(i, x)| {
                    if i < target_params.types_outlive.len() {
                        x.substitute_explicits(&shape_contents)
                    } else {
                        x
                    }
                })
                .collect();
            shape_params
        };

        // The first few trait params correspond to the original item clauses so we can pass them
        // unmodified.
        shape_contents.trait_refs = shape_params.identity_args().trait_refs;
        shape_contents
            .trait_refs
            .truncate(target_params.trait_clauses.slot_count());

        let shape_args = builder.extracted;
        let shape = Binder::new(BinderKind::Other, shape_params, shape_contents);
        (shape, shape_args)
    }

    /// Replace this value with a fresh variable, and record that we did so.
    fn replace_with_fresh_var<Id, Param, Arg>(
        &mut self,
        val: &mut Arg,
        mk_param: impl FnOnce(Id) -> Param,
        mk_value: impl FnOnce(DeBruijnVar<Id>) -> Arg,
    ) where
        Id: Idx + Display,
        Arg: TyVisitable + Clone,
        GenericParams: HasVectorOf<Id, Output = Param>,
        GenericArgs: HasVectorOf<Id, Output = Arg>,
    {
        let Some(shifted_val) = val.clone().move_from_under_binders(self.binder_depth) else {
            // Give up on this value.
            return;
        };
        // Record the mapping in the output `GenericArgs`.
        self.extracted.get_vector_mut().push(shifted_val);
        // Put a fresh param in place of `val`.
        let id = self.params.get_vector_mut().push_with(mk_param);
        *val = mk_value(DeBruijnVar::bound(self.binder_depth, id));
    }
}

impl<'pm, 'ctx> VisitorWithBinderDepth for MutabilityShapeBuilder<'pm, 'ctx> {
    fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
        &mut self.binder_depth
    }
}

impl<'pm, 'ctx> VisitAstMut for MutabilityShapeBuilder<'pm, 'ctx> {
    fn visit<'a, T: AstVisitable>(&'a mut self, x: &mut T) -> ControlFlow<Self::Break> {
        VisitWithBinderDepth::new(self).visit(x)
    }

    fn enter_ty(&mut self, ty: &mut Ty) {
        if !self.pm.is_infected(ty) {
            self.replace_with_fresh_var(
                ty,
                |id| TypeParam::new(id, format!("T{id}")),
                |v| v.into(),
            );
        }
    }
    fn exit_ty_kind(&mut self, kind: &mut TyKind) {
        if let TyKind::Adt(TypeDeclRef {
            id: TypeId::Adt(id),
            generics,
        }) = kind
        {
            // Since the type was not replaced with a type var, it's an infected type. We've
            // traversed it so we have its final explicit arguments. Now we need to satisfy its
            // predicates. For that we add all its predicates to the new item, and pass those new
            // trait clauses to it.
            let Some(target_params) = self.pm.generic_params.get(&(*id).into()) else {
                return;
            };
            let Some(shifted_generics) =
                generics.clone().move_from_under_binders(self.binder_depth)
            else {
                // Give up on this value.
                return;
            };

            // Add the target predicates (properly substituted) to the new item params.
            let num_clauses_before_merge = self.params.trait_clauses.slot_count();
            self.params.merge_predicates_from(
                target_params
                    .clone()
                    .substitute_explicits(&shifted_generics),
            );

            // Record the trait arguments in the output `GenericArgs`.
            self.extracted
                .trait_refs
                .extend(shifted_generics.trait_refs);

            // Replace each trait ref with a clause var.
            for (target_clause_id, tref) in generics.trait_refs.iter_mut_indexed() {
                let clause_id = target_clause_id + num_clauses_before_merge;
                *tref =
                    self.params.trait_clauses[clause_id].identity_tref_at_depth(self.binder_depth);
            }
        }
    }
    fn enter_region(&mut self, r: &mut Region) {
        self.replace_with_fresh_var(r, |id| RegionParam::new(id, None), |v| v.into());
    }
    // TODO: we're missing type info for this
    // fn enter_const_generic(&mut self, cg: &mut ConstGeneric) {
    //     self.replace_with_fresh_var(cg, |id| {
    //         ConstGenericParam::new(id, format!("N{id}"), cg.ty().clone())
    //     });
    // }
    fn visit_trait_ref(&mut self, _tref: &mut TraitRef) -> ControlFlow<Self::Break> {
        // We don't touch trait refs or we'd risk adding duplicated extra params. They'll get fixed
        // up afterwards.
        ControlFlow::Continue(())
    }
}

#[derive(Visitor)]
struct PartialMonomorphizer<'a> {
    ctx: &'a mut TransformCtx,
    span: Span,
    /// Types that contain mutable references.
    infected_types: HashSet<TypeDeclId>,
    /// Map of generic params for each item. We can't use `ctx.translated` because while iterating
    /// over items the current item isn't available anymore, which would break recursive types.
    /// This also makes it possible to record the generics of our to-be-added items without adding
    /// them.
    generic_params: HashMap<ItemId, GenericParams>,
    /// Map of partial monomorphizations. The source item applied with the generic params gives the
    /// target item. The resulting partially-monomorphized item will have the binder params as
    /// generic params.
    partial_mono_shapes: IndexMap<(TypeDeclId, MutabilityShape), TypeDeclId>,
    /// Reverse of `partial_mono_shapes`.
    reverse_shape_map: HashMap<TypeDeclId, (TypeDeclId, MutabilityShape)>,
    // Record which entries in `partial_mono_shapes` have been created already.
    instantiated_items: usize,
}

impl<'a> PartialMonomorphizer<'a> {
    pub fn new(ctx: &'a mut TransformCtx) -> Self {
        // Compute the types that contain `&mut` (even indirectly).
        // TODO: this needs a fixpoint. Might have to build a graph and do reachability.
        let infected_types = ctx
            .translated
            .type_decls
            .iter_indexed()
            .filter(|(_, decl)| {
                let mut any_ref_mut = false;
                decl.dyn_visit(|x: &Ty| {
                    if matches!(x.kind(), TyKind::Ref(_, _, RefKind::Mut)) {
                        any_ref_mut = true;
                    }
                });
                any_ref_mut
            })
            .map(|(id, _)| id)
            .collect();

        // Record the generic params of all items.
        let generic_params: HashMap<ItemId, GenericParams> = ctx
            .translated
            .all_items()
            .map(|item| (item.id(), item.generic_params().clone()))
            .collect();
        PartialMonomorphizer {
            ctx,
            span: Span::dummy(),
            infected_types,
            generic_params,
            partial_mono_shapes: IndexMap::default(),
            reverse_shape_map: Default::default(),
            // TODO: use a single processing queue instead of this index
            instantiated_items: 0,
        }
    }

    fn get_mutability_shape(
        &self,
        target: impl Into<ItemId>,
        args: &GenericArgs,
    ) -> Option<(MutabilityShape, GenericArgs)> {
        let item = self.generic_params.get(&target.into())?;
        Some(MutabilityShapeBuilder::compute_shape(self, item, args))
    }

    /// Whether this type is or contains a `&mut`. This assumes that we've already visited this
    /// type and partially monomorphized any ADT references.
    fn is_infected(&self, ty: &Ty) -> bool {
        match ty.kind() {
            TyKind::Ref(_, _, RefKind::Mut) => true,
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => self.is_infected(ty),
            TyKind::Adt(tref) => match &tref.id {
                // We don't need to check the ADT generics as we've already visited this.
                TypeId::Adt(id) => self.infected_types.contains(id),
                TypeId::Tuple | TypeId::Builtin(..) => {
                    tref.generics.types.iter().any(|ty| self.is_infected(ty))
                }
            },
            TyKind::DynTrait(_dyn_predicate) => false, // TODO
            TyKind::FnDef(_region_binder) => false,    // TODO
            TyKind::TypeVar(..)
            | TyKind::Literal(..)
            | TyKind::Never
            | TyKind::TraitType(..)
            | TyKind::FnPtr(..)
            | TyKind::PtrMetadata(..)
            | TyKind::Error(_) => false,
        }
    }

    /// Traverse the item, replacing any type instantiations we don't want with references to
    /// soon-to-be-created partially-monomorphized types. This does not access the items in
    /// `self.translated`, which may be missing since we took `item` out for processing.
    pub fn process_item(&mut self, item: &mut ItemRefMut<'_>) {
        let _ = item.drive_mut(self);
    }

    /// In `process_item` we accumulated a list of items that must be partially instantiated. This
    /// creates one of these required items by duplicating and substituting the existing one.
    ///
    /// This accesses the items in `self.translated`, which must therefore all be there.
    /// That's why items are created outside of `process_item`.
    pub fn create_pending_instantiation(&mut self) -> Option<ItemId> {
        // Return `None` if `self.instantiated_items` is already at the end of the list.
        let (&(orig_id, ref shape), &new_id) = self
            .partial_mono_shapes
            .get_index(self.instantiated_items)?;
        self.instantiated_items += 1;

        let mut decl = self
            .ctx
            .translated
            .type_decls
            .get(orig_id)?
            .clone()
            .substitute(&shape.skip_binder);
        decl.def_id = new_id;
        decl.generics = shape.params.clone();
        decl.item_meta.name = decl.item_meta.name.instantiate(shape.clone());

        self.ctx
            .translated
            .item_names
            .insert(new_id.into(), decl.item_meta.name.clone());
        self.ctx.translated.type_decls.set_slot(new_id, decl);

        Some(new_id.into())
    }
}

impl VisitorWithSpan for PartialMonomorphizer<'_> {
    fn current_span(&mut self) -> &mut Span {
        &mut self.span
    }
}
impl VisitAstMut for PartialMonomorphizer<'_> {
    fn visit<'a, T: AstVisitable>(&'a mut self, x: &mut T) -> ControlFlow<Self::Break> {
        // Track a useful enclosing span, for error messages.
        VisitWithSpan::new(self).visit(x)
    }

    // TODO: also partial mono `FnPtr`s, tdecls, timpls, basically every item ref.
    // TODO: any `Trait::method<&mut A>` requires monomorphizing all the instances of that method
    // just in case :>>>
    fn exit_type_decl_ref(&mut self, x: &mut TypeDeclRef) {
        let TypeId::Adt(id) = x.id else {
            return;
        };

        if !x.generics.types.iter().any(|ty| self.is_infected(ty)) {
            return;
        }

        // If the type is already an instantiation, transform this reference into a reference to
        // the original type so we don't instantiate the instantiation.
        let (id, generics) = if let Some((base_id, shape)) = self.reverse_shape_map.get(&id) {
            (*base_id, &shape.clone().apply(&x.generics))
        } else {
            (id, &*x.generics)
        };

        // Split the args between the infected part and the non-infected part.
        let Some((shape, shape_args)) = self.get_mutability_shape(id, generics) else {
            return;
        };

        // Create a new type id.
        let new_params = shape.params.clone();
        let key: (TypeDeclId, MutabilityShape) = (id, shape);
        let mut_shape_id = *self
            .partial_mono_shapes
            .entry(key.clone())
            .or_insert_with(|| {
                let new_id = self.ctx.translated.type_decls.reserve_slot();
                self.infected_types.insert(new_id);
                self.generic_params.insert(new_id.into(), new_params);
                self.reverse_shape_map.insert(new_id, key);
                new_id
            });

        *x = TypeDeclRef {
            id: TypeId::Adt(mut_shape_id),
            generics: Box::new(shape_args),
        }
    }
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        if !ctx.options.monomorphize_mut {
            return;
        }
        // TODO: test name matcher, also with methods
        let mut visitor = PartialMonomorphizer::new(ctx);
        // Items to process. We only need to process a given item once.
        let mut to_process: VecDeque<_> = visitor.ctx.translated.all_ids().collect();
        while let Some(id) = to_process.pop_front() {
            // Take the item out so we can modify it. Warning: don't look up other items in the
            // meantime as this would break in recursive cases.
            let Some(mut decl) = visitor.ctx.translated.remove_item(id) else {
                continue;
            };
            // Visit the item, replacing type instantiations with references to soon-to-be-created
            // partially-monomorphized types.
            visitor.process_item(&mut decl.as_mut());
            // Put the item back.
            visitor.ctx.translated.set_item_slot(id, decl);

            // Add the new items.
            while let Some(new_id) = visitor.create_pending_instantiation() {
                // Enqueue the item as this instantiation may trigger more instantiations.
                to_process.push_back(new_id);
            }
        }
    }
}
