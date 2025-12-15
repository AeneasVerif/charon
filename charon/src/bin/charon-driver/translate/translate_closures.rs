//! In rust, closures behave like ADTs that implement the FnOnce/FnMut/Fn traits automatically.
//!
//! Here we convert closures to a struct containing the closure's state (upvars), along with
//! matching trait impls and fun decls (e.g. a Fn closure will have a trait impl for Fn, FnMut and
//! FnOnce, along with 3 matching method implementations for call, call_mut and call_once).
//!
//! For example, given the following Rust code:
//! ```rust
//! pub fn test_closure_capture<T: Clone>() {
//!     let mut v = vec![];
//!     let mut add = |x: &u32| v.push(*x);
//!     add(&0);
//!     add(&1);
//! }
//! ```
//!
//! We generate the equivalent desugared code:
//! ```rust
//! struct {test_closure_capture::closure#0}<'a, T: Clone> (&'a mut Vec<u32>);
//!
//! // The 'a comes from captured variables, the 'b comes from the closure higher-kinded signature.
//! impl<'a, 'b, T: Clone> FnMut<(&'b u32,)> for {test_closure_capture::closure#0}<'a, T> {
//!     fn call_mut<'c>(&'c mut self, arg: (&'b u32,)) {
//!         self.0.push(*arg.0);
//!     }
//! }
//!
//! impl<'a, 'b, T: Clone> FnOnce<(&'b u32,)> for {test_closure_capture::closure#0}<'a, T> {
//!     type Output = ();
//!     ...
//! }
//!
//! pub fn test_closure_capture<T: Clone>() {
//!     let mut v = vec![];
//!     let mut add = {test_closure_capture::closure#0} (&mut v);
//!     state.call_mut(&0);
//!     state.call_mut(&1);
//! }
//! ```

use std::mem;

use super::translate_crate::TransItemSourceKind;
use super::translate_ctx::*;
use charon_lib::ast::ullbc_ast_utils::BodyBuilder;
use charon_lib::ast::*;
use charon_lib::ids::IndexVec;
use charon_lib::ullbc_ast::*;
use itertools::Itertools;

pub fn translate_closure_kind(kind: &hax::ClosureKind) -> ClosureKind {
    match kind {
        hax::ClosureKind::Fn => ClosureKind::Fn,
        hax::ClosureKind::FnMut => ClosureKind::FnMut,
        hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
    }
}

/// References to closure items are subtle because there are three sources of lifetimes on top of
/// the normal generics: the by-ref upvars, the higher-kindedness of the closure itself, and the
/// late-bound generics of the `call`/`call_mut` methods. One must be careful to choose the right
/// method from these.
impl ItemTransCtx<'_, '_> {
    /// If we're translating a closure-related item, get the upvar regions in scope; otherwise get
    /// erased regions.
    fn by_ref_upvar_regions(&self, closure: &hax::ClosureArgs) -> IndexMap<RegionId, Region> {
        if self.item_src.def_id() == &closure.item.def_id {
            // We have fresh upvar regions in scope.
            self.outermost_binder()
                .by_ref_upvar_regions
                .iter()
                .map(|r| Region::Var(DeBruijnVar::bound(self.binding_levels.depth(), *r)))
                .collect()
        } else {
            closure
                .iter_upvar_borrows()
                .map(|_| Region::Erased)
                .collect()
        }
    }

    /// If we're translating a closure-related item, get the late regions in scope; otherwise get
    /// erased regions.
    fn closure_late_regions(&self, closure: &hax::ClosureArgs) -> IndexMap<RegionId, Region> {
        if self.item_src.def_id() == &closure.item.def_id {
            // We have fresh late regions in scope.
            self.outermost_binder()
                .bound_region_vars
                .iter()
                .map(|r| Region::Var(DeBruijnVar::bound(self.binding_levels.depth(), *r)))
                .collect()
        } else {
            closure
                .fn_sig
                .bound_vars
                .iter()
                .map(|_| Region::Erased)
                .collect()
        }
    }

    /// If we're translating a closure-related item, get the method regions in scope; otherwise get
    /// erased regions.
    fn closure_method_regions(
        &self,
        closure: &hax::ClosureArgs,
        target_kind: ClosureKind,
    ) -> IndexMap<RegionId, Region> {
        if self.item_src.def_id() == &closure.item.def_id {
            // We have fresh method regions in scope.
            self.outermost_binder()
                .closure_call_method_region
                .iter()
                .map(|r| Region::Var(DeBruijnVar::bound(self.binding_levels.depth(), *r)))
                .collect()
        } else {
            match target_kind {
                ClosureKind::FnOnce => IndexMap::new(),
                ClosureKind::FnMut | ClosureKind::Fn => [Region::Erased].into_iter().collect(),
            }
        }
    }

    /// Translate a reference to a closure item that takes only upvar lifetimes. The resulting type
    /// needs lifetime arguments for the upvars (captured variables). If you want to instantiate
    /// this binder, use the lifetimes from `self.by_ref_upvar_regions`.
    fn translate_closure_bound_ref_with_upvars(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
        kind: TransItemSourceKind,
    ) -> Result<RegionBinder<DeclRef<ItemId>>, Error> {
        // We add lifetime args for each borrowing upvar, gotta supply them here.
        let upvar_binder = hax::Binder {
            value: (),
            bound_vars: closure
                .iter_upvar_borrows()
                .map(|_| hax::BoundVariableKind::Region(hax::BoundRegionKind::Anon))
                .collect(),
        };
        let mut tref: DeclRef<ItemId> = self.translate_item(span, &closure.item, kind)?;
        // Hack to recover some lifetimes that are erased in `ClosureArgs`.
        if self.item_src.def_id() == &closure.item.def_id && !self.monomorphize() {
            let depth = self.binding_levels.depth();
            // At this point `tref` contains exactly the generic arguments of the enclosing item.
            // Every closure item gets at least these as generics, so we can simply reuse the
            // in-scope generics.
            for (rid, r) in tref.generics.regions.iter_mut_indexed() {
                *r = Region::Var(DeBruijnVar::bound(depth, rid));
            }
        }
        self.translate_region_binder(span, &upvar_binder, |ctx, _| {
            let mut tref = tref.move_under_binder();
            tref.generics.regions.extend(
                ctx.innermost_binder()
                    .params
                    .identity_args()
                    .regions
                    .into_iter(),
            );
            Ok(tref)
        })
    }

    /// Translate a reference to a closure item that takes upvar lifetimes and late-bound
    /// lifetimes. The binder binds the late-bound lifetimes of the closure itself, if it is
    /// higher-kinded. If you want to instantiate the binder, use the lifetimes from
    /// `self.closure_late_regions`.
    fn translate_closure_bound_ref_with_late_bound(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
        kind: TransItemSourceKind,
    ) -> Result<RegionBinder<DeclRef<ItemId>>, Error> {
        let inner_ref = self
            .translate_closure_bound_ref_with_upvars(span, closure, kind)?
            .apply(self.by_ref_upvar_regions(closure));
        self.translate_region_binder(span, &closure.fn_sig, |ctx, _| {
            let mut inner_ref = inner_ref.move_under_binder();
            inner_ref.generics.regions.extend(
                ctx.innermost_binder()
                    .params
                    .identity_args()
                    .regions
                    .into_iter(),
            );
            Ok(inner_ref)
        })
    }
}

impl ItemTransCtx<'_, '_> {
    /// Translate a reference to the closure ADT.
    pub fn translate_closure_type_ref(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
    ) -> Result<TypeDeclRef, Error> {
        let kind = TransItemSourceKind::Type;
        let bound_dref = self.translate_closure_bound_ref_with_upvars(span, closure, kind)?;
        let dref = bound_dref.apply(self.by_ref_upvar_regions(closure));
        Ok(dref.try_into().unwrap())
    }

    /// For stateless closures, translate a function reference to the top-level function that
    /// executes the closure code without taking the state as parameter.If you want to instantiate
    /// the binder, use the lifetimes from `self.closure_late_regions`.
    pub fn translate_stateless_closure_as_fn_ref(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
    ) -> Result<RegionBinder<FunDeclRef>, Error> {
        let kind = TransItemSourceKind::ClosureAsFnCast;
        let bound_dref = self.translate_closure_bound_ref_with_late_bound(span, closure, kind)?;
        Ok(bound_dref.map(|dref| dref.try_into().unwrap()))
    }

    /// Translate a reference to the chosen closure impl. The resulting value needs lifetime
    /// arguments for late-bound lifetimes. If you want to instantiate the binder, use the
    /// lifetimes from `self.closure_late_regions`.
    pub fn translate_closure_bound_impl_ref(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
        target_kind: ClosureKind,
    ) -> Result<RegionBinder<TraitImplRef>, Error> {
        let kind = TransItemSourceKind::TraitImpl(TraitImplSource::Closure(target_kind));
        let bound_dref = self.translate_closure_bound_ref_with_late_bound(span, closure, kind)?;
        Ok(bound_dref.map(|dref| dref.try_into().unwrap()))
    }

    /// Translate a reference to the chosen closure impl.
    pub fn translate_closure_impl_ref(
        &mut self,
        span: Span,
        closure: &hax::ClosureArgs,
        target_kind: ClosureKind,
    ) -> Result<TraitImplRef, Error> {
        Ok(self
            .translate_closure_bound_impl_ref(span, closure, target_kind)?
            .apply(self.closure_late_regions(closure)))
    }

    pub fn translate_closure_info(
        &mut self,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<ClosureInfo, Error> {
        use ClosureKind::*;
        let kind = translate_closure_kind(&args.kind);

        let fn_once_impl = self.translate_closure_bound_impl_ref(span, args, FnOnce)?;
        let fn_mut_impl = if matches!(kind, FnMut | Fn) {
            Some(self.translate_closure_bound_impl_ref(span, args, FnMut)?)
        } else {
            None
        };
        let fn_impl = if matches!(kind, Fn) {
            Some(self.translate_closure_bound_impl_ref(span, args, Fn)?)
        } else {
            None
        };
        let signature = self.translate_poly_fun_sig(span, &args.fn_sig)?;
        Ok(ClosureInfo {
            kind,
            fn_once_impl,
            fn_mut_impl,
            fn_impl,
            signature,
        })
    }

    pub fn get_closure_state_ty(
        &mut self,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<Ty, Error> {
        let tref = self.translate_closure_type_ref(span, args)?;
        Ok(TyKind::Adt(tref).into_ty())
    }

    pub fn translate_closure_adt(
        &mut self,
        _trans_id: TypeDeclId,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<TypeDeclKind, Error> {
        let mut by_ref_upvar_regions = self
            .the_only_binder()
            .by_ref_upvar_regions
            .clone()
            .into_iter();
        let fields: IndexVec<FieldId, Field> = args
            .upvar_tys
            .iter()
            .map(|ty| -> Result<Field, Error> {
                let mut ty = self.translate_ty(span, ty)?;
                // We supply fresh regions for the by-ref upvars.
                if let TyKind::Ref(Region::Erased, deref_ty, kind) = ty.kind() {
                    let region_id = by_ref_upvar_regions.next().unwrap();
                    ty = TyKind::Ref(
                        Region::Var(DeBruijnVar::new_at_zero(region_id)),
                        deref_ty.clone(),
                        *kind,
                    )
                    .into_ty();
                }
                Ok(Field {
                    span,
                    attr_info: AttrInfo::dummy_private(),
                    name: None,
                    ty,
                })
            })
            .try_collect()?;
        Ok(TypeDeclKind::Struct(fields))
    }

    /// Given an item that is a closure, generate the signature of the
    /// `call_once`/`call_mut`/`call` method (depending on `target_kind`).
    fn translate_closure_method_sig(
        &mut self,
        def: &hax::FullDef,
        span: Span,
        args: &hax::ClosureArgs,
        target_kind: ClosureKind,
    ) -> Result<RegionBinder<FunSig>, Error> {
        let signature = &args.fn_sig;
        trace!(
            "signature of closure {:?}:\n{:?}",
            def.def_id(),
            signature.value,
        );

        let mut bound_regions = IndexMap::new();
        let mut fun_sig = self
            .translate_fun_sig(span, signature.hax_skip_binder_ref())?
            .move_under_binder();
        let state_ty = self.get_closure_state_ty(span, args)?.move_under_binder();

        // Depending on the kind of the closure generated, add a reference
        let state_ty = match target_kind {
            ClosureKind::FnOnce => state_ty,
            ClosureKind::Fn | ClosureKind::FnMut => {
                let rid = bound_regions.push_with(|index| RegionParam { index, name: None });
                let r = Region::Var(DeBruijnVar::new_at_zero(rid));
                let mutability = if target_kind == ClosureKind::Fn {
                    RefKind::Shared
                } else {
                    RefKind::Mut
                };
                TyKind::Ref(r, state_ty, mutability).into_ty()
            }
        };

        // The types that the closure takes as input.
        let input_tys: Vec<Ty> = mem::take(&mut fun_sig.inputs);
        // The method takes `self` and the closure inputs as a tuple.
        fun_sig.inputs = vec![state_ty, Ty::mk_tuple(input_tys)];

        Ok(RegionBinder {
            regions: bound_regions,
            skip_binder: fun_sig,
        })
    }

    fn translate_closure_method_body(
        &mut self,
        span: Span,
        def: &hax::FullDef,
        target_kind: ClosureKind,
        args: &hax::ClosureArgs,
        signature: &FunSig,
    ) -> Result<Body, Error> {
        use ClosureKind::*;
        let closure_kind = translate_closure_kind(&args.kind);
        Ok(match (target_kind, closure_kind) {
            (Fn, Fn) | (FnMut, FnMut) | (FnOnce, FnOnce) => {
                // Translate the function's body normally
                let mut body = self.translate_def_body(span, def);
                // The body is translated as if the locals are: ret value, state, arg-1,
                // ..., arg-N, rest...
                // However, there is only one argument with the tupled closure arguments;
                // we must thus shift all locals with index >=2 by 1, and add a new local
                // for the tupled arg, giving us: ret value, state, args, arg-1, ...,
                // arg-N, rest...
                // We then add N statements of the form `locals[N+3] := move locals[2].N`,
                // to destructure the arguments.
                let Body::Unstructured(GExprBody {
                    locals,
                    body: blocks,
                    ..
                }) = &mut body
                else {
                    return Ok(body);
                };

                blocks.dyn_visit_mut(|local: &mut LocalId| {
                    if local.index() >= 2 {
                        *local += 1;
                    }
                });

                let mut old_locals = mem::take(&mut locals.locals).into_iter();
                locals.arg_count = 2;
                locals.locals.push(old_locals.next().unwrap()); // ret
                locals.locals.push(old_locals.next().unwrap()); // state
                let tupled_arg =
                    locals.new_var(Some("tupled_args".to_string()), signature.inputs[1].clone());
                locals.locals.extend(old_locals.map(|mut l| {
                    l.index += 1;
                    l
                }));

                let untupled_args = signature.inputs[1].as_tuple().unwrap();
                let closure_arg_count = untupled_args.elem_count();
                let new_stts = untupled_args.iter().cloned().enumerate().map(|(i, ty)| {
                    let nth_field = tupled_arg.clone().project(
                        ProjectionElem::Field(
                            FieldProjKind::Tuple(closure_arg_count),
                            FieldId::new(i),
                        ),
                        ty,
                    );
                    let local_id = LocalId::new(i + 3);
                    Statement::new(
                        span,
                        StatementKind::Assign(
                            locals.place_for_var(local_id),
                            Rvalue::Use(Operand::Move(nth_field)),
                        ),
                    )
                });
                blocks[BlockId::ZERO].statements.splice(0..0, new_stts);

                body
            }
            // Target translation:
            //
            // fn call_once(state: Self, args: Args) -> Output {
            //   let temp_ref = &[mut] state;
            //   let ret = self.call[_mut](temp, args);
            //   drop state;
            //   return ret;
            // }
            //
            (FnOnce, Fn | FnMut) => {
                // Hax (via rustc) gives us the MIR to do this.
                let hax::FullDefKind::Closure {
                    once_shim: Some(body),
                    ..
                } = &def.kind
                else {
                    panic!("missing shim for closure")
                };
                self.translate_body(span, body, &def.source_text)
            }
            // Target translation:
            //
            // fn call_mut(state: &mut Self, args: Args) -> Output {
            //   let reborrow = &*state;
            //   self.call(reborrow, args)
            // }
            (FnMut, Fn) => {
                let fun_id: FunDeclId = self.register_item(
                    span,
                    def.this(),
                    TransItemSourceKind::ClosureMethod(closure_kind),
                );
                let impl_ref = self.translate_closure_impl_ref(span, args, closure_kind)?;
                // TODO: make a trait call to avoid needing to concatenate things ourselves.
                // TODO: can we ask hax for the trait ref?
                let fn_op = FnOperand::Regular(FnPtr::new(
                    fun_id.into(),
                    impl_ref.generics.concat(&GenericArgs {
                        regions: vec![Region::Erased].into(),
                        ..GenericArgs::empty()
                    }),
                ));

                let mut builder = BodyBuilder::new(span, 2);

                let output = builder.new_var(None, signature.output.clone());
                let state = builder.new_var(Some("state".to_string()), signature.inputs[0].clone());
                let args = builder.new_var(Some("args".to_string()), signature.inputs[1].clone());
                let deref_state = state.deref();
                let reborrow_ty =
                    TyKind::Ref(Region::Erased, deref_state.ty.clone(), RefKind::Shared).into_ty();
                let reborrow = builder.new_var(None, reborrow_ty);

                builder.push_statement(StatementKind::Assign(
                    reborrow.clone(),
                    Rvalue::Ref {
                        place: deref_state,
                        kind: BorrowKind::Shared,
                        // The state must be Sized, hence `()` as ptr-metadata
                        ptr_metadata: Operand::mk_const_unit(),
                    },
                ));

                builder.call(Call {
                    func: fn_op,
                    args: vec![Operand::Move(reborrow), Operand::Move(args)],
                    dest: output,
                });

                Body::Unstructured(builder.build())
            }
            (Fn, FnOnce) | (Fn, FnMut) | (FnMut, FnOnce) => {
                panic!(
                    "Can't make a closure body for a more restrictive kind \
                    than the closure kind"
                )
            }
        })
    }

    /// Given an item that is a closure, generate the `call_once`/`call_mut`/`call` method
    /// (depending on `target_kind`).
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_method(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        target_kind: ClosureKind,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let hax::FullDefKind::Closure {
            args,
            fn_once_impl,
            fn_mut_impl,
            fn_impl,
            ..
        } = &def.kind
        else {
            unreachable!()
        };

        // Hax gives us trait-related information for the impl we're building.
        let vimpl = match target_kind {
            ClosureKind::FnOnce => fn_once_impl,
            ClosureKind::FnMut => fn_mut_impl.as_ref().unwrap(),
            ClosureKind::Fn => fn_impl.as_ref().unwrap(),
        };
        let implemented_trait = self.translate_trait_predicate(span, &vimpl.trait_pred)?;

        let impl_ref = self.translate_closure_impl_ref(span, args, target_kind)?;
        let src = ItemSource::TraitImpl {
            impl_ref,
            trait_ref: implemented_trait,
            item_name: TraitItemName(target_kind.method_name().into()),
            reuses_default: false,
        };

        // Translate the function signature
        let signature = self
            .translate_closure_method_sig(def, span, args, target_kind)?
            .apply(self.closure_method_regions(args, target_kind));

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            self.translate_closure_method_body(span, def, target_kind, args, &signature)?
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature,
            src,
            is_global_initializer: None,
            body,
        })
    }

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_trait_impl(
        mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        target_kind: ClosureKind,
    ) -> Result<TraitImpl, Error> {
        let span = item_meta.span;
        let hax::FullDefKind::Closure {
            fn_once_impl,
            fn_mut_impl,
            fn_impl,
            ..
        } = &def.kind
        else {
            unreachable!()
        };

        // Hax gives us trait-related information for the impl we're building.
        let vimpl = match target_kind {
            ClosureKind::FnOnce => fn_once_impl,
            ClosureKind::FnMut => fn_mut_impl.as_ref().unwrap(),
            ClosureKind::Fn => fn_impl.as_ref().unwrap(),
        };
        let mut timpl = self.translate_virtual_trait_impl(def_id, item_meta, vimpl)?;

        // Construct the `call_*` method reference.
        let call_fn_id = self.register_item(
            span,
            def.this(),
            TransItemSourceKind::ClosureMethod(target_kind),
        );
        let call_fn_name = TraitItemName(target_kind.method_name().into());
        let call_fn_binder = {
            let mut method_params = GenericParams::empty();
            match target_kind {
                ClosureKind::FnOnce => {}
                ClosureKind::FnMut | ClosureKind::Fn => {
                    method_params
                        .regions
                        .push_with(|index| RegionParam { index, name: None });
                }
            };

            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(DeBruijnId::one())
                .concat(&method_params.identity_args_at_depth(DeBruijnId::zero()));
            Binder::new(
                BinderKind::TraitMethod(timpl.impl_trait.id, call_fn_name.clone()),
                method_params,
                FunDeclRef {
                    id: call_fn_id,
                    generics: Box::new(generics),
                },
            )
        };
        timpl.methods.push((call_fn_name, call_fn_binder));

        Ok(timpl)
    }

    /// Given an item that is a non-capturing closure, generate the equivalent function,
    /// by removing the state from the parameters and untupling the arguments.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_stateless_closure_as_fn(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let hax::FullDefKind::Closure { args: closure, .. } = &def.kind else {
            unreachable!()
        };

        trace!("About to translate closure as fn:\n{:?}", def.def_id());

        assert!(
            closure.upvar_tys.is_empty(),
            "Only stateless closures can be translated as functions"
        );

        // Translate the function signature
        let signature = self.translate_fun_sig(span, closure.fn_sig.hax_skip_binder_ref())?;
        let state_ty = self.get_closure_state_ty(span, closure)?;

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            // Target translation:
            //
            // fn call_fn(arg0: Args[0], ..., argN: Args[N]) -> Output {
            //   let closure: Closure = {};
            //   let args = (arg0, ..., argN);
            //   closure.call(args)
            // }
            let fun_id: FunDeclId = self.register_item(
                span,
                def.this(),
                TransItemSourceKind::ClosureMethod(ClosureKind::FnOnce),
            );
            let impl_ref = self.translate_closure_impl_ref(span, closure, ClosureKind::FnOnce)?;
            let fn_op = FnOperand::Regular(FnPtr::new(fun_id.into(), impl_ref.generics.clone()));

            let mut builder = BodyBuilder::new(span, signature.inputs.len());

            let output = builder.new_var(None, signature.output.clone());
            let args: Vec<Place> = signature
                .inputs
                .iter()
                .enumerate()
                .map(|(i, ty)| builder.new_var(Some(format!("arg{}", i + 1)), ty.clone()))
                .collect();
            let args_tupled_ty = Ty::mk_tuple(signature.inputs.clone());
            let args_tupled = builder.new_var(Some("args".to_string()), args_tupled_ty.clone());
            let state = builder.new_var(Some("state".to_string()), state_ty.clone());

            builder.push_statement(StatementKind::Assign(
                args_tupled.clone(),
                Rvalue::Aggregate(
                    AggregateKind::Adt(args_tupled_ty.as_adt().unwrap().clone(), None, None),
                    args.into_iter().map(Operand::Move).collect(),
                ),
            ));

            let state_ty_adt = state_ty.as_adt().unwrap();
            builder.push_statement(StatementKind::Assign(
                state.clone(),
                Rvalue::Aggregate(AggregateKind::Adt(state_ty_adt.clone(), None, None), vec![]),
            ));

            builder.call(Call {
                func: fn_op,
                args: vec![Operand::Move(state), Operand::Move(args_tupled)],
                dest: output,
            });

            Body::Unstructured(builder.build())
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature,
            src: ItemSource::TopLevel,
            is_global_initializer: None,
            body,
        })
    }
}
