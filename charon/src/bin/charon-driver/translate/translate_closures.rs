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

use crate::translate::translate_bodies::BodyTransCtx;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::{Formatter, IntoFormatter};
use charon_lib::ids::Vector;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
use itertools::Itertools;

pub fn translate_closure_kind(kind: &hax::ClosureKind) -> ClosureKind {
    match kind {
        hax::ClosureKind::Fn => ClosureKind::Fn,
        hax::ClosureKind::FnMut => ClosureKind::FnMut,
        hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
    }
}

impl ItemTransCtx<'_, '_> {
    pub fn translate_closure_info(
        &mut self,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<ClosureInfo, Error> {
        let kind = translate_closure_kind(&args.kind);
        let signature = self.translate_region_binder(span, &args.untupled_sig, |ctx, sig| {
            let inputs = sig
                .inputs
                .iter()
                .map(|x| ctx.translate_ty(span, x))
                .try_collect()?;
            let output = ctx.translate_ty(span, &sig.output)?;
            Ok((inputs, output))
        })?;
        Ok(ClosureInfo { kind, signature })
    }

    /// Translate a reference to the closure ADT.
    pub fn translate_closure_type_ref(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        closure: &hax::ClosureArgs,
    ) -> Result<TypeDeclRef, Error> {
        let type_id = self.register_type_decl_id(span, def_id);
        let mut args = self.translate_generic_args(
            span,
            &closure.parent_args,
            &closure.parent_trait_refs,
            None,
            GenericsSource::item(type_id),
        )?;
        // We add lifetime args for each borrowing upvar, gotta supply them here.
        if self.def_id == *def_id {
            args.regions.extend(
                self.the_only_binder()
                    .by_ref_upvar_regions
                    .iter()
                    .map(|r| Region::Var(DeBruijnVar::new_at_zero(*r))),
            );
        } else {
            args.regions.extend(
                closure
                    .upvar_tys
                    .iter()
                    .filter(|ty| {
                        matches!(
                            ty.kind(),
                            hax::TyKind::Ref(
                                hax::Region {
                                    kind: hax::RegionKind::ReErased
                                },
                                ..
                            )
                        )
                    })
                    .map(|_| Region::Erased),
            );
        }

        Ok(TypeDeclRef {
            id: TypeId::Adt(type_id),
            generics: Box::new(args),
        })
    }

    /// Translate a reference to the chosen closure impl.
    pub fn translate_closure_impl_ref(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        closure: &hax::ClosureArgs,
        target_kind: ClosureKind,
    ) -> Result<TraitImplRef, Error> {
        let impl_id = self.register_closure_trait_impl_id(span, def_id, target_kind);
        let adt_ref = self.translate_closure_type_ref(span, def_id, closure)?;
        let mut args = adt_ref.generics.with_target(GenericsSource::item(impl_id));
        // Add the lifetime generics coming from the higher-kindedness of the signature.
        if self.def_id == *def_id {
            args.regions.extend(
                self.the_only_binder()
                    .bound_region_vars
                    .iter()
                    .map(|r| Region::Var(DeBruijnVar::new_at_zero(*r))),
            );
        } else {
            args.regions
                .extend(closure.tupled_sig.bound_vars.iter().map(|_| Region::Erased));
        }

        Ok(TraitImplRef {
            impl_id,
            generics: Box::new(args),
        })
    }

    /// Translate a trait reference to the chosen closure impl.
    pub fn translate_closure_trait_ref(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        args: &hax::ClosureArgs,
        target_kind: ClosureKind,
    ) -> Result<TraitDeclRef, Error> {
        // TODO: how much can we ask hax for this?
        let fn_trait = match target_kind {
            ClosureKind::FnOnce => self.get_lang_item(rustc_hir::LangItem::FnOnce),
            ClosureKind::FnMut => self.get_lang_item(rustc_hir::LangItem::FnMut),
            ClosureKind::Fn => self.get_lang_item(rustc_hir::LangItem::Fn),
        };
        let trait_id = self.register_trait_decl_id(span, &fn_trait);

        let state_ty = self.get_closure_state_ty(span, def_id, args)?;
        // The input tuple type and output type of the signature.
        let (inputs, _) = self.translate_closure_info(span, args)?.signature.erase();
        let input_tuple = Ty::mk_tuple(inputs);

        Ok(TraitDeclRef {
            trait_id,
            generics: Box::new(GenericArgs::new_types(
                [state_ty, input_tuple].into(),
                GenericsSource::item(trait_id),
            )),
        })
    }

    pub fn get_closure_state_ty(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
        args: &hax::ClosureArgs,
    ) -> Result<Ty, Error> {
        let ty_ref = self.translate_closure_type_ref(span, def_id, args)?;
        Ok(TyKind::Adt(ty_ref.id, *ty_ref.generics).into_ty())
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
        let fields: Vector<FieldId, Field> = args
            .upvar_tys
            .iter()
            .map(|ty| {
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
                    attr_info: AttrInfo {
                        attributes: vec![],
                        inline: None,
                        rename: None,
                        public: false,
                    },
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
    ) -> Result<FunSig, Error> {
        let signature = &args.tupled_sig;

        // Translate the signature
        trace!(
            "signature of closure {:?}:\n{:?}",
            def.def_id,
            signature.value
        );
        let mut inputs: Vec<Ty> = signature
            .value
            .inputs
            .iter()
            .map(|ty| self.translate_ty(span, ty))
            .try_collect()?;
        let output = self.translate_ty(span, &signature.value.output)?;

        let fmt_ctx = self.into_fmt();
        trace!(
            "# Input variables types:\n{}",
            pretty_display_list(|x| fmt_ctx.format_object(x), &inputs)
        );
        trace!(
            "# Output variable type:\n{}",
            fmt_ctx.format_object(&output)
        );

        let is_unsafe = match signature.value.safety {
            hax::Safety::Unsafe => true,
            hax::Safety::Safe => false,
        };

        let state_ty = self.get_closure_state_ty(span, def.def_id(), args)?;

        // Depending on the kind of the closure generated, add a reference
        let state_ty = match target_kind {
            ClosureKind::FnOnce => state_ty,
            ClosureKind::Fn | ClosureKind::FnMut => {
                let rid = self
                    .innermost_generics_mut()
                    .regions
                    .push_with(|index| RegionVar { index, name: None });
                let r = Region::Var(DeBruijnVar::new_at_zero(rid));
                let mutability = if target_kind == ClosureKind::Fn {
                    RefKind::Shared
                } else {
                    RefKind::Mut
                };
                TyKind::Ref(r, state_ty, mutability).into_ty()
            }
        };
        assert_eq!(inputs.len(), 1);
        inputs.insert(0, state_ty);

        Ok(FunSig {
            generics: self.the_only_binder().params.clone(),
            is_unsafe,
            inputs,
            output,
        })
    }

    fn translate_closure_method_body(
        mut self,
        span: Span,
        def: &hax::FullDef,
        target_kind: ClosureKind,
        args: &hax::ClosureArgs,
        signature: &FunSig,
    ) -> Result<Result<Body, Opaque>, Error> {
        use ClosureKind::*;
        let closure_kind = translate_closure_kind(&args.kind);
        let mk_stt = |content| Statement::new(span, content);
        let mk_block = |statements, terminator| -> BlockData {
            BlockData {
                statements,
                terminator: Terminator::new(span, terminator),
            }
        };
        let mk_body = |locals, blocks: Vector<BlockId, BlockData>| -> Result<Body, Opaque> {
            let body: ExprBody = GExprBody {
                span,
                locals,
                comments: vec![],
                body: blocks,
            };
            Ok(Body::Unstructured(body))
        };
        let mut mk_call = |dst, arg1, arg2, target, on_unwind| -> Result<RawTerminator, Error> {
            // TODO: make a trait call to avoid needing to concatenate things ourselves.
            // TODO: can we ask hax for the trait ref?
            let fun_id = self.register_closure_method_decl_id(span, def.def_id(), closure_kind);
            let impl_ref =
                self.translate_closure_impl_ref(span, def.def_id(), args, closure_kind)?;
            Ok(RawTerminator::Call {
                target,
                call: Call {
                    func: FnOperand::Regular(FnPtr {
                        func: FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id.clone())).into(),
                        generics: Box::new(impl_ref.generics.concat(
                            GenericsSource::item(fun_id),
                            &GenericArgs {
                                regions: vec![Region::Erased].into(),
                                ..GenericArgs::empty(GenericsSource::item(fun_id))
                            },
                        )),
                    }),
                    args: vec![Operand::Move(arg1), Operand::Move(arg2)],
                    dest: dst,
                },
                on_unwind,
            })
        };

        Ok(match (target_kind, closure_kind) {
            (Fn, Fn) | (FnMut, FnMut) | (FnOnce, FnOnce) => {
                // Translate the function's body normally
                let mut bt_ctx = BodyTransCtx::new(&mut self);
                match bt_ctx.translate_body(span, def) {
                    Ok(Ok(mut body)) => {
                        // The body is translated as if the locals are: ret value, state, arg-1,
                        // ..., arg-N, rest...
                        // However, there is only one argument with the tupled closure arguments;
                        // we must thus shift all locals with index >=2 by 1, and add a new local
                        // for the tupled arg, giving us: ret value, state, args, arg-1, ...,
                        // arg-N, rest...
                        // We then add N statements of the form `locals[N+3] := move locals[2].N`,
                        // to destructure the arguments.
                        let GExprBody {
                            locals,
                            body: blocks,
                            ..
                        } = body.as_unstructured_mut().unwrap();

                        blocks.dyn_visit_mut(|local: &mut LocalId| {
                            let idx = local.index();
                            if idx >= 2 {
                                *local = LocalId::new(idx + 1)
                            }
                        });

                        let mut old_locals = mem::take(&mut locals.locals).into_iter();
                        locals.arg_count = 2;
                        locals.locals.push(old_locals.next().unwrap()); // ret
                        locals.locals.push(old_locals.next().unwrap()); // state
                        let tupled_arg = locals
                            .new_var(Some("tupled_args".to_string()), signature.inputs[1].clone());
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
                            mk_stt(RawStatement::Assign(
                                locals.place_for_var(LocalId::new(i + 3)),
                                Rvalue::Use(Operand::Move(nth_field)),
                            ))
                        });
                        blocks[BlockId::ZERO].statements.splice(0..0, new_stts);

                        Ok(body)
                    }
                    Ok(Err(Opaque)) => Err(Opaque),
                    Err(_) => Err(Opaque),
                }
            }
            // Target translation:
            //
            // fn call_mut(state: &mut Self, args: Args) -> Output {
            //   let reborrow = &*state;
            //   self.call(reborrow, args)
            // }
            (FnMut, Fn) => {
                let mut locals = Locals {
                    arg_count: 2,
                    locals: Vector::new(),
                };
                let mut statements = vec![];
                let mut blocks = Vector::default();

                let output = locals.new_var(None, signature.output.clone());
                let state = locals.new_var(Some("state".to_string()), signature.inputs[0].clone());
                let args = locals.new_var(Some("args".to_string()), signature.inputs[1].clone());
                let deref_state = state.deref();
                let reborrow_ty =
                    TyKind::Ref(Region::Erased, deref_state.ty.clone(), RefKind::Shared).into_ty();
                let reborrow = locals.new_var(None, reborrow_ty);

                statements.push(mk_stt(RawStatement::Assign(
                    reborrow.clone(),
                    Rvalue::Ref(deref_state, BorrowKind::Shared),
                )));

                let start_block = blocks.reserve_slot();
                let ret_block = blocks.push(mk_block(vec![], RawTerminator::Return));
                let unwind_block = blocks.push(mk_block(vec![], RawTerminator::UnwindResume));
                let call = mk_call(output, reborrow, args, ret_block, unwind_block)?;
                blocks.set_slot(start_block, mk_block(statements, call));

                mk_body(locals, blocks)
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
                // TODO: could possibly ask hax for the body, using
                // `InstanceKind::ClosureOnceShim`.
                let mut locals = Locals {
                    arg_count: 2,
                    locals: Vector::new(),
                };
                let mut statements = vec![];
                let mut blocks = Vector::default();

                let output = locals.new_var(None, signature.output.clone());
                let state = locals.new_var(Some("state".to_string()), signature.inputs[0].clone());
                let args = locals.new_var(Some("args".to_string()), signature.inputs[1].clone());

                let (refkind, borrowkind) = if closure_kind == FnMut {
                    (RefKind::Mut, BorrowKind::Mut)
                } else {
                    (RefKind::Shared, BorrowKind::Shared)
                };

                let borrow_ty =
                    TyKind::Ref(Region::Erased, signature.inputs[0].clone(), refkind).into_ty();
                let state_ref = locals.new_var(Some("temp_ref".to_string()), borrow_ty);
                statements.push(mk_stt(RawStatement::Assign(
                    state_ref.clone(),
                    Rvalue::Ref(state.clone(), borrowkind),
                )));

                let start_block = blocks.reserve_slot();
                let drop = mk_stt(RawStatement::Drop(state));
                let ret_block = blocks.push(mk_block(vec![drop], RawTerminator::Return));
                let unwind_block = blocks.push(mk_block(vec![], RawTerminator::UnwindResume));
                let call = mk_call(output, state_ref, args, ret_block, unwind_block)?;
                blocks.set_slot(start_block, mk_block(statements, call));

                mk_body(locals, blocks)
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
        let hax::FullDefKind::Closure { args, .. } = &def.kind else {
            unreachable!()
        };

        trace!("About to translate closure:\n{:?}", def.def_id);

        self.translate_def_generics(span, def)?;
        // Add the lifetime generics coming from the higher-kindedness of the signature.
        assert!(self.innermost_binder_mut().bound_region_vars.is_empty(),);
        self.innermost_binder_mut()
            .push_params_from_binder(args.tupled_sig.rebind(()))?;

        let impl_ref = self.translate_closure_impl_ref(span, def.def_id(), args, target_kind)?;
        let implemented_trait =
            self.translate_closure_trait_ref(span, def.def_id(), args, target_kind)?;
        let kind = ItemKind::TraitImpl {
            impl_ref,
            trait_ref: implemented_trait,
            item_name: TraitItemName(target_kind.method_name().to_owned()),
            reuses_default: false,
        };

        // Translate the function signature
        let signature = self.translate_closure_method_sig(def, span, args, target_kind)?;

        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Err(Opaque)
        } else {
            self.translate_closure_method_body(span, def, target_kind, args, &signature)?
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind,
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
        let hax::FullDefKind::Closure { args, .. } = &def.kind else {
            unreachable!()
        };

        self.translate_def_generics(span, def)?;
        // Add the lifetime generics coming from the higher-kindedness of the signature.
        assert!(self.innermost_binder_mut().bound_region_vars.is_empty(),);
        self.innermost_binder_mut()
            .push_params_from_binder(args.tupled_sig.rebind(()))?;

        // The builtin traits we need.
        let sized_trait = self.get_lang_item(rustc_hir::LangItem::Sized);
        let sized_trait = self.register_trait_decl_id(span, &sized_trait);

        let tuple_trait = self.get_lang_item(rustc_hir::LangItem::Tuple);
        let tuple_trait = self.register_trait_decl_id(span, &tuple_trait);

        let implemented_trait =
            self.translate_closure_trait_ref(span, def.def_id(), args, target_kind)?;
        let fn_trait = implemented_trait.trait_id;

        // The input tuple type and output type of the signature.
        let (inputs, output) = self.translate_closure_info(span, args)?.signature.erase();
        let input = Ty::mk_tuple(inputs);

        let parent_trait_refs = {
            // Makes a built-in trait ref for `ty: trait`.
            let builtin_tref = |trait_id, ty| {
                let generics = Box::new(GenericArgs::new_types(
                    vec![ty].into(),
                    GenericsSource::item(trait_id),
                ));
                let trait_decl_ref = TraitDeclRef { trait_id, generics };
                let trait_decl_ref = RegionBinder::empty(trait_decl_ref);
                TraitRef {
                    kind: TraitRefKind::BuiltinOrAuto {
                        trait_decl_ref: trait_decl_ref.clone(),
                        parent_trait_refs: Vector::new(),
                        types: vec![],
                    },
                    trait_decl_ref,
                }
            };

            match target_kind {
                ClosureKind::FnOnce => [
                    builtin_tref(sized_trait, input.clone()),
                    builtin_tref(tuple_trait, input.clone()),
                    builtin_tref(sized_trait, output.clone()),
                ]
                .into(),
                ClosureKind::FnMut | ClosureKind::Fn => {
                    let parent_kind = match target_kind {
                        ClosureKind::FnOnce => unreachable!(),
                        ClosureKind::FnMut => ClosureKind::FnOnce,
                        ClosureKind::Fn => ClosureKind::FnMut,
                    };
                    let parent_impl_ref =
                        self.translate_closure_impl_ref(span, def.def_id(), args, parent_kind)?;
                    let parent_predicate =
                        self.translate_closure_trait_ref(span, def.def_id(), args, parent_kind)?;
                    let parent_trait_ref = TraitRef {
                        kind: TraitRefKind::TraitImpl(
                            parent_impl_ref.impl_id,
                            parent_impl_ref.generics,
                        ),
                        trait_decl_ref: RegionBinder::empty(parent_predicate),
                    };
                    [
                        parent_trait_ref,
                        builtin_tref(sized_trait, input.clone()),
                        builtin_tref(tuple_trait, input.clone()),
                    ]
                    .into()
                }
            }
        };
        let types = match target_kind {
            ClosureKind::FnOnce => vec![(TraitItemName("Output".into()), output.clone())],
            ClosureKind::FnMut | ClosureKind::Fn => vec![],
        };

        // Construct the `call_*` method reference.
        let call_fn_id = self.register_closure_method_decl_id(span, &def.def_id, target_kind);
        let call_fn_name = TraitItemName(target_kind.method_name().to_string());
        let call_fn_binder = {
            let mut method_params = GenericParams::empty();
            match target_kind {
                ClosureKind::FnOnce => {}
                ClosureKind::FnMut | ClosureKind::Fn => {
                    method_params
                        .regions
                        .push_with(|index| RegionVar { index, name: None });
                }
            };

            let generics = self
                .outermost_binder()
                .params
                .identity_args_at_depth(GenericsSource::item(def_id), DeBruijnId::one())
                .concat(
                    GenericsSource::item(call_fn_id),
                    &method_params.identity_args_at_depth(
                        GenericsSource::Method(fn_trait, call_fn_name.clone()),
                        DeBruijnId::zero(),
                    ),
                );
            Binder::new(
                BinderKind::TraitMethod(fn_trait, call_fn_name.clone()),
                method_params,
                FunDeclRef {
                    id: call_fn_id,
                    generics: Box::new(generics),
                },
            )
        };

        let self_generics = self.into_generics();

        Ok(TraitImpl {
            def_id,
            item_meta,
            impl_trait: implemented_trait,
            generics: self_generics,
            parent_trait_refs,
            type_clauses: vec![],
            consts: vec![],
            types,
            methods: vec![(call_fn_name, call_fn_binder)],
        })
    }
}
