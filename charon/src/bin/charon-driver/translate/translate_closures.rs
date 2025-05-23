//! In MIR, closures are special cased, and have their own type; calling a closure then uses
//! builtins, requiring consumers to special case them.
//! Here we convert closures to a struct containing the closure's state (upvars), along with
//! matching trait impls and fun decls (e.g. a Fn closure will have a trait impl for Fn, FnMut
//! and FnOnce, along with 3 matching functions for call, call_mut and call_once).
//!
//! For example, given the following Rust code:
//! ```rust
//! pub fn test_closure_capture(x: u32, y: u32) -> u32 {
//!   let f = &|z| x + y + z;
//!   (f)(0)
//! }
//! ```
//!
//! We generate the equivalent desugared code:
//! ```rust
//! struct {test_closure_capture::closure#0} (
//!     u32,
//!     u32,
//! )
//!
//! impl Fn<(u32,)> for {test_closure_capture::closure#0} {
//!     type Output = u32;
//!     fn call(&self, arg: (u32,)) -> u32 {
//!         self.0 + self.1 + arg.0
//!     }
//! }
//!
//! impl FnMut<(u32,)> for {test_closure_capture::closure#0} { ... }
//! impl FnOnce<(u32,)> for {test_closure_capture::closure#0} { ... }
//!
//! pub fn test_closure_capture(x: u32, y: u32) -> u32 {
//!     let state = {test_closure_capture::closure#0} ( x, y );
//!     state.call((0,))
//! }
//! ```

use crate::translate::translate_bodies::BodyTransCtx;

use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::common::*;
use charon_lib::formatter::{Formatter, IntoFormatter};
use charon_lib::ids::Vector;
use charon_lib::ullbc_ast::*;
use hax_frontend_exporter as hax;
use itertools::Itertools;

impl ItemTransCtx<'_, '_> {
    pub fn translate_closure_generic_args(
        &mut self,
        span: Span,
        args: &hax::ClosureArgs,
        source: GenericsSource,
    ) -> Result<GenericArgs, Error> {
        self.translate_generic_args(
            span,
            &args.parent_args,
            &args.parent_trait_refs,
            Some(hax::Binder {
                value: (),
                bound_vars: args.tupled_sig.bound_vars.clone(),
            }),
            source,
        )
    }

    pub fn get_closure_state_ty(
        &mut self,
        span: Span,
        def: &hax::DefId,
        args: &hax::ClosureArgs,
    ) -> Result<Ty, Error> {
        let state_id = self.register_type_decl_id(span, def);
        let gen_args =
            self.translate_closure_generic_args(span, args, GenericsSource::item(state_id))?;
        Ok(TyKind::Adt(TypeId::Adt(state_id), gen_args).into_ty())
    }

    pub fn translate_closure_ty(
        &mut self,
        _trans_id: TypeDeclId,
        span: Span,
        args: &hax::ClosureArgs,
    ) -> Result<TypeDeclKind, Error> {
        let fields: Vector<FieldId, Field> = args
            .upvar_tys
            .iter()
            .map(|ty| {
                let ty = self.translate_ty(span, ty)?;
                Ok(Field {
                    span,
                    attr_info: AttrInfo {
                        attributes: vec![],
                        inline: None,
                        rename: None,
                        public: true,
                    },
                    name: None,
                    ty,
                })
            })
            .try_collect()?;

        let signature = self.translate_region_binder(span, &args.untupled_sig, |ctx, sig| {
            let inputs = sig
                .inputs
                .iter()
                .map(|x| ctx.translate_ty(span, x))
                .try_collect()?;
            let output = ctx.translate_ty(span, &sig.output)?;
            Ok((inputs, output))
        })?;
        let kind = match args.kind {
            hax::ClosureKind::Fn => ClosureKind::Fn,
            hax::ClosureKind::FnMut => ClosureKind::FnMut,
            hax::ClosureKind::FnOnce => ClosureKind::FnOnce,
        };

        Ok(TypeDeclKind::Struct(
            fields,
            Some(ClosureInfo { kind, signature }),
        ))
    }

    fn translate_closure_signature(
        &mut self,
        def: &hax::FullDef,
        item_meta: &ItemMeta,
        args: &hax::ClosureArgs,
        target_kind: &hax::ClosureKind,
    ) -> Result<FunSig, Error> {
        let span = item_meta.span;

        self.translate_def_generics(span, def)?;

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

        assert_eq!(inputs.len(), 1);

        let state_ty = self.get_closure_state_ty(span, def.def_id(), args)?;

        // Depending on the kind of the closure generated, add a reference
        let state_ty = match target_kind {
            hax::ClosureKind::FnOnce => state_ty,
            hax::ClosureKind::Fn | hax::ClosureKind::FnMut => {
                let rid = self
                    .innermost_generics_mut()
                    .regions
                    .push_with(|index| RegionVar { index, name: None });
                let r = Region::Var(DeBruijnVar::new_at_zero(rid));
                let mutability = if args.kind == hax::ClosureKind::Fn {
                    RefKind::Shared
                } else {
                    RefKind::Mut
                };
                TyKind::Ref(r, state_ty, mutability).into_ty()
            }
        };
        inputs.splice(0..0, vec![state_ty]);

        Ok(FunSig {
            generics: self.the_only_binder().params.clone(),
            is_unsafe,
            is_closure: true,
            inputs,
            output,
        })
    }

    /// Translate the function for the implementation of a closure
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_fun(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        target_kind: &hax::ClosureKind,
    ) -> Result<FunDecl, Error> {
        let hax::FullDefKind::Closure { args, .. } = &def.kind else {
            unreachable!()
        };

        trace!("About to translate closure:\n{:?}", def.def_id);
        let span = item_meta.span;

        // Translate the function signature
        trace!("Translating closure signature");
        let signature = self.translate_closure_signature(def, &item_meta, args, target_kind)?;

        let kind = self.get_item_kind(span, def)?;

        let body_id = if item_meta.opacity.with_private_contents().is_opaque() {
            Err(Opaque)
        } else {
            // Utils to make constructing the body nicer
            let mk_stt = |content| Statement {
                content,
                comments_before: vec![],
                span,
            };
            let mk_block = |statements, terminator| -> BlockData {
                BlockData {
                    statements,
                    terminator: Terminator {
                        content: terminator,
                        comments_before: vec![],
                        span,
                    },
                }
            };
            let mk_body = |locals, blocks: Vec<BlockData>| -> Result<Body, Opaque> {
                let body: ExprBody = GExprBody {
                    span,
                    locals,
                    comments: vec![],
                    body: blocks.into(),
                };
                Ok(Body::Unstructured(body))
            };
            let mut mk_call = |dst, arg1, arg2, target| -> Result<RawTerminator, Error> {
                // FIXME: @N1ark do we want to make the call a trait impl call, rather than
                // a simple fun call? My intuition is that we may as well take the simple
                // option of making it a fun call, since a pass will simplify it away anyways.

                let fun_id = self.register_closure_fun_decl_id(span, &def.def_id, &args.kind);

                let parent_args =
                    self.translate_closure_generic_args(span, args, GenericsSource::Builtin)?;

                Ok(RawTerminator::Call {
                    target,
                    call: Call {
                        func: FnOperand::Regular(FnPtr {
                            func: FunIdOrTraitMethodRef::Fun(FunId::Regular(fun_id.clone())).into(),
                            generics: Box::new(parent_args.concat(
                                GenericsSource::item(fun_id),
                                &GenericArgs {
                                    const_generics: Vector::new(),
                                    regions: vec![Region::Erased].into(),
                                    trait_refs: Vector::new(),
                                    types: Vector::new(),
                                    target: GenericsSource::item(fun_id),
                                },
                            )),
                        }),
                        args: vec![Operand::Move(arg1), Operand::Move(arg2)],
                        dest: dst,
                    },
                    // TODO: wrong, will fix later
                    on_unwind: BlockId::ZERO,
                })
            };

            use hax::ClosureKind::*;
            match (target_kind, &args.kind) {
                (Fn, Fn) | (FnMut, FnMut) | (FnOnce, FnOnce) => {
                    // Translate the function's body normally
                    let mut bt_ctx = BodyTransCtx::new(&mut self);
                    match bt_ctx.translate_body(item_meta.span, def) {
                        Ok(Ok(body)) => {
                            // The body is translated as if the locals are:
                            // ret value, state, arg-1, ..., arg-N, rest...
                            // However, there is only one argument with the tupled closure
                            // arguments; we must thus shift all locals with index >=2 by 1,
                            // and add a new local for the tupled arg, giving us:
                            // ret value, state, args, arg-1, ..., arg-N, rest...
                            // We then add N statements of the form `locals[N+3] := move locals[2].N`,
                            // to destructure the arguments.
                            let Body::Unstructured(GExprBody {
                                span,
                                mut locals,
                                comments,
                                mut body,
                            }) = body
                            else {
                                unreachable!()
                            };

                            body.dyn_visit_mut(|local: &mut LocalId| {
                                let idx = local.index();
                                if idx >= 2 {
                                    *local = LocalId::new(idx + 1)
                                }
                            });

                            let closure_arg_count = locals.arg_count - 1;
                            locals.arg_count = 2;
                            let mut old_locals = Vector::new();
                            std::mem::swap(&mut old_locals, &mut locals.locals);
                            locals.locals.push(old_locals.remove(0.into()).unwrap()); // ret
                            locals.locals.push(old_locals.remove(1.into()).unwrap()); // state
                            let tupled_args = locals.new_var(
                                Some("tupled_args".to_string()),
                                signature.inputs[1].clone(),
                            );
                            locals.locals.extend(old_locals.into_iter().map(|mut l| {
                                l.index = LocalId::new(l.index.index() + 1);
                                l
                            }));

                            let untupled_args = signature.inputs[1].as_tuple().unwrap();
                            let new_stts = (0..closure_arg_count).into_iter().map(|idx| {
                                mk_stt(RawStatement::Assign(
                                    locals.place_for_var(LocalId::new(idx + 3)),
                                    Rvalue::Use(Operand::Move(Place {
                                        kind: PlaceKind::Projection(
                                            tupled_args.clone().into(),
                                            ProjectionElem::Field(
                                                FieldProjKind::Tuple(closure_arg_count),
                                                FieldId::new(idx),
                                            ),
                                        ),
                                        ty: untupled_args[TypeVarId::new(idx)].clone(),
                                    })),
                                ))
                            });
                            let fst_block = &mut body.get_mut(BlockId::ZERO).unwrap().statements;
                            fst_block.splice(0..0, new_stts);

                            Ok(Body::Unstructured(GExprBody {
                                span,
                                locals,
                                comments,
                                body,
                            }))
                        }
                        Ok(Err(Opaque)) => Err(Opaque),
                        Err(_) => Err(Opaque),
                    }
                }
                (FnMut, Fn) => {
                    // Target translation:
                    //
                    // fn call_mut(state: &mut Self, args: Args) -> Output {
                    //   self.call(state, args)
                    // }
                    //

                    let mut locals = Locals {
                        arg_count: 2,
                        locals: Vector::new(),
                    };
                    let output = locals.new_var(None, signature.output.clone());
                    let state =
                        locals.new_var(Some("state".to_string()), signature.inputs[0].clone());
                    let args =
                        locals.new_var(Some("args".to_string()), signature.inputs[1].clone());
                    let call = mk_call(output, state, args, BlockId::new(1))?;
                    let main_block = mk_block(vec![], call);
                    let ret_block = mk_block(vec![], RawTerminator::Return);
                    mk_body(locals, vec![main_block, ret_block])
                }
                (FnOnce, Fn) | (FnOnce, FnMut) => {
                    // Target translation:
                    //
                    // fn call_once(state: Self, args: Args) -> Output {
                    //   let temp_ref = &[mut] state;
                    //   let ret = self.call[_mut](temp, args);
                    //   drop state;
                    //   return ret;
                    // }
                    //
                    // FIXME: @N1ark do we want to make the call a trait impl call, rather than
                    // a simple fun call? My intuition is that we may as well take the simple
                    // option of making it a fun call, since a pass will simplify it away anyways.

                    let (refkind, borrowkind) = if args.kind == FnMut {
                        (RefKind::Mut, BorrowKind::Mut)
                    } else {
                        (RefKind::Shared, BorrowKind::Shared)
                    };

                    let ref_ty =
                        TyKind::Ref(Region::Erased, signature.inputs[0].clone(), refkind).into_ty();

                    let mut locals = Locals {
                        arg_count: 2,
                        locals: Vector::new(),
                    };
                    let output = locals.new_var(None, signature.output.clone());
                    let state =
                        locals.new_var(Some("state".to_string()), signature.inputs[0].clone());
                    let args =
                        locals.new_var(Some("args".to_string()), signature.inputs[1].clone());
                    let state_ref = locals.new_var(Some("temp_ref".to_string()), ref_ty);
                    let mk_ref = mk_stt(RawStatement::Assign(
                        state_ref.clone(),
                        Rvalue::Ref(state.clone(), borrowkind),
                    ));
                    let call = mk_call(output, state_ref, args, BlockId::new(1))?;
                    let main_block = mk_block(vec![mk_ref], call);

                    let drop = mk_stt(RawStatement::Drop(state));
                    let ret_block = mk_block(vec![drop], RawTerminator::Return);
                    mk_body(locals, vec![main_block, ret_block])
                }

                (Fn, FnOnce) | (Fn, FnMut) | (FnMut, FnOnce) => {
                    panic!("Can't make a closure body for a more restrictive kind")
                }
            }
        };

        Ok(FunDecl {
            def_id,
            item_meta,
            signature,
            kind,
            is_global_initializer: None,
            body: body_id,
        })
    }

    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_closure_trait_impl(
        mut self,
        def_id: TraitImplId,
        item_meta: ItemMeta,
        def: &hax::FullDef,
        target_kind: &hax::ClosureKind,
    ) -> Result<TraitImpl, Error> {
        trace!("About to translate closure trait impl:\n{:?}", def.def_id);
        trace!("Trait impl id:\n{:?}", def_id);

        let span = item_meta.span;
        self.translate_def_generics(span, def)?;

        let hax::FullDefKind::Closure { args, .. } = &def.kind else {
            unreachable!()
        };

        let fn_trait = match target_kind {
            hax::ClosureKind::FnOnce => self.get_lang_item(rustc_hir::LangItem::FnOnce),
            hax::ClosureKind::FnMut => self.get_lang_item(rustc_hir::LangItem::FnMut),
            hax::ClosureKind::Fn => self.get_lang_item(rustc_hir::LangItem::Fn),
        };
        let fn_trait = self.register_trait_decl_id(span, &fn_trait);

        let call_fn = self.register_closure_fun_decl_id(span, &def.def_id, target_kind);
        let call_fn_name = match target_kind {
            hax::ClosureKind::FnOnce => "call_once".to_string(),
            hax::ClosureKind::FnMut => "call_mut".to_string(),
            hax::ClosureKind::Fn => "call".to_string(),
        };
        let call_fn_name = TraitItemName(call_fn_name);
        let mut call_fn_params = GenericParams::empty();
        match target_kind {
            hax::ClosureKind::FnOnce => {}
            hax::ClosureKind::FnMut | hax::ClosureKind::Fn => {
                call_fn_params
                    .regions
                    .push_with(|index| RegionVar { index, name: None });
            }
        };
        let fn_ref_args_target = GenericsSource::Method(fn_trait, call_fn_name.clone());
        let fn_ref_args = match target_kind {
            hax::ClosureKind::FnOnce => GenericArgs::empty(fn_ref_args_target),
            hax::ClosureKind::FnMut | hax::ClosureKind::Fn => GenericArgs {
                regions: vec![Region::Erased].into(),
                types: Vector::new(),
                const_generics: Vector::new(),
                trait_refs: Vector::new(),
                target: fn_ref_args_target,
            },
        };
        let call_fn_binder = Binder::new(
            BinderKind::TraitMethod(fn_trait, call_fn_name.clone()), //fix
            call_fn_params,
            FunDeclRef {
                id: call_fn,
                // TODO: @N1ark this is wrong -- we need to concat the args of the impl and of the method
                generics: Box::new(fn_ref_args),
            },
        );

        let sig_binder = self.translate_region_binder(span, &args.tupled_sig, |ctx, fnsig| {
            let inputs: Vec<Ty> = fnsig
                .inputs
                .iter()
                .map(|ty| ctx.translate_ty(span, ty))
                .try_collect()?;
            let inputs = Ty::mk_tuple(inputs);
            let output = ctx.translate_ty(span, &fnsig.output)?;
            Ok((inputs, output))
        })?;
        let (inputs, output) = sig_binder.erase();

        let state_ty = self.get_closure_state_ty(span, def.def_id(), args)?;

        let sized_trait = self.get_lang_item(rustc_hir::LangItem::Sized);
        let sized_trait = self.register_trait_decl_id(span, &sized_trait);

        let tuple_trait = self.get_lang_item(rustc_hir::LangItem::Tuple);
        let tuple_trait = self.register_trait_decl_id(span, &tuple_trait);

        let mk_tref = |trait_id, ty| {
            let generics = GenericArgs {
                regions: Vector::new(),
                const_generics: Vector::new(),
                trait_refs: Vector::new(),
                types: vec![ty].into(),
                target: GenericsSource::item(trait_id),
            };
            let tdeclref = TraitDeclRef {
                trait_id,
                generics: generics.clone().into(),
            };
            TraitRef {
                kind: TraitRefKind::BuiltinOrAuto {
                    trait_decl_ref: RegionBinder::empty(tdeclref.clone()),
                    parent_trait_refs: Vector::new(),
                    types: vec![],
                },
                trait_decl_ref: RegionBinder::empty(tdeclref),
            }
        };

        let fn_trait_arguments = GenericArgs {
            regions: Vector::new(),
            types: vec![state_ty.clone(), inputs.clone()].into(),
            const_generics: Vector::new(),
            trait_refs: Vector::new(),
            target: GenericsSource::item(fn_trait),
        };

        let (parent_trait_refs, types) = match target_kind {
            hax::ClosureKind::FnOnce => {
                let trait_refs = vec![
                    mk_tref(sized_trait, inputs.clone()),
                    mk_tref(tuple_trait, inputs),
                    mk_tref(sized_trait, output.clone()),
                ];
                let types = vec![(TraitItemName("Output".into()), output)];
                (trait_refs.into(), types)
            }
            hax::ClosureKind::FnMut | hax::ClosureKind::Fn => {
                let parent_kind = match target_kind {
                    hax::ClosureKind::FnOnce => unreachable!(),
                    hax::ClosureKind::FnMut => hax::ClosureKind::FnOnce,
                    hax::ClosureKind::Fn => hax::ClosureKind::FnMut,
                };
                let parent_impl =
                    self.register_closure_trait_impl_id(span, def.def_id(), &parent_kind);
                let parent_decl = match parent_kind {
                    hax::ClosureKind::FnOnce => self.get_lang_item(rustc_hir::LangItem::FnOnce),
                    hax::ClosureKind::FnMut => self.get_lang_item(rustc_hir::LangItem::FnMut),
                    hax::ClosureKind::Fn => unreachable!(),
                };
                let parent_args = self.translate_closure_generic_args(
                    span,
                    args,
                    GenericsSource::item(parent_impl),
                )?;
                let parent_decl = self.register_trait_decl_id(span, &parent_decl);
                let parent_trait_ref = TraitRef {
                    kind: TraitRefKind::TraitImpl(parent_impl, Box::new(parent_args)),
                    trait_decl_ref: RegionBinder::empty(TraitDeclRef {
                        trait_id: parent_decl,
                        generics: fn_trait_arguments
                            .clone()
                            .with_target(GenericsSource::item(parent_decl))
                            .into(),
                    }),
                };
                let trait_refs = vec![
                    parent_trait_ref,
                    mk_tref(sized_trait, inputs.clone()),
                    mk_tref(tuple_trait, inputs),
                ];
                (trait_refs.into(), vec![])
            }
        };

        let self_generics = self.into_generics();

        Ok(TraitImpl {
            def_id,
            item_meta,
            impl_trait: TraitDeclRef {
                trait_id: fn_trait,
                generics: fn_trait_arguments.into(),
            },
            generics: self_generics,
            parent_trait_refs,
            type_clauses: vec![],
            consts: vec![],
            types,
            methods: vec![(call_fn_name, call_fn_binder)],
        })
    }
}
