//! Strings (the `str` type) are really just `&[u8]` slices; however Charon handles strings
//! as literal values, hiding the fact there is in fact a reference there.
//! This pass allows translating strings into global variables containing the unsized array
//! of bytes for that string.

use derive_generic_visitor::Visitor;
use std::collections::HashMap;

use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use super::ctx::UllbcPass;

fn str_ty() -> Ty {
    TyKind::Ref(
        Region::Static,
        TyKind::Adt(TypeDeclRef {
            id: TypeId::Builtin(BuiltinTy::Str),
            generics: Box::new(GenericArgs::empty()),
        })
        .into_ty(),
        RefKind::Shared,
    )
    .into_ty()
}

fn item_meta_for_str(str: String) -> ItemMeta {
    ItemMeta {
        name: Name {
            name: vec![
                PathElem::Ident("string_constant".to_string(), Disambiguator::ZERO),
                PathElem::Monomorphized(Box::new(GenericArgs {
                    const_generics: vec![ConstGeneric::Value(Literal::Str(str.clone()))].into(),
                    regions: Vector::new(),
                    types: Vector::new(),
                    trait_refs: Vector::new(),
                })),
            ],
        },
        attr_info: AttrInfo {
            attributes: vec![],
            inline: None,
            rename: None,
            public: true,
        },
        is_local: false,
        lang_item: None,
        opacity: ItemOpacity::Transparent,
        source_text: None,
        span: Span::dummy(),
    }
}

fn global_decl_for_string(str: &String, id: GlobalDeclId, fun: FunDeclId) -> GlobalDecl {
    return GlobalDecl {
        def_id: id,
        item_meta: item_meta_for_str(str.clone()),
        generics: GenericParams::empty(),
        ty: str_ty(),
        kind: ItemKind::TopLevel,
        global_kind: GlobalKind::Static,
        init: fun,
    };
}

fn fun_decl_for_string(str: &String, id: FunDeclId, global: GlobalDeclId) -> FunDecl {
    let str_bytes = str.as_bytes();
    let u8_ty = TyKind::Literal(LiteralTy::UInt(UIntTy::U8)).into_ty();
    let len_const = ConstGeneric::Value(Literal::Scalar(ScalarValue::Unsigned(
        UIntTy::Usize,
        str_bytes.len() as u128,
    )));

    // We want to generate a body that looks like:
    //     arr: [u8; N] = [...]; // <-- string bytes
    //     arr_ref: &[u8; N] = &arr;
    //     slice: &[u8] = <unsize>(arr);
    //     str: str = <transmute>(slice);
    //     return str;
    let mut body = ExprBody {
        body: Vector::new(),
        comments: vec![],
        locals: Locals::default(),
        span: Span::dummy(),
    };
    let ret = body.locals.new_var(Some("str".into()), str_ty());
    let arr = body.locals.new_var(
        Some("arr".into()),
        TyKind::Adt(TypeDeclRef {
            id: TypeId::Builtin(BuiltinTy::Array),
            generics: Box::new(GenericArgs {
                types: vec![u8_ty.clone()].into(),
                const_generics: vec![len_const.clone()].into(),
                regions: Vector::new(),
                trait_refs: Vector::new(),
            }),
        })
        .into_ty(),
    );
    let arr_ref = body.locals.new_var(
        Some("arr_ref".into()),
        TyKind::Ref(Region::Erased, arr.ty.clone(), RefKind::Shared).into_ty(),
    );
    let slice = body.locals.new_var(
        Some("slice".into()),
        TyKind::Ref(
            Region::Erased,
            TyKind::Adt(TypeDeclRef {
                id: TypeId::Builtin(BuiltinTy::Slice),
                generics: Box::new(GenericArgs::new_types(vec![u8_ty.clone()].into())),
            })
            .into_ty(),
            RefKind::Shared,
        )
        .into_ty(),
    );
    let statements = vec![
        RawStatement::Assign(
            arr.clone(),
            Rvalue::Use(Operand::Const(Box::new(ConstantExpr {
                value: RawConstantExpr::RawMemory(str.clone().into_bytes()),
                ty: arr.ty.clone(),
            }))),
        ),
        RawStatement::Assign(arr_ref.clone(), Rvalue::Ref(arr, BorrowKind::Shared)),
        RawStatement::Assign(
            slice.clone(),
            Rvalue::UnaryOp(
                UnOp::Cast(CastKind::Unsize(
                    arr_ref.ty.clone(),
                    slice.ty.clone(),
                    UnsizingMetadata::Length(len_const),
                )),
                Operand::Move(arr_ref),
            ),
        ),
        RawStatement::Assign(
            ret.clone(),
            Rvalue::UnaryOp(
                UnOp::Cast(CastKind::Transmute(slice.ty.clone(), ret.ty.clone())),
                Operand::Move(slice),
            ),
        ),
    ];
    let block = BlockData {
        statements: statements
            .into_iter()
            .map(|stt| Statement::new(Span::dummy(), stt))
            .collect(),
        terminator: Terminator::new(Span::dummy(), RawTerminator::Return),
    };
    body.body.push(block);

    FunDecl {
        def_id: id,
        body: Ok(Body::Unstructured(body)),
        is_global_initializer: Some(global),
        item_meta: item_meta_for_str(str.clone()),
        kind: ItemKind::TopLevel,
        signature: FunSig {
            is_unsafe: false,
            generics: GenericParams::empty(),
            inputs: vec![],
            output: str_ty(),
        },
    }
}

#[derive(Visitor)]
struct StringVisitor<'a> {
    data: &'a mut HashMap<String, GlobalDeclId>,
    krate: &'a mut TranslatedCrate,
}

impl<'a> StringVisitor<'a> {
    fn new(data: &'a mut HashMap<String, GlobalDeclId>, krate: &'a mut TranslatedCrate) -> Self {
        Self { data, krate }
    }

    fn alloc(&mut self, str: &String) -> GlobalDeclRef {
        let id = if let Some(global) = self.data.get(str) {
            global.clone()
        } else {
            let id = self.krate.global_decls.reserve_slot();
            self.data.insert(str.clone(), id.clone());
            id
        };
        GlobalDeclRef {
            id,
            generics: Box::new(GenericArgs::empty()),
        }
    }
}

impl VisitAstMut for StringVisitor<'_> {
    fn enter_constant_expr(&mut self, c: &mut ConstantExpr) {
        match &mut c.value {
            RawConstantExpr::Literal(Literal::Str(str)) => {
                let gref = self.alloc(str);
                c.value = RawConstantExpr::Global(gref);
            }
            _ => {}
        }
    }
}

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        // Check the option which instructs to ignore this pass
        if !ctx.options.strings_as_globals {
            return;
        }

        let mut substs = HashMap::new();
        ctx.for_each_body(|ctx, body| {
            let mut visitor = StringVisitor::new(&mut substs, &mut ctx.translated);
            let _ = body.drive_mut(&mut visitor);
        });
        for (str, id) in substs.iter() {
            let fun_id = ctx.translated.fun_decls.reserve_slot();
            let global = global_decl_for_string(&str, *id, fun_id);
            let fun = fun_decl_for_string(&str, fun_id, *id);

            ctx.translated
                .item_names
                .insert(AnyTransId::Global(*id), global.item_meta.name.clone());
            ctx.translated
                .item_names
                .insert(AnyTransId::Fun(fun_id), fun.item_meta.name.clone());

            ctx.translated.global_decls.set_slot(*id, global);
            ctx.translated.fun_decls.set_slot(fun_id, fun);
        }
    }
}
