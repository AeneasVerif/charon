//! This file groups everything which is linked to implementations about [crate::expressions]
use crate::expressions::*;
use crate::formatter::{AstFormatter, FmtCtx};
use crate::gast::{
    AssumedFunId, Call, FnOperand, FunDeclId, FunId, FunIdOrTraitMethodRef, TraitItemName,
};
use crate::types::*;
use crate::ullbc_ast::GlobalDeclId;
use crate::values::*;
use macros::make_generic_in_borrows;
use std::vec::Vec;

impl Place {
    pub fn new(var_id: VarId::Id) -> Place {
        Place {
            var_id,
            projection: Vec::new(),
        }
    }
}

impl std::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            BorrowKind::Shared => write!(f, "Shared"),
            BorrowKind::Mut => write!(f, "Mut"),
            BorrowKind::TwoPhaseMut => write!(f, "TwoPhaseMut"),
            BorrowKind::Shallow => write!(f, "Shallow"),
        }
    }
}

impl CastKind {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            CastKind::Integer(src, tgt) => format!("cast<{src},{tgt}>"),
            CastKind::FnPtr(src, tgt) => {
                format!("cast<{},{}>", src.fmt_with_ctx(ctx), tgt.fmt_with_ctx(ctx))
            }
        }
    }
}

impl UnOp {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            UnOp::Not => "~".to_string(),
            UnOp::Neg => "-".to_string(),
            UnOp::Cast(kind) => kind.fmt_with_ctx(ctx),
            UnOp::ArrayToSlice(..) => "array_to_slice".to_string(),
        }
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            BinOp::BitXor => write!(f, "^"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Ge => write!(f, ">="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Shr => write!(f, ">>"),
        }
    }
}

impl Place {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let mut out = ctx.format_object(self.var_id);

        for p in &self.projection {
            match p {
                ProjectionElem::Deref => {
                    out = format!("*({out})");
                }
                ProjectionElem::DerefBox => {
                    out = format!("deref_box ({out})");
                }
                ProjectionElem::DerefRawPtr => {
                    out = format!("deref_raw_ptr ({out})");
                }
                ProjectionElem::Field(proj_kind, field_id) => match proj_kind {
                    FieldProjKind::Adt(adt_id, opt_variant_id) => {
                        let field_name = ctx.format_object((*adt_id, *opt_variant_id, *field_id));
                        let downcast = match opt_variant_id {
                            None => "".to_string(),
                            Some(variant_id) => format!(" as variant @{variant_id}"),
                        };
                        out = format!("({out}{downcast}).{field_name}");
                    }
                    FieldProjKind::Tuple(_) => {
                        out = format!("({out}).{field_id}");
                    }
                },
                ProjectionElem::Index(i, _) => out = format!("({out})[{}]", ctx.format_object(*i)),
            }
        }

        out
    }
}

impl std::fmt::Display for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl ConstantExpr {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        self.value.fmt_with_ctx(ctx)
    }
}

impl RawConstantExpr {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            RawConstantExpr::Literal(c) => c.to_string(),
            RawConstantExpr::Adt(variant_id, values) => {
                // It is a bit annoying: in order to properly format the value,
                // we need the type (which contains the type def id).
                // Anyway, the printing utilities are mostly for debugging.
                let variant_id = match variant_id {
                    Option::Some(id) => format!("Some({id})"),
                    Option::None => "None".to_string(),
                };
                let values: Vec<String> = values.iter().map(|v| v.fmt_with_ctx(ctx)).collect();
                format!("ConstAdt {} [{}]", variant_id, values.join(", "))
            }
            RawConstantExpr::Global(id) => ctx.format_object(*id),
            RawConstantExpr::TraitConst(trait_ref, substs, name) => {
                format!(
                    "{}{}::{name}",
                    trait_ref.fmt_with_ctx(ctx),
                    substs.fmt_with_ctx_split_trait_refs(ctx)
                )
            }
            RawConstantExpr::Ref(cv) => {
                format!("&{}", cv.fmt_with_ctx(ctx))
            }
            RawConstantExpr::Var(id) => format!("const {}", ctx.format_object(*id)),
            RawConstantExpr::FnPtr(f) => {
                format!("{}", f.fmt_with_ctx(ctx),)
            }
        }
    }
}

impl FnPtr {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let generics = self.generics.fmt_with_ctx_split_trait_refs(ctx);
        let f = match &self.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id)) => {
                format!("{}", ctx.format_object(*def_id),)
            }
            FunIdOrTraitMethodRef::Fun(FunId::Assumed(assumed)) => {
                format!("@{}", assumed.variant_name())
            }
            FunIdOrTraitMethodRef::Trait(trait_ref, method_id, _) => {
                format!("{}::{}", trait_ref.fmt_with_ctx(ctx), &method_id.0)
            }
        };

        format!("{}{}", f, generics)
    }
}

impl std::fmt::Display for ConstantExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl Operand {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            Operand::Copy(p) => format!("copy ({})", p.fmt_with_ctx(ctx)),
            Operand::Move(p) => format!("move ({})", p.fmt_with_ctx(ctx)),
            Operand::Const(c) => format!("const ({})", c.fmt_with_ctx(ctx)),
        }
    }
}

impl std::fmt::Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl Rvalue {
    pub fn fmt_with_ctx<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        match self {
            Rvalue::Use(x) => x.fmt_with_ctx(ctx),
            Rvalue::Ref(place, borrow_kind) => match borrow_kind {
                BorrowKind::Shared => format!("&{}", place.fmt_with_ctx(ctx)),
                BorrowKind::Mut => format!("&mut {}", place.fmt_with_ctx(ctx)),
                BorrowKind::TwoPhaseMut => {
                    format!("&two-phase-mut {}", place.fmt_with_ctx(ctx))
                }
                BorrowKind::Shallow => format!("&shallow {}", place.fmt_with_ctx(ctx)),
            },
            Rvalue::UnaryOp(unop, x) => {
                format!("{}({})", unop.fmt_with_ctx(ctx), x.fmt_with_ctx(ctx))
            }
            Rvalue::BinaryOp(binop, x, y) => {
                format!("{} {} {}", x.fmt_with_ctx(ctx), binop, y.fmt_with_ctx(ctx))
            }
            Rvalue::Discriminant(p) => {
                format!("@discriminant({})", p.fmt_with_ctx(ctx),)
            }
            Rvalue::Aggregate(kind, ops) => {
                let ops_s: Vec<String> = ops.iter().map(|op| op.fmt_with_ctx(ctx)).collect();
                match kind {
                    AggregateKind::Adt(def_id, variant_id, _) => {
                        match def_id {
                            TypeId::Tuple => format!("({})", ops_s.join(", ")),
                            TypeId::Assumed(_) => unreachable!(),
                            TypeId::Adt(def_id) => {
                                // Format every field
                                let mut fields = vec![];
                                for (i, op) in ops.iter().enumerate() {
                                    let field_id = FieldId::Id::new(i);
                                    let field_name =
                                        ctx.format_object((*def_id, *variant_id, field_id));
                                    fields.push(format!(
                                        "{}: {}",
                                        field_name,
                                        op.fmt_with_ctx(ctx)
                                    ));
                                }

                                let variant = match variant_id {
                                    None => ctx.format_object(*def_id),
                                    Some(variant_id) => ctx.format_object((*def_id, *variant_id)),
                                };
                                format!("{} {{ {} }}", variant, fields.join(", "))
                            }
                        }
                    }
                    AggregateKind::Array(_, len) => {
                        format!("[{}; {}]", ops_s.join(", "), len.fmt_with_ctx(ctx))
                    }
                    AggregateKind::Closure(fn_id) => {
                        format!("{}", ctx.format_object(*fn_id))
                    }
                }
            }
            Rvalue::Global(gid) => ctx.format_object(*gid),
            Rvalue::Len(place, ..) => format!("len({})", place.fmt_with_ctx(ctx)),
            Rvalue::Repeat(op, _ty, cg) => {
                format!("[{}; {}]", op.fmt_with_ctx(ctx), cg.fmt_with_ctx(ctx))
            }
        }
    }
}

impl std::fmt::Display for Rvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

// Derive two implementations at once: one which uses shared borrows, and one
// which uses mutable borrows.
// Generates the traits: `SharedExprVisitor` and `MutExprVisitor`.
make_generic_in_borrows! {

/// A visitor for expressions.
///
/// TODO: implement macros to automatically derive visitors.
pub trait ExprVisitor: crate::types::TypeVisitor {
    fn visit_place(&mut self, p: &Place) {
        self.visit_var_id(&p.var_id);
        self.visit_projection(&p.projection);
    }

    fn visit_var_id(&mut self, _: &VarId::Id) {}

    fn visit_projection(&mut self, p: &Projection) {
        for pe in p.iter() {
            self.visit_projection_elem(pe)
        }
    }

    fn default_visit_projection_elem(&mut self, pe: &ProjectionElem) {
        match pe {
            ProjectionElem::Deref => self.visit_deref(),
            ProjectionElem::DerefBox => self.visit_deref_box(),
            ProjectionElem::DerefRawPtr => self.visit_deref_raw_ptr(),
            ProjectionElem::Field(proj_kind, fid) => self.visit_projection_field(proj_kind, fid),
            ProjectionElem::Index(i, _) => self.visit_var_id(i),
        }
    }

    fn visit_projection_elem(&mut self, pe: &ProjectionElem) {
        self.default_visit_projection_elem(pe)
    }

    fn visit_deref(&mut self) {}
    fn visit_deref_box(&mut self) {}
    fn visit_deref_raw_ptr(&mut self) {}
    fn visit_projection_field(&mut self, _: &FieldProjKind, _: &FieldId::Id) {}

    fn default_visit_operand(&mut self, o: &Operand) {
        match o {
            Operand::Copy(p) => self.visit_copy(p),
            Operand::Move(p) => self.visit_move(p),
            Operand::Const(cv) => self.visit_operand_const(cv),
        }
    }

    fn visit_operand(&mut self, o: &Operand) {
        self.default_visit_operand(o)
    }

    fn visit_copy(&mut self, p: &Place) {
        self.visit_place(p)
    }

    fn visit_move(&mut self, p: &Place) {
        self.visit_place(p)
    }

    fn visit_operand_const(&mut self, op: &ConstantExpr) {
        self.visit_constant_expr(op);
    }

    fn visit_constant_expr(&mut self, expr: &ConstantExpr) {
        self.visit_ty(&expr.ty);
        self.visit_raw_constant_expr(&expr.value);
    }

    fn visit_raw_constant_expr(&mut self, expr: &RawConstantExpr) {
        self.default_visit_raw_constant_expr(expr)
    }

    fn default_visit_raw_constant_expr(&mut self, expr: &RawConstantExpr) {
        use RawConstantExpr::*;
        match expr {
            Literal(lit) => self.visit_literal(lit),
            Adt(oid, ops) => self.visit_constant_expr_adt(oid, ops),
            Global(id) => self.visit_global_decl_id(id),
            TraitConst(trait_ref, generics, _name) => {
                self.visit_trait_ref(trait_ref);
                self.visit_generic_args(generics);
            }
            Ref(cv) => self.visit_constant_expr(cv),
            Var(id) => self.visit_const_generic_var_id(id),
            FnPtr(f) => {
                self.visit_fn_ptr(f);
            }
        }
    }

    fn visit_constant_expr_adt(&mut self, _oid: &Option<VariantId::Id>, ops: &Vec<ConstantExpr>) {
        for op in ops {
            self.visit_constant_expr(op)
        }
    }

    fn default_visit_rvalue(&mut self, rv: &Rvalue) {
        match rv {
            Rvalue::Use(o) => self.visit_use(o),
            Rvalue::Ref(p, bkind) => self.visit_ref(p, bkind),
            Rvalue::UnaryOp(op, o1) => self.visit_unary_op(op, o1),
            Rvalue::BinaryOp(op, o1, o2) => self.visit_binary_op(op, o1, o2),
            Rvalue::Discriminant(p) => self.visit_discriminant(p),
            Rvalue::Aggregate(kind, ops) => self.visit_aggregate(kind, ops),
            Rvalue::Global(gid) => self.visit_global(gid),
            Rvalue::Len(p, ty, cg) => self.visit_len(p, ty, cg),
            Rvalue::Repeat(op, ty, cg) => self.visit_repeat(op, ty, cg),
        }
    }

    fn visit_rvalue(&mut self, o: &Rvalue) {
        self.default_visit_rvalue(o)
    }

    fn visit_use(&mut self, o: &Operand) {
        self.visit_operand(o)
    }

    fn visit_ref(&mut self, p: &Place, _: &BorrowKind) {
        self.visit_place(p)
    }

    fn visit_unary_op(&mut self, unop: &UnOp, o1: &Operand) {
        match unop {
            UnOp::Not | UnOp::Neg | UnOp::Cast(CastKind::Integer(_, _)) => (),
            UnOp::Cast(CastKind::FnPtr(src, tgt)) => {
                self.visit_ty(src);
                self.visit_ty(tgt);
            }
            UnOp::ArrayToSlice(_, ty, cg) => {
                self.visit_ty(ty);
                self.visit_const_generic(cg);
            }
        }
        self.visit_operand(o1)
    }

    fn visit_binary_op(&mut self, _: &BinOp, o1: &Operand, o2: &Operand) {
        self.visit_operand(o1);
        self.visit_operand(o2);
    }

    fn visit_discriminant(&mut self, p: &Place) {
        self.visit_place(p)
    }

    fn visit_aggregate(&mut self, ak: &AggregateKind, ops: &Vec<Operand>) {
        self.visit_aggregate_kind(ak);
        for o in ops {
            self.visit_operand(o)
        }
    }

    fn visit_aggregate_kind(&mut self, ak: &AggregateKind) {
        use AggregateKind::*;
        // We could generalize and introduce auxiliary functions for
        // the various cases - this is not necessary for now
        match ak {
            Adt(adt_id, _, generics) => {
                self.visit_type_id(adt_id);
                self.visit_generic_args(generics);
            }
            Array(ty, cg) => {
                self.visit_ty(ty);
                self.visit_const_generic(cg);
            }
            Closure(fn_id) => self.visit_fun_decl_id(fn_id),
        }
    }

    fn visit_global(&mut self, _: &GlobalDeclId::Id) {}

    fn visit_len(&mut self, p: &Place, ty: &Ty, cg: &Option<ConstGeneric>) {
        self.visit_place(p);
        self.visit_ty(ty);
        match cg {
            Some(cg) => self.visit_const_generic(cg),
            None => (),
        }
    }

    fn visit_repeat(&mut self, op: &Operand, ty: &Ty, cg: &ConstGeneric) {
        self.visit_operand(op);
        self.visit_ty(ty);
        self.visit_const_generic(cg);
    }

    fn visit_call(&mut self, c: &Call) {
        let Call {
            func,
            args,
            dest,
        } = c;
        self.visit_fn_operand(func);
        for o in args {
            self.visit_operand(o);
        }
        self.visit_place(dest);
    }

    fn visit_fn_ptr(&mut self, fn_ptr: &FnPtr) {
        let FnPtr { func, generics, trait_and_method_generic_args } = fn_ptr;
        self.visit_fun_id_or_trait_ref(func);
        self.visit_generic_args(generics);
        match trait_and_method_generic_args {
            None => (),
            Some(generics) => {
                self.visit_generic_args(generics);
            }
        }
    }

    fn visit_fn_operand(&mut self, fn_op: &FnOperand) {
        match fn_op {
            FnOperand::Regular(func) => self.visit_fn_ptr(func),
            FnOperand::Move(p) => self.visit_place(p),
        }
    }

    fn visit_fun_id(&mut self, fun_id: &FunId) {
        match fun_id {
            FunId::Regular(fid) => self.visit_fun_decl_id(fid),
            FunId::Assumed(aid) => self.visit_assumed_fun_id(aid),
        }
    }

    fn visit_fun_id_or_trait_ref(&mut self, fun_id: &FunIdOrTraitMethodRef) {
        use FunIdOrTraitMethodRef::*;
        match fun_id {
            Fun(fun_id) => self.visit_fun_id(fun_id),
            Trait(trait_ref, method_id, fun_decl_id) => {
                self.visit_trait_ref(trait_ref);
                self.visit_trait_method_name(method_id);
                self.visit_fun_decl_id(fun_decl_id);
            }
        }
    }

    fn visit_trait_method_name(&mut self, _: &TraitItemName) {}

    fn visit_fun_decl_id(&mut self, _: &FunDeclId::Id) {}
    fn visit_assumed_fun_id(&mut self, _: &AssumedFunId) {}
}

} // make_generic_in_borrows
