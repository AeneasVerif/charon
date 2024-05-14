//! This file groups everything which is linked to implementations about [crate::expressions]
use crate::expressions::*;
use crate::gast::{AssumedFunId, Call, FnOperand, FunId, FunIdOrTraitMethodRef, TraitItemName};
use crate::types::*;
use crate::ullbc_ast::GlobalDeclId;
use crate::values::*;
use macros::make_generic_in_borrows;
use std::vec::Vec;

impl Place {
    pub fn new(var_id: VarId) -> Place {
        Place {
            var_id,
            projection: Vec::new(),
        }
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

    fn visit_var_id(&mut self, _: &VarId) {}

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
    fn visit_projection_field(&mut self, _: &FieldProjKind, _: &FieldId) {}

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
            Global(id, generics) => {
                self.visit_global_decl_id(id);
                self.visit_generic_args(generics);
            }
            TraitConst(trait_ref, _name) => {
                self.visit_trait_ref(trait_ref);
            }
            Ref(cv) => self.visit_constant_expr(cv),
            Var(id) => self.visit_const_generic_var_id(id),
            FnPtr(f) => {
                self.visit_fn_ptr(f);
            }
        }
    }

    fn visit_constant_expr_adt(&mut self, _oid: &Option<VariantId>, ops: &Vec<ConstantExpr>) {
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
            Rvalue::Discriminant(p, adt_id) => self.visit_discriminant(p, adt_id),
            Rvalue::Aggregate(kind, ops) => self.visit_aggregate(kind, ops),
            Rvalue::Global(gid, generics) => {
                self.visit_global(gid);
                self.visit_generic_args(generics);
            }
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
            UnOp::Not | UnOp::Neg | UnOp::Cast(CastKind::Scalar(_, _)) => (),
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

    fn visit_discriminant(&mut self, p: &Place, adt_id: &TypeDeclId) {
        self.visit_place(p);
        self.visit_type_decl_id(adt_id);
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
            Closure(fn_id, generics) => {
                self.visit_fun_decl_id(fn_id);
                self.visit_generic_args(generics);
            }
        }
    }

    fn visit_global(&mut self, _: &GlobalDeclId) {}

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
        let FnPtr { func, generics } = fn_ptr;
        self.visit_fun_id_or_trait_ref(func);
        self.visit_generic_args(generics);
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
    fn visit_assumed_fun_id(&mut self, _: &AssumedFunId) {}
}

} // make_generic_in_borrows
