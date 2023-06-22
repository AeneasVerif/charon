//! LLBC
//!
//! MIR code where we have rebuilt the control-flow (`if ... then ... else ...`,
//! `while ...`, ...).
//!
//! Also note that we completely break the definitions Statement and Terminator
//! from MIR to use Statement only.

#![allow(dead_code)]
use crate::expressions::*;
pub use crate::llbc_ast_utils::*;
use crate::meta::Meta;
use crate::types::*;
use crate::ullbc_ast::*;
pub use crate::ullbc_ast::{CtxNames, FunDeclId, GlobalDeclId, Var};
use crate::values::*;
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantIndexArity, VariantName};
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct Assert {
    pub cond: Operand,
    pub expected: bool,
}

/// TODO: factor out with [Rvalue]
#[derive(Debug, Clone, Serialize)]
pub struct Call {
    pub func: FunId,
    /// Technically this is useless, but we still keep it because we might
    /// want to introduce some information (and the way we encode from MIR
    /// is as simple as possible - and in MIR we also have a vector of erased
    /// regions).
    pub region_args: Vec<ErasedRegion>,
    pub type_args: Vec<ETy>,
    pub args: Vec<Operand>,
    pub dest: Place,
}

/// A raw statement: a statement without meta data.
#[derive(Debug, Clone, EnumIsA, EnumToGetters, EnumAsGetters, Serialize)]
pub enum RawStatement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId::Id),
    Drop(Place),
    Assert(Assert),
    Call(Call),
    /// Panic also handles "unreachable"
    Panic,
    Return,
    /// Break to outer loops.
    /// The `usize` gives the index of the outer loop to break to:
    /// * 0: break to first outer loop (the current loop)
    /// * 1: break to second outer loop
    /// * ...
    Break(usize),
    /// Continue to outer loops.
    /// The `usize` gives the index of the outer loop to continue to:
    /// * 0: continue to first outer loop (the current loop)
    /// * 1: continue to second outer loop
    /// * ...
    Continue(usize),
    /// No-op.
    Nop,
    /// The left statement must NOT be a sequence.
    /// For instance, `(s0; s1); s2` is forbidden and should be rewritten
    /// to the semantically equivalent statement `s0; (s1; s2)`
    /// To ensure that, use [crate::llbc_ast_utils::new_sequence] to build sequences.
    Sequence(Box<Statement>, Box<Statement>),
    Switch(Switch),
    Loop(Box<Statement>),
}

#[derive(Debug, Clone, Serialize)]
pub struct Statement {
    pub meta: Meta,
    pub content: RawStatement,
}

#[derive(Debug, Clone, EnumIsA, EnumToGetters, EnumAsGetters, VariantName, VariantIndexArity)]
pub enum Switch {
    /// Gives the `if` block and the `else` block
    If(Operand, Box<Statement>, Box<Statement>),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    /// Also, we use a `Vec` to make sure the order of the switch
    /// branches is preserved.
    ///
    /// Rk.: we use a vector of values, because some of the branches may
    /// be grouped together, like for the following code:
    /// ```text
    /// match e {
    ///   E::V1 | E::V2 => ..., // Grouped
    ///   E::V3 => ...
    /// }
    /// ```
    SwitchInt(
        Operand,
        IntegerTy,
        Vec<(Vec<ScalarValue>, Statement)>,
        Box<Statement>,
    ),
    /// A match over an ADT.
    ///
    /// The match statement is introduced in [crate::remove_read_discriminant]
    /// (whenever we find a discriminant read, we merge it with the subsequent
    /// switch into a match)
    Match(Place, Vec<(Vec<VariantId::Id>, Statement)>, Box<Statement>),
}

pub type ExprBody = GExprBody<Statement>;

pub type FunDecl = GFunDecl<Statement>;
pub type FunDecls = FunDeclId::Vector<FunDecl>;

pub type GlobalDecl = GGlobalDecl<Statement>;
pub type GlobalDecls = GlobalDeclId::Vector<GlobalDecl>;

/* A mutable visitor for the LLBC AST

   Remark: we can't call the "super" method when reimplementing a method
   (unlike what can be done in, say, OCaml). This makes imlementing visitors
   slightly awkward, and is the reason why we split some visit functions in two:
   a "standard" version to be overriden, and a "default" version which should
   not be overriden and gives access to the "super" method.

  TODO: split into several visitors, for Operand, etc., and make the AST
  visitor inherit from those traits.

  TODO: implement macros to automatically derive visitors
*/
pub trait AstMoveVisitor<T> {
    fn visit_statement(&mut self, st: &mut Statement) {
        self.visit_raw_statement(&mut st.content)
    }

    fn default_visit_raw_statement(&mut self, st: &mut RawStatement) {
        match st {
            RawStatement::Assign(p, rv) => {
                self.visit_assign(p, rv);
            }
            RawStatement::FakeRead(p) => {
                self.visit_fake_read(p);
            }
            RawStatement::SetDiscriminant(p, vid) => {
                self.visit_set_discriminant(p, vid);
            }
            RawStatement::Drop(p) => {
                self.visit_drop(p);
            }
            RawStatement::Assert(a) => {
                self.visit_assert(a);
            }
            RawStatement::Call(c) => {
                self.visit_call(c);
            }
            RawStatement::Panic => {
                self.visit_panic();
            }
            RawStatement::Return => self.visit_return(),
            RawStatement::Break(i) => {
                self.visit_break(i);
            }
            RawStatement::Continue(i) => {
                self.visit_continue(i);
            }
            RawStatement::Nop => self.visit_nop(),
            RawStatement::Sequence(st1, st2) => self.visit_sequence(st1, st2),
            RawStatement::Switch(s) => self.visit_switch(s),
            RawStatement::Loop(lp) => self.visit_loop(lp),
        }
    }

    fn visit_raw_statement(&mut self, st: &mut RawStatement) {
        self.default_visit_raw_statement(st);
    }

    fn visit_assign(&mut self, p: &mut Place, rv: &mut Rvalue) {
        self.visit_place(p);
        self.visit_rvalue(rv)
    }

    fn visit_fake_read(&mut self, p: &mut Place) {
        self.visit_place(p);
    }

    fn visit_set_discriminant(&mut self, p: &mut Place, _: &mut VariantId::Id) {
        self.visit_place(p);
    }

    fn visit_drop(&mut self, p: &mut Place) {
        self.visit_place(p);
    }

    fn visit_assert(&mut self, a: &mut Assert) {
        self.visit_operand(&mut a.cond);
    }

    fn visit_call(&mut self, c: &mut Call) {
        for o in &mut c.args {
            self.visit_operand(o);
        }
        self.visit_place(&mut c.dest);
    }

    fn visit_panic(&mut self) {}
    fn visit_return(&mut self) {}
    fn visit_break(&mut self, _: &mut usize) {}
    fn visit_continue(&mut self, _: &mut usize) {}
    fn visit_nop(&mut self) {}

    fn visit_sequence(&mut self, st1: &mut Statement, st2: &mut Statement) {
        self.visit_statement(st1);
        self.visit_statement(st2);
    }

    fn default_visit_switch(&mut self, s: &mut Switch) {
        match s {
            Switch::If(scrut, then_branch, else_branch) => {
                self.visit_if(scrut, then_branch, else_branch)
            }
            Switch::SwitchInt(scrut, int_ty, branches, otherwise) => {
                self.visit_switch_int(scrut, int_ty, branches, otherwise)
            }
            Switch::Match(scrut, branches, otherwise) => {
                self.visit_match(scrut, branches, otherwise)
            }
        }
    }

    fn visit_switch(&mut self, s: &mut Switch) {
        self.default_visit_switch(s)
    }

    fn visit_if(
        &mut self,
        scrut: &mut Operand,
        then_branch: &mut Statement,
        else_branch: &mut Statement,
    ) {
        self.visit_operand(scrut);
        self.visit_statement(then_branch);
        self.visit_statement(else_branch);
    }

    fn visit_switch_int(
        &mut self,
        scrut: &mut Operand,
        _: &mut IntegerTy,
        branches: &mut Vec<(Vec<ScalarValue>, Statement)>,
        otherwise: &mut Statement,
    ) {
        self.visit_operand(scrut);
        for (_, st) in branches {
            self.visit_statement(st);
        }
        self.visit_statement(otherwise);
    }

    fn visit_match(
        &mut self,
        scrut: &mut Place,
        branches: &mut Vec<(Vec<VariantId::Id>, Statement)>,
        otherwise: &mut Statement,
    ) {
        self.visit_place(scrut);
        for (_, st) in branches {
            self.visit_statement(st);
        }
        self.visit_statement(otherwise);
    }

    fn visit_loop(&mut self, lp: &mut Statement) {
        self.visit_statement(lp)
    }

    fn visit_place(&mut self, p: &mut Place) {
        self.visit_var_id(&mut p.var_id);
        self.visit_projection(&mut p.projection);
    }

    fn visit_var_id(&mut self, _: &mut VarId::Id) {}

    fn visit_projection(&mut self, p: &mut Projection) {
        for pe in p.iter_mut() {
            self.visit_projection_elem(pe)
        }
    }

    fn default_visit_projection_elem(&mut self, pe: &mut ProjectionElem) {
        match pe {
            ProjectionElem::Deref => self.visit_deref(),
            ProjectionElem::DerefBox => self.visit_deref_box(),
            ProjectionElem::DerefRawPtr => self.visit_deref_raw_ptr(),
            ProjectionElem::DerefPtrUnique => self.visit_deref_ptr_unique(),
            ProjectionElem::DerefPtrNonNull => self.visit_deref_ptr_non_null(),
            ProjectionElem::Field(proj_kind, fid) => self.visit_projection_field(proj_kind, fid),
            ProjectionElem::Offset(o) => self.visit_offset(o),
        }
    }

    fn visit_projection_elem(&mut self, pe: &mut ProjectionElem) {
        self.default_visit_projection_elem(pe)
    }

    fn visit_deref(&mut self) {}
    fn visit_deref_box(&mut self) {}
    fn visit_deref_raw_ptr(&mut self) {}
    fn visit_deref_ptr_unique(&mut self) {}
    fn visit_deref_ptr_non_null(&mut self) {}
    fn visit_projection_field(&mut self, _: &mut FieldProjKind, _: &mut FieldId::Id) {}
    fn visit_offset(&mut self, o: &mut Operand) {
        self.visit_operand(o)
    }

    fn default_visit_operand(&mut self, o: &mut Operand) {
        match o {
            Operand::Copy(p) => self.visit_copy(p),
            Operand::Move(p) => self.visit_move(p),
            Operand::Const(ety, cv) => self.visit_operand_const(ety, cv),
        }
    }

    fn visit_operand(&mut self, o: &mut Operand) {
        self.default_visit_operand(o)
    }

    fn visit_copy(&mut self, p: &mut Place) {
        self.visit_place(p)
    }

    fn visit_move(&mut self, p: &mut Place) {
        self.visit_place(p)
    }

    fn visit_operand_const(&mut self, _: &mut ETy, _: &mut OperandConstantValue) {}

    fn default_visit_rvalue(&mut self, rv: &mut Rvalue) {
        match rv {
            Rvalue::Use(o) => self.visit_use(o),
            Rvalue::Ref(p, bkind) => self.visit_ref(p, bkind),
            Rvalue::UnaryOp(op, o1) => self.visit_unary_op(op, o1),
            Rvalue::BinaryOp(op, o1, o2) => self.visit_binary_op(op, o1, o2),
            Rvalue::Discriminant(p) => self.visit_discriminant(p),
            Rvalue::Aggregate(kind, ops) => self.visit_aggregate(kind, ops),
            Rvalue::Global(gid) => self.visit_global(gid),
            Rvalue::Len(p) => self.visit_len(p),
        }
    }

    fn visit_rvalue(&mut self, o: &mut Rvalue) {
        self.default_visit_rvalue(o)
    }

    fn visit_use(&mut self, o: &mut Operand) {
        self.visit_operand(o)
    }

    fn visit_ref(&mut self, p: &mut Place, _: &mut BorrowKind) {
        self.visit_place(p)
    }

    fn visit_unary_op(&mut self, _: &mut UnOp, o1: &mut Operand) {
        self.visit_operand(o1)
    }

    fn visit_binary_op(&mut self, _: &mut BinOp, o1: &mut Operand, o2: &mut Operand) {
        self.visit_operand(o1);
        self.visit_operand(o2);
    }

    fn visit_discriminant(&mut self, p: &mut Place) {
        self.visit_place(p)
    }

    fn visit_aggregate(&mut self, _: &mut AggregateKind, ops: &mut Vec<Operand>) {
        for o in ops {
            self.visit_operand(o)
        }
    }

    fn visit_global(&mut self, _: &mut GlobalDeclId::Id) {}

    fn visit_len(&mut self, p: &mut Place) {
        self.visit_place(p)
    }
}
