//! Desugar array/slice index operations to function calls.

#![allow(dead_code)]

use crate::expressions::{BorrowKind, MutExprVisitor, Operand, Place, ProjectionElem, Rvalue};
use crate::gast::{Call, Var};
use crate::llbc_ast::{
    iter_function_bodies, iter_global_bodies, AssumedFunId, CtxNames, FunDecls, FunId, GlobalDecls,
    MutAstVisitor, RawStatement, Statement, Switch,
};
use crate::meta::Meta;
use crate::types::{AssumedTy, ConstGeneric, ErasedRegion, RefKind, Ty};
use crate::values::VarId;
use im::Vector;
use std::mem::replace;

/// Visitor to transform the operands by introducing intermediate let
/// statements.
///
/// We explore the statements without diving into substatements, and in particular explore
/// the places and operands. Places always appear as destinations we are writing to.
/// While we explore the places/operands present in a statement, We temporarily
/// store the new statements inside the visitor. Once we've finished exploring
/// the statement, we insert those before the statement.
struct Transform<'a> {
    locals: &'a mut VarId::Vector<Var>,
    statements: Vec<Statement>,
    /// Meta information of the outer statement
    meta: Option<Meta>,
}

impl<'a> Transform<'a> {
    fn visit_transform_place(&mut self, mut_access: bool, p: &mut Place) {
        // Explore the place from the **end** to the beginning
        let mut var_id = p.var_id;
        let mut proj = Vector::new();
        for pe in p.projection.clone().into_iter() {
            if pe.is_index() {
                let (index_var_id, buf_ty) = pe.to_index();

                let (id, _, tys, cgs) = buf_ty.as_adt();
                let cgs: Vec<ConstGeneric> = cgs.iter().cloned().collect();
                let index_id = match id.as_assumed() {
                    AssumedTy::Array => {
                        if mut_access {
                            AssumedFunId::ArrayMutIndex
                        } else {
                            AssumedFunId::ArraySharedIndex
                        }
                    }
                    AssumedTy::Slice => {
                        if mut_access {
                            AssumedFunId::SliceMutIndex
                        } else {
                            AssumedFunId::SliceSharedIndex
                        }
                    }
                    _ => unreachable!(),
                };

                let elem_ty = tys[0].clone();

                // We need to introduce intermediate statements (and
                // temporary variables)
                let (ref_kind, borrow_kind) = if mut_access {
                    (RefKind::Mut, BorrowKind::Mut)
                } else {
                    (RefKind::Shared, BorrowKind::Shared)
                };

                // Push the statement:
                //`tmp0 = & proj`
                let buf_borrow_ty = Ty::Ref(ErasedRegion::Erased, Box::new(buf_ty), ref_kind);
                let buf_borrow_var = self.locals.fresh_var(Option::None, buf_borrow_ty);
                let borrow_st = RawStatement::Assign(
                    Place::new(buf_borrow_var),
                    Rvalue::Ref(
                        Place {
                            var_id,
                            projection: proj,
                        },
                        borrow_kind,
                    ),
                );
                let borrow_st = Statement {
                    content: borrow_st,
                    meta: self.meta.unwrap(),
                };
                self.statements.push(borrow_st);

                // Push the statement:
                // `tmp1 = Array{Mut,Shared}Index(move tmp0, copy i)`
                let elem_borrow_ty =
                    Ty::Ref(ErasedRegion::Erased, Box::new(elem_ty.clone()), ref_kind);
                let elem_borrow_var = self.locals.fresh_var(Option::None, elem_borrow_ty);
                let arg_buf = Operand::Move(Place::new(buf_borrow_var));
                let arg_index = Operand::Copy(Place::new(index_var_id));
                let index_dest = Place {
                    var_id: elem_borrow_var,
                    projection: Vector::new(),
                };
                let index_id = FunId::Assumed(index_id);
                let index_call = Call {
                    func: index_id,
                    region_args: vec![ErasedRegion::Erased],
                    type_args: vec![elem_ty],
                    const_generic_args: cgs,
                    args: vec![arg_buf, arg_index],
                    dest: index_dest,
                };
                let index_st = Statement {
                    content: RawStatement::Call(index_call),
                    meta: self.meta.unwrap(),
                };
                self.statements.push(index_st);

                // Update the variable in the place, and the projection
                var_id = elem_borrow_var;
                proj = im::vector![ProjectionElem::Deref];
            } else {
                // Just stack the projection element
                proj.push_back(pe);
            }
        }

        // Update the current place
        *p = Place {
            var_id,
            projection: proj,
        }
    }
}

impl<'a> MutExprVisitor for Transform<'a> {
    fn visit_place(&mut self, p: &mut Place) {
        // By default, places are used to access elements to mutate them.
        // We intercept the places where it is not the case.
        let mut_access = true;
        self.visit_transform_place(mut_access, p);
    }

    fn visit_operand(&mut self, op: &mut Operand) {
        match op {
            Operand::Move(p) => self.visit_transform_place(true, p),
            Operand::Copy(p) => self.visit_transform_place(false, p),
            Operand::Const(..) => (),
        }
    }

    fn visit_rvalue(&mut self, rv: &mut Rvalue) {
        use Rvalue::*;
        match rv {
            Use(_) | UnaryOp(..) | BinaryOp(..) | Aggregate(..) | Global(..) => {
                // We don't access places here, only operands
                self.default_visit_rvalue(rv)
            }
            Ref(p, bkind) => {
                // Ref is special
                match *bkind {
                    BorrowKind::Mut | BorrowKind::TwoPhaseMut => {
                        self.visit_transform_place(true, p)
                    }
                    BorrowKind::Shared | BorrowKind::Shallow => {
                        self.visit_transform_place(false, p)
                    }
                }
            }
            Discriminant(p) | Len(p, _, _) => {
                // We access places, but those places are used to access
                // elements without mutating them
                self.visit_transform_place(false, p);
            }
        }
    }
}

impl<'a> MutAstVisitor for Transform<'a> {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        let statements = replace(&mut self.statements, Vec::new());
        visitor(self);
        // Make sure we didn't update the vector of statements
        assert!(self.statements.is_empty());
        let _ = replace(&mut self.statements, statements);
    }

    fn merge(&mut self) {}

    fn visit_statement(&mut self, st: &mut Statement) {
        // Retrieve the meta-information
        self.meta = Option::Some(st.meta);
        self.visit_raw_statement(&mut st.content);
        self.meta = Option::None;
    }

    fn visit_raw_statement(&mut self, st: &mut RawStatement) {
        use RawStatement::*;
        // The match is explicit on purpose: we want to make sure we intercept changes
        match st {
            Sequence(..) => {
                // Do nothing: we don't want to dive
            }
            FakeRead(p) => {
                self.visit_transform_place(false, p);
            }
            Assign(..) | SetDiscriminant(..) | Drop(..) | Assert(..) | Call(..) | Panic
            | Return | Break(..) | Continue(..) | Nop | Switch(..) | Loop(..) => {
                // Explore
                self.default_visit_raw_statement(st)
            }
        }
    }

    fn visit_switch(&mut self, s: &mut Switch) {
        match s {
            Switch::If(op, ..) | Switch::SwitchInt(op, ..) => self.visit_operand(op),
            Switch::Match(p, _, _) => {
                let mut_access = false;
                self.visit_transform_place(mut_access, p);
            }
        }
    }
}

fn transform_st(locals: &mut VarId::Vector<Var>, s: &mut Statement) -> Vec<Statement> {
    // Explore the places/operands
    let mut visitor = Transform {
        locals,
        statements: Vec::new(),
        meta: Option::None,
    };
    visitor.visit_statement(s);

    // Return the statements to insert before the current one
    visitor.statements
}

/// We do the following.
///
/// If `p` is a projection (for instance: `var`, `*var`, `var.f`, etc.), we
/// detect:
/// - whether it operates on a slice or an array (we keep track of the types)
/// - whether the access might mutate the value or not (it is
///   the case if it is in a `move`, `&mut` or at the lhs of an assignment),
///   and do the following transformations
///
/// ```text
///   // If array and mutable access:
///   ... p[i] ...
///      ~~>
///   tmp0 = &mut p
///   tmp1 = ArrayMutIndex(move p, i)
///   ... *tmp1 ...
///
///   // If array and non-mutable access:
///   ... p[i] ...
///      ~~>
///   tmp0 := & p
///   tmp1 := ArraySharedIndex(move tmp0, i)
///   ... *tmp1 ...
///
///   // Omitting the slice cases, which are similar
/// ```
///
/// For instance, it leads to the following transformations:
/// ```text
///   // x : [u32; N]
///   y : u32 = copy x[i]
///      ~~>
///   tmp0 : & [u32; N] := &x
///   tmp1 : &u32 = ArraySharedIndex(move tmp0, i)
///   y : u32 = copy (*tmp1)
///
///   // x : &[T; N]
///   y : &T = & (*x)[i]
///      ~~>
///   tmp0 : & [T; N] := & (*x)
///   tmp1 : &T = ArraySharedIndex(move tmp0, i)
///   y : &T = & (*tmp1)
///
///   // x : [u32; N]
///   y = &mut x[i]
///      ~~>
///   tmp0 : &mut [u32; N] := &mut x
///   tmp1 : &mut u32 := ArrayMutIndex(move tmp0, i)
///   y = &mut (*tmp)
///
///   // When using an index on the lhs:
///   // y : [T; N]
///   y[i] = x
///      ~~>
///   tmp0 : &mut [T; N] := &mut y;
///   tmp1 : &mut T = ArrayMutIndex(move y, i)
///   *tmp1 = x
/// ```
pub fn transform(fmt_ctx: &CtxNames<'_>, funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!(
            "# About to transform array/slice index operations to function calls: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
        let body = &mut b.body;
        let locals = &mut b.locals;

        let mut tr = |s: &mut Statement| transform_st(locals, s);
        body.transform(&mut tr);
        trace!(
            "# After transforming array/slice index operations to function calls: {name}:\n{}",
            b.fmt_with_ctx_names(fmt_ctx)
        );
    }
}
