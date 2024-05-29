//! Desugar array/slice index operations to function calls.

use crate::expressions::{BorrowKind, MutExprVisitor, Operand, Place, ProjectionElem, Rvalue};
use crate::formatter::{Formatter, IntoFormatter};
use crate::gast::{Call, GenericArgs, Var};
use crate::ids::Vector;
use crate::llbc_ast::*;
use crate::meta::Span;
use crate::translate_ctx::TransformCtx;
use crate::types::*;
use crate::values::VarId;
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
    locals: &'a mut Vector<VarId, Var>,
    statements: Vec<Statement>,
    /// Span information of the outer statement
    span: Option<Span>,
}

impl<'a> Transform<'a> {
    fn fresh_var(&mut self, name: Option<String>, ty: Ty) -> VarId {
        self.locals.push_with(|index| Var { index, name, ty })
    }

    fn visit_transform_place(&mut self, mut_access: bool, p: &mut Place) {
        // Explore the place from the **end** to the beginning
        let mut var_id = p.var_id;
        let mut proj = Vec::new();
        for pe in p.projection.clone().into_iter() {
            if pe.is_index() {
                let (operand, buf_ty) = pe.to_index();
                let index_var_id = match &operand {
                    // If we have a place, just use directly its identifier
                    Operand::Copy(place) => place.var_id,
                    // Otherwise, we push a new local and an `Assign` statement
                    Operand::Const(ConstantExpr { ty, .. }) => {
                        let var_id = self.fresh_var(None, ty.clone());
                        let place = Place {
                            var_id,
                            projection: vec![],
                        };
                        let content = RawStatement::Assign(place, Rvalue::Use(operand));
                        let span = self.span.unwrap();
                        self.statements.push(Statement { span, content });
                        var_id
                    }
                    Operand::Move(_) => {
                        panic!("Unexpected `Oparand::Move` on a `ProjectionElem::Index`")
                    }
                };
                let (id, generics) = buf_ty.as_adt();
                let cgs: Vec<ConstGeneric> = generics.const_generics.to_vec();
                let index_id = match id.as_assumed() {
                    AssumedTy::Array => {
                        if mut_access {
                            AssumedFunId::ArrayIndexMut
                        } else {
                            AssumedFunId::ArrayIndexShared
                        }
                    }
                    AssumedTy::Slice => {
                        if mut_access {
                            AssumedFunId::SliceIndexMut
                        } else {
                            AssumedFunId::SliceIndexShared
                        }
                    }
                    _ => unreachable!(),
                };

                let elem_ty = generics.types[0].clone();

                // We need to introduce intermediate statements (and
                // temporary variables)
                let (ref_kind, borrow_kind) = if mut_access {
                    (RefKind::Mut, BorrowKind::Mut)
                } else {
                    (RefKind::Shared, BorrowKind::Shared)
                };

                // Push the statement:
                //`tmp0 = & proj`
                let buf_borrow_ty = Ty::Ref(Region::Erased, Box::new(buf_ty), ref_kind);
                let buf_borrow_var = self.fresh_var(Option::None, buf_borrow_ty);
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
                    span: self.span.unwrap(),
                };
                self.statements.push(borrow_st);

                // Push the statement:
                // `tmp1 = Array{Mut,Shared}Index(move tmp0, copy i)`
                let elem_borrow_ty = Ty::Ref(Region::Erased, Box::new(elem_ty.clone()), ref_kind);
                let elem_borrow_var = self.fresh_var(Option::None, elem_borrow_ty);
                let arg_buf = Operand::Move(Place::new(buf_borrow_var));
                let arg_index = Operand::Copy(Place::new(index_var_id));
                let index_dest = Place::new(elem_borrow_var);
                let index_id = FunIdOrTraitMethodRef::mk_assumed(index_id);
                let generics = GenericArgs::new(vec![Region::Erased], vec![elem_ty], cgs, vec![]);
                let func = FnOperand::Regular(FnPtr {
                    func: index_id,
                    generics,
                });
                let index_call = Call {
                    func,
                    args: vec![arg_buf, arg_index],
                    dest: index_dest,
                };
                let index_st = Statement {
                    content: RawStatement::Call(index_call),
                    span: self.span.unwrap(),
                };
                self.statements.push(index_st);

                // Update the variable in the place, and the projection
                var_id = elem_borrow_var;
                proj = vec![ProjectionElem::Deref];
            } else {
                // Just stack the projection element
                proj.push(pe);
            }
        }

        // Update the current place
        *p = Place {
            var_id,
            projection: proj,
        }
    }
}

impl<'a> MutTypeVisitor for Transform<'a> {}

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
            Use(_) | UnaryOp(..) | BinaryOp(..) | Aggregate(..) | Global(..) | Repeat(..) => {
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
            Discriminant(p, _) | Len(p, _, _) => {
                // We access places, but those places are used to access
                // elements without mutating them
                self.visit_transform_place(false, p);
            }
        }
    }
}

impl<'a> MutAstVisitor for Transform<'a> {
    fn spawn(&mut self, visitor: &mut dyn FnMut(&mut Self)) {
        #[allow(clippy::mem_replace_with_default)]
        let statements = replace(&mut self.statements, Vec::new());
        visitor(self);
        // Make sure we didn't update the vector of statements
        assert!(self.statements.is_empty());
        let _ = replace(&mut self.statements, statements);
    }

    fn merge(&mut self) {}

    fn visit_statement(&mut self, st: &mut Statement) {
        // Retrieve the span information
        self.span = Option::Some(st.span);
        self.visit_raw_statement(&mut st.content);
        self.span = Option::None;
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

fn transform_st(locals: &mut Vector<VarId, Var>, s: &mut Statement) -> Option<Vec<Statement>> {
    // Explore the places/operands
    let mut visitor = Transform {
        locals,
        statements: Vec::new(),
        span: Option::None,
    };
    visitor.visit_statement(s);

    // Return the statements to insert before the current one
    Some(visitor.statements)
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
///   tmp1 = ArrayIndexMut(move p, i)
///   ... *tmp1 ...
///
///   // If array and non-mutable access:
///   ... p[i] ...
///      ~~>
///   tmp0 := & p
///   tmp1 := ArrayIndexShared(move tmp0, i)
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
///   tmp1 : &u32 = ArrayIndexShared(move tmp0, i)
///   y : u32 = copy (*tmp1)
///
///   // x : &[T; N]
///   y : &T = & (*x)[i]
///      ~~>
///   tmp0 : & [T; N] := & (*x)
///   tmp1 : &T = ArrayIndexShared(move tmp0, i)
///   y : &T = & (*tmp1)
///
///   // x : [u32; N]
///   y = &mut x[i]
///      ~~>
///   tmp0 : &mut [u32; N] := &mut x
///   tmp1 : &mut u32 := ArrayIndexMut(move tmp0, i)
///   y = &mut (*tmp)
///
///   // When using an index on the lhs:
///   // y : [T; N]
///   y[i] = x
///      ~~>
///   tmp0 : &mut [T; N] := &mut y;
///   tmp1 : &mut T = ArrayIndexMut(move y, i)
///   *tmp1 = x
/// ```
pub fn transform(ctx: &mut TransformCtx) {
    ctx.iter_structured_bodies(|ctx, name, b| {
        let ctx = ctx.into_fmt();
        trace!(
            "# About to transform array/slice index operations to function calls: {}:\n{}",
            name.fmt_with_ctx(&ctx),
            ctx.format_object(&*b)
        );
        let body = &mut b.body;
        let locals = &mut b.locals;

        let mut tr = |s: &mut Statement| transform_st(locals, s);
        body.transform(&mut tr);
        trace!(
            "# After transforming array/slice index operations to function calls: {}:\n{}",
            name.fmt_with_ctx(&ctx),
            ctx.format_object(&*b)
        );
    });
}
