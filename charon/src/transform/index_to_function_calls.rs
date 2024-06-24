//! Desugar array/slice index operations to function calls.

use derive_visitor::{DriveMut, VisitorMut};

use crate::expressions::{BorrowKind, Operand, Place, ProjectionElem, Rvalue};
use crate::gast::{Call, GenericArgs, Var};
use crate::ids::Vector;
use crate::llbc_ast::*;
use crate::meta::Span;
use crate::transform::TransformCtx;
use crate::types::*;
use crate::values::VarId;

use super::ctx::LlbcPass;

/// Visitor to transform the operands by introducing intermediate let
/// statements.
///
/// We explore the statements without diving into substatements, and in particular explore
/// the places and operands. Places always appear as destinations we are writing to.
/// While we explore the places/operands present in a statement, We temporarily
/// store the new statements inside the visitor. Once we've finished exploring
/// the statement, we insert those before the statement.
#[derive(VisitorMut)]
#[visitor(
    Statement(enter, exit),
    Place(enter),
    Operand(enter),
    Call(enter),
    FnOperand(enter),
    Rvalue(enter),
    RawStatement(enter),
    Switch(enter)
)]
struct Visitor<'a> {
    locals: &'a mut Vector<VarId, Var>,
    statements: Vec<Statement>,
    // When we encounter a place, we remember when a given place is accessed mutably in this
    // stack. Unfortunately this requires us to be very careful to catch all the cases where we
    // see places.
    place_mutability_stack: Vec<bool>,
    // Span information of the outer statement
    span: Option<Span>,
}

impl<'a> Visitor<'a> {
    fn fresh_var(&mut self, name: Option<String>, ty: Ty) -> VarId {
        self.locals.push_with(|index| Var { index, name, ty })
    }

    fn transform_place(&mut self, mut_access: bool, p: &mut Place) {
        // Explore the place from the **end** to the beginning
        let mut var_id = p.var_id;
        let mut proj = Vec::new();
        for pe in p.projection.clone().into_iter() {
            if let ProjectionElem::Index(arg_index, buf_ty) = pe {
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
                let buf_borrow_var = self.fresh_var(None, buf_borrow_ty);
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
                let elem_borrow_var = self.fresh_var(None, elem_borrow_ty);
                let arg_buf = Operand::Move(Place::new(buf_borrow_var));
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

    fn enter_place(&mut self, p: &mut Place) {
        // We intercept every traversal that would reach a place and push the correct mutability on
        // the stack. If we missed one this will panic.
        let mut_access = *self.place_mutability_stack.last().unwrap();
        self.transform_place(mut_access, p);
        self.place_mutability_stack.pop();
    }

    fn enter_operand(&mut self, op: &mut Operand) {
        match op {
            Operand::Move(_) => {
                self.place_mutability_stack.push(true);
            }
            Operand::Copy(_) => {
                self.place_mutability_stack.push(false);
            }
            Operand::Const(..) => {}
        }
    }

    fn enter_call(&mut self, _c: &mut Call) {
        self.place_mutability_stack.push(true);
    }

    fn enter_fn_operand(&mut self, fn_op: &mut FnOperand) {
        match fn_op {
            FnOperand::Regular(_) => {}
            FnOperand::Move(_) => {
                self.place_mutability_stack.push(true);
            }
        }
    }

    fn enter_rvalue(&mut self, rv: &mut Rvalue) {
        use Rvalue::*;
        match rv {
            Use(_) | UnaryOp(..) | BinaryOp(..) | Aggregate(..) | Global(..) | Repeat(..) => {}
            Ref(_, bkind) => match *bkind {
                BorrowKind::Mut | BorrowKind::TwoPhaseMut => {
                    self.place_mutability_stack.push(true);
                }
                BorrowKind::Shared | BorrowKind::Shallow => {
                    self.place_mutability_stack.push(false);
                }
            },
            Discriminant(..) | Len(..) => {
                // We access places, but those places are used to access
                // elements without mutating them
                self.place_mutability_stack.push(false);
            }
        }
    }

    fn enter_statement(&mut self, st: &mut Statement) {
        // Retrieve the span information
        self.span = Some(st.span);
        // As we explore this statement, we may collect extra statements to prepend to it.
        assert!(self.statements.is_empty());
    }

    fn exit_statement(&mut self, st: &mut Statement) {
        self.span = None;

        // Reparenthesize sequences we messed up while traversing.
        st.flatten();

        // We potentially collected statements to prepend to this one.
        let seq = std::mem::take(&mut self.statements);
        if !seq.is_empty() {
            take_mut::take(st, |st| chain_statements(seq, st))
        }
    }

    fn enter_raw_statement(&mut self, st: &mut RawStatement) {
        use RawStatement::*;
        // The match is explicit on purpose: we want to make sure we intercept changes
        match st {
            Sequence(..) | Abort(..) | Return | Break(..) | Continue(..) | Nop | Switch(..)
            | Loop(..) | Error(..) | Assert(..) | Call(..) => {}
            FakeRead(_) => {
                self.place_mutability_stack.push(false);
            }
            Assign(..) | SetDiscriminant(..) | Drop(..) => {
                self.place_mutability_stack.push(true);
            }
        }
    }

    fn enter_switch(&mut self, s: &mut Switch) {
        match s {
            Switch::If(..) | Switch::SwitchInt(..) => {}
            Switch::Match(..) => {
                self.place_mutability_stack.push(false);
            }
        }
    }
}

pub struct Transform;

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
impl LlbcPass for Transform {
    fn transform_body(&self, _ctx: &mut TransformCtx<'_>, b: &mut ExprBody) {
        let mut visitor = Visitor {
            locals: &mut b.locals,
            statements: Vec::new(),
            place_mutability_stack: Vec::new(),
            span: None,
        };
        b.body.drive_mut(&mut visitor);
    }
}
