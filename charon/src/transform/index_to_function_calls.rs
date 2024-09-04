//! Desugar array/slice index operations to function calls.

use std::mem;

use derive_visitor::{DriveMut, VisitorMut};

use crate::ids::Vector;
use crate::llbc_ast::*;
use crate::transform::TransformCtx;

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
        use ProjectionElem::*;
        // Explore the place from the **end** to the beginning
        for pe in mem::take(&mut p.projection) {
            let (Index { ty, .. } | Subslice { ty, .. }) = &pe else {
                // Just stack the projection element
                p.projection.push(pe);
                continue;
            };

            let Ty::Adt(TypeId::Builtin(builtin_ty), generics) = ty else {
                unreachable!()
            };

            // The built-in function to call.
            let indexing_function = {
                let builtin_fun = BuiltinFunId::Index(BuiltinIndexOp {
                    is_array: matches!(builtin_ty, BuiltinTy::Array),
                    mutability: RefKind::mutable(mut_access),
                    is_range: matches!(pe, Subslice { .. }),
                });
                // Same generics as the array/slice type, except for the extra lifetime.
                let generics = GenericArgs {
                    regions: vec![Region::Erased].into(),
                    ..generics.clone()
                };
                FnOperand::Regular(FnPtr {
                    func: FunIdOrTraitMethodRef::mk_builtin(builtin_fun),
                    generics,
                })
            };

            let input_ty = Ty::Ref(
                Region::Erased,
                Box::new(ty.clone()),
                RefKind::mutable(mut_access),
            );

            let output_ty = {
                let elem_ty = generics.types[0].clone();
                let output_inner_ty = if matches!(pe, Index { .. }) {
                    elem_ty
                } else {
                    Ty::Adt(
                        TypeId::Builtin(BuiltinTy::Slice),
                        GenericArgs::new_from_types(vec![elem_ty].into()),
                    )
                };
                Ty::Ref(
                    Region::Erased,
                    Box::new(output_inner_ty),
                    RefKind::mutable(mut_access),
                )
            };

            // Push the statement:
            //`tmp0 = &{mut}p`
            let input_var = {
                let input_var = self.fresh_var(None, input_ty);
                let borrow_st = RawStatement::Assign(
                    Place::new(input_var),
                    Rvalue::Ref(p.clone(), BorrowKind::mutable(mut_access)),
                );
                let borrow_st = Statement {
                    content: borrow_st,
                    span: self.span.unwrap(),
                };
                self.statements.push(borrow_st);
                input_var
            };

            // Construct the arguments to pass to the indexing function.
            let mut args = vec![Operand::Move(Place::new(input_var))];
            if let Subslice { from, .. } = &pe {
                args.push(from.clone());
            }
            let (last_arg, from_end) = match &pe {
                Index {
                    offset: x,
                    from_end,
                    ..
                }
                | Subslice {
                    to: x, from_end, ..
                } => (x.clone(), *from_end),
                _ => unreachable!(),
            };
            if from_end {
                let usize_ty = Ty::Literal(LiteralTy::Integer(IntegerTy::Usize));
                let len_var = self.fresh_var(None, usize_ty.clone());
                self.statements.push(Statement {
                    content: RawStatement::Assign(
                        Place::new(len_var),
                        Rvalue::Len(
                            p.clone(),
                            ty.clone(),
                            generics.const_generics.get(0.into()).cloned(),
                        ),
                    ),
                    span: self.span.unwrap(),
                });
                // `index_var = len(p) - last_arg`
                let index_var = self.fresh_var(None, usize_ty);
                self.statements.push(Statement {
                    content: RawStatement::Assign(
                        Place::new(index_var),
                        Rvalue::BinaryOp(BinOp::Sub, Operand::Copy(Place::new(len_var)), last_arg),
                    ),
                    span: self.span.unwrap(),
                });
                args.push(Operand::Copy(Place::new(index_var)));
            } else {
                args.push(last_arg);
            }

            // Call the indexing function:
            // `tmp1 = {Array,Slice}{Mut,Shared}{Index,SubSlice}(move tmp0, <other args>)`
            let output_var = {
                let output_var = self.fresh_var(None, output_ty);
                let index_call = Call {
                    func: indexing_function,
                    args,
                    dest: Place::new(output_var),
                };
                self.statements.push(Statement {
                    content: RawStatement::Call(index_call),
                    span: self.span.unwrap(),
                });
                output_var
            };

            // Update the place.
            *p = Place {
                var_id: output_var,
                projection: vec![ProjectionElem::Deref],
            };
        }
    }
}

/// The visitor methods.
impl<'a> Visitor<'a> {
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
            Use(_) | NullaryOp(..) | UnaryOp(..) | BinaryOp(..) | Aggregate(..) | Global(..)
            | GlobalRef(..) | Repeat(..) | ShallowInitBox(..) => {}
            RawPtr(_, ptrkind) => match *ptrkind {
                RefKind::Mut => {
                    self.place_mutability_stack.push(true);
                }
                RefKind::Shared => {
                    self.place_mutability_stack.push(false);
                }
            },
            Ref(_, bkind) => match *bkind {
                // `UniqueImmutable` de facto gives mutable access and only shows up if there is
                // nested mutable access.
                BorrowKind::Mut | BorrowKind::TwoPhaseMut | BorrowKind::UniqueImmutable => {
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
