//! Desugar array/slice index operations to function calls.

use derive_visitor::{DriveMut, VisitorMut};

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
#[visitor(Place(exit), Operand, Call, FnOperand, Rvalue)]
struct Visitor<'a> {
    locals: &'a mut Locals,
    statements: Vec<Statement>,
    // When we encounter a place, we remember when a given place is accessed mutably in this
    // stack. Unfortunately this requires us to be very careful to catch all the cases where we
    // see places.
    place_mutability_stack: Vec<bool>,
    // Span information of the statement
    span: Span,
}

impl<'a> Visitor<'a> {
    fn fresh_var(&mut self, name: Option<String>, ty: Ty) -> Place {
        self.locals.new_var(name, ty)
    }

    fn transform_place(&mut self, mut_access: bool, place: &mut Place) {
        use ProjectionElem::*;
        let Some((subplace, pe @ (Index { .. } | Subslice { .. }))) = place.as_projection() else {
            return;
        };
        let TyKind::Adt(TypeId::Builtin(builtin_ty), generics) = subplace.ty().kind() else {
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

        let input_ty = TyKind::Ref(
            Region::Erased,
            subplace.ty().clone(),
            RefKind::mutable(mut_access),
        )
        .into_ty();

        let elem_ty = generics.types[0].clone();
        let output_inner_ty = if matches!(pe, Index { .. }) {
            elem_ty
        } else {
            TyKind::Adt(
                TypeId::Builtin(BuiltinTy::Slice),
                GenericArgs::new_from_types(vec![elem_ty].into()),
            )
            .into_ty()
        };
        let output_ty = {
            TyKind::Ref(
                Region::Erased,
                output_inner_ty.clone(),
                RefKind::mutable(mut_access),
            )
            .into_ty()
        };

        // Push the statement:
        //`tmp0 = &{mut}p`
        let input_var = {
            let input_var = self.fresh_var(None, input_ty);
            let kind = RawStatement::Assign(
                input_var.clone(),
                Rvalue::Ref(subplace.clone(), BorrowKind::mutable(mut_access)),
            );
            self.statements.push(Statement::new(self.span, kind));
            input_var
        };

        // Construct the arguments to pass to the indexing function.
        let mut args = vec![Operand::Move(input_var)];
        if let Subslice { from, .. } = &pe {
            args.push(from.as_ref().clone());
        }
        let (last_arg, from_end) = match &pe {
            Index {
                offset: x,
                from_end,
                ..
            }
            | Subslice {
                to: x, from_end, ..
            } => (x.as_ref().clone(), *from_end),
            _ => unreachable!(),
        };
        if from_end {
            let usize_ty = TyKind::Literal(LiteralTy::Integer(IntegerTy::Usize)).into_ty();
            let len_var = self.fresh_var(None, usize_ty.clone());
            let kind = RawStatement::Assign(
                len_var.clone(),
                Rvalue::Len(
                    subplace.clone(),
                    subplace.ty().clone(),
                    generics.const_generics.get(0.into()).cloned(),
                ),
            );
            self.statements.push(Statement::new(self.span, kind));
            // `index_var = len(p) - last_arg`
            let index_var = self.fresh_var(None, usize_ty);
            let kind = RawStatement::Assign(
                index_var.clone(),
                Rvalue::BinaryOp(BinOp::Sub, Operand::Copy(len_var), last_arg),
            );
            self.statements.push(Statement::new(self.span, kind));
            args.push(Operand::Copy(index_var));
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
                dest: output_var.clone(),
            };
            let kind = RawStatement::Call(index_call);
            self.statements.push(Statement::new(self.span, kind));
            output_var
        };

        // Update the place.
        *place = output_var.project(ProjectionElem::Deref, output_inner_ty);
    }
}

/// The visitor methods.
impl<'a> Visitor<'a> {
    /// We explore places from the inside-out.
    fn exit_place(&mut self, place: &mut Place) {
        // We intercept every traversal that would reach a place and push the correct mutability on
        // the stack.
        let mut_access = *self.place_mutability_stack.last().unwrap();
        self.transform_place(mut_access, place);
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

    fn exit_operand(&mut self, op: &mut Operand) {
        match op {
            Operand::Move(_) | Operand::Copy(_) => {
                self.place_mutability_stack.pop();
            }
            Operand::Const(..) => {}
        }
    }

    fn enter_call(&mut self, _c: &mut Call) {
        self.place_mutability_stack.push(true);
    }

    fn exit_call(&mut self, _c: &mut Call) {
        self.place_mutability_stack.pop();
    }

    fn enter_fn_operand(&mut self, fn_op: &mut FnOperand) {
        match fn_op {
            FnOperand::Regular(_) => {}
            FnOperand::Move(_) => {
                self.place_mutability_stack.push(true);
            }
        }
    }

    fn exit_fn_operand(&mut self, fn_op: &mut FnOperand) {
        match fn_op {
            FnOperand::Regular(_) => {}
            FnOperand::Move(_) => {
                self.place_mutability_stack.pop();
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

    fn exit_rvalue(&mut self, rv: &mut Rvalue) {
        use Rvalue::*;
        match rv {
            Use(_) | NullaryOp(..) | UnaryOp(..) | BinaryOp(..) | Aggregate(..) | Global(..)
            | GlobalRef(..) | Repeat(..) | ShallowInitBox(..) => {}
            RawPtr(..) | Ref(..) | Discriminant(..) | Len(..) => {
                self.place_mutability_stack.pop();
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
    fn transform_body(&self, _ctx: &mut TransformCtx, b: &mut ExprBody) {
        b.body.transform(&mut |st: &mut Statement| {
            let mut visitor = Visitor {
                locals: &mut b.locals,
                statements: Vec::new(),
                place_mutability_stack: Vec::new(),
                span: st.span,
            };

            // We don't explore sub-statements.
            use llbc_ast::Switch::*;
            use RawStatement::*;
            match &mut st.content {
                Loop(..) => {}
                Switch(If(op, ..) | SwitchInt(op, ..)) => op.drive_mut(&mut visitor),
                Switch(Match(place, ..)) => {
                    visitor.place_mutability_stack.push(false); // Unsure why we do this
                    place.drive_mut(&mut visitor)
                }
                Abort(..) | Return | Break(..) | Continue(..) | Nop | Error(..) | Assert(..)
                | Call(..) => {
                    st.drive_mut(&mut visitor);
                }
                FakeRead(place) => {
                    visitor.place_mutability_stack.push(false);
                    place.drive_mut(&mut visitor);
                }
                Assign(..) | SetDiscriminant(..) | Drop(..) => {
                    visitor.place_mutability_stack.push(true);
                    st.drive_mut(&mut visitor);
                }
            }
            visitor.statements
        });
    }
}
