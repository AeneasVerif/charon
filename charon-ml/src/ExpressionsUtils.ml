open Types
open Expressions

let unop_can_fail : unop -> bool = function
  | Neg (OPanic | OUB) | Cast _ -> true
  | Neg OWrap | Not -> false

let binop_can_fail : binop -> bool = function
  | BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt
  | Add OWrap
  | Sub OWrap
  | Mul OWrap
  | Shl OWrap
  | Shr OWrap
  | AddChecked | SubChecked | MulChecked | Cmp -> false
  | Div _ | Rem _ | Add _ | Sub _ | Mul _ | Shl _ | Shr _ | Offset -> true

let constant_expr_of_const_generic : const_generic -> constant_expr_kind =
  function
  | CgGlobal g -> CGlobal { id = g; generics = TypesUtils.empty_generic_args }
  | CgVar v -> CVar v
  | CgValue c -> CLiteral c
