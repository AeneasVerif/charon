open Expressions

let unop_can_fail (unop : unop) : bool =
  match unop with Neg | Cast _ -> true | Not -> false

let binop_can_fail (binop : binop) : bool =
  match binop with
  | BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt | CheckedAdd
  | CheckedSub | CheckedMul ->
      false
  | Div | Rem | Add | Sub | Mul | Shl | Shr -> true
