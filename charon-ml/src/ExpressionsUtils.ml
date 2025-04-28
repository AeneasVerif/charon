open Expressions

let unop_can_fail (unop : unop) : bool =
  match unop with
  | Neg | Cast _ | PtrMetadata -> true
  | Not -> false

let binop_can_fail (binop : binop) : bool =
  match binop with
  | BitXor
  | BitAnd
  | BitOr
  | Eq
  | Lt
  | Le
  | Ne
  | Ge
  | Gt
  | WrappingAdd
  | WrappingSub
  | WrappingMul
  | CheckedAdd
  | CheckedSub
  | CheckedMul
  | Cmp -> false
  | Div | Rem | Add | Sub | Mul | Shl | Shr | Offset -> true
