(** Pretty-printing for primitive values *)

module T = Types
module TU = TypesUtils
module E = Expressions
module A = LlbcAst
module PT = PrintTypes
open PrimitiveValues

let big_int_to_string (bi : big_int) : string = Z.to_string bi

let scalar_value_to_string (sv : scalar_value) : string =
  big_int_to_string sv.value ^ ": " ^ PT.integer_type_to_string sv.int_ty

let primitive_value_to_string (cv : primitive_value) : string =
  match cv with
  | Scalar sv -> scalar_value_to_string sv
  | Bool b -> Bool.to_string b
  | Char c -> String.make 1 c
  | String s -> s
