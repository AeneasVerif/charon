(** Pretty-printing for primitive values *)

module T = Types
module TU = TypesUtils
module E = Expressions
module A = LlbcAst
open PrimitiveValues

let integer_type_to_string = function
  | Isize -> "isize"
  | I8 -> "i8"
  | I16 -> "i16"
  | I32 -> "i32"
  | I64 -> "i64"
  | I128 -> "i128"
  | Usize -> "usize"
  | U8 -> "u8"
  | U16 -> "u16"
  | U32 -> "u32"
  | U64 -> "u64"
  | U128 -> "u128"

let literal_type_to_string (ty : literal_type) : string =
  match ty with
  | TInteger ity -> integer_type_to_string ity
  | TBool -> "bool"
  | TChar -> "char"

let big_int_to_string (bi : big_int) : string = Z.to_string bi

let scalar_value_to_string (sv : scalar_value) : string =
  big_int_to_string sv.value ^ ": " ^ integer_type_to_string sv.int_ty

let literal_to_string (lit : literal) : string =
  match lit with
  | VScalar sv -> scalar_value_to_string sv
  | VBool b -> Bool.to_string b
  | VChar c -> String.make 1 c
