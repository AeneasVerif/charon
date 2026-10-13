(** The primitive values. *)
include BigInt

include Uchar

(** A char value *)
type char_value = (Uchar.t[@visitors.opaque]) [@@deriving show, eq, ord]

let hash_char_value = Uchar.hash

(* Ancestors for the scalar visitors *)
class ['self] iter_scalar_base =
  object (self : 'self)
    inherit [_] Generated_Meta.iter_meta
    method visit_char_value : 'env -> char_value -> unit = fun _ _ -> ()
  end

class ['self] map_scalar_base =
  object (self : 'self)
    inherit [_] Generated_Meta.map_meta
    method visit_char_value : 'env -> char_value -> char_value = fun _ x -> x
  end

class virtual ['self] reduce_scalar_base =
  object (self : 'self)
    inherit [_] Generated_Meta.reduce_meta
    method visit_char_value : 'env -> char_value -> 'a = fun _ _ -> self#zero
  end

class virtual ['self] mapreduce_scalar_base =
  object (self : 'self)
    inherit [_] Generated_Meta.mapreduce_meta

    method visit_char_value : 'env -> char_value -> char_value * 'a =
      fun _ x -> (x, self#zero)
  end

type float_type = F16 | F32 | F64 | F128

(** This is simlar to the Scalar value above. However, instead of storing the
    float value itself, we store its String representation. This allows to
    derive the Eq and Ord traits, which are not implemented for floats *)
and float_value = { float_value : string; float_ty : float_type }

and int_ty = Isize | I8 | I16 | I32 | I64 | I128
and integer_type = Signed of int_ty | Unsigned of u_int_ty

(** A scalar value. *)
and integer_value =
  | UnsignedInteger of u_int_ty * big_int
  | SignedInteger of int_ty * big_int

(** Types of primitive scalar values. *)
and scalar_type =
  | TInteger of integer_type
  | TFloat of float_type
  | TBool
  | TChar

and u_int_ty = Usize | U8 | U16 | U32 | U64 | U128
[@@deriving
  show,
  eq,
  ord,
  visitors
    {
      name = "iter_scalar";
      monomorphic = [ "env" ];
      variety = "iter";
      ancestors = [ "iter_scalar_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "map_scalar";
      monomorphic = [ "env" ];
      variety = "map";
      ancestors = [ "map_scalar_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "reduce_scalar";
      monomorphic = [ "env" ];
      variety = "reduce";
      ancestors = [ "reduce_scalar_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    },
  visitors
    {
      name = "mapreduce_scalar";
      monomorphic = [ "env" ];
      variety = "mapreduce";
      ancestors = [ "mapreduce_scalar_base" ];
      nude = true (* Don't inherit VisitorsRuntime *);
    }]

let rec hash_float_type : float_type -> int =
 fun (x : float_type) ->
  match x with
  | F16 -> 0
  | F32 -> 1
  | F64 -> 2
  | F128 -> 3

and hash_float_value : float_value -> int =
 fun (x : float_value) ->
  HashBasic.combine
    (HashBasic.combine 0 (HashBasic.hash_string x.float_value))
    (hash_float_type x.float_ty)

and hash_int_ty : int_ty -> int =
 fun (x : int_ty) ->
  match x with
  | Isize -> 0
  | I8 -> 1
  | I16 -> 2
  | I32 -> 3
  | I64 -> 4
  | I128 -> 5

and hash_integer_type : integer_type -> int =
 fun (x : integer_type) ->
  match x with
  | Signed x0 -> HashBasic.combine 0 (hash_int_ty x0)
  | Unsigned x0 -> HashBasic.combine 1 (hash_u_int_ty x0)

and hash_integer_value : integer_value -> int =
 fun (x : integer_value) ->
  match x with
  | UnsignedInteger (x0, x1) ->
      HashBasic.combine
        (HashBasic.combine 0 (hash_u_int_ty x0))
        (hash_big_int x1)
  | SignedInteger (x0, x1) ->
      HashBasic.combine (HashBasic.combine 1 (hash_int_ty x0)) (hash_big_int x1)

and hash_scalar_type : scalar_type -> int =
 fun (x : scalar_type) ->
  match x with
  | TInteger x0 -> HashBasic.combine 0 (hash_integer_type x0)
  | TFloat x0 -> HashBasic.combine 1 (hash_float_type x0)
  | TBool -> 2
  | TChar -> 3

and hash_u_int_ty : u_int_ty -> int =
 fun (x : u_int_ty) ->
  match x with
  | Usize -> 0
  | U8 -> 1
  | U16 -> 2
  | U32 -> 3
  | U64 -> 4
  | U128 -> 5
