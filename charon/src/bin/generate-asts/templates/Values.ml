(** The primitive values. *)
include BigInt
include Uchar

(** A char value *)
type char_value = Uchar.t [@visitors.opaque] [@@deriving show, eq, ord]

(* __REPLACE0__ *)
