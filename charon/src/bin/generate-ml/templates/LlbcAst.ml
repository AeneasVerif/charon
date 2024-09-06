include GAst
open Types
open Values
open Expressions
open Meta

(* Hand-written because we encode sequences differently. *)
type raw_statement =
  | Assign of place * rvalue
  | FakeRead of place
  | SetDiscriminant of place * variant_id
  | Drop of place
  | Assert of assertion
  | Call of call
  (* FIXME: rename to `Abort` *)
  | Panic
  | Return
  | Break of int
      (** Break to (outer) loop. The [int] identifies the loop to break to:
          * 0: break to the first outer loop (the current loop)
          * 1: break to the second outer loop
          * ...
          *)
  | Continue of int
      (** Continue to (outer) loop. The loop identifier works
          the same way as for {!Break} *)
  | Nop
  | Sequence of statement * statement
  | Switch of switch
  | Loop of statement
  | Error of string

(* __REPLACE0__ *)

type expr_body = statement gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = statement gfun_decl [@@deriving show]

(* TODO: the function id should be an option *)
type global_decl = FunDeclId.id gglobal_decl [@@deriving show]

(** LLBC crate *)
type crate = (statement, FunDeclId.id) gcrate
