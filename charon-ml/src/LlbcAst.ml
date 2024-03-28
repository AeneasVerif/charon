include GAst
open Identifiers
open Types
open Values
open Expressions
open Meta
module LoopId = IdGen ()

type loop_id = LoopId.id [@@deriving show]

(** Ancestor the {!LlbcAst.statement} and {!Charon.UllbcAst.statement} iter visitors *)
class ['self] iter_statement_base =
  object (_self : 'self)
    inherit [_] GAst.iter_statement_base
    method visit_loop_id : 'env -> loop_id -> unit = fun _ _ -> ()
  end

(** Ancestor the {!LlbcAst.statement} and {!Charon.UllbcAst.statement} map visitors *)
class ['self] map_statement_base =
  object (_self : 'self)
    inherit [_] GAst.map_statement_base
    method visit_loop_id : 'env -> loop_id -> loop_id = fun _ x -> x
  end

type statement = {
  meta : meta;  (** The statement meta-data *)
  content : raw_statement;  (** The statement itself *)
}

and raw_statement =
  | Assign of place * rvalue
  | FakeRead of place
  | SetDiscriminant of place * variant_id
  | Drop of place
  | Assert of assertion
  | Call of call
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
  | Loop of loop_id * statement

and switch =
  | If of operand * statement * statement
  | SwitchInt of
      operand * integer_type * (scalar_value list * statement) list * statement
      (** The targets for a switch over an integer are:
          - the list [(matched values, statement to execute)]
            We need a list for the matched values in case we do something like this:
            [switch n { 0 | 1 => ..., _ => ... }]
          - the "otherwise" statement
          Also note that we precise the type of the integer (uint32, int64, etc.)
          which we switch on. *)
  | Match of place * (variant_id list * statement) list * statement option
      (** A match over an ADT.

          Similar comments as for {!SwitchInt}. Note that the "otherwise" branch
          is optional.
       *)
[@@deriving
  show,
    visitors
      {
        name = "iter_statement";
        variety = "iter";
        ancestors = [ "iter_statement_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_statement";
        variety = "map";
        ancestors = [ "map_statement_base" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type fun_body = statement gexpr_body [@@deriving show]
type fun_decl = statement gfun_decl [@@deriving show]

(* TODO: the function id should be an option *)
type global_decl = FunDeclId.id gglobal_decl [@@deriving show]

(** LLBC crate *)
type crate = (statement, FunDeclId.id) gcrate
