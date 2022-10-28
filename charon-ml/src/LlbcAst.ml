include GAst
open Types
open PrimitiveValues
open Expressions
open Meta
open Names

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
  | Switch of operand * switch_targets
  | Loop of statement

and switch_targets =
  | If of statement * statement  (** Gives the "if" and "else" blocks *)
  | SwitchInt of integer_type * (scalar_value list * statement) list * statement
      (** The targets for a switch over an integer are:
          - the list [(matched values, statement to execute)]
            We need a list for the matched values in case we do something like this:
            [switch n { 0 | 1 => ..., _ => ... }]
          - the "otherwise" statement
          Also note that we precise the type of the integer (uint32, int64, etc.)
          which we switch on. *)
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

type global_decl = {
  meta : meta;
  def_id : GlobalDeclId.id;
  name : global_name;
  ty : ety;
  body_id : FunDeclId.id;  (** TODO: this field should be an option *)
}
[@@deriving show]

(** LLBC crate *)
type crate = (fun_decl, global_decl) gcrate
