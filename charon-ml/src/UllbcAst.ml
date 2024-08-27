include GAst
open Types
open Values
open Expressions
open Meta
open Identifiers
module BlockId = IdGen ()

(** We define this type to control the name of the visitor functions
    (see e.g., {!UllbcAst.iter_statement_base} and {!switch}).
  *)
type block_id = BlockId.id [@@deriving show, ord]

(** Ancestor for {!UllbcAst.statement} iter visitor *)
class ['self] iter_statement_base =
  object (_self : 'self)
    inherit [_] GAst.iter_statement_base
    method visit_block_id : 'env -> block_id -> unit = fun _ _ -> ()
    method visit_abort_kind : 'env -> abort_kind -> unit = fun _ _ -> ()
  end

(** Ancestor for {!UllbcAst.statement} map visitor *)
class ['self] map_statement_base =
  object (_self : 'self)
    inherit [_] GAst.map_statement_base
    method visit_block_id : 'env -> block_id -> block_id = fun _ x -> x
    method visit_abort_kind : 'env -> abort_kind -> abort_kind = fun _ x -> x
  end

type statement = {
  span : span;  (** The statement span *)
  content : raw_statement;  (** The statement itself *)
}

and raw_statement =
  | Assign of place * rvalue
  | FakeRead of place
  | SetDiscriminant of place * variant_id
  | StorageDead of var_id
  | Deinit of place
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

type switch =
  | If of block_id * block_id
  | SwitchInt of integer_type * (scalar_value * block_id) list * block_id
[@@deriving
  show,
    visitors
      {
        name = "iter_switch";
        variety = "iter";
        ancestors = [ "iter_statement" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_switch";
        variety = "map";
        ancestors = [ "map_statement" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type terminator = {
  span : span;  (** The terminator span *)
  content : raw_terminator;  (** The terminator itself *)
}

and raw_terminator =
  | Goto of block_id
  | Switch of operand * switch
  | Abort of abort_kind
  | Return
  | Drop of place * block_id
  | Call of call * block_id option
  | Assert of assertion * block_id
[@@deriving
  show,
    visitors
      {
        name = "iter_terminator";
        variety = "iter";
        ancestors = [ "iter_switch" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      },
    visitors
      {
        name = "map_terminator";
        variety = "map";
        ancestors = [ "map_switch" ];
        nude = true (* Don't inherit {!VisitorsRuntime.iter} *);
        concrete = true;
      }]

type block = { statements : statement list; terminator : terminator }
[@@deriving show]

type blocks = block list [@@deriving show]
type expr_body = blocks gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = blocks gfun_decl [@@deriving show]
type global_body = expr_body [@@deriving show]
type global_decl = global_body option gglobal_decl [@@deriving show]

(** ULLBC crate *)
type crate = (blocks, global_body option) gcrate
