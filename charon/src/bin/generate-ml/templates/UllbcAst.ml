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
  end

(** Ancestor for {!UllbcAst.statement} map visitor *)
class ['self] map_statement_base =
  object (_self : 'self)
    inherit [_] GAst.map_statement_base
    method visit_block_id : 'env -> block_id -> block_id = fun _ x -> x
  end

(* __REPLACE0__ *)
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

(* __REPLACE1__ *)
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

(* __REPLACE2__ *)
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

(* __REPLACE3__ *)
[@@deriving show]

type expr_body = blocks gexpr_body [@@deriving show]
type fun_body = expr_body [@@deriving show]
type fun_decl = blocks gfun_decl [@@deriving show]
type global_body = expr_body [@@deriving show]
type global_decl = global_body option gglobal_decl [@@deriving show]

(** ULLBC crate *)
type crate = (blocks, global_body option) gcrate
