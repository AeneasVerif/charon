include GAstUtils
open Types
open UllbcAst

let compute_defs_maps (c : crate) :
    type_decl TypeDeclId.Map.t
    * fun_decl FunDeclId.Map.t
    * global_decl GlobalDeclId.Map.t =
  GAstUtils.compute_defs_maps (fun (g : global_decl) -> g.def_id) c
