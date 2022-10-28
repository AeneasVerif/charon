open Names
module T = Types
module TU = TypesUtils
module E = Expressions
module GA = GAst

let option_to_string (to_string : 'a -> string) (x : 'a option) : string =
  match x with Some x -> "Some (" ^ to_string x ^ ")" | None -> "None"

let name_to_string (name : name) : string = Names.name_to_string name
let fun_name_to_string (name : fun_name) : string = name_to_string name
let global_name_to_string (name : global_name) : string = name_to_string name

let block_id_to_string (id : UllbcAst.BlockId.id) : string =
  "block@" ^ UllbcAst.BlockId.to_string id

let var_id_to_string (id : E.VarId.id) : string = "var@" ^ E.VarId.to_string id

let var_to_string (v : GA.var) : string =
  match v.name with None -> var_id_to_string v.index | Some name -> name
