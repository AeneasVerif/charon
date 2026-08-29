open Values

let scalar_type_is_integer (t : scalar_type) : bool =
  match t with
  | TInteger _ -> true
  | _ -> false
