open Values

let literal_as_scalar (v : literal) : scalar_value =
  match v with
  | VScalar v -> v
  | _ -> raise (Failure "Unexpected")

let literal_type_is_integer (t : literal_type) : bool =
  match t with
  | TInt _ -> true
  | TUInt _ -> true
  | _ -> false

let literal_list_to_scalar_list (llist : literal list) : scalar_value list =
  List.map (fun lit -> literal_as_scalar lit) llist
