open PrimitiveValues

let literal_as_scalar (v : literal) : scalar_value =
  match v with Scalar v -> v | _ -> raise (Failure "Unexpected")

let literal_type_is_integer (t : literal_type) : bool =
  match t with Integer _ -> true | _ -> false
