(** Utility exception

    When looking for something while exploring a term, it can be easier to
    just throw an exception to signal we found what we were looking for.
    
    TODO: merge with Errors.ml into Exceptions.ml
 *)
exception Found
