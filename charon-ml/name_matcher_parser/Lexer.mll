{
  open Parser
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']

let ident = (alpha) (alpha | digit | '_')*

(*let whitespace = [' ' '\t']+*)
let whitespace = [' ']+

(* Rules *)
rule token = parse
  | "::" { SEP }
  | ident { IDENT (Lexing.lexeme lexbuf) }
  | '{' { LEFT_CURLY }
  | '}' { RIGHT_CURLY }
  | '[' { LEFT_SQUARE }
  | ']' { RIGHT_SQUARE }
  | "@T" { TYPE_VAR(index lexbuf) }
  | "@C" { CONST_GENERIC_VAR(index lexbuf) }
  | ';' { SEMICOL }
  | whitespace { token lexbuf }
  | eof { EOF }
(*  | '<' { LEFT_ANGLE }
  | '>' { RIGHT_ANGLE }
  | '|' { BAR }
  | ',' { COMMA } *)
  | _ { raise (Failure ("Character not allowed in source text: '" ^ Lexing.lexeme lexbuf ^ "'")) }

and ty = parse
  | "@T" { TYPE_VAR(index lexbuf) }
  | _ { raise (Failure ("Character not allowed in source text: '" ^ Lexing.lexeme lexbuf ^ "'")) }

and index = parse
  | digit+ { Some (int_of_string (Lexing.lexeme lexbuf)) }
  | "" { None }

(*and token = parse
  | int_constant { INT_CONSTANT (int_of_string (Lexing.lexeme lexbuf)) }
  | float_constant { FLOAT_CONSTANT (float_of_string (Lexing.lexeme lexbuf)) }
  | identifier { WORD (Lexing.lexeme lexbuf) }
  (* etc. *)
  | whitespace { token lexbuf }
  | eof { EOF }
  | _ { raise (Failure ("Character not allowed in source text: '" ^ Lexing.lexeme lexbuf ^ "'"))
} *)