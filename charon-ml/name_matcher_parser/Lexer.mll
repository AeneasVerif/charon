{
  open Parser
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha) (alpha | digit | '_')*
let whitespace = [' ']+

(* Rules *)
rule token = parse
  | "::" { SEP }
  | "mut" { MUT }
  | ident { IDENT (Lexing.lexeme lexbuf) }
  | digit { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | '(' { LEFT_BRACKET }
  | ')' { RIGHT_BRACKET }
  | '{' { LEFT_CURLY }
  | '}' { RIGHT_CURLY }
  | '[' { LEFT_SQUARE }
  | ']' { RIGHT_SQUARE }
  | "@R" { REGION_VAR(index lexbuf) }
  | "@T" { TYPE_VAR(index lexbuf) }
  | "@C" { CONST_GENERIC_VAR(index lexbuf) }
  | ';' { SEMICOL }
  | '&' { AMPERSAND }
  | whitespace { token lexbuf }
  | eof { EOF }
  | '<' { LEFT_ANGLE }
  | '>' { RIGHT_ANGLE }
  | ',' { COMMA } 
  | _ { raise (Failure ("Character not allowed in source text: '" ^ Lexing.lexeme lexbuf ^ "'")) }

and index = parse
  | digit+ { Some (int_of_string (Lexing.lexeme lexbuf)) }
  | "" { None }
