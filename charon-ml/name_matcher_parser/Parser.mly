%{
open Ast
%}

/*%token <int> INT_CONSTANT
%token <float> FLOAT_CONSTANT
%token <string> WORD*/

//%token <int option> INDEX
%token <string> IDENT
%token <int option> TYPE_VAR
%token <int option> CONST_GENERIC_VAR
%token SEP
%token LEFT_CURLY
%token RIGHT_CURLY
%token LEFT_SQUARE
%token RIGHT_SQUARE
%token SEMICOL
%token EOF

/* Types */

/*%type <Ast.program> program*/
%type <name> name
%type <name_elem> name_elem
%type <ty> ty
//%type <const_generic> cg

//%start program
%start ty
%start name

%%

name:
//  | n=separated_nonempty_list(SEP, name_elem) { n }
  | e=name_elem EOF { [e] }
  | e=name_elem SEP n=name { e :: n }

/*name:
  | e=name_elem { [e] }
  | e=name_elem; SEP; n=name { e :: n }*/

name_elem:
  | id=IDENT { Ident id }
  | LEFT_CURLY; ty=ty; RIGHT_CURLY { Impl ty }

ty:
  /*| i=TYPE_VAR { TVar i }*/
  // Type variables
  | i=TYPE_VAR { TVar i }
  // Slices
  | LEFT_SQUARE; ty=ty; RIGHT_SQUARE {
      TAdt (TAssumed TSlice, [GType ty]) }
  // Arrays
  | LEFT_SQUARE; ty=ty; SEMICOL; cg=cg; RIGHT_SQUARE {
      TAdt (TAssumed TSlice, [GType ty; GConstGeneric cg]) }
  ;

cg:
  | cg=CONST_GENERIC_VAR { CgVar cg }

/*
pattern:
  | n=name EOF { Pattern n }
  ;

name:
  | 
*/
