%{
open Ast
%}

/*%token <int> INT_CONSTANT
%token <float> FLOAT_CONSTANT
%token <string> WORD*/

//%token <int option> INDEX
%token <string> IDENT
%token <int option> REGION_VAR
%token <int option> TYPE_VAR
%token <int option> CONST_GENERIC_VAR
%token <Z.t> INT
%token SEP
%token LEFT_BRACKET
%token RIGHT_BRACKET
%token LEFT_CURLY
%token RIGHT_CURLY
%token LEFT_SQUARE
%token RIGHT_SQUARE
%token SEMICOL
%token AMPERSAND
%token MUT
%token LEFT_ANGLE
%token RIGHT_ANGLE
%token COMMA
%token EOF

/* Types */

/*%type <Ast.program> program*/
%type <name> name_pattern
%type <inst_name> inst_name_pattern
%type <name> name
%type <name_elem> name_elem
%type <region option> region
%type <ty> ty
%type <const_generic> cg
%type <generic_args> generic_args
%type <generic_arg> generic_arg

//%start program
%start name_pattern
%start inst_name_pattern

%%

name_pattern:
  | n=name EOF { n }

/* Instantiated names.

   Useful for trait references for instance:
   `core::slice::index::SliceIndex<Range<usize>, [T]>`
 */
inst_name_pattern:
  | name=name; LEFT_ANGLE; generics=generic_args; RIGHT_ANGLE; EOF {
    { name; generics } }

name:
  | e=name_elem { [e] }
  | e=name_elem SEP n=name { e :: n }

name_elem:
  | id=IDENT { Ident id }
  // Impl path elem
  | LEFT_CURLY; ty=ty; RIGHT_CURLY { Impl ty }

ty:
  // Type variables
  | i=TYPE_VAR { TVar i }
  // Slices
  | LEFT_SQUARE; ty=ty; RIGHT_SQUARE {
      TTy (TSlice, [GType ty]) }
  // Arrays
  | LEFT_SQUARE; ty=ty; SEMICOL; cg=cg; RIGHT_SQUARE {
      TTy (TSlice, [GType ty; GConstGeneric cg]) }
  // References
  | AMPERSAND; r=region; MUT; ty=ty {
      TRef (r, ty, RMut) }
  | AMPERSAND; r=region; ty=ty {
      TRef (r, ty, RShared) }
  // Compound types
  | n=name; LEFT_ANGLE; g=generic_args; RIGHT_ANGLE {
    TTy (TName n, g) }
  | n=name {
    TTy (TName n, []) }
  // Tuples
  | LEFT_BRACKET; tys=separated_list(COMMA, ty); RIGHT_BRACKET {
    TTy (TTuple, List.map (fun x -> GType x) tys) }
  ;

cg:
  | cg=CONST_GENERIC_VAR { CgVar cg }
  | i=INT { CgValue i }

region:
  | r=REGION_VAR { r }

generic_args:
  | g=generic_arg { [ g ] }
  | g=generic_arg; COMMA; gl=generic_args { g :: gl }

generic_arg:
  | r=region { GRegion r }
  | ty=ty { GType ty }
  | cg=cg { GConstGeneric cg }
