%{
    (* open Symbols *)
    open Ast
%}

%token SYM_EOF
%token SYM_VOID SYM_CHAR SYM_INT SYM_STRUCT SYM_POINT SYM_BOOL_NOT SYM_BOOL_AND SYM_BOOL_OR
%token SYM_ARROW SYM_BITWISE_OR SYM_BITWISE_AND SYM_BIT_NOT SYM_XOR SYM_LBRACKET SYM_RBRACKET
%token SYM_ALLOC SYM_EXTERN SYM_AMPERSAND
%token<char> SYM_CHARACTER
%token<string> SYM_STRING
%token<string> SYM_INCLUDE
%token<string> SYM_IDENTIFIER
%token<int> SYM_INTEGER
%token SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD
%token SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
%token SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA SYM_PRINT
%token SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ

%left SYM_EQUALITY SYM_NOTEQ
%left SYM_GEQ SYM_LEQ SYM_LT SYM_GT
%left SYM_PLUS SYM_MINUS
%left SYM_ASTERISK SYM_DIV SYM_MOD
%nonassoc UMINUS

%start main
%type <Ast.tree> main

%%

  main:
    | fundefs SYM_EOF { Node(Tlistglobdef, $1) }
    ;
      fundefs:
        | fundef fundefs { $1 :: $2 }
        | { [] }
    ;
      fundef:
        identifier SYM_LPARENTHESIS lparams SYM_RPARENTHESIS instr {
            let fargs = $3 in
            let instr = $5 in
            Node (Tfundef, [$1; Node (Tfunargs, fargs) ; instr ])
          }
    ;
      identifier:
        SYM_IDENTIFIER {  StringLeaf ($1) }
    ;

      integer : SYM_INTEGER { IntLeaf ($1) };

    lparams :
      identifier rest_params { Node (Targ, [$1]) :: $2 }
      | { [] };
    rest_params :
      SYM_COMMA identifier rest_params {
          Node (Targ, [$2]) :: $3
        }
      | { [] };
    instrs :
      | instr instrs { $1 :: $2 }
      | { [] };
    linstrs :
      SYM_LBRACE instrs SYM_RBRACE { Node (Tblock, $2) };
    instr :
      identifier SYM_ASSIGN expr SYM_SEMICOLON {
          Node (Tassign, [Node (Tassignvar,[$1; $3])])
        }
      | SYM_IF SYM_LPARENTHESIS expr SYM_RPARENTHESIS linstrs ntelse { Node (Tif, [$3; $5; $6]) }
      | SYM_WHILE SYM_LPARENTHESIS expr SYM_RPARENTHESIS instr { Node( Twhile, [$3; $5]) }
      | SYM_RETURN expr SYM_SEMICOLON { Node(Treturn, [$2]) }
      | SYM_PRINT expr SYM_SEMICOLON { Node(Tprint, [$2]) }
      | linstrs { $1 };
      ntelse :
        SYM_ELSE linstrs { $2 }
        | { Node(Tblock, []) };

      expr :
        | expr SYM_EQUALITY expr { Node (Tceq, [$1; $3]) }
        | expr SYM_NOTEQ expr { Node (Tne, [$1; $3]) }
        | expr SYM_PLUS expr { Node (Tadd, [$1; $3]) }
        | expr SYM_MINUS expr { Node (Tsub, [$1; $3]) }
        | expr SYM_ASTERISK expr { Node (Tmul, [$1; $3]) }
        | expr SYM_DIV expr { Node (Tdiv, [$1; $3]) }
        | expr SYM_MOD expr { Node (Tmod, [$1; $3]) }
        | expr SYM_LT expr { Node (Tclt, [$1; $3]) }
        | expr SYM_GT expr { Node (Tcgt, [$1; $3]) }
        | expr SYM_LEQ expr { Node (Tcle, [$1; $3]) }
        | expr SYM_GEQ expr { Node (Tcge, [$1; $3]) }
        | SYM_MINUS expr %prec UMINUS { Node (Tneg, [$2])}
        | integer { Node(Tlitteral, [$1])}
        | identifier { $1 }
        | SYM_LPARENTHESIS expr SYM_RPARENTHESIS { $2 }
      ;
