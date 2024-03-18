tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int> SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA SYM_PRINT
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ
non-terminals S INSTR<tree> INSTRS<tree list> LINSTRS ELSE EXPR FACTOR
non-terminals LPARAMS REST_PARAMS PARAMS_LIST
non-terminals IDENTIFIER INTEGER
non-terminals FUNDEF FUNDEFS
non-terminals ADD_EXPRS ADD_EXPR
non-terminals MUL_EXPRS MUL_EXPR
non-terminals CMP_EXPRS CMP_EXPR
non-terminals EQ_EXPRS EQ_EXPR
axiom S
{

open Symbols
open Ast
open BatPrintf
open BatBuffer
open Batteries
open Utils

let resolve_associativity term other =
  List.fold_left (fun acc (tag, leaf) -> Node(tag, [acc; leaf])) term other

}

rules
S -> FUNDEFS SYM_EOF {  Node (Tlistglobdef, $1) }

IDENTIFIER -> SYM_IDENTIFIER { Node(Tvar, [StringLeaf($1)]) }
INTEGER -> SYM_INTEGER { Node(Tint, [IntLeaf($1)]) }

FUNDEFS -> { [] }
FUNDEFS -> FUNDEF FUNDEFS { $1::$2 }

FUNDEF -> IDENTIFIER SYM_LPARENTHESIS PARAMS_LIST SYM_RPARENTHESIS SYM_LBRACE INSTRS SYM_RBRACE { Node(Tfundef, [Node(Tfunname, [$1]); $3; Node(Tfunbody, $6)]) }

PARAMS_LIST -> { Node(Tfunargs, []) }
PARAMS_LIST -> LPARAMS REST_PARAMS { Node(Tfunargs, $1::$2) }

REST_PARAMS -> { [] }
REST_PARAMS -> SYM_COMMA LPARAMS REST_PARAMS { $2::$3 }

LPARAMS -> IDENTIFIER { Node(Targ, [$1]) }

ELSE -> { Node(Tblock, []) }
ELSE -> SYM_ELSE SYM_LBRACE INSTRS SYM_RBRACE { Node(Tblock, $3) }

LINSTRS -> { [] }
LINSTRS -> INSTR LINSTRS { $1::$2 }

INSTRS -> { [] }
INSTRS -> INSTR LINSTRS { $1::$2 }

INSTR -> SYM_LBRACE INSTRS SYM_RBRACE { Node(Tblock, $2) }
INSTR -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS SYM_LBRACE INSTRS SYM_RBRACE ELSE { Node(Tif, [$3] @ $6 @ [$8]) }
INSTR -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS INSTR { Node(Twhile, [$3; $5]) }
INSTR -> SYM_RETURN EXPR SYM_SEMICOLON { Node(Treturn, [$2]) }
INSTR -> SYM_PRINT EXPR SYM_SEMICOLON { Node(Tprint, [$2]) }
INSTR -> IDENTIFIER SYM_ASSIGN EXPR SYM_SEMICOLON { Node(Tassign, [$1; $3]) }

EXPR -> EQ_EXPR EQ_EXPRS { resolve_associativity $1 $2 }

EQ_EXPRS -> { [] }
EQ_EXPRS -> SYM_EQUALITY EQ_EXPR EQ_EXPRS { (Tceq, $2)::$3 }
EQ_EXPRS -> SYM_NOTEQ EQ_EXPR EQ_EXPRS { (Tne, $2)::$3 }

EQ_EXPR -> CMP_EXPR CMP_EXPRS { resolve_associativity $1 $2 }

CMP_EXPRS -> { [] }
CMP_EXPRS -> SYM_GEQ CMP_EXPR CMP_EXPRS { (Tcge, $2)::$3 }
CMP_EXPRS -> SYM_GT CMP_EXPR CMP_EXPRS { (Tcgt, $2)::$3 }
CMP_EXPRS -> SYM_LEQ CMP_EXPR CMP_EXPRS { (Tcle, $2)::$3 }
CMP_EXPRS -> SYM_LT CMP_EXPR CMP_EXPRS { (Tclt, $2)::$3 }

CMP_EXPR -> ADD_EXPR ADD_EXPRS { resolve_associativity $1 $2}

ADD_EXPRS -> { [] }
ADD_EXPRS -> SYM_PLUS ADD_EXPR ADD_EXPRS { (Tadd, $2)::$3 }
ADD_EXPRS -> SYM_MINUS ADD_EXPR ADD_EXPRS { (Tsub, $2)::$3 }

ADD_EXPR -> MUL_EXPR MUL_EXPRS { resolve_associativity $1 $2 }

MUL_EXPRS -> { [] } 
MUL_EXPRS -> SYM_ASTERISK MUL_EXPR MUL_EXPRS { (Tmul, $2)::$3 }
MUL_EXPRS -> SYM_DIV MUL_EXPR MUL_EXPRS { (Tdiv, $2)::$3 }
MUL_EXPRS -> SYM_MOD MUL_EXPR MUL_EXPRS { (Tmod, $2)::$3}

MUL_EXPR -> FACTOR { $1 }
MUL_EXPR -> SYM_MINUS FACTOR { Node(Tneg, [$2]) }

FACTOR -> INTEGER { $1 }
FACTOR -> IDENTIFIER { $1 }
FACTOR -> SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS { $2 }
