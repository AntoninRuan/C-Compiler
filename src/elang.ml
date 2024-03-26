open Prog

type binop = Eadd | Emul | Emod | Exor | Ediv | Esub (* binary operations *)
           | Eclt | Ecle | Ecgt | Ecge | Eceq | Ecne (* comparisons *)
type unop = Eneg

type expr =
    Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Eint of int
  | Evar of string
  | Echar of char
  | Ecall of string * expr list
  | Eaddrof of expr
  | Eload of expr

type instr =
  | Iassign of string * expr option
  | Iif of expr * instr * instr
  | Iwhile of expr * instr
  | Iblock of instr list
  | Ireturn of expr
  | Icall of string * expr list
  | Istore of expr * expr option
  | Ibuiltin of string * string list

type efun = {
  funreturntype : typ;
  funargs: ( string * typ ) list;
  funvarinmem: (string, int) Hashtbl.t;
  funstksz: int;
  funbody: instr;
}

type eprog = efun prog
