open Batteries
open Elang
open Cfg

type reg = int

type rtl_cmp = Rclt | Rcle | Rcgt | Rcge | Rceq | Rcne

type rtl_instr = Rbinop of binop * reg * reg * reg
               | Runop of unop * reg * reg
               | Rconst of reg * int
               | Rbranch of rtl_cmp * reg * reg * int
               | Rjmp of int
               | Rmov of reg * reg
               | Rret of reg
               | Rlabel of int
               | Rcall of reg option * string * reg list

type rtl_fun = { rtlfunargs: reg list;
                 rtlfunbody: (int, rtl_instr list) Hashtbl.t;
                 rtlfunentry: int;
                 rtlfuninfo: (string*reg) list
               }

let written_rtl_regs_instr (i: rtl_instr) =
  match i with
  | Rbinop (_, rd, _, _)
  | Runop (_, rd, _)
  | Rconst (rd, _)
  | Rmov (rd, _) -> Set.singleton rd
  | Rret _
  | Rlabel _
  | Rbranch (_, _, _, _)
  | Rjmp _ -> Set.empty
  | Rcall(reg_option, _, _) -> match reg_option with None -> Set.empty | Some v -> Set.singleton v

let written_rtl_regs (l: rtl_instr list) =
  List.fold_left (fun acc i -> Set.union acc (written_rtl_regs_instr i))
    Set.empty l
