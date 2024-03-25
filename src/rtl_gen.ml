open Batteries
open Elang
open Cfg
open Rtl
open Prog
open Utils
open Report
open Rtl_print
open Options

(* Une partie de la génération de RTL consiste à allouer les variables dans des
   pseudo-registres RTL.

   Ces registres sont en nombre illimité donc ce problème est facile.

   Étant donnés :
   - [next_reg], le premier numéro de registre disponible (pas encore alloué à
   une variable)
   - [var2reg], une liste d'associations dont les clés sont des variables et les
   valeurs des numéros de registres
   - [v] un nom de variable (de type [string]),

   [find_var (next_reg, var2reg) v] renvoie un triplet [(r, next_reg, var2reg)]:

   - [r] est le registre RTL associé à la variable [v]
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.

*)
let find_var (next_reg, var2reg) v =
  match List.assoc_opt v var2reg with
    | Some r -> (r, next_reg, var2reg)
    | None -> (next_reg, next_reg + 1, assoc_set var2reg v next_reg)


(* [rtl_instrs_of_cfg_expr (next_reg, var2reg) e] construit une liste
   d'instructions RTL correspondant à l'évaluation d'une expression E.

   Le retour de cette fonction est un quadruplet [(r,l,next_reg,var2reg)], où :
   - [r] est le registre RTL dans lequel le résultat de l'évaluation de [e] aura
     été stocké
   - [l] est une liste d'instructions RTL.
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.
*)
let rec rtl_instrs_of_cfg_expr (next_reg, var2reg) (e: expr) =
  match e with
  | Ebinop (binop, lexpr, rexpr) -> let (lr, lrexprs, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) lexpr
    in let (rr, rrexprs, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) rexpr
    in (next_reg, lrexprs @ rrexprs @ [Rbinop(binop, next_reg, lr, rr)], next_reg + 1, var2reg) 
  | Eunop (unop, expr) -> let (r, rexprs, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) expr 
    in (r, rexprs @ [Runop(unop, next_reg, r)], next_reg + 1, var2reg)
  | Eint value -> (next_reg, [Rconst(next_reg, value)], next_reg + 1, var2reg)
  | Evar var -> let (r, next_reg, var2reg) = find_var (next_reg, var2reg) var in (r, [], next_reg, var2reg)
  | Ecall (str, args) -> 
    let reg_list, rexprs, next_reg, var2reg = rtl_instrs_of_cfg_fun_call_args (next_reg, var2reg) args in
    (next_reg, rexprs @ [Rcall(Some next_reg, str, reg_list)], next_reg + 1, var2reg)

and rtl_instrs_of_cfg_fun_call_args (next_reg, var2reg) (args: Cfg.expr list) = 
  List.fold_left (fun (reg_list, lexprs, next_reg, var2reg) elt -> 
    let r, rexprs, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) elt
    in (reg_list @ [r], lexprs @ rexprs, next_reg, var2reg)
  ) ([], [], next_reg, var2reg) args
   

let is_cmp_op =
  function Eclt -> Some Rclt
         | Ecle -> Some Rcle
         | Ecgt -> Some Rcgt
         | Ecge -> Some Rcge
         | Eceq -> Some Rceq
         | Ecne -> Some Rcne
         | _ -> None

let rtl_cmp_of_cfg_expr (e: expr) =
  match e with
  | Ebinop (b, e1, e2) ->
    (match is_cmp_op b with
     | None -> (Rcne, e, Eint 0)
     | Some rop -> (rop, e1, e2))
  | _ -> (Rcne, e, Eint 0)


let rtl_instrs_of_cfg_node ((next_reg:int), (var2reg: (string*int) list)) (c: cfg_node) =
  match c with
  | Cassign (var, expr, next) -> let (rd, next_reg, var2reg) = find_var (next_reg, var2reg) var
    in let (rs, rexprs, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) expr
    in (rexprs @ [Rmov(rd, rs); Rjmp next], next_reg, var2reg)
  | Creturn expr -> let (r, rexprs, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) expr 
    in (rexprs @ [Rret r], next_reg, var2reg)
  | Ccmp (expr, lnext, rnext) -> let (rcmp, lexpr, rexpr) = rtl_cmp_of_cfg_expr expr 
    in let (lr, lrexprs, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) lexpr
    in let (rr, rrexprs, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) rexpr
    in (lrexprs @ rrexprs @ [Rbranch(rcmp, lr, rr, lnext); Rjmp rnext], next_reg, var2reg)
  | Cnop next -> ([], next_reg, var2reg)
  | Ccall (str, args, next) -> 
    let reg_list, rexprs, next_reg, var2reg = rtl_instrs_of_cfg_fun_call_args (next_reg, var2reg) args in
    (rexprs @ [Rcall(None, str, reg_list); Rjmp next], next_reg, var2reg)

let rtl_instrs_of_cfg_fun cfgfunname ({ cfgfunargs; cfgfunbody; cfgentry }: cfg_fun) =
  let (rargs, next_reg, var2reg) =
    List.fold_left (fun (rargs, next_reg, var2reg) a ->
        let (r, next_reg, var2reg) = find_var (next_reg, var2reg) a in
        (rargs @ [r], next_reg, var2reg)
      )
      ([], 0, []) cfgfunargs
  in
  let rtlfunbody = Hashtbl.create 17 in
  let (next_reg, var2reg) = Hashtbl.fold (fun n node (next_reg, var2reg)->
      let (l, next_reg, var2reg) = rtl_instrs_of_cfg_node (next_reg, var2reg) node in
      Hashtbl.replace rtlfunbody n l;
      (next_reg, var2reg)
    ) cfgfunbody (next_reg, []) in
  {
    rtlfunargs = rargs;
    rtlfunentry = cfgentry;
    rtlfunbody;
    rtlfuninfo = var2reg;
  }

let rtl_of_gdef funname = function
    Gfun f -> Gfun (rtl_instrs_of_cfg_fun funname f)

let rtl_of_cfg cp = List.map (fun (s, gd) -> (s, rtl_of_gdef s gd)) cp

let pass_rtl_gen cfg =
  let rtl = rtl_of_cfg cfg in
  dump !rtl_dump dump_rtl_prog rtl
    (fun file () -> add_to_report "rtl" "RTL" (Code (file_contents file)));
  OK rtl
