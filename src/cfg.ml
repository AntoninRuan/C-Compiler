open Elang
open Prog
open Batteries
open BatList

type expr =
    Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Eint of int
  | Evar of string
  | Ecall of string * expr list

type cfg_node =
  | Cassign of string * expr * int
  | Creturn of expr
  | Ccmp of expr * int * int
  | Cnop of int
  | Ccall of string * expr list * int

type cfg_fun = {
  cfgfunargs: (string * typ) list;
  cfgfunbody: (int, cfg_node) Hashtbl.t;
  cfgentry: int;
}

type cprog = cfg_fun prog


(* [succs cfg n] donne l'ensemble des successeurs d'un nœud [n] dans un CFG
   [cfg]. *)
let succs cfg n =
  match Hashtbl.find_option cfg n with
  | None -> Set.empty
  | Some (Cassign (_, _, s)) -> Set.singleton s
  | Some (Creturn _) -> Set.empty
  | Some (Ccmp (_, s1, s2)) -> Set.of_list [s1;s2]
  | Some (Cnop s) -> Set.singleton s
  | Some (Ccall (_, _, s)) -> Set.singleton s


(* [preds cfg n] donne l'ensemble des prédécesseurs d'un nœud [n] dans un CFG [cfg]
   *)
let preds cfgfunbody n =
  Hashtbl.fold (fun m m' acc ->
      match m' with
      | Cassign (_, _, s)
      | Ccall (_, _, s)
      | Cnop s -> if s = n then Set.add m acc else acc
      | Creturn _ -> acc
      | Ccmp (_, s1, s2) -> if s1 = n || s2 = n then Set.add m acc else acc
    ) cfgfunbody Set.empty


let size_binop _ e1 e2 =
  1 + e1 + e2

let size_unop _ e =
  1 + e

let rec size_expr (e: expr) : int =
  match e with
  | Ebinop (b, e1, e2) -> size_binop b (size_expr e1) (size_expr e2)
  | Eunop (u, e) -> size_unop u (size_expr e)
  | Eint _ -> 1
  | Evar _ -> 1
  | Ecall (_, args) -> 1 + (List.fold_left (fun acc elt -> acc + size_expr elt) 0 args)  

let size_instr (i: cfg_node) : int =
  match (i : cfg_node) with
  | Cassign (_, e, _) -> 1 + size_expr e
  | Creturn e -> 1 + (size_expr e)
  | Ccmp (e, _, _) -> 1 + size_expr e
  | Cnop _ -> 1
  | Ccall (_, args, _) -> 1 + (List.fold (fun acc elt -> acc + size_expr elt) 0 args)

let size_fun f =
  Hashtbl.fold (fun _ v acc -> acc + size_instr v) f 0

