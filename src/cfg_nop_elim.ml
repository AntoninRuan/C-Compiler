open BatList
open Batteries
open Prog
open Utils
open Cfg
open Report
open Cfg_print
open Options

(* Élimination des NOPs. *)

(* [nop_transitions cfg] donne la liste des transitions NOP dans un CFG.

   Si le nœud [n] contient [Cnop s], alors [(n,s)] devrait être dans le résultat.
*)
let nop_transitions (cfgfunbody: (int, cfg_node) Hashtbl.t) : (int * int) list =
   Hashtbl.fold (fun key value acc -> 
      match value with 
      | Cnop next -> (key, next)::acc
      | _ -> acc   
   ) cfgfunbody []


(* [follow n l visited] donne le premier successeur à partir de [n] qui ne soit
   pas un NOP. Pour connaître le successeur d'un nœud NOP, on utilisara la liste
   [l] telle que produite précédemment. Pour rappel [(x,y)] dans [l] signifie
   qu'il y a un transition depuis un nœud [x] qui contient une instruction [Cnop
   y].

   L'ensemble [visited] est utilisé pour éviter les boucles.
   *)
let rec follow (n: int) (l: (int * int) list) (visited: int Set.t) : int =
   let is_nop = List.mem_assoc n l 
   in if is_nop then
      let s = List.assoc n l 
      in if Set.mem s visited then n else follow s l (Set.union visited (Set.singleton n))
   else 
      n

(* [nop_transitions_closed] contient la liste [(n,s)] telle que l'instruction au
   nœud [n] est le début d'une chaîne de NOPs qui termine au nœud [s]. Les
   enseignants du cours de compiilation sont heureux de vous offrir cette
   fonction. *)
let nop_transitions_closed cfgfunbody =
  List.map (fun (node_id, node) ->
      (node_id, follow node_id (nop_transitions cfgfunbody) Set.empty))
    (nop_transitions cfgfunbody)

(* Nous allons maintenant réécrire notre programme pour remplacer les
   successeurs [s] de chaque nœud du CFG de la manière suivante : si [s] est le
   début d'une chaîne de NOPs, on remplace [s] par la fin de cette chaîne, en
   éliminant ainsi les nœuds NOPs. *)

(* [replace_succ nop_succs s] donne le nouveau nom du nœud [s], en utilisant la
   liste [nop_succs] (telle que renvoyée par [nop_transitions_closed]). *)
let replace_succ nop_succs s =
   if List.mem_assoc s nop_succs then List.assoc s nop_succs else s

(* [replace_succs nop_succs n] remplace le nœud [n] par un nœud équivalent où on
   a remplacé les successeurs, en utilisant la liste [nop_succs]. *)
let replace_succs nop_succs (n: cfg_node) =
   match n with 
   | Cassign (var, expr, next) -> Cassign(var, expr, replace_succ nop_succs next)
   | Creturn expr -> n
   | Cprint (expr, next) -> Cprint(expr, replace_succ nop_succs next)
   | Ccmp (expr, lnext, rnext) -> Ccmp(expr, replace_succ nop_succs lnext, replace_succ nop_succs rnext)
   | Cnop next -> Cnop(replace_succ nop_succs next)
   | Ccall (str, args, next) -> Ccall(str, args, replace_succ nop_succs next)

(* [nop_elim_fun f] applique la fonction [replace_succs] à chaque nœud du CFG. *)
let nop_elim_fun ({ cfgfunargs; cfgfunbody; cfgentry } as f: cfg_fun) =
  let nop_transf = nop_transitions_closed cfgfunbody in
  (* On utilise la fonction [Hashtbl.filter_map f h] qui permet d'appliquer une
     fonction à chaque nœud de [h] et d'éliminer ceux pour lesquels [f] renvoie
     [None].

     On souhaite éliminer les nœuds qui n'ont pas de prédécesseurs
     (inaccessibles), et appliquer la fonction [replace_succs] aux nœuds qui
     resteront.
  *)
  let cfgfunbody = Hashtbl.filter_map (fun n node ->
         match node with
         | Cnop next -> None
         | _ -> Some (replace_succs nop_transf node)
    ) cfgfunbody in
  (* La fonction renvoyée est composée du nouveau [cfgfunbody] que l'on vient de
     calculer, et le point d'entrée est transformé en conséquence. *)
  {f with cfgfunbody; cfgentry = replace_succ nop_transf cfgentry }

let nop_elim_gdef gd =
  match gd with
    Gfun f -> Gfun (nop_elim_fun f)

let nop_elimination cp =
  if !Options.no_cfg_ne
  then cp
  else assoc_map nop_elim_gdef cp

let pass_nop_elimination cfg =
  let cfg = nop_elimination cfg in
  record_compile_result "NopElim";
  dump (!cfg_dump >*> fun s -> s ^ "3") dump_cfg_prog cfg
    (call_dot "cfg-after-nop" "CFG after NOP elim");
  OK cfg
