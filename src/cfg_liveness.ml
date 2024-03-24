open Batteries
open Cfg

(* Analyse de vivacité *)

(* [vars_in_expr e] renvoie l'ensemble des variables qui apparaissent dans [e]. *)
let rec vars_in_expr (e: expr) =
   match e with
   | Ebinop (_, lexpr, rexpr) -> Set.union (vars_in_expr lexpr) (vars_in_expr rexpr)
   | Eunop  (_, expr) -> vars_in_expr expr
   | Eint int -> Set.empty
   | Evar string -> Set.singleton string
   | Ecall (string, args) -> List.fold_left (fun acc elt -> Set.union acc (vars_in_expr elt)) Set.empty args

(* [live_after_node cfg n] renvoie l'ensemble des variables vivantes après le
   nœud [n] dans un CFG [cfg]. [lives] est l'état courant de l'analyse,
   c'est-à-dire une table dont les clés sont des identifiants de nœuds du CFG et
   les valeurs sont les ensembles de variables vivantes avant chaque nœud. *)
let live_after_node cfg n (lives: (int, string Set.t) Hashtbl.t) : string Set.t =
   Set.fold (fun elt acc -> Set.union acc (match (Hashtbl.find_option lives elt) with | None -> Set.empty | Some v -> v)) (succs cfg n) Set.empty

(* [live_cfg_node node live_after] renvoie l'ensemble des variables vivantes
   avant un nœud [node], étant donné l'ensemble [live_after] des variables
   vivantes après ce nœud. *)
let live_cfg_node (node: cfg_node) (live_after: string Set.t) =
   let use, def = (match node with
   | Cassign (var, expr, next) -> (vars_in_expr expr, Set.singleton var)
   | Creturn expr -> (vars_in_expr expr, Set.empty)
   | Cprint (expr, next) -> (vars_in_expr expr, Set.empty)
   | Ccmp (expr, lnext, rnext) -> (vars_in_expr expr, Set.empty)
   | Cnop int -> (Set.empty, Set.empty)
   | Ccall (str, args, next) -> (List.fold_left (fun acc elt -> Set.union acc (vars_in_expr elt)) Set.empty args, Set.empty)
   )
   in Set.union use (Set.diff live_after def)

(* [live_cfg_nodes cfg lives] effectue une itération du calcul de point fixe.

   Cette fonction met à jour l'état de l'analyse [lives] et renvoie un booléen
   qui indique si le calcul a progressé durant cette itération (i.e. s'il existe
   au moins un nœud n pour lequel l'ensemble des variables vivantes avant ce
   nœud a changé). *)
let live_cfg_nodes (cfg: (int, cfg_node) Hashtbl.t) (lives : (int, string Set.t) Hashtbl.t) =
   Hashtbl.fold (fun key value acc -> 
      let live_after = live_after_node cfg key lives in
      let live = live_cfg_node value live_after and old_live = (match Hashtbl.find_option lives key with | None -> Set.empty | Some v -> v) in 
      let change = if Set.diff live old_live = Set.empty then false else (Hashtbl.replace lives key (Set.union live old_live); true) in
      change || acc
   ) cfg false

(* [live_cfg_fun f] calcule l'ensemble des variables vivantes avant chaque nœud
   du CFG en itérant [live_cfg_nodes] jusqu'à ce qu'un point fixe soit atteint.
   *)
let live_cfg_fun (f: cfg_fun) : (int, string Set.t) Hashtbl.t =
   let lives = Hashtbl.create 17 in
      let changed = ref true in
      while !changed do
         changed := live_cfg_nodes f.cfgfunbody lives
      done;
   lives
