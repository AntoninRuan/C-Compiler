open Batteries
open Elang
open Elang_gen
open Elang_print
open Cfg
open Utils
open Prog
open Report
open Cfg_print
open Options

(* [cfg_expr_of_eexpr e] converts an [Elang.expr] into a [expr res]. This should
   always succeed and be straightforward.

   In later versions of this compiler, you will add more things to [Elang.expr]
   but not to [Cfg.expr], hence the distinction.
*)
let rec cfg_expr_of_eexpr (f: efun) (e: Elang.expr) : expr res =
  match e with
  | Elang.Ebinop (b, lhe, rhe) ->
    cfg_expr_of_eexpr f lhe >>= fun e1 ->(
      cfg_expr_of_eexpr f rhe >>= ( fun e2 ->
        type_expr f.funtypvar f.funtypfun lhe >>= (fun lhe_t ->
          type_expr f.funtypvar f.funtypfun rhe >>= (fun rhe_t ->
            match (lhe_t, rhe_t) with
            | (Tptr t, Tint) -> 
              if (b = Eadd) || (b = Esub) then
                (size_type t) >>= (fun size -> OK (Ebinop(b, e1, Ebinop(Emul, e2, Eint size))))
              else
                Error (Format.sprintf "Operation (%s) between %s(%s) and %s(%s) is not defined"
                   (dump_binop b)
                   (dump_eexpr lhe) (string_of_type lhe_t)
                   (dump_eexpr rhe) (string_of_type rhe_t)
                )
            | (Tint, Tptr t) -> 
              if (b = Eadd) then
                (size_type t) >>= (fun size -> OK (Ebinop(b, (Ebinop(Emul, e1, Eint size)), e2)))
              else
                Error (Format.sprintf "Operation (%s) between %s(%s) and %s(%s) is not defined"
                   (dump_binop b)
                   (dump_eexpr lhe) (string_of_type lhe_t)
                   (dump_eexpr rhe) (string_of_type rhe_t)
                )
            | _ -> OK (Ebinop (b, e1, e2))  
          )  
        )
      )
    )
  | Elang.Eunop (u, e) ->
    cfg_expr_of_eexpr f e >>= fun ee ->
    OK (Eunop (u, ee))
  | Elang.Eint i -> OK (Eint i)
  | Elang.Echar c -> OK (Eint (int_of_char c))
  | Elang.Evar v ->
    if (Hashtbl.mem f.funvarinmem v) then(
      let typ = Hashtbl.find f.funtypvar v and ofs = Hashtbl.find f.funvarinmem v in
      size_type typ >>= fun size -> OK(Eload (Estk ofs, size))
    ) else
      OK (Evar v) 
  | Elang.Ecall (str, args) -> OK (Ecall (str, List.map (fun elt -> (cfg_expr_of_eexpr f elt) >>! identity) args))
  | Elang.Eaddrof expr -> 
    var_in_eaddr_of e >>= (fun var -> 
      let ofs = option_to_res_bind (Hashtbl.find_option (f.funvarinmem) var) 
      (Format.sprintf "Trying to take address of %s but it is not in memory" var)
      (fun x -> OK x) in 
      ofs >>= (fun ofs ->
         OK (Estk ofs)
      )  
    )
  | Elang.Eload expr -> 
    cfg_expr_of_eexpr f expr >>= (fun cexpr ->
      (type_expr f.funtypvar f.funtypfun expr) >>= (fun typ ->
        (size_type typ) >>= (fun size ->
          OK (Eload (cexpr, size))  
        )
      )  
    )

(* [cfg_node_of_einstr next cfg succ i] builds the CFG node(s) that correspond
   to the E instruction [i].

   [cfg] is the current state of the control-flow graph.

   [succ] is the successor of this node in the CFG, i.e. where to go after this
   instruction.

   [next] is the next available CFG node identifier.

   This function returns a pair (n, next) where [n] is the identifer of the
   node generated, and [next] is the new next available CFG node identifier.

   Hint: several nodes may be generated for a single E instruction.
*)
let rec cfg_node_of_einstr (f: efun) (next: int) (cfg : (int, cfg_node) Hashtbl.t)
    (succ: int) (i: instr) : (int * int) res =
  match i with
  | Elang.Iassign (v, e) -> (match e with
    | None -> 
      if not (Hashtbl.mem f.funvarinmem v) then Hashtbl.replace cfg next (Cassign(v, None, succ)); 
      OK (next, next + 1)
    | Some expr -> 
      cfg_expr_of_eexpr f expr >>= (fun e -> 
        if Hashtbl.mem f.funvarinmem v then
          let typ = Hashtbl.find f.funtypvar v and ofs = Hashtbl.find f.funvarinmem v in
          size_type typ >>= fun size -> Hashtbl.replace cfg next (Cstore(Estk ofs, e, size, succ)); OK(next, next + 1)
        else
          (Hashtbl.replace cfg next (Cassign(v, Some e, succ)); OK (next, next + 1))
      )
  )
    (* cfg_expr_of_eexpr e >>= fun e ->
    Hashtbl.replace cfg next (Cassign(v,e,succ));
    OK (next, next + 1) *)
  | Elang.Iif (c, ithen, ielse) ->
    cfg_expr_of_eexpr f c >>= fun c ->
    cfg_node_of_einstr f next cfg succ ithen >>= fun (nthen, next) ->
    cfg_node_of_einstr f next cfg succ ielse  >>= fun (nelse, next) ->
    Hashtbl.replace cfg next (Ccmp(c, nthen, nelse)); OK (next, next + 1)
  | Elang.Iwhile (c, i) ->
    cfg_expr_of_eexpr f c >>= fun c ->
    let (cmp, next) = (next, next+1) in
    cfg_node_of_einstr f next cfg cmp i >>= fun (nthen, next) ->
    Hashtbl.replace cfg cmp (Ccmp(c, nthen, succ)); OK (cmp, next + 1)
  | Elang.Iblock il ->
    List.fold_right (fun i acc ->
        acc >>= fun (succ, next) ->
        cfg_node_of_einstr f next cfg succ i
      ) il (OK (succ, next))
  | Elang.Ireturn e ->
    cfg_expr_of_eexpr f e >>= fun e ->
    Hashtbl.replace cfg next (Creturn e); OK (next, next + 1)
  | Elang.Icall (str, args) -> 
    Hashtbl.replace cfg next (Ccall(str, List.map (fun elt -> (cfg_expr_of_eexpr f elt) >>! identity) args, succ));
    OK (next, next + 1)
  | Elang.Istore (Eload e1, e2) -> (match e2 with
    | None -> Hashtbl.replace cfg next (Cnop(succ));OK(next, next + 1)
    | Some e2 -> 
      cfg_expr_of_eexpr f e1 >>= (fun lhe ->
        cfg_expr_of_eexpr f e2 >>= (fun rhe ->
          type_expr f.funtypvar f.funtypfun e1 >>= (fun lhe_t ->
            size_type lhe_t >>= fun size -> 
              Hashtbl.replace cfg next (Cstore (lhe, rhe, size, succ)); 
              OK(next, next + 1)  
          )
        )  
      ) 
  )
  | Elang.Istore (e1, _) -> Error (Format.sprintf "Trying to derefence %s but it is not a pointer" (dump_eexpr e1))
  | Elang.Ibuiltin _ -> Error "There should not be any builtin"

(* Some nodes may be unreachable after the CFG is entirely generated. The
   [reachable_nodes n cfg] constructs the set of node identifiers that are
   reachable from the entry node [n]. *)
let rec reachable_nodes n (cfg: (int,cfg_node) Hashtbl.t) =
  let rec reachable_aux n reach =
    if Set.mem n reach then reach
    else let reach = Set.add n reach in
      match Hashtbl.find_option cfg n with
      | None -> reach
      | Some (Cnop succ)
      | Some (Ccall (_, _, succ))
      | Some (Cstore (_, _, _, succ))
      | Some (Cbuiltin (_, _, succ))
      | Some (Cassign (_, _, succ)) -> reachable_aux succ reach
      | Some (Creturn _) -> reach
      | Some (Ccmp (_, s1, s2)) ->
        reachable_aux s1 (reachable_aux s2 reach)
  in reachable_aux n Set.empty

(* [cfg_fun_of_efun f] builds the CFG for E function [f]. *)
let cfg_fun_of_efun (f: efun) =
  let cfg = Hashtbl.create 17 in
  Hashtbl.replace cfg 0 (Creturn (Eint 0));
  cfg_node_of_einstr f 1 cfg 0 f.funbody >>= fun (node, _) ->
  (* remove unreachable nodes *)
  let r = reachable_nodes node cfg in
  Hashtbl.filteri_inplace (fun k _ -> Set.mem k r) cfg;
  OK { 
      cfgfunargs = f.funargs;
      cfgfunbody = cfg;
      cfgfunstksz = f.funstksz;
      cfgentry = node;
     }

let cfg_gdef_of_edef gd =
  match gd with
    Gfun f -> cfg_fun_of_efun f >>= fun f -> OK (Gfun f)

let cfg_prog_of_eprog (ep: eprog) : cfg_fun prog res =
  assoc_map_res (fun _ -> cfg_gdef_of_edef) ep

let pass_cfg_gen ep =
  match cfg_prog_of_eprog ep with
  | Error msg ->
    record_compile_result ~error:(Some msg) "CFG"; Error msg
  | OK cfg ->
    record_compile_result "CFG";
    dump !cfg_dump dump_cfg_prog cfg (call_dot "cfg" "CFG");
    OK cfg
