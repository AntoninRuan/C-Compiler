open Ast
open Elang
open Prog
open Report
open Options
open Batteries
open Elang_print
open Utils

let tag_is_binop =
  function
    Tadd -> true
  | Tsub -> true
  | Tmul -> true
  | Tdiv -> true
  | Tmod -> true
  | Txor -> true
  | Tcle -> true
  | Tclt -> true
  | Tcge -> true
  | Tcgt -> true
  | Tceq -> true
  | Tne  -> true
  | _    -> false

let binop_of_tag =
  function
    Tadd -> Eadd
  | Tsub -> Esub
  | Tmul -> Emul
  | Tdiv -> Ediv
  | Tmod -> Emod
  | Txor -> Exor
  | Tcle -> Ecle
  | Tclt -> Eclt
  | Tcge -> Ecge
  | Tcgt -> Ecgt
  | Tceq -> Eceq
  | Tne -> Ecne
  | _ -> assert false

(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)
let rec make_eexpr_of_ast (a: tree) : expr res =
  let res =
    match a with
    | Node(t, [e1; e2]) when tag_is_binop t ->
        let lsubtree = error_fail (make_eexpr_of_ast e1) identity and rsubtree = error_fail (make_eexpr_of_ast e2) identity in
        OK (Ebinop (binop_of_tag t, lsubtree, rsubtree))
    | Node(t, [e1]) when t = Tneg -> let subtree = error_fail (make_eexpr_of_ast e1) identity in
        OK (Eunop (Eneg, subtree))
    | Node(t, [IntLeaf x]) when t = Tint -> OK (Eint x)
    | Node(t, [StringLeaf s]) when t = Tvar -> OK(Evar s)
    | Node(t, [StringLeaf s; Node(Targs, args)]) when t = Tfuncall -> let subtree_list = List.map make_eexpr_of_ast args in 
        let args_list = List.map (fun elt -> error_fail elt identity) subtree_list in OK (Ecall(s, args_list))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let rec make_einstr_of_ast (a: tree) : instr res =
  let res =
    match a with
    | Node(t, list) when t = Tblock -> let subtree_list = List.map make_einstr_of_ast list in
        let instr_list = List.map (fun elt -> error_fail elt identity) subtree_list in
        OK (Iblock instr_list)
    | Node(t, subtree) when t = Tif -> (
      match subtree with
      | [cnd; if_block; else_block] -> let ecnd_res = make_eexpr_of_ast cnd 
                                        and if_instr_res = make_einstr_of_ast if_block 
                                        and else_instr_res = make_einstr_of_ast else_block
        in let ecnd = error_fail ecnd_res identity and if_instr = error_fail if_instr_res identity and else_instr = error_fail else_instr_res identity
        in OK (Iif (ecnd, if_instr, else_instr))
      | [cnd; if_block] -> let ecnd_res = make_eexpr_of_ast cnd and if_instr_res = make_einstr_of_ast if_block 
        in let ecnd = error_fail ecnd_res identity and if_instr = error_fail if_instr_res identity
        in OK(Iif(ecnd , if_instr, Iblock []))
      | _ -> Error "" 
    )
    | Node(t, [cnd; instrs]) when t = Twhile -> let icnd_res = make_eexpr_of_ast cnd and instrs = make_einstr_of_ast instrs
      in let icnd = error_fail icnd_res identity and instrs = error_fail instrs identity in
      OK (Iwhile (icnd, instrs))
    | Node(t, [expr]) when t = Treturn -> let eexpr = error_fail (make_eexpr_of_ast expr) identity in OK(Ireturn eexpr)
    | Node(t, [expr]) when t = Tprint -> let eexpr = error_fail (make_eexpr_of_ast expr) identity in OK(Iprint eexpr)
    | Node(t, [id; expr]) when t = Tassign -> let eid = error_fail (make_eexpr_of_ast id) identity and eexpr = error_fail (make_eexpr_of_ast expr) identity
      in (match eid with 
        | (Evar str) -> OK (Iassign (str, eexpr))
        | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s. Left subtree must be of type Tvar when in Tassign" (string_of_ast a))
      )
    | Node(t, [StringLeaf s; Node(Targs, args)]) when t = Tfuncall -> let subtree_list = List.map make_eexpr_of_ast args in
        let args_list = List.map (fun elt -> error_fail elt identity) subtree_list in OK (Icall (s, args_list))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : string res =
  match a with
  | Node (Targ, [Node(Tvar, [s])]) ->
    OK (string_of_stringleaf s)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_fundef_of_ast (a: tree) : (string * efun) res =
  match a with
  | Node (Tfundef, [Node(Tfunname, [StringLeaf fname]); Node (Tfunargs, fargs); Node(Tfunbody, [fbody])]) ->
    list_map_res make_ident fargs >>= fun fargs ->
     let funbody = (make_einstr_of_ast fbody) >>! identity in
     OK (fname, {funargs = fargs; funbody = funbody})
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a))

let make_eprog_of_ast (a: tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
    list_map_res (fun a -> make_fundef_of_ast a >>= fun (fname, efun) -> OK (fname, Gfun efun)) l
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tlistglobdef, got %s."
             (string_of_ast a))

let pass_elang ast =
  match make_eprog_of_ast ast with
  | Error msg ->
    record_compile_result ~error:(Some msg) "Elang";
    Error msg
  | OK  ep ->
    dump !e_dump dump_e ep (fun file () ->
        add_to_report "e" "E" (Code (file_contents file))); OK ep

