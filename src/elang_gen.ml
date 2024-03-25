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

let rec type_expr (typ_var: (string, typ) Hashtbl.t) (typ_fun: (string, typ list * typ) Hashtbl.t) (e: expr) : typ res =
  match e with
  | Ebinop (binop, lexpr, rexpr) -> 
    (type_expr typ_var typ_fun lexpr) >>= (fun ltype ->
      (type_expr typ_var typ_fun rexpr) >>= (fun rtype -> 
        let _, res = are_compatible ltype rtype in
        res >>= (fun retype -> OK (retype))
      )
    )
  | Eunop (unop, expr) -> type_expr typ_var typ_fun expr
  | Eint int -> OK (Tint)
  | Evar str -> option_to_res_bind (Hashtbl.find_option typ_var str) 
    (Format.sprintf "Undeclared variable %s in expr %s" str (dump_eexpr e)) 
    (fun t -> OK (t))
  | Echar char -> OK Tchar
  | Ecall (str, exprs) -> option_to_res_bind (Hashtbl.find_option typ_fun str)
    (Format.sprintf "Undeclared function %s in expr %s\n" str (dump_eexpr e))
    (fun (_, rt) -> OK (rt))
and are_compatible (t1: typ) (t2: typ): (bool * typ res) = 
  match (t1, t2) with
  | (Tint, Tint)
  | (Tint, Tchar)
  | (Tchar, Tint) -> (true, OK Tint)
  | (Tchar, Tchar) -> (true, OK Tchar)
  | _ -> (false, Error (Format.sprintf "Incompatible type %s and %s\n" (string_of_type t1) (string_of_type t2)))
  
(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)
let rec make_eexpr_of_ast (typ_var: (string, typ) Hashtbl.t) (typ_fun: (string, typ list * typ) Hashtbl.t) (a: tree) : expr res =
  let res =
    match a with
    | Node(t, [e1; e2]) when tag_is_binop t ->
      (make_eexpr_of_ast typ_var typ_fun e1) >>= (fun lexpr ->
        (make_eexpr_of_ast typ_var typ_fun e2) >>= (fun rexpr ->
          let retexpr = Ebinop(binop_of_tag t, lexpr, rexpr) in
          (type_expr typ_var typ_fun rexpr) >>= (fun _ -> OK (retexpr))
          )
        )
        (* let lsubtree = error_fail (make_eexpr_of_ast typ_var typ_fun e1) identity and rsubtree = error_fail (make_eexpr_of_ast typ_var typ_fun e2) identity in
        OK (Ebinop (binop_of_tag t, lsubtree, rsubtree)) *)
    | Node(t, [e1]) when t = Tneg -> 
      (make_eexpr_of_ast typ_var typ_fun e1) >>= (fun expr ->
        let retexpr = Eunop(Eneg, expr) in
        (type_expr typ_var typ_fun retexpr) >>= (fun _ -> OK (retexpr))
        )
      (* let subtree = error_fail (make_eexpr_of_ast typ_var typ_fun e1) identity in
        OK (Eunop (Eneg, subtree)) *)
    | Node(t, [IntLeaf x]) when t = Tlitteral -> OK (Eint x)
    | Node(t, [CharLeaf c]) when t = Tlitteral -> OK (Echar c)
    | Node(t, (StringLeaf s)::_) when t = Tvar -> OK(Evar s)
    | Node(t, [StringLeaf s; Node(Targs, args)]) when t = Tfuncall -> 
      let subtree_list = List.map (make_eexpr_of_ast typ_var typ_fun) args in 
      let args_list = List.map (fun elt -> error_fail elt identity) subtree_list in
      let fun_sign = option_to_res_bind (Hashtbl.find_option typ_fun s)
        (Format.sprintf "Undeclared function %s\n" s)
        (fun sign -> OK sign)
      in
      fun_sign >>= (fun (args_t, ret_t) -> 
        let exprs_t = List.map(fun elt -> (type_expr typ_var typ_fun elt) >>! identity) args_list in
        if (List.equal (=) args_t exprs_t) then
          let retexpr = Ecall(s, args_list) in
          (type_expr typ_var typ_fun retexpr) >>= (fun typ -> 
            if typ = Tvoid then
              Error (Format.sprintf "Cannot call void function %s in an expression" s)
            else
              OK(retexpr)
          )
        else
          Error (Format.sprintf "Function call of %s does not fit function signature" s)
      )  
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s\n"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let rec make_einstr_of_ast (cfun: string) (typ_var: (string, typ) Hashtbl.t) (typ_fun: (string, typ list * typ) Hashtbl.t) (a: tree) : instr res =
  let res =
    match a with
    | Node(t, list) when t = Tblock -> 
      let subtree_list = List.map (make_einstr_of_ast cfun typ_var typ_fun) list in
      let instr_list = List.map (fun elt -> error_fail elt identity) subtree_list in
      OK (Iblock instr_list)
    | Node(t, subtree) when t = Tif -> (
      match subtree with
      | [cnd; if_block; else_block] -> 
        (make_eexpr_of_ast typ_var typ_fun cnd) >>= (fun ecnd ->
          (make_einstr_of_ast cfun typ_var typ_fun if_block) >>= (fun if_instrs ->
            (make_einstr_of_ast cfun typ_var typ_fun else_block) >>= (fun else_instrs ->
              (type_expr typ_var typ_fun ecnd) >>= (fun cnd_type -> 
                (snd (are_compatible Tint cnd_type)) >>= (fun _ -> 
                  OK (Iif (ecnd, if_instrs, else_instrs)) 
                )
              ) 
            )  
          )  
        )
        (* let ecnd_res = make_eexpr_of_ast typ_var typ_fun cnd 
          and if_instr_res = make_einstr_of_ast typ_var typ_fun if_block 
          and else_instr_res = make_einstr_of_ast typ_var typ_fun else_block in
        let ecnd = error_fail ecnd_res identity 
          and if_instr = error_fail if_instr_res identity 
          and else_instr = error_fail else_instr_res identity
        in OK (Iif (ecnd, if_instr, else_instr)) *)
      | [cnd; if_block] -> 
        (make_eexpr_of_ast typ_var typ_fun cnd) >>= (fun ecnd ->
          (make_einstr_of_ast cfun typ_var typ_fun if_block) >>= (fun if_instrs ->
            (type_expr typ_var typ_fun ecnd) >>= (fun cnd_type ->
              (snd (are_compatible Tint cnd_type)) >>= (fun _ ->
                OK(Iif(ecnd, if_instrs, Iblock []))  
              )  
            )  
          )  
        )
        (* let ecnd_res = make_eexpr_of_ast typ_var typ_fun cnd and if_instr_res = make_einstr_of_ast typ_var typ_fun if_block 
        in let ecnd = error_fail ecnd_res identity and if_instr = error_fail if_instr_res identity
        in OK(Iif(ecnd , if_instr, Iblock [])) *)
      | _ -> Error "" 
    )
    | Node(t, [cnd; instrs]) when t = Twhile -> 
      (make_eexpr_of_ast typ_var typ_fun cnd) >>= (fun ecnd ->
        (make_einstr_of_ast cfun typ_var typ_fun instrs) >>= (fun instrs ->
          (type_expr typ_var typ_fun ecnd) >>= (fun cnd_type ->
            (snd (are_compatible Tint cnd_type)) >>= (fun _ -> OK(Iwhile(ecnd, instrs)))  
          )  
        )  
      )
      (* let icnd_res = make_eexpr_of_ast typ_var typ_fun cnd and instrs = make_einstr_of_ast typ_var typ_fun instrs
      in let icnd = error_fail icnd_res identity and instrs = error_fail instrs identity in
      OK (Iwhile (icnd, instrs)) *)
    | Node(t, [expr]) when t = Treturn -> 
      (make_eexpr_of_ast typ_var typ_fun expr) >>= (fun expr ->
        (type_expr typ_var typ_fun expr) >>= (fun ret_type ->
          let _, sret_type = Hashtbl.find typ_fun cfun in 
          if (fst (are_compatible sret_type ret_type)) then
            OK (Ireturn expr)
          else 
            Error (Format.sprintf "Wrong return type for function %s, expected %s got %s" 
              cfun
              (string_of_type sret_type)
              (string_of_type ret_type)
            )  
        )  
      )
      (* let eexpr = error_fail (make_eexpr_of_ast typ_var typ_fun expr) identity in OK(Ireturn eexpr) *)
    | Node(t, (Node(Tvar, (StringLeaf id)::typ))::s) when t = Tassign ->
      let get_type (potential_type: typ option) : typ res =
        option_to_res_bind potential_type
        (Format.sprintf "Undeclared variable %s" id)
        (fun typ -> OK typ)
      in
      let potential_type = (match typ with 
        | (Node(Ttype, [TypeLeaf t]))::_ -> Some t 
        | _ -> Hashtbl.find_option typ_var id
        ) in 
      (get_type potential_type) >>= (fun typ ->
        match typ with
        | Tvoid -> Error (Format.sprintf "Cannot declare variable %s as type void" id)
        | _ -> Hashtbl.replace typ_var id typ; (match s with 
          | [] -> OK (Iassign(id, None))
          | expr::_ -> (make_eexpr_of_ast typ_var typ_fun expr) >>= (fun expr ->
              (type_expr typ_var typ_fun expr) >>= (fun t_expr ->
                if (fst (are_compatible typ t_expr)) then 
                  OK (Iassign(id, Some expr))
                else 
                  Error (Format.sprintf "Incompatible type trying to assign %s type to %s type variable %s" 
                    (string_of_type t_expr) 
                    (string_of_type typ)
                    id )  
              )
            )
        )
      )
      (* let eid = error_fail (make_eexpr_of_ast typ_var typ_fun id) identity
      in (match eid with 
        | (Evar str) -> (match s with | [] -> OK (Iassign (str, None)) | expr::_ -> OK (Iassign (str, Some ((make_eexpr_of_ast typ_var typ_fun expr) >>! identity))))
        | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s. Left subtree must be of type Tvar when in Tassign" (string_of_ast a))
      ) *)
    | Node(t, [StringLeaf s; Node(Targs, args)]) when t = Tfuncall -> 
      let subtree_list = List.map (make_eexpr_of_ast typ_var typ_fun) args in
      let args_list = List.map (fun elt -> error_fail elt identity) subtree_list in 
      let fun_sig = option_to_res_bind (Hashtbl.find_option typ_fun s) 
        (Format.sprintf "Undeclared function %s" s)
        (fun sign -> OK sign)
      in
      fun_sig >>= (fun (args_t, ret_t) ->
        let exprs_t = List.map (fun elt -> (type_expr typ_var typ_fun elt) >>! identity) args_list in
        if (List.equal (=) args_t exprs_t) then 
          OK (Icall(s, args_list)) 
        else 
          Error (Format.sprintf "Function call of %s does not fit function signature" s)
      )
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : (string * typ) res =
  match a with
  | Node (Targ, [Node(Tvar, [s; Node(Ttype, [t])])]) ->
    OK (string_of_stringleaf s, typ_of_typeleaf t)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_funsig_of_ast (a: tree) : (string * (typ list * typ) ) res =
  match a with
  | Node (Tfundef, [Node(Ttype, [typ]); Node(Tfunname, [StringLeaf fname]); Node(Tfunargs, fargs); Node(Tfunbody, _)]) ->
    list_map_res make_ident fargs >>= (fun fargs ->
      OK (fname, (List.map (snd) fargs, typ_of_typeleaf typ))
    )
  | _ -> 
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s." (string_of_ast a))

let make_fundef_of_ast (typ_fun: (string, typ list * typ) Hashtbl.t) (a: tree) : (string * efun option) res =
  match a with
  | Node (Tfundef, [Node(Ttype, [typ]); Node(Tfunname, [StringLeaf fname]); Node (Tfunargs, fargs); Node(Tfunbody, [fbody])]) ->
    list_map_res make_ident fargs >>= fun fargs ->
      let fun_sign = option_to_res_bind (Hashtbl.find_option typ_fun fname)
        (Format.sprintf "Undeclared function %s" fname)
        (fun x -> OK x) in
      fun_sign >>= (fun sign ->
        (make_funsig_of_ast a) >>= (fun potential_sig -> 
          let typ_var = Hashtbl.create 17 in
          List.iter (fun (var_name, typ) -> Hashtbl.replace typ_var var_name typ) fargs;
          let funbody = (make_einstr_of_ast fname typ_var typ_fun fbody) >>! identity in
          OK (fname, Some {funreturntype = typ_of_typeleaf typ;funargs = fargs; funbody = funbody})
        ) 
      )
  | Node (Tfundef, [Node(Ttype, [typ]); Node(Tfunname, [StringLeaf fname]); Node (Tfunargs, fargs); Node(Tfunbody, _)]) ->
    OK (fname, None)
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a))

let make_eprog_of_ast (a: tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
    let typ_fun = Hashtbl.create (List.length l) in
    Hashtbl.replace typ_fun "print" ([Tint], Tvoid);
    Hashtbl.replace typ_fun "print_int" ([Tint], Tvoid);
    Hashtbl.replace typ_fun "print_char" ([Tchar], Tvoid); 
    let _ = list_map_res (fun a -> 
      make_funsig_of_ast a >>= (fun (fname, sign) -> 
        Hashtbl.replace typ_fun fname sign; OK None
        (* OK (fname, Gfun efun) *)
      )
    ) l in
    let potential_fun = list_map_res (fun a ->
      make_fundef_of_ast typ_fun a >>= (fun (fname, efun_option ) -> OK (fname, efun_option))
    ) l in 
    potential_fun >>= (fun potential_fun -> 
      let funs = List.filter (fun (_, option) -> match option with | None -> false | Some _ -> true) potential_fun in
      list_map_res (fun (fname, f) ->
        OK (fname, Gfun (Option.get f))
      ) funs
    )
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

