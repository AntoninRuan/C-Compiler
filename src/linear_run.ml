open Batteries
open BatList
open Prog
open Elang
open Cfg
open Elang_run
open Cfg_run
open Rtl
open Rtl_print
open Rtl_run
open Linear
open Builtins
open Utils

let rec exec_linear_instr oc lp fname f st (sp: int) (i: rtl_instr) =
  match i with
  | Rbinop (b, rd, rs1, rs2) ->
    begin match Hashtbl.find_option st.regs rs1,
                Hashtbl.find_option st.regs rs2 with
    | Some v1, Some v2 ->
               Hashtbl.replace st.regs rd (eval_binop b v1 v2);
      OK (None, st)
    | _, _ -> Error (Printf.sprintf "Binop applied on undefined registers (%s and %s)" (print_reg rs1) (print_reg rs2))
    end
  | Runop (u, rd, rs) ->
    begin match Hashtbl.find_option st.regs rs with
      | Some v ->
      Hashtbl.replace st.regs rd (eval_unop u v);
      OK (None, st)
    | _ -> Error (Printf.sprintf "Unop applied on undefined register %s" (print_reg rs))
    end
  | Rconst (rd, i) ->
    Hashtbl.replace st.regs rd i;
    OK (None, st)
  | Rbranch (cmp, r1, r2, s1) ->
    begin match Hashtbl.find_option st.regs r1,
                Hashtbl.find_option st.regs r2 with
    | Some v1, Some v2 ->
      if eval_rtl_cmp cmp v1 v2 then exec_linear_instr_at oc lp fname f st sp s1 else OK (None, st)
    | _, _ -> Error (Printf.sprintf "Branching on undefined registers (%s and %s)" (print_reg r1) (print_reg r2))
    end
  | Rjmp s -> exec_linear_instr_at oc lp fname f st sp s
  | Rmov (rd, rs) ->
    begin match Hashtbl.find_option st.regs rs with
    | Some s ->
      Hashtbl.replace st.regs rd s;
      OK (None, st)
    | _ -> Error (Printf.sprintf "Mov on undefined register (%s)" (print_reg rs))
    end
  | Rret r ->
    begin match Hashtbl.find_option st.regs r with
      | Some s -> OK (Some s, st)
      | _ -> Error (Printf.sprintf "Ret on undefined register (%s)" (print_reg r))
    end
  | Rlabel n -> OK (None, st)
  | Rcall(rd, gname, args) -> 
    let args_value = List.map (fun reg -> Hashtbl.find st.regs reg) args in
    find_function lp gname >>= (fun g ->
      exec_linear_fun oc lp st (sp + f.linearfunstksz) gname g args_value >>= (fun (result, st) ->
        (match rd with 
          | None -> OK (None, st)
          | Some rd -> (match result with 
            | None -> Error (Printf.sprintf "Function %s does has not returned any value" fname) 
            | Some res -> Hashtbl.replace st.regs rd res; OK (None, st)
            )
        )  
      )
    )
    (* let result, st = (exec_linear_fun oc lp st sp fname ((find_function lp fname) >>! identity) args_value) >>! identity in
    (match rd with 
      | None -> OK (None, st)
      | Some rd -> (match result with 
        | None -> Error (Printf.sprintf "Function %s does has not returned any value" fname) 
        | Some res -> Hashtbl.replace st.regs rd res; OK (None, st)
        )
    ) *)
    | Rstk (rd, ofs) -> Hashtbl.replace st.regs rd (sp - ofs); OK (None, st)
    | Rload (rd, rs, sz) -> 
      (match Hashtbl.find_option st.regs rs with
      | Some addr -> 
        Mem.read_bytes_as_int st.mem addr sz >>= fun v -> Hashtbl.replace st.regs rd v; OK (None, st)
      | None -> Error (Format.sprintf "load on undefined register (%s)" (print_reg rs)) 
      )
    | Rstore (rd, rs, sz) -> 
      (match (Hashtbl.find_option st.regs rd, Hashtbl.find_option st.regs rs) with
      | (Some addr, Some v) -> 
        Mem.write_bytes st.mem addr (split_bytes sz v) >>= fun () -> OK (None, st)
      | _ -> Error (Format.sprintf "store on some undefined register (%s, %s)" (print_reg rd) (print_reg rs)))
    | Rbuiltin (fname, args) -> let _ = do_builtin oc st.mem fname (List.map (fun elt -> 
        Hashtbl.find st.regs elt
    ) args) in OK (None, st)

and exec_linear_instr_at oc lp fname ({  linearfunbody;  } as f) st (sp:int) i =
  let l = List.drop_while (fun x -> x <> Rlabel i) linearfunbody in
  exec_linear_instrs oc lp fname f st sp l

and exec_linear_instrs oc lp fname f st (sp: int) l =
  List.fold_left (fun acc i ->
      match acc with
      | Error _ -> acc
      | OK (Some v, st) -> OK (Some v, st)
      | OK (None, st) ->
        exec_linear_instr oc lp fname f st sp i
    ) (OK (None, st)) l

and exec_linear_fun oc lp st (sp: int) fname f params =
  let regs' = Hashtbl.create 17 in
  match List.iter2 (fun n v -> Hashtbl.replace regs' n v) f.linearfunargs params with
  | exception Invalid_argument _ ->
   Error (Format.sprintf "Linear: Called function %s with %d arguments, expected %d\n" fname
            (List.length params) (List.length f.linearfunargs))
  | _ ->
    let l = f.linearfunbody in
    let regs_save = Hashtbl.copy st.regs in
    let st' = {st with regs = regs' } in
    exec_linear_instrs oc lp fname f st' sp l >>= fun (v,st) ->
    OK(v, {st with regs = regs_save })

and exec_linear_prog oc lp memsize params =
  let st = init_state memsize in
  let lp = ("print", Gfun {
    linearfunargs = [0];
    linearfunstksz = 0;
    linearfuninfo = [("x", 0)];
    linearfunbody = [Rbuiltin("print", [0])]
  })::lp in
  find_function lp "main" >>= fun f ->
  let n = List.length f.linearfunargs in
  let params = take n params in
  exec_linear_fun oc lp st 0 "main" f params >>= fun (v, st) ->
  OK v


