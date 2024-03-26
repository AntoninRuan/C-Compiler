open Batteries
open BatList
open Elang
open Cfg
open Elang_run
open Cfg_run
open Rtl
open Rtl_print
open Utils
open Builtins
open Prog
open Elang_print

type state = {
  mem: Mem.t;
  regs: (reg, int) Hashtbl.t;
}

let init_state memsize =
  {
    mem = Mem.init memsize;
    regs = Hashtbl.create 17
  }

let eval_rtl_cmp = function
    Rcle -> (<=)
  | Rclt -> (<)
  | Rcge -> (>=)
  | Rcgt -> (>)
  | Rceq -> (=)
  | Rcne -> (<>)

let rec exec_rtl_instr oc rp rtlfunname f st (sp: int) (i: rtl_instr) =
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
      (if eval_rtl_cmp cmp v1 v2 then exec_rtl_instr_at oc rp rtlfunname f st sp s1 else OK (None, st))
    | _, _ -> Error (Printf.sprintf "Branching on undefined registers (%s and %s)" (print_reg r1) (print_reg r2))
    end
  | Rjmp lbl -> exec_rtl_instr_at oc rp rtlfunname f st sp lbl
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
  | Rcall (reg_option, fname, args) -> 
    let args_value = List.map (fun reg -> Hashtbl.find st.regs reg) args in
    find_function rp fname >>= (fun g ->
      exec_rtl_fun oc rp st (sp + f.rtlfunstksz) fname g args_value >>= (fun (result, st) ->
        (match reg_option with 
          | None -> OK (None, st)
          | Some rd -> (match result with 
            | None -> Error (Printf.sprintf "Function %s has not returned any value" fname) 
            | Some res -> Hashtbl.replace st.regs rd res; OK (None, st)
            )
        )  
      ) 
    )
  | Rstk (rd, ofs) -> Hashtbl.replace st.regs rd (sp + ofs); OK (None, st)
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

and exec_rtl_instr_at oc rp rtlfunname ({ rtlfunbody;  } as f: rtl_fun) st (sp: int) i =
  match Hashtbl.find_option rtlfunbody i with
  | Some l -> exec_rtl_instrs oc rp rtlfunname f st sp l
  | None -> Error (Printf.sprintf "Jump to undefined label (%s_%d)" rtlfunname i)

and exec_rtl_instrs oc rp rtlfunname f st (sp: int) l =
  List.fold_left (fun acc i ->
      match acc with
      | Error _ -> acc
      | OK (Some v, st) -> OK (Some v, st)
      | OK (None, st) ->
        exec_rtl_instr oc rp rtlfunname f st sp i
    ) (OK (None, st)) l

and exec_rtl_fun oc rp st (sp: int) rtlfunname f params =
  let regs' = Hashtbl.create 17 in
  match List.iter2 (fun n v -> Hashtbl.replace regs' n v) f.rtlfunargs params with
  | exception Invalid_argument _ ->
    Error (Format.sprintf "RTL: Called function %s with %d arguments, expected %d\n"
             rtlfunname
             (List.length params)
             (List.length f.rtlfunargs)
          )
  | _ ->
    match Hashtbl.find_option f.rtlfunbody f.rtlfunentry with
    | None ->
      Error (Printf.sprintf "Unknown node (%s_%d)" rtlfunname f.rtlfunentry)
    | Some l ->
      let regs_save = Hashtbl.copy st.regs in
      let st' = {st with regs = regs'; } in
      exec_rtl_instrs oc rp rtlfunname f st' sp l >>= fun (v, st) ->
      OK(v, {st with regs = regs_save })

and exec_rtl_prog oc rp memsize params =
  let st = init_state memsize in
  let rp = ("print", Gfun {
    rtlfunargs = [0];
    rtlfunstksz = 0;
    rtlfuninfo = [("x", 0)];
    rtlfunentry = 0;
    rtlfunbody = (let body = Hashtbl.create 1 in
    Hashtbl.replace body 0 [Rbuiltin("print", [0])];
    body)
  })::rp in
  find_function rp "main" >>= fun f ->
  let n = List.length f.rtlfunargs in
  let params = take n params in
  exec_rtl_fun oc rp st 0 "main" f params >>= fun (v, st) ->
  OK v


