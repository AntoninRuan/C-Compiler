open Prog
open Elang
open Elang_run
open Batteries
open BatList
open Cfg
open Cfg_print
open Utils
open Builtins

let rec eval_cfgexpr oc st (prog: cfg_fun prog) (f: cfg_fun) (sp: int) (e: expr) : (int * (int option) state) res =
  match e with
  | Ebinop(b, e1, e2) ->
    eval_cfgexpr oc st prog f sp e1 >>= fun (v1, st) ->
    eval_cfgexpr oc st prog f sp e2 >>= fun (v2, st) ->
    let v = eval_binop b v1 v2 in
    OK (v, st)
  | Eunop(u, e) ->
    eval_cfgexpr oc st prog f sp e >>= fun (v1, st) ->
    let v = (eval_unop u v1) in
    OK (v, st)
  | Eint i -> OK (i, st)
  | Evar s ->
    begin match Hashtbl.find_option st.env s with
      | Some (Some v) -> OK (v, st)
      | _ -> Error (Printf.sprintf "Unknown variable %s\n" s)
    end
  | Ecall(str, args) -> 
    let args, st = eval_args oc st prog f sp args in
    (find_function prog str) >>= (fun g ->
      eval_cfgfun oc st prog str g (sp + f.cfgfunstksz) args >>= (fun (result, st) ->
        match result with
        | None -> Error (Printf.sprintf "Function %s does has not returned any value" str)
        | Some value -> OK(value, st)  
      )  
    )
    (* let result, st = (eval_cfgfun oc st prog str ((find_function prog str) >>! identity) sp args) >>! identity in 
    (match result with | None -> Error (Printf.sprintf "Function %s does has not returned any value" str) | Some value -> OK (value, st)) *)
  | Estk ofs -> OK (ofs + sp, st)
  | Eload (expr, sz) -> 
    eval_cfgexpr oc st prog f sp expr >>= (fun (addr, st) ->
      let mem_read_res = Mem.read_bytes_as_int st.mem addr (sz) in
      mem_read_res >>= fun x -> OK(x, st)  
    )

and eval_args oc (st: (int option) state) (prog: cfg_fun prog) (f: cfg_fun) (sp: int) args: (int list * (int option) state) = 
  List.fold_left (
    fun (partial_args, st) elt -> let res, st = (eval_cfgexpr oc st prog f sp elt) >>! identity in (partial_args @ [res], st)
  ) ([], st) args

and eval_cfginstr oc (st: (int option) state) ht (prog: cfg_fun prog) (f: cfg_fun) (sp: int) (n: int): (int * (int option) state) res =
  match Hashtbl.find_option ht n with
  | None -> Error (Printf.sprintf "Invalid node identifier\n")
  | Some node ->
    match node with
    | Cnop succ ->
      eval_cfginstr oc st ht prog f sp succ
    | Cassign(v, None, succ) ->
      Hashtbl.replace st.env v None;
      eval_cfginstr oc st ht prog f sp succ
    | Cassign(v, Some e, succ) ->
      eval_cfgexpr oc st prog f sp e >>= fun (i, st) ->
      Hashtbl.replace st.env v (Some i);
      eval_cfginstr oc st ht prog f sp succ
    | Ccmp(cond, i1, i2) ->
      eval_cfgexpr oc st prog f sp cond >>= fun (i, st) ->
      if i = 0 then eval_cfginstr oc st ht prog f sp i2 else eval_cfginstr oc st ht prog f sp i1
    | Creturn(e) ->
      eval_cfgexpr oc st prog f sp e >>= fun (e, st) ->
      OK (e, st)
    | Ccall (str, args, succ) -> 
      let args, st = eval_args oc st prog f sp args in
      find_function prog str >>= (fun g ->
        eval_cfgfun oc st prog str g (sp + f.cfgfunstksz) args >>= (fun (_, st) -> eval_cfginstr oc st ht prog f sp succ)
      )
      (* let _, st = (eval_cfgfun oc st prog str ((find_function prog str) >>! identity) sp args) >>! identity in
         eval_cfginstr oc st ht prog f sp succ *)
    | Cstore (lhe, rhe, sz, succ) -> 
      eval_cfgexpr oc st prog f sp lhe >>= (fun (addr, st) ->
        eval_cfgexpr oc st prog f sp rhe >>= (fun (v, st) ->
          let mem_write_res = Mem.write_bytes st.mem addr (split_bytes sz v) in
          mem_write_res >>= fun () -> eval_cfginstr oc st ht prog f sp succ
        )
      )
    | Cbuiltin (fname, args, succ) ->
      let _ = do_builtin oc st.mem fname (List.map (fun elt -> 
        let res = option_to_res_bind (Hashtbl.find st.env elt) 
        (Format.sprintf "Variable %s not initialized" elt)
        (fun x -> OK x) in 
        res >>! identity
      ) args) in 
      eval_cfginstr oc st ht prog f sp succ


and eval_cfgfun oc st prog cfgfunname (f: cfg_fun) (sp: int) (vargs: int list) =
  let st' = { st with env = Hashtbl.create 17 } in
  match List.iter2 (fun (a, _) v -> Hashtbl.replace st'.env a (Some v)) f.cfgfunargs vargs with
  | () -> 
    (* Format.fprintf oc "Call %s with sp=%d and args (%s)\n" cfgfunname sp (String.concat ", " (List.map (Format.sprintf "%d") vargs)); *)
    eval_cfginstr oc st' f.cfgfunbody prog f sp f.cfgentry >>= fun (v, st') ->
    OK (Some v, {st' with env = st.env})
  | exception Invalid_argument _ ->
    Error (Format.sprintf "CFG: Called function %s with %d arguments, expected %d.\n"
             cfgfunname (List.length vargs) (List.length f.cfgfunargs)
          )

let eval_cfgprog oc cp memsize params =
  let st = init_state memsize in
  let cp = ("print", Gfun {
    cfgentry = 1;
    cfgfunargs = [("x", Tint)];
    cfgfunstksz = 0;
    cfgfunbody = (let body = Hashtbl.create 1 in 
    Hashtbl.replace body 1 (Cbuiltin("print", ["x"], 0));
    Hashtbl.replace body 0 (Creturn(Eint 0));
    body) 
  })::cp in
  find_function cp "main" >>= fun f ->
  let n = List.length f.cfgfunargs in
  let params = take n params in
  eval_cfgfun oc st cp "main" f 0 params >>= fun (v, st) ->
  OK v


