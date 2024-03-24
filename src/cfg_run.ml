open Prog
open Elang
open Elang_run
open Batteries
open BatList
open Cfg
open Utils
open Builtins

let rec eval_cfgexpr oc st (prog: cfg_fun prog) (e: expr) : (int * int state) res =
  match e with
  | Ebinop(b, e1, e2) ->
    eval_cfgexpr oc st prog e1 >>= fun (v1, st) ->
    eval_cfgexpr oc st prog e2 >>= fun (v2, st) ->
    let v = eval_binop b v1 v2 in
    OK (v, st)
  | Eunop(u, e) ->
    eval_cfgexpr oc st prog e >>= fun (v1, st) ->
    let v = (eval_unop u v1) in
    OK (v, st)
  | Eint i -> OK (i, st)
  | Evar s ->
    begin match Hashtbl.find_option st.env s with
      | Some v -> OK (v, st)
      | None -> Error (Printf.sprintf "Unknown variable %s\n" s)
    end
  | Ecall(str, args) -> let args, st = eval_args oc st prog args in 
    let result, st = (eval_cfgfun oc st prog str ((find_function prog str) >>! identity) args) >>! identity in 
    (match result with | None -> Error (Printf.sprintf "Function %s does has not returned any value" str) | Some value -> OK (value, st))

and eval_args oc (st: int state) prog args: (int list * int state) = 
  List.fold_left (
    fun (partial_args, st) elt -> let res, st = (eval_cfgexpr oc st prog elt) >>! identity in (partial_args @ [res], st)
  ) ([], st) args

and eval_cfginstr oc (st: int state) ht (prog: cfg_fun prog) (n: int): (int * int state) res =
  match Hashtbl.find_option ht n with
  | None -> Error (Printf.sprintf "Invalid node identifier\n")
  | Some node ->
    match node with
    | Cnop succ ->
      eval_cfginstr oc st ht prog succ
    | Cassign(v, e, succ) ->
      eval_cfgexpr oc st prog e >>= fun (i, st) ->
      Hashtbl.replace st.env v i;
      eval_cfginstr oc st ht prog succ
    | Ccmp(cond, i1, i2) ->
      eval_cfgexpr oc st prog cond >>= fun (i, st) ->
      if i = 0 then eval_cfginstr oc st ht prog i2 else eval_cfginstr oc st ht prog i1
    | Creturn(e) ->
      eval_cfgexpr oc st prog e >>= fun (e, st) ->
      OK (e, st)
    | Cprint(e, succ) ->
      eval_cfgexpr oc st prog e >>= fun (e, st) ->
      Format.fprintf oc "%d\n" e;
      eval_cfginstr oc st ht prog succ
    | Ccall (str, args, succ) -> let args, st = eval_args oc st prog args in
      let _, st = (eval_cfgfun oc st prog str ((find_function prog str) >>! identity) args) >>! identity in
      eval_cfginstr oc st ht prog succ

and eval_cfgfun oc st prog cfgfunname { cfgfunargs;
                                      cfgfunbody;
                                      cfgentry} (vargs: int list) =
  let st' = { st with env = Hashtbl.create 17 } in
  match List.iter2 (fun a v -> Hashtbl.replace st'.env a v) cfgfunargs vargs with
  | () -> eval_cfginstr oc st' cfgfunbody prog cfgentry >>= fun (v, st') ->
    OK (Some v, {st' with env = st.env})
  | exception Invalid_argument _ ->
    Error (Format.sprintf "CFG: Called function %s with %d arguments, expected %d.\n"
             cfgfunname (List.length vargs) (List.length cfgfunargs)
          )

let eval_cfgprog oc cp memsize params =
  let st = init_state memsize in
  find_function cp "main" >>= fun f ->
  let n = List.length f.cfgfunargs in
  let params = take n params in
  eval_cfgfun oc st cp "main" f params >>= fun (v, st) ->
  OK v


