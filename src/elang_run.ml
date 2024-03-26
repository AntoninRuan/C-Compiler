open Elang
open Elang_gen
open Elang_print
open Batteries
open Prog
open Utils
open Builtins

let binop_bool_to_int f x y = if f x y then 1 else 0

(* [eval_binop b x y] évalue l'opération binaire [b] sur les arguments [x]
   et [y]. *)
let eval_binop (b: binop) : int -> int -> int =
  match b with
   | Eadd -> fun x y -> x + y
   | Emul -> fun x y -> x * y
   | Emod -> fun x y -> x mod y
   | Exor -> fun x y -> x lxor y
   | Ediv -> fun x y -> x / y
   | Esub -> fun x y -> x - y
   | Eclt -> fun x y -> Bool.to_int (x < y)
   | Ecle -> fun x y -> Bool.to_int (x <= y)
   | Ecgt -> fun x y -> Bool.to_int (x > y)
   | Ecge -> fun x y -> Bool.to_int (x >= y)
   | Eceq -> fun x y -> Bool.to_int (x = y)
   | Ecne -> fun x y -> Bool.to_int (x <> y)

(* [eval_unop u x] évalue l'opération unaire [u] sur l'argument [x]. *)
let eval_unop (u: unop) : int -> int =
  match u with
   | Eneg -> fun x -> -x

(* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
   erreur si besoin. *)
let rec eval_eexpr oc (st: (int option) state) (prog: eprog) (f: efun) (sp: int) (e : expr) : (int * (int option) state) res =
   match e with 
   | Ebinop (op, lhe, rhe) -> 
      (eval_eexpr oc st prog f sp lhe) >>= (fun (x, st) ->
         (eval_eexpr oc st prog f sp rhe) >>= (fun (y, st) ->
            (type_expr f.funtypvar f.funtypfun lhe) >>= (fun lhe_t ->
               (type_expr f.funtypvar f.funtypfun rhe) >>= (fun rhe_t ->
                  match (lhe_t, rhe_t) with
                  | (Tptr t, Tint) -> 
                     if (op = Eadd) || (op = Esub) then
                        (size_type t) >>= (fun size -> OK ((eval_binop op) x (y * size), st))
                     else
                        Error (Format.sprintf "Operation (%s) between %s(%s) and %s(%s) is not defined"
                           (dump_binop op)
                           (dump_eexpr lhe) (string_of_type lhe_t)
                           (dump_eexpr rhe) (string_of_type rhe_t)
                        )
                  | (Tint, Tptr t) -> 
                     if op = Eadd then
                        (size_type t) >>= (fun size -> OK ((eval_binop op) (x * size) y, st))
                     else
                        Error (Format.sprintf "Operation (%s) between %s(%s) and %s(%s) is not defined"
                           (dump_binop op)
                           (dump_eexpr lhe) (string_of_type lhe_t)
                           (dump_eexpr rhe) (string_of_type rhe_t)
                        )
                  | _ -> OK ((eval_binop op) x y, st)  
               )   
            )
         ) 
      )
   | Eunop (op, x) -> (eval_eexpr oc st prog f sp x) >>= fun (x, st) -> OK ((eval_unop op) x, st)
   | Echar c -> OK (int_of_char c, st)
   | Eint x -> OK(x, st)
   | Evar str ->
      let potential_v = Hashtbl.find_option st.env str in (match potential_v with 
      | Some v -> (match v with | None -> Error (Format.sprintf "Variable %s not initialized" str) | Some x -> OK(x, st))
      | None -> option_to_res_bind (Hashtbl.find_option f.funvarinmem str)
         (Format.sprintf "Variable %s not declared" str)
         (fun ofs -> 
            (size_type (Hashtbl.find f.funtypvar str)) >>= (fun size ->
               Mem.read_bytes_as_int st.mem (sp + ofs) size >>= fun res -> OK (res, st) 
            )  
         )
      ) 
      (* option_to_res_bind (Hashtbl.find_option st.env str) 
      (Printf.sprintf "Variable %s not declared" str) 
      (fun a -> match a with 
         | None -> Error (Printf.sprintf "Variable %s not initialized" str) 
         | Some x -> OK(x, st)) *)
   | Ecall (str, args) -> 
      let args_values, st = eval_args oc st prog f sp args in
      (find_function prog str) >>= (fun g ->
         eval_efun oc st prog (sp + f.funstksz) g str args_values >>= (fun (res, st) ->
            match res with 
               | None -> Error (Printf.sprintf "Function %s has not returned any value" str)
               | Some v -> OK(v, st)   
         )   
      )
   | Eaddrof expr -> (var_in_eaddr_of e) >>= (fun var -> 
      let ofs = option_to_res_bind (Hashtbl.find_option (f.funvarinmem) var) 
      (Format.sprintf "Trying to take address of %s but it is not in memory" var)
      (fun x -> OK x)
      in 
      ofs >>= (fun ofs ->
         OK(sp + ofs, st)  
      )
   )
   | Eload expr -> (eval_eexpr oc st prog f sp expr) >>= (fun (addr, st) -> 
      (type_expr f.funtypvar f.funtypfun expr) >>= (fun typ ->
         (size_type typ) >>= (fun size ->
            let res = Mem.read_bytes_as_int st.mem addr size in
            res >>= (fun res ->
               OK (res, st)   
            )   
         )
      )
   )

(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
and eval_einstr oc (st: (int option) state) (prog: eprog) (f: efun) (sp: int) (ins: instr) :
  (int option * (int option) state) res =
   match ins with
   | Iassign (str, exp) -> 
      (match exp with 
      | None -> if not (Hashtbl.mem f.funvarinmem str) then Hashtbl.replace st.env str None; OK(None, st)
      | Some expr -> (eval_eexpr oc st prog f sp expr) >>= (fun (x, st) -> 
         if (Hashtbl.mem f.funvarinmem str) then (
            let typ = Hashtbl.find f.funtypvar str 
            in (size_type typ) >>= (fun size ->
               let res = Mem.write_bytes st.mem (sp + (Hashtbl.find f.funvarinmem str)) (split_bytes size x) in
               res >>= (fun () -> OK(None, st))  
            )
         ) else (
            Hashtbl.replace st.env str (Some x); 
            OK (None, st)
         )
      )
      )
      (* let result, st = (eval_eexpr oc st prog exp) >>! identity in Hashtbl.replace st.env str result; OK (None, st) *)
   | Iif (cnd, if_instr, else_instr) -> 
      let cmp_res, st = ((eval_eexpr oc st prog f sp cnd) >>! identity) in 
      if cmp_res = 1 then 
         (eval_einstr oc st prog f sp if_instr) 
      else 
         eval_einstr oc st prog f sp else_instr
   | Iwhile (cnd, instr) -> let res = ref (None, st) and cont = ref true in 
      while (let cmp_res, st = ((eval_eexpr oc (snd !res) prog f sp cnd) >>! identity) in res := (fst !res, st);cmp_res = 1) && !cont do 
         res := (eval_einstr oc (snd !res) prog f sp instr) >>! identity; 
         (match !res with
         | (Some v, _) -> cont := false; ()
         | (None, _) -> cont := true; ()
         );
      done;
      OK (!res)
   | Iblock instrs -> List.fold_left (fun acc elt -> 
      let (old_res, old_st) = acc >>! identity in 
      (match old_res with | None -> (eval_einstr oc old_st prog f sp elt) | Some value -> acc)
      ) (OK (None, st)) instrs 
   | Ireturn expr -> let value, st = (eval_eexpr oc st prog f sp expr) >>! identity in OK (Some value, st)
   | Icall (str, args) -> 
      let args_values, st = eval_args oc st prog f sp args in 
      (find_function prog str) >>= (fun g ->
         (eval_efun oc st prog (sp + f.funstksz) g str args_values) >>= (fun (_, st) -> OK (None, st))
      )
   | Istore (Eload e1, e2) -> (match e2 with 
      | None -> OK(None, st)
      | Some e2 -> 
         eval_eexpr oc st prog f sp e1 >>= (fun (addr, st) ->
            eval_eexpr oc st prog f sp e2 >>= (fun (x, st) ->
               type_expr f.funtypvar f.funtypfun e1 >>= (fun lhe_t ->
                  size_type lhe_t >>= (fun size ->
                     let mem_write_res = Mem.write_bytes st.mem addr (split_bytes size x) in
                     mem_write_res >>= (fun () -> OK(None, st))     
                  )  
               )
            )  
         )
   )
   | Istore (e1, _ ) -> Error (Format.sprintf "Trying to derefence %s but it is not a pointer" (dump_eexpr e1))
   | Ibuiltin (str, vargs) -> 
      (do_builtin oc st.mem str (List.map (fun elt -> 
         let res = option_to_res_bind (Hashtbl.find st.env elt) 
         (Format.sprintf "Variable %s not initialized" elt)
         (fun x -> OK x) in 
         res >>! identity
      ) vargs)) >>= (fun _ ->
         OK(None, st)
      )
      

and eval_args oc (st: (int option) state) (prog: eprog) (f: efun) (sp: int) (args: expr list) = List.fold_left (
   fun (partial_args, st) elt -> let res, st = (eval_eexpr oc st prog f sp elt) >>! identity in (partial_args @ [res], st)
   ) ([], st) args 

(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
and eval_efun oc (st: (int option) state) (prog: eprog) (sp: int) (f: efun)
    (fname: string) (vargs: int list)
  : (int option * (int option) state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restore l'environnement de l'appelant. *)
  let env_save = Hashtbl.copy st.env in
  let (env: (string, int option) Hashtbl.t) = Hashtbl.create 17 in
  match List.iter2 (fun (arg_name, _) v -> Hashtbl.replace env arg_name (Some v)) f.funargs vargs with
  | () ->
    eval_einstr oc { st with env } prog f sp f.funbody >>= fun (v, st') ->
    OK (v, { st' with env = env_save })
  | exception Invalid_argument _ ->
    Error (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n"
             fname (List.length vargs) (List.length f.funargs)
          )

(* [eval_eprog oc ep memsize params] évalue un programme complet [ep], avec les
   arguments [params].

   Le paramètre [memsize] donne la taille de la mémoire dont ce programme va
   disposer. Ce n'est pas utile tout de suite (nos programmes n'utilisent pas de
   mémoire), mais ça le sera lorsqu'on ajoutera de l'allocation dynamique dans
   nos programmes.

   Renvoie:

   - [OK (Some v)] lorsque l'évaluation de la fonction a lieu sans problèmes et renvoie une valeur [v].

   - [OK None] lorsque l'évaluation de la fonction termine sans renvoyer de valeur.

   - [Error msg] lorsqu'une erreur survient.
   *)
let eval_eprog oc (ep: eprog) (memsize: int) (params: int list)
  : int option res =
   let (st: (int option) state) = init_state memsize in
   let ep = ("print", Gfun(
      {
         funreturntype = Tvoid; 
         funargs = [("x", Tint)]; 
         funvarinmem = Hashtbl.create 1;
         funstksz = 0;
         funtypvar = Hashtbl.create 1;
         funtypfun = Hashtbl.create 1;
         funbody = Ibuiltin("print", ["x"])
      }))::ep in
   find_function ep "main" >>= fun f ->
   (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
   let n = List.length f.funargs in
   let params = take n params in
   List.iter2 (fun (name, _) value -> Hashtbl.replace st.env name (Some value)) f.funargs params;
   eval_efun oc st ep 0 f "main" params >>= fun (v, _) ->
   OK v
