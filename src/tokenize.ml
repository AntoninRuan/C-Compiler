open Batteries
open Lexer_generator
open Report
open Utils
open Options
open Symbols

let tokenize_handwritten file =
  (* Printf.printf "Handwritten lexer\n"; *)
  Lexer_generator.tokenize_file file >>= fun tokens ->
  OK (List.map (fun tok -> (tok, None)) tokens)

let tokenize_ocamllex file =
  Printf.printf "OCamlLex lexer\n";
  let ic = open_in file in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with pos_fname = file };
  let rec get_symbols () =
    let s = Lexer.token lexbuf in
    let ss = (s, Lexing.lexeme_start_p lexbuf) in
    if s = SYM_EOF
    then [ss]
    else ss :: get_symbols ()
  in
  let l = get_symbols () in
  close_in ic;
  OK (List.map (fun (tok, pos) -> (tok, Some pos)) l)

let tokenize file =
  if !Options.handwritten_lexer
  then tokenize_handwritten file
  else tokenize_ocamllex file

let pass_tokenize file =
  tokenize file >>* (fun msg ->
      record_compile_result ~error:(Some msg) "Lexing";
      Error msg
    ) $ fun tokens ->
      record_compile_result "Lexing";
      dump !show_tokens (fun oc tokens ->
          List.iter (fun (tok,_) ->
              Format.fprintf oc "%s\n" (string_of_symbol tok)
            ) tokens) tokens (fun f () -> add_to_report "lexer" "Lexer" (Code (file_contents f)));
      OK tokens
