(** Top level code. *)

let debug = false

let show_rules = false

let try_normalization = false

let env_limit = Some 9

open Error
open Variables
open Typesystem
open Names
open Universe
open Hash
open Printf
open Printer
open Definitions

module Load = struct
  open Tactics
end

exception Error_Handled
exception FileFinished
exception StopParsingFile
exception Debugging
exception WithPosition of position * exn

let raise_switch ex1 ex2 = raise (if debug then ex1 else ex2)

let error_summary pos =
  let n = !Tokens.error_count in
  if n > 0 
  then (
    fprintf stderr "%s: %d error%s encountered, see messages above\n" (errfmt pos) n (if n == 1 then "" else "s");
    flush stderr;
    exit 1
   )

let print_inconsistency lhs rhs = 
  Printf.fprintf stderr "%a: universe inconsistency:\n" _pos_of lhs;
  Printf.fprintf stderr "%a:         %a\n"  _pos_of lhs  _ts lhs;
  Printf.fprintf stderr "%a:      != %a\n"  _pos_of rhs  _ts rhs;
  flush stderr;
  Tokens.bump_error_count()

let rec handle_exception pos0 e =
  let pos = errfmt pos0 in
  match e with
  | WithPosition(pos,e) -> 
      handle_exception pos e
  | Eof -> 
      error_summary pos0;
      raise StopParsingFile
  | Failure s as ex -> 
      fprintf stderr "%s: failure: %s\n" pos s;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex (Failure s)
  | GeneralError s as ex ->
      fprintf stderr "%s: %s\n" pos s;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | Grammar.Error | Parsing.Parse_error as ex -> 
      fprintf stderr "%s: syntax error\n" pos;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | TypeCheckingFailure (env,ps) as ex -> 
      List.iter (fun (pos,s) -> fprintf stderr "%s: %s\n" (errfmt pos) s) ps;
      flush stderr;
      print_context env_limit stderr env;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | MarkedError (p,s) as ex ->
      fprintf stderr "%s: %s\n" (errfmt p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | Unimplemented s as ex ->
      fprintf stderr "%s: feature not yet implemented: %s\n" pos s;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | Universe.Inconsistency (lhs,rhs) as ex ->
      print_inconsistency lhs rhs;
      raise_switch ex Error_Handled
  | e -> raise e

let wrap_position posfun f x = try f x with d -> WithPosition(posfun(), d)

let protect f x posfun = try f x with d -> handle_exception posfun d

let lexpos lexbuf = 
  let p = Tokens.lexing_pos lexbuf in
  let _ = Tokens.command_flush lexbuf in
  p

let add_tVars env tvars = 
    List.rev_append 
      (List.flatten
	 (List.map
	    (fun t -> 
	      [
	       (Var t, texp);
	       (newfresh (Var "ist"), istype (var_to_lf (Var t)));
	     ]
	    )
	    tvars
	 )
      )
      env

let ts_axiomCommand env pos name t = 
  if show_rules then ( printf "\nAxiom TS %s: %a\n%!" name  _ts t );
  let t = Lfcheck.type_check env t texp in
  if show_rules then ( printf "        : %a\n%!" _e t );
  let v = Var name in
  ensure_new_name env pos v;
  ts_bind (v,t) env

let lf_axiomCommand env pos name t =
  if show_rules then ( printf "\nAxiom LF %s: %a\n%!" name  _t t );
  let t = Lfcheck.type_validity env t in
  let v = Var name in
  ensure_new_name env pos v;
  (v,t) :: env

let is_can x = (function (APPLY _) -> true | _ -> false) (unmark x)

let checkLFCommand env pos x =
  printf "\nCheck LF   = %a\n%!" _e x;
  if is_can x then 
    let (x',t) = Lfcheck.type_synthesis env x in
    printf "           = %a\n" _e x';
    printf "           : %a\n%!" _t t;
    if try_normalization then
      let x'' = Lfcheck.term_normalization env x' t in
      printf "           = %a [normalized]\n%!" _e x'';
      let t' = Lfcheck.type_normalization env t in
      printf "           : %a [normalized]\n%!" _t t'

let checkLFtypeCommand env t =
  printf "\nCheck      : %a\n%!" _t t;
  let t = Lfcheck.type_validity env t in
  printf "           : %a [after tactics]\n%!" _t t;
  if try_normalization then
    let t = Lfcheck.type_normalization env t in
    printf "           : %a [after normalization]\n%!" _t t

let checkTSCommand env x =
  printf "\nCheck TS   : %a\n" _ts x;
  flush stdout;
  flush stdout;
  let (x,t) = Lfcheck.type_synthesis env x in
  printf "     type :: %a\n" _t t;
  if unmark t = unmark oexp then (
    match unmark x with
    | LAMBDA _ ->
	let ts = Tau.tau env x in
	printf "      type : %a ?\n" _ts ts;
	flush stdout
    | _ -> ()
   )

let alphaCommand env (x,y) =
  printf "\nAlpha      : %s\n" (if (Alpha.UEqual.term_equiv Definitions.emptyUContext x y) then "true" else "false");
  printf "           : %a\n" _ts x;
  printf "           : %a\n" _ts y;
  flush stdout

let checkUniversesCommand env pos =
  try
    Universe.consistency env;
    printf "\nCheck Universes: okay\n"
  with Universe.Inconsistency (p,q) -> print_inconsistency p q

let show_command env n = 
  ( match n with None -> print_signature env stdout | _ -> () );
  print_context n stdout env

let process_command env lexbuf = 
  let c = 
    try 
      Grammar.command Tokens.expr_tokens lexbuf
    with e -> raise (WithPosition(lexbuf_position lexbuf,e)) in
  match c with (pos,c) ->
    match c with
    | Toplevel.UVariable (uvars,eqns) -> ubind env uvars eqns
    | Toplevel.Variable tvars -> add_tVars env tvars
    | Toplevel.Rule (num,name,t) -> lf_axiomCommand env pos name t
    | Toplevel.AxiomLF (name,t) -> lf_axiomCommand env pos name t
    | Toplevel.AxiomTS (name,t) -> ts_axiomCommand env pos name t
    | Toplevel.CheckLF x -> checkLFCommand env pos x; env
    | Toplevel.CheckLFtype x -> checkLFtypeCommand env x; env
    | Toplevel.CheckTS x -> checkTSCommand env x; env
    | Toplevel.Alpha (x,y) -> alphaCommand env (x,y); env
    | Toplevel.TDefinition defs -> tDefCommand env defs
    | Toplevel.ODefinition defs -> oDefCommand env defs
    | Toplevel.Theorem defs -> theoremCommand env defs
    | Toplevel.TeqDefinition defs -> teqDefCommand env defs
    | Toplevel.OeqDefinition defs -> oeqDefCommand env defs
    | Toplevel.Show n -> show_command env n; env
    | Toplevel.CheckUniverses -> checkUniversesCommand env pos; env
    | Toplevel.End -> error_summary pos; raise StopParsingFile

let read_eval_command env lexbuf =
  let rec repeat env =
    try 
      repeat (
      try
	process_command env lexbuf
      with e -> handle_exception (lexbuf_position lexbuf) e
     )
    with 
    | Error_Handled -> 
	repeat env
    | StopParsingFile -> 
	env
  in repeat env

let parse_file env filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
  let env = read_eval_command env lexbuf in
  printf "done parsing file %s\n%!" filename;
  env

let strname =
  let n = ref 0 in
  fun () ->
    let p = "string_" ^ string_of_int !n in
    incr n;
    p

let read_expr env lexbuf =
  try
    Grammar.ts_exprEof Tokens.expr_tokens lexbuf
  with e -> handle_exception (lexbuf_position lexbuf) e

let parse_string env grammar s = 
    let lexbuf = Lexing.from_string s in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = strname()};
    read_expr env lexbuf

let expr_from_string env s = parse_string env Grammar.ts_exprEof s

let toplevel() = 
  let env = ref [] in
  (try
    Arg.parse 
      (Arg.align
	 [
	  ("--debug" , Arg.Set debug_mode, " Turn on debug mode");
	  ("--no-debug" , Arg.Clear debug_mode, " Turn off debug mode");
	])
      (fun filename -> env := parse_file !env filename)
      ("usage: " ^ (Filename.basename Sys.argv.(0)) ^ " [option|filename] ...");
  with FileFinished -> ());
  if false then
  let env = !env in 
  try
    let x = expr_from_string env "[Pt]()" in
    checkLFCommand env (no_pos 124) x
    with 
    | e -> handle_exception (no_pos 125) e
    

let _ = try
  toplevel()
with
| Internal_expr e as ex ->
    fprintf stderr "%a: internal error: %a\n%!" _pos_of e  _e e;
    raise ex
| Unimplemented_expr e as ex ->
    fprintf stderr "%a: unimplemented feature: %a\n%!" _pos_of e  _e e;
    raise ex

