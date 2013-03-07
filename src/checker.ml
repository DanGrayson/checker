(** Top level code. *)

let debug = false

let show_rules = false

let show_definitions = false

let try_normalization = true

let env_limit = Some 20

open Error
open Variables
open Typesystem
open Names
open Universe
open Hash
open Printf
open Printer
open Lfcheck

module Load = struct
  open Tactics
end

exception Error_Handled
exception FileFinished
exception StopParsingFile
exception WithPosition of position * exn

let raise_switch ex1 ex2 = raise (if debug then ex1 else ex2)

let error_summary pos =
  let n = !error_count in
  if n > 0
  then (
    fprintf stderr "%s: %d error%s encountered, see messages above\n%!" (errfmt pos) n (if n == 1 then "" else "s");
    exit 1
   )

let print_inconsistency pos lhs rhs =
  Printf.fprintf stderr "%a: universe inconsistency:\n" _pos_of lhs;
  Printf.fprintf stderr "%a:         %a\n"  _pos_of lhs  _ts lhs;
  Printf.fprintf stderr "%a:      != %a\n%!"  _pos_of rhs  _ts rhs;
  bump_error_count pos

let protect f posfun =
  let spos () = errfmt (posfun ()) in
  try f() with
  (* | WithPosition(spos,e) ->  *)
  (*     handle_exception (spos ()) e *)
  | Eof ->
      error_summary (posfun ());
      raise StopParsingFile
  (* | Failure s -> *)
  (*     fprintf stderr "%s: %s \n%!" (spos ()) s; *)
  (*     raise (Failure "exiting") *)
  | GeneralError s as ex ->
      fprintf stderr "%s: %s\n%!" (spos ()) s;
      bump_error_count (posfun ());
      raise_switch ex Error_Handled
  | Grammar.Error | Parsing.Parse_error as ex ->
      fprintf stderr "%s: syntax error\n%!" (spos ());
      bump_error_count (posfun ());
      raise_switch ex Error_Handled
  | TypeCheckingFailure (env,surr,ps) as ex ->
      List.iter (fun (spos,s) -> fprintf stderr "%s: %s\n%!" (errfmt spos) s) ps;
      print_surroundings surr;
      print_context env_limit stderr env;
      bump_error_count (posfun ());
      raise_switch ex Error_Handled
  | MarkedError (p,s) as ex ->
      fprintf stderr "%s: %s\n%!" (errfmt p) s;
      bump_error_count (posfun ());
      raise_switch ex Error_Handled
  | Unimplemented s as ex ->
      fprintf stderr "%s: feature not yet implemented: %s\n%!" (spos ()) s;
      bump_error_count (posfun ());
      raise_switch ex Error_Handled
  | Universe.Inconsistency (lhs,rhs) as ex ->
      print_inconsistency (posfun ()) lhs rhs;
      raise_switch ex Error_Handled

let add_tVars env tvars =
  List.fold_left
    (fun env (pos,t) ->
      let env = global_tts_declare_type env pos t in
      let env = global_lf_bind env pos (id t) texp in
      let env = global_lf_bind env pos (id (t ^ "$istype")) (istype (var_to_lf (Var (id t)))) in
      env 
    ) env tvars

let add_oVars env ovars t =
  List.fold_left
    (fun env (pos,o) -> 
      let env = global_tts_declare_object env pos o t in
      let env = global_lf_bind env pos (id o) oexp in
      let env = global_lf_bind env pos (id (o ^ "$hastype")) (hastype (var_to_lf (Var (id o))) t) in
      env 
    ) env ovars

let lf_axiomCommand env pos name t =
  if show_rules then printf "Axiom LF %a: %a\n%!" _i name _t t;
  let t = Lfcheck.type_validity [] env t in
  let r = axiom_bind name pos t env in
  if !proof_general_mode then printf "%a is declared\n%!" _i name;
  r

let defCommand env defs =
  List.fold_left
    (fun env (name, pos, tm, tp) ->
      if show_definitions then printf "Define %s = %a\n%!" name  _e tm (* else printf "Define %a\n%!" name *);
      if show_definitions then printf "       %s : %a\n%!" name  _t tp;
      let tp' = type_validity [] env tp in
      if not (type_equiv tp tp') then
      if show_definitions then printf "       %s : %a [after tactics]\n%!" name  _t tp';
      let tm' = type_check [] env tm tp' in
      if not (term_equiv tm tm') then (
	if show_definitions then printf "       %s = %a [after tactics]\n%!" name  _e tm');
      let tm'' = term_normalization env tm' tp' in
      if not (term_equiv tm' tm'') then (
	if show_definitions then printf "       %s = %a [normalized]\n%!" name  _e tm'';
	(* if show_definitions then printf "       %s = %a [normalized, TS format]\n%!" name  _ts tm''; *)
	let _ = type_check [] env tm'' tp' in ();
       );
      let tp'' = type_normalization env tp' in
      if not (type_equiv tp' tp'') then (
	if show_definitions then printf "       %s : %a [normalized]\n%!" name  _t tp'';
	let _ = type_validity [] env tp'' in ();
       );
      let env = def_bind (id name) pos tm' tp' env in
      if !proof_general_mode then printf "%s is defined\n%!" name;
      env
    )
    env defs

let is_can x = (function (APPLY _) -> true | _ -> false) (unmark x)

let checkLFCommand env pos x =
  printf "Check LF   = %a\n%!" _e x;
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
  printf "Check      : %a\n%!" _t t;
  let t' = Lfcheck.type_validity [] env t in
  if not (type_equiv t t') then
    printf "           : %a [after tactics]\n%!" _t t';
  if try_normalization then (
    let t'' = Lfcheck.type_normalization env t' in
    if not (type_equiv t' t'') then (
      printf "           : %a [after normalization] ... %!" _t t'';
      ignore (Lfcheck.type_validity [] env t'');
      printf "okay\n%!";
      )
   )

let checkWitnessedJudgmentCommand env t =
  printf "Check      : %a\n%!" _t t;
  let t' = Lfcheck.type_validity [] env t in
  if not (type_equiv t t') then
    printf "           : %a [after tactics]\n%!" _t t';
  Lfcheck.check env t';
  printf "           : okay\n%!"

let checkTSCommand env x =
  printf "Check      : %a\n%!" _ts x;
  let (x,t) = Lfcheck.type_synthesis env x in
  printf "     type :: %a\n" _t t;
  if unmark t = unmark oexp then (
    match unmark x with
    | LAMBDA _ ->
	let ts = Tau.tau env x in
	printf "      type : %a ?\n%!" _ts ts
    | _ -> ()
   );
  if try_normalization then
    let x' = Lfcheck.term_normalization env x t in
    printf "           = %a [normalized]\n%!" _e x'

let alphaCommand env (x,y) =
  printf "Alpha      : %s\n" (if (term_equiv x y) then "true" else "false");
  printf "           : %a\n" _ts x;
  printf "           : %a\n%!" _ts y

let checkUniversesCommand env pos =
  try
    Universe.consistency env;
    printf "Check Universes: okay\n"
  with Universe.Inconsistency (p,q) -> print_inconsistency pos p q

let show_command env n =
  print_context n stdout env;
  ( match n with None -> print_signature env stdout | _ -> () )

let chk_u env u =
  let u = Lfcheck.type_check [] env u uexp in
  Lfcheck.term_normalization env u uexp

let ueqn_counter = new_counter()

let ubind env uvars ueqns =
  let env = List.fold_left (fun env (pos,u) -> global_lf_bind env pos (id u) uexp) env uvars in
  (* let uvars = List.map (fun u -> Var u) uvars in *)
  let ueqns = List.map (fun (u,v) -> ("ueq" ^ (string_of_int (ueqn_counter()))), chk_u env u, chk_u env v) ueqns in
  let env = List.fold_left (fun env (name,u,v) -> global_lf_bind env (no_pos 123) (id name) (ulevel_equality u v)) env ueqns in
  (* chk_ueqns env ueqns; *)
  env

let rec process_command env lexbuf =
  if !interactive then prompt env;
  let c =
    (* try *)
      Grammar.command Tokens.expr_tokens lexbuf
    (* with e -> raise (WithPosition(lexbuf_position lexbuf,e)) *)
  in
  match c with (pos,c) ->
    match c with
    | Toplevel.UVariable (uvars,eqns) -> ubind env uvars eqns
    | Toplevel.TVariable tvars -> add_tVars env tvars
    | Toplevel.OVariable (ovars,t) -> add_oVars env ovars t
    | Toplevel.Axiom (num,name,t) -> lf_axiomCommand env pos name t
    | Toplevel.CheckLF x -> checkLFCommand env pos x; env
    | Toplevel.CheckLFtype x -> checkLFtypeCommand env x; env
    | Toplevel.CheckWitness x -> checkWitnessedJudgmentCommand env x; env
    | Toplevel.CheckTS x -> checkTSCommand env x; env
    | Toplevel.Alpha (x,y) -> alphaCommand env (x,y); env
    | Toplevel.Theorem (pos,name,deriv,thm) -> defCommand env [ name, pos, deriv, thm ]
    | Toplevel.Show n -> show_command env n; env
    | Toplevel.Back n -> if n > 0 then raise (GoBack n) else env
    | Toplevel.BackTo n ->
        if env.state <= n then env else raise (GoBackTo n)
    | Toplevel.CheckUniverses -> checkUniversesCommand env pos; env
    | Toplevel.Include filename ->
	let save_interactive = !interactive in
	let env = parse_file env filename in
	interactive := save_interactive;
	env
    | Toplevel.Clear -> empty_context
    | Toplevel.SyntaxError -> env
    | Toplevel.End ->
	error_summary pos;
	fprintf stderr "%a: End.\n%!" _pos pos;
	raise StopParsingFile

and read_eval_command env lexbuf =
  let rec repeat env =
    try
      repeat (incr_state
		(protect
		   (fun () -> process_command env lexbuf)
		   (fun () -> lexbuf_position lexbuf)))
    with
    | GoBack i ->
	if i <= 0 then repeat env
	else if env.state = 0 then ( printf "warning: can back up no further\n%!"; repeat env )
	else raise (GoBack (i-1))
    | GoBackTo n as e ->
	if env.state <= n then repeat env else raise e
    | Error_Handled -> repeat env
    | StopParsingFile -> env
  in repeat env

and parse_file env filename =
  let lexbuf = Lexing.from_channel (if filename = "-" then stdin else open_in filename) in
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
  let env = read_eval_command env lexbuf in
  (* printf "done parsing file %s\n%!" filename; *)
  env

let strname =
  let n = ref 0 in
  fun () ->
    let p = "string_" ^ string_of_int !n in
    incr n;
    p

let read_expr env lexbuf =
  protect (fun () -> Grammar.ts_exprEof Tokens.expr_tokens lexbuf) (fun () -> lexbuf_position lexbuf)

let parse_string env grammar s =
    let lexbuf = Lexing.from_string s in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = strname()};
    read_expr env lexbuf

let expr_from_string env s = parse_string env Grammar.ts_exprEof s

let toplevel() =
  let env = ref empty_context in
  (try
    Arg.parse
      (Arg.align
	 [
	  ("--proof-general" , Arg.Set proof_general_mode, " Turn on Proof General mode");
	  ("--debug" , Arg.Set debug_mode, " Turn on debug mode");
	  ("--no-debug" , Arg.Clear debug_mode, " Turn off debug mode")
	])
      (fun filename ->
	try
	  env := parse_file !env filename
	with Failure "exiting" -> exit 1	(* after too many errors in a file, we don't parse the other files *)
      )
      ("usage: " ^ (Filename.basename Sys.argv.(0)) ^ " [option|filename] ...");
  with FileFinished -> ());
  if !proof_general_mode
  then (
    interactive := true;
    try
      env := parse_file !env "-"
    with Failure "exiting" -> exit 1	(* after too many errors in a file, we don't parse the other files *)
   )

let unused env =
  if false then
  let env = !env in
  protect
    (fun () ->
      let x = expr_from_string env "@[Pt][]" in
      checkLFCommand env (no_pos 124) x)
    (fun () -> no_pos 125)

let _ = try
  toplevel()
with
(* | NotImplemented -> *)
(*     fprintf stderr "error: feature not implemented\n%!" *)
(* | Internal -> *)
(*     fprintf stderr "error: internal error\n%!" *)
| Internal_expr e ->
    fprintf stderr "%a: internal error: %a\n%!" _pos_of e  _e e
| Unimplemented_expr e ->
    fprintf stderr "%a: unimplemented feature: %a\n%!" _pos_of e  _e e

(*
  Local Variables:
  compile-command: "make -C .. src/checker.cmo "
  End:
 *)
