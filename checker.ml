(** Top level code. *)

let debug = false

let env_limit = None

open Error
open Typesystem
open Names
open Universe
open Hash
open Printf
open Printer

module Load = struct
  open Template
  open Tactics
end

exception Error_Handled
exception FileFinished
exception StopParsingFile
exception Debugging

let raise_switch ex1 ex2 = raise (if debug then ex1 else ex2)

let error_summary pos =
  let n = !Tokens.error_count in
  if n > 0 
  then (
    fprintf stderr "%s: %d error%s encountered, see messages above\n" pos n (if n == 1 then "" else "s");
    flush stderr;
    exit 1
   )

let leave pos = 
  error_summary pos;
  raise StopParsingFile

let errpos x = errfmt (get_pos x)

let print_inconsistency lhs rhs =
  fprintf stderr "%s: universe inconsistency:\n" (errpos lhs);
  fprintf stderr "%s:         %s\n" (errpos lhs) (ts_expr_to_string lhs);
  fprintf stderr "%s:      != %s\n" (errpos lhs) (ts_expr_to_string rhs);
  flush stderr;
  Tokens.bump_error_count()

let handle_exception (posfun:unit->string) = function
  | Eof -> leave (posfun ())
  | Failure s as ex -> 
      fprintf stderr "%s: failure: %s\n" (posfun ()) s;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex (Failure s)
  | GeneralError s as ex ->
      fprintf stderr "%s: %s\n" (posfun ()) s;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | Grammar.Error | Parsing.Parse_error as ex -> 
      fprintf stderr "%s: syntax error\n" (posfun ());
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | TypeCheckingFailure (env,p,s) as ex -> 
      fprintf stderr "%s: type checking failure: %s\n" (errfmt p) s;
      flush stderr;
      print_context env_limit stderr env;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | TypeCheckingFailure2 (env,p1,s1,p2,s2) as ex -> 
      fprintf stderr "%s: type mismatch: %s\n" (errfmt p1) s1;
      fprintf stderr "%s:      ...       %s\n" (errfmt p2) s2;
      flush stderr;
      print_context env_limit stderr env;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | TypeCheckingFailure3 (env,p1,s1,p2,s2,p3,s3) as ex -> 
      fprintf stderr "%s: type mismatch: %s\n" (errfmt p1) s1;
      fprintf stderr "%s:      ...       %s\n" (errfmt p2) s2;
      fprintf stderr "%s:      ...       %s\n" (errfmt p3) s3;
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
      fprintf stderr "%s: feature not yet implemented: %s\n" (posfun ()) s;
      flush stderr;
      Tokens.bump_error_count();
      raise_switch ex Error_Handled
  | Universe.Inconsistency (lhs,rhs) as ex ->
      print_inconsistency lhs rhs;
      raise_switch ex Error_Handled
  | e -> raise e

let protect f x posfun = try f x with d -> handle_exception posfun d

let protect1 f = protect f () (fun () -> nopos 11)

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

let fix env t = Fillin.fillin env t

let axiomCommand env name t = 
  printf "Axiom %s: %s\n" name (lf_atomic_to_string t);
  let t = protect1 ( fun () -> Lfcheck.type_check (get_pos t) env (Phi t) texp) in
  printf "        : %s\n" (lf_expr_to_string t);
  flush stdout;
  match t with
  | Phi t -> ts_bind (Var name, t) env
  | LAMBDA _ -> raise Internal

let ruleCommand env num name t =
  let t = protect1 ( fun () -> Lfcheck.type_validity env t ) in
  (Var name, t) :: env

let check0 env x =
  flush stdout;
  let x = protect1 ( fun () -> Fillin.fillin env x ) in
  printf "        LF : %s\n" (lf_atomic_to_string x);
  flush stdout;
  let (x,t) = protect1 ( fun () -> Lfcheck.type_synthesis env (Phi x) ) in
  printf "    LF type: %s\n" (lf_type_to_string t);
  if unmark t = unmark oexp then (
    match x with
    | Phi x ->
	let ts = protect1 ( fun () -> Tau.tau env x ) in
	printf "    TS type: %s ?\n" (ts_expr_to_string ts);
	flush stdout
    | _ -> raise Internal
   )

let is_lambda = function LAMBDA _ -> true | _ -> false

let checkLFCommand env pos x =
  printf "Check LF   = %s\n" (lf_expr_to_string x);
  flush stdout;
  if not (is_lambda x) then 
    let (x',t) = protect1 ( fun () -> Lfcheck.type_synthesis env x ) in
    printf "           = %s\n" (lf_expr_to_string x');
    flush stdout;
    let x'' = protect1 ( fun () -> Lfcheck.term_normalization env x' t) in
    printf "           = %s\n" (lf_expr_to_string x'');
    printf "           : %s\n" (lf_type_to_string t);
    flush stdout;
    let t' = protect1 ( fun () -> Lfcheck.type_normalization env t) in
    printf "           = %s\n" (lf_type_to_string t');
    flush stdout

let checkLFtypeCommand env t =
  printf "CheckLFtype: %s\n" (lf_type_to_string t);
  flush stdout;
  let t = protect1 ( fun () -> Lfcheck.type_validity env t ) in
  printf "           : %s\n" (lf_type_to_string t);
  flush stdout

let checkCommand env x =
  printf "Check      : %s\n" (ts_expr_to_string x);
  check0 env x

let alphaCommand env (x,y) =
  let x = protect (fix env) x (fun () -> errpos x) in
  let y = protect (fix env) y (fun () -> nopos 13) in
  printf "Alpha      : %s\n" (if (Alpha.UEqual.term_equiv Grammar0.emptyUContext (Phi x) (Phi y)) then "true" else "false");
  printf "           : %s\n" (ts_expr_to_string x);
  printf "           : %s\n" (ts_expr_to_string y);
  flush stdout

let checkUniversesCommand env pos =
  try
    Universe.consistency env;
    printf "Check Universes: okay\n"
  with Universe.Inconsistency (p,q) -> print_inconsistency p q

let show_command env n = 
  ( match n with None -> print_signature env stdout | _ -> () );
  print_context n stdout env

let addDefinition env v pos o t = def_bind v pos o t env

let defCommand env defs = protect1 ( fun () -> 
  List.fold_left
    (fun env (v, pos, tm, tp) -> 
      printf "Define %s = %s\n" (vartostring v) (lf_expr_to_string tm);
      printf "       %s : %s\n" (vartostring v) (lf_type_to_string tp);
      flush stdout;
      let tp = Lfcheck.type_validity env tp in
      let tm = Lfcheck.type_check pos env tm tp in
      addDefinition env v pos tm tp
    ) 
    env
    defs)

let process_command env lexbuf = 
  let c = protect (Grammar.command (Tokens.expr_tokens)) lexbuf (fun () -> lexpos lexbuf) in
  match c with (pos,c) ->
    match c with
    | Toplevel.UVariable (uvars,eqns) -> protect1 ( fun () -> ubind env uvars eqns )
    | Toplevel.Variable tvars -> add_tVars env tvars
    | Toplevel.Rule (num,name,t) -> ruleCommand env num name t
    | Toplevel.Axiom (name,t) -> axiomCommand env name t
    | Toplevel.CheckLF x -> checkLFCommand env pos x; env
    | Toplevel.CheckLFtype x -> checkLFtypeCommand env x; env
    | Toplevel.Check x -> checkCommand env x; env
    | Toplevel.Alpha (x,y) -> alphaCommand env (x,y); env
    | Toplevel.Definition defs -> defCommand env defs
    | Toplevel.Show n -> show_command env n; env
    | Toplevel.CheckUniverses -> checkUniversesCommand env pos; env
    | Toplevel.End -> printf "%s: ending.\n" (errfmt pos); flush stdout; raise StopParsingFile

let parse_file env filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
  let rec repeat env =
    try 
      repeat (process_command env lexbuf)
    with 
    | Error_Handled -> 
	repeat env
    | StopParsingFile -> 
	printf "done parsing file %s\n" filename; flush stdout;
	env
  in repeat env

let strname =
  let n = ref 0 in
  fun () ->
    let p = "string_" ^ (string_of_int !n) in
    incr n;
    p

let parse_string grammar s = 
    let lexbuf = Lexing.from_string s in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = strname()};
    protect (grammar (Tokens.expr_tokens)) lexbuf (fun () -> lexpos lexbuf)
let expr_from_string s = Phi(parse_string Grammar.ts_exprEof s)

let toplevel() = 
  let env = ref [] in
  (try
    Arg.parse 
      [
       ("--debug" , Arg.Set Debugging.debug_mode, "turn on debug mode")
     ]
      (fun filename -> env := parse_file !env filename)
      "usage: [options] filename ...";
  with FileFinished -> ());
  let env = !env in 
  (*
  let env =
    (try checkLFCommand env (no_pos 124) (expr_from_string "x0" ); env with Error_Handled -> env)
  in 
    *)
  flush stdout;
  ignore env

let _ = try
  toplevel()
with
| Internal_expr      ( Phi(pos,_) as e ) 
| Internal_expr      ( LAMBDA(_,Phi(pos,_)) as e ) 
    as ex ->
    fprintf stderr "%s: internal error: %s\n" (errfmt pos) (lf_expr_to_string e);
    raise ex
| Unimplemented_expr ( Phi(pos,_) as e )
| Unimplemented_expr ( LAMBDA(_,Phi(pos,_)) as e ) 
    as ex ->
    fprintf stderr "%s: unimplemented feature: %s\n" (errfmt pos) (lf_expr_to_string e);
    raise ex

