(** Top level code. *)

let debug = false

let env_limit = Some 10

open Typesystem
open Template				(*otherwise unused*)
open Universe
open Error
open Hash
open Printf
open Printer

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
    flush stderr)

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

let initialize_environment () = global_context := []

let add_tVars tvars = 
  global_context := 
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
      !global_context

let fix t = Fillin.fillin !global_context t

let axiomCommand name t = 
  printf "Axiom %s: %s\n" name (lf_atomic_to_string t);
  let t = protect1 ( fun () -> Lfcheck.type_check (get_pos t) !global_context (CAN t) texp) in
  printf "        : %s\n" (lf_canonical_to_string t);
  flush stdout;
  match t with
  | CAN t -> global_context := ts_bind (Var name, t) !global_context
  | LAMBDA _ -> raise Internal

let ruleCommand num name t =
  let t = Lfcheck.type_validity !global_context t in
  let t = protect1 ( fun () -> Lfcheck.type_validity !global_context t ) in
  global_context := (Var name, t) :: !global_context

let check0 x =
  flush stdout;
  let x = protect1 ( fun () -> Fillin.fillin !global_context x ) in
  printf "        LF : %s\n" (lf_atomic_to_string x);
  flush stdout;
  let (x,t) = protect1 ( fun () -> Lfcheck.type_synthesis !global_context (CAN x) ) in
  printf "    LF type: %s\n" (lf_type_to_string t);
  if unmark t = unmark oexp then (
    match x with
    | CAN x ->
	let ts = protect1 ( fun () -> Tau.tau !global_context x ) in
	printf "    TS type: %s ?\n" (ts_expr_to_string ts);
	flush stdout
    | _ -> raise Internal
   )

let is_lambda = function LAMBDA _ -> true | _ -> false

let checkLFCommand pos x =
  printf "Check LF   = %s\n" (lf_canonical_to_string x);
  flush stdout;
  if not (is_lambda x) then 
    let (x',t) = protect1 ( fun () -> Lfcheck.type_synthesis !global_context x ) in
    printf "           = %s\n" (lf_canonical_to_string x');
    let x'' = protect1 ( fun () -> Lfcheck.term_normalization !global_context x' t) in
    printf "           = %s\n" (lf_canonical_to_string x'');
    printf "           : %s\n" (lf_type_to_string t);
    let t' = protect1 ( fun () -> Lfcheck.type_normalization !global_context t) in
    printf "           = %s\n" (lf_type_to_string t')

let checkLFtypeCommand t =
  printf "CheckLFtype: %s\n" (lf_type_to_string t);
  flush stdout;
  let t = protect1 ( fun () -> Lfcheck.type_validity !global_context t ) in
  printf "           : %s\n" (lf_type_to_string t);
  flush stdout

let checkCommand x =
  printf "Check      : %s\n" (ts_expr_to_string x);
  check0 x

let alphaCommand (x,y) =
  let x = protect fix x (fun () -> errpos x) in
  let y = protect fix y (fun () -> nopos 13) in
  printf "Alpha      : %s\n" (if (Alpha.UEqual.term_equiv Grammar0.emptyUContext (CAN x) (CAN y)) then "true" else "false");
  printf "           : %s\n" (ts_expr_to_string x);
  printf "           : %s\n" (ts_expr_to_string y);
  flush stdout

let checkUniversesCommand pos =
  try
    Universe.consistency !global_context;
    printf "Check Universes: okay\n"
  with Universe.Inconsistency (p,q) -> print_inconsistency p q

let show_command () = 
  print_signature stdout;
  print_context None stdout !global_context

let addDefinition v pos o t = 
  global_context := def_bind v pos o t !global_context

let defCommand defs = protect1 ( fun () -> 
  List.iter
    (fun (v, pos, tm, tp) -> 
      printf "Define %s = %s\n" (vartostring v) (lf_canonical_to_string tm);
      printf "       %s : %s\n" (vartostring v) (lf_type_to_string tp);
      flush stdout;
      let tp = Lfcheck.type_validity !global_context tp in
      let tm = Lfcheck.type_check pos !global_context tm tp in
      addDefinition v pos tm tp
    ) 
    defs)

let process_command lexbuf = 
  let c = protect (Grammar.command (Tokens.expr_tokens)) lexbuf (fun () -> lexpos lexbuf) in
  match c with (pos,c) ->
    match c with
    | Toplevel.UVariable (uvars,eqns) -> protect1 ( fun () -> ubind uvars eqns )
    | Toplevel.Variable tvars -> add_tVars tvars
    | Toplevel.Rule (num,name,t) -> ruleCommand num name t
    | Toplevel.Axiom (name,t) -> axiomCommand name t
    | Toplevel.CheckLF x -> checkLFCommand pos x
    | Toplevel.CheckLFtype x -> checkLFtypeCommand x
    | Toplevel.Check x -> checkCommand x
    | Toplevel.Alpha (x,y) -> alphaCommand (x,y)
    | Toplevel.Definition defs -> defCommand defs
    | Toplevel.End -> printf "%s: ending.\n" (errfmt pos) ; flush stdout; raise StopParsingFile
    | Toplevel.Show -> show_command()
    | Toplevel.CheckUniverses -> checkUniversesCommand pos

let parse_file filename =
  Tokens.error_count := 0;
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
  try while true do (try process_command lexbuf with Error_Handled -> ()) done
  with StopParsingFile -> printf "parsing file %s\n" filename; flush stdout
  
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
let expr_from_string = parse_string Grammar.ts_exprEof

let toplevel() = 
  (try
    Arg.parse 
      [
       ("--debug" , Arg.Set Debugging.debug_mode, "turn on debug mode")
     ]
      parse_file
      "usage: [options] filename ...";
  with FileFinished -> ());
  (*
  (try checkLFCommand (expr_from_string "Pi f:T->[U](uuu0), Pi o:T, *f o" ) with Error_Handled -> ());
  (try checkLFCommand (expr_from_string "lambda f:T->U, lambda o:T, f o") with Error_Handled -> ());
    *)
  flush stdout

let _ = try
  toplevel()
with
| Internal_expr      ( CAN(pos,_) as e ) 
| Internal_expr      ( LAMBDA(_,CAN(pos,_)) as e ) 
    as ex ->
    fprintf stderr "%s: internal error: %s\n" (errfmt pos) (lf_canonical_to_string e);
    raise ex
| Unimplemented_expr ( CAN(pos,_) as e )
| Unimplemented_expr ( LAMBDA(_,CAN(pos,_)) as e ) 
    as ex ->
    fprintf stderr "%s: unimplemented feature: %s\n" (errfmt pos) (lf_canonical_to_string e);
    raise ex

