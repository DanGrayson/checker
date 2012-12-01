(** Top level code. *)

open Typesystem
open Template				(*otherwise unused*)
open Universe
open Error
open Hash

exception Error_Handled
exception FileFinished
exception StopParsingFile

let error_summary pos =
  let n = !Tokens.error_count in
  if n > 0 
  then (
    Printf.fprintf stderr "%s: %d error%s encountered, see messages above\n" pos n (if n == 1 then "" else "s");
    flush stderr)

let leave pos = 
  error_summary pos;
  raise StopParsingFile

let errpos x = errfmt (get_pos x)

let print_inconsistency lhs rhs =
  Printf.fprintf stderr "%s: universe inconsistency:\n" (errpos lhs);
  Printf.fprintf stderr "%s:         %s\n" (errpos lhs) (Printer.ts_expr_to_string lhs);
  Printf.fprintf stderr "%s:      != %s\n" (errpos lhs) (Printer.ts_expr_to_string rhs);
  flush stderr;
  Tokens.bump_error_count()

let handle_exception (posfun:unit->string) = function
  | Eof -> leave (posfun ())
  | Failure s -> 
      Printf.fprintf stderr "%s: failure: %s\n" (posfun ()) s;
      flush stderr;
      Tokens.bump_error_count();
      raise (Failure s)
  | GeneralError s ->
      Printf.fprintf stderr "%s: %s\n" (posfun ()) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | Grammar.Error | Parsing.Parse_error -> 
      Printf.fprintf stderr "%s: syntax error\n" (posfun ());
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | Lfcheck.TypingError (p,s) ->
      Printf.fprintf stderr "%s: LF type checking failure: %s\n" (errfmt p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | TypeCheckingFailure (p,s) -> 
      Printf.fprintf stderr "%s: type checking failure: %s\n" (errfmt p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | TypeCheckingFailure2 (p1,s1,p2,s2) -> 
      Printf.fprintf stderr "%s: %s\n" (errfmt p1) s1;
      Printf.fprintf stderr "%s: %s\n" (errfmt p2) s2;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | TypeCheckingFailure3 (p1,s1,p2,s2,p3,s3) -> 
      Printf.fprintf stderr "%s: type checking failure: %s\n" (errfmt p1) s1;
      Printf.fprintf stderr "%s: ... %s\n" (errfmt p2) s2;
      Printf.fprintf stderr "%s: ... %s\n" (errfmt p3) s3;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | TypingError (p,s) ->
      Printf.fprintf stderr "%s: %s\n" (errfmt p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | TypingUnimplemented (p,s) -> 
      Printf.fprintf stderr "%s: type checking unimplemented: %s\n" (errfmt p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | Unimplemented s ->
      Printf.fprintf stderr "%s: feature not yet implemented: %s\n" (posfun ()) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | Universe.Inconsistency (lhs,rhs) ->
      print_inconsistency lhs rhs;
      raise Error_Handled
  | e -> raise e

let protect f x posfun = try (f x) with d -> handle_exception posfun d

let protect1 f = protect f () nopos

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
	       (LF_Var (Var t), texp);
	       (LF_Var (newfresh (Var "ist")), istype (ATOMIC (nowhere (Variable (Var t)))));
	     ]
	    )
	    tvars
	 )
      )
      !global_context

let fix t = Fillin.fillin !global_context t

let axiomCommand name t = global_context := ts_bind' (Var name, t) !global_context

let ruleCommand num name x =
  Printf.printf "Rule %d %s: %s\n" num name (Printer.lf_type_to_string x);
  global_context := (LF_Var (Var name), x) :: !global_context;
  flush stdout;
  protect1 ( fun () -> Lfcheck.type_validity !global_context x )

let f_print_Command x =
  Printf.printf "F_Print : %s\n" (Printer.lf_type_to_string x);
  flush stdout

let check0 x =
  flush stdout;
  let x = protect1 ( fun () -> Fillin.fillin !global_context x ) in
  Printf.printf "   LF : %s\n" (Printer.lf_atomic_to_string x);
  flush stdout;
  let t = protect1 ( fun () -> Lfcheck.type_synthesis !global_context x ) in
  Printf.printf " type : %s\n" (Printer.lf_type_to_string t);
  if t = oexp then protect1 (fun () -> Check.ocheck !global_context x);
  flush stdout

let checkLFCommand x =
  Printf.printf "CheckLF: %s\n" (Printer.lf_canonical_to_string x);
  flush stdout;
  match x with 
  | ATOMIC x ->
      let t = protect1 ( fun () -> Lfcheck.type_synthesis !global_context x ) in
      Printf.printf " type : %s\n" (Printer.lf_type_to_string t)
  | _ -> ()

let checkLFtypeCommand x =
  Printf.printf "CheckLFtype: %s\n" (Printer.lf_type_to_string x);
  flush stdout;
  protect1 ( fun () -> Lfcheck.type_validity !global_context x )

let checkCommand x =
  Printf.printf "Check : %s\n" (Printer.ts_expr_to_string x);
  check0 x

let alphaCommand (x,y) =
  let x = protect fix x (fun () -> errpos x) in
  let y = protect fix y nopos in
  Printf.printf "Alpha: %s\n" (if (Alpha.UEqual.term_equiv Grammar0.emptyUContext (ATOMIC x) (ATOMIC y)) then "true" else "false");
  Printf.printf "     : %s\n" (Printer.ts_expr_to_string x);
  Printf.printf "     : %s\n" (Printer.ts_expr_to_string y);
  flush stdout

let checkUniversesCommand pos =
  try
    Universe.consistency !global_context
  with Universe.Inconsistency (p,q) -> print_inconsistency p q

let typeCommand x = (
  Printf.printf "Tau: %s ... \n" (Printer.ts_expr_to_string x);
  let t = protect1 ( fun () -> Lfcheck.type_synthesis !global_context x ) in
  Printf.printf " --- LF type synthesis yielded %s\n" (Printer.lf_type_to_string t);
  try 
    let tx = Tau.tau !global_context x in
    Printf.printf "Tau: %s : %s\n" (Printer.ts_expr_to_string x) (Printer.ts_expr_to_string tx);
    flush stdout;
  with 
  | GeneralError s -> raise NotImplemented
  | TypingError (p,s) 
    -> Printf.fprintf stderr "%s: %s\n" (errfmt p) s; 
      flush stderr;
      Tokens.bump_error_count())
    
let show_command () = 
  Printer.print_env !global_context

let addDefinition name aspect pos o t = global_context := def_bind name aspect pos o t !global_context

let process_command lexbuf = (
  let c = protect (Grammar.command (Tokens.expr_tokens)) lexbuf (fun () -> lexpos lexbuf) in
  match c with (pos,c) ->
    match c with
    | Toplevel.UVariable (uvars,eqns) -> protect1 ( fun () -> ubind uvars eqns )
    | Toplevel.Variable tvars -> add_tVars tvars
    | Toplevel.Rule (num,name,t) -> ruleCommand num name t
    | Toplevel.Axiom (name,t) -> axiomCommand name t
    | Toplevel.F_Print x -> f_print_Command x
    | Toplevel.CheckLF x -> checkLFCommand x
    | Toplevel.CheckLFtype x -> checkLFtypeCommand x
    | Toplevel.Check x -> checkCommand x
    | Toplevel.Alpha (x,y) -> alphaCommand (x,y)
    | Toplevel.Type x -> typeCommand x
    | Toplevel.Definition defs -> List.iter (fun (name, aspect, pos, tm, tp) -> addDefinition name aspect pos tm tp) defs
    | Toplevel.End -> Printf.printf "%s: ending.\n" (errfmt pos) ; flush stdout; raise StopParsingFile
    | Toplevel.Show -> show_command()
    | Toplevel.CheckUniverses -> checkUniversesCommand pos
 )

let parse_file filename =
  Printf.printf "-- parsing file %s\n" filename; flush stdout;
  Tokens.error_count := 0;
  let lexbuf = Lexing.from_channel (open_in filename) in
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
  (
   try
     while true do (try process_command lexbuf with Error_Handled -> ());
     done
   with StopParsingFile -> ()
  )
  
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
  List.iter 
    (
     fun x -> Printf.printf "F_Print: %s : %s\n" (label_to_string x) (Printer.lf_type_to_string' (label_to_lf_type x))
    )
    labels;
  List.iter 
    (
     fun (Rule(num,name) as head,_) -> 
       Printf.printf "Rule %d %s : %s\n" num name (Printer.lf_type_to_string' (label_to_lf_type (R head)))
    )
    (List.rev !rules);
    *)
  flush stdout

let _ = try
  toplevel()
with
| Internal_expr      ( ATOMIC(pos,_) as e ) 
| Internal_expr      ( LAMBDA(_,ATOMIC(pos,_)) as e ) 
| Unimplemented_expr ( ATOMIC(pos,_) as e )
| Unimplemented_expr ( LAMBDA(_,ATOMIC(pos,_)) as e ) 
    as ex ->
    Printf.fprintf stderr "%s: internal error on ts_expr %s\n" (errfmt pos) (Printer.lf_canonical_to_string e);
    raise ex

