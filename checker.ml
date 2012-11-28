(** Top level code. *)

open Typesystem
open Template				(*otherwise unused*)
open Lfcheck				(*otherwise unused*)
open Universe

exception Error_Handled
exception FileFinished
exception StopParsingFile

let error_summary pos =
  let n = !Tokens.error_count in
  if n > 0 
  then (
    Printf.fprintf stderr "%s: exiting, %d error%s encountered, see messages above\n" pos n (if n == 1 then "" else "s");
    flush stderr)

let leave pos = 
  error_summary pos;
  raise StopParsingFile

let protect1 f =
  try f () with
  | Error.TypingError (p,s) ->
      Printf.fprintf stderr "%s: %s\n" (Error.error_format_pos p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | Error.TypingUnimplemented (p,s) -> 
      Printf.fprintf stderr "%s: type checking unimplemented: %s\n" (Error.error_format_pos p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | Error.TypeCheckingFailure (p,s) -> 
      Printf.fprintf stderr "%s: type checking failure: %s\n" (Error.error_format_pos p) s;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled
  | Error.TypeCheckingFailure3 (p1,s1,p2,s2,p3,s3) -> 
      Printf.fprintf stderr "%s: type checking failure: %s\n" (Error.error_format_pos p1) s1;
      Printf.fprintf stderr "%s: ... %s\n" (Error.error_format_pos p2) s2;
      Printf.fprintf stderr "%s: ... %s\n" (Error.error_format_pos p3) s3;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled

let protect parser lexbuf posfun =
    try parser lexbuf
    with 
      Error.Eof -> leave (posfun lexbuf)
    | Error.TypingUnimplemented (p,s) -> 
	Printf.fprintf stderr "%s: type checking unimplemented: %s\n" (Error.error_format_pos p) s;
	flush stderr;
	Tokens.bump_error_count();
	raise Error_Handled
    | Failure s -> 
	Printf.fprintf stderr "%s: failure: %s\n" (posfun lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	raise (Failure s)
    | Error.TypingError (p,s) ->
	Printf.fprintf stderr "%s: %s\n" (Error.error_format_pos p) s;
	flush stderr;
	Tokens.bump_error_count();
	raise Error_Handled
    | Error.GeneralError s ->
	Printf.fprintf stderr "%s: %s\n" (posfun lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	raise Error_Handled
    | Error.Unimplemented s ->
	Printf.fprintf stderr "%s: feature not yet implemented: %s\n" (posfun lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	raise Error_Handled
    | Grammar.Error
    | Parsing.Parse_error -> 
	Printf.fprintf stderr "%s: syntax error\n" (posfun lexbuf);
	flush stderr;
	Tokens.bump_error_count();
	raise Error_Handled

let lexpos lexbuf = 
  let p = Tokens.lexing_pos lexbuf in
  let _ = Tokens.command_flush lexbuf in
  p

let environment = ref {
  ulevel_context = emptyUContext;
  ts_context = [];
  lf_context = [];
}

let add_tVars tvars = environment := 
  { !environment with 
    lf_context = List.rev_append (List.map (fun t -> (Helpers.make_Var t, texp)) tvars) (!environment).lf_context ;
  }
let add_uVars uvars eqns =
  environment := {
    !environment with
		  ulevel_context = mergeUContext (!environment).ulevel_context (UContext(List.map Helpers.make_Var uvars,eqns));
		  lf_context = List.rev_append (List.map (fun u -> (Helpers.make_Var u, uexp)) uvars) (!environment).lf_context;
		}

let fix t = Fillin.fillin !environment t

let printCommand x =
  Printf.printf "Print: %s\n" (Printer.lfexpr_to_string x);
  flush stdout

let ruleCommand num name x =
  rules := (Rule (num,name), x) :: !rules;
  Printf.printf "Rule %d %s: %s\n" num name (Printer.lftype_to_string true x);
  flush stdout

let lf_type_printCommand x =
  Printf.printf "F_Print: %s\n" (Printer.lftype_to_string true x);
  flush stdout

let checkCommand x =
  Printf.printf "Check: %s\n" (Printer.ts_expr_to_string x);
  Printf.printf "   LF: %s\n" (Printer.lfexpr_to_string x);
  Printf.printf "   filling in ...\n";
  flush stdout;
  let x = protect1 ( fun () -> Fillin.fillin !environment x ) in
  match x with
  | POS(_,APPLY(O _,_)) -> 
      Printf.printf "     : o-expression, will check its type\n";
      flush stdout;
      protect1 (fun () -> Check.ocheck !environment x)
  | POS(_,APPLY(R _,_)) -> 
      Printf.printf "     : inference rule\n"
  | POS(_,APPLY(T _,_)) -> 
      Printf.printf "     : t-expression\n"
  | POS(_,APPLY(U _,_)) -> 
      Printf.printf "     : u-expression\n"
  | POS(_,APPLY(V _,_)) -> 
      Printf.printf "     : lf-application, with variable as label\n"
  | POS(_,Variable _) -> 
      Printf.printf "     : variable\n"
  | POS(_,EmptyHole n) -> 
      Printf.printf "     : empty hole ?%d\n" n
  | LAMBDA _ ->
      Printf.printf "     : binder\n";
  flush stdout

let alphaCommand (x,y) =
  let x = protect fix x Error.nopos in
  let y = protect fix y Error.nopos in
  Printf.printf "Alpha: %s\n" (if (Alpha.UEqual.equiv (!environment).ulevel_context x y) then "true" else "false");
  Printf.printf "     : %s\n" (Printer.ts_expr_to_string x);
  Printf.printf "     : %s\n" (Printer.ts_expr_to_string y);
  flush stdout

let checkUniversesCommand pos =
  try
    Universe.consistency (!environment.ulevel_context)
  with Error.UniverseInconsistency 
    ->Printf.fprintf stderr "%s: universe inconsistency\n" (Error.error_format_pos pos); 
      flush stderr;
      Tokens.bump_error_count()

let typeCommand x = (
  try 
    let tx = Tau.tau !environment x in
    Printf.printf "Tau: %s : %s\n" (Printer.ts_expr_to_string x) (Printer.ts_expr_to_string tx);
    flush stdout;
  with 
  | Error.GeneralError s -> raise Error.NotImplemented
  | Error.TypingError (p,s) 
    -> Printf.fprintf stderr "%s: %s\n" (Error.error_format_pos p) s; 
      flush stderr;
      Tokens.bump_error_count())
    
let show_command () = 
  Printf.printf "Show:\n";
  (
   Printf.printf "  LF context:\n";
   List.iter 
     (fun (v,t) -> Printf.printf "     %s : %s\n" 
	 (vartostring' v)
	 (Printer.lftype_to_string true t)) 
     (List.rev (!environment).lf_context);
  );
  flush stdout

let addDefinition name aspect o t = environment := def_bind (VarDefined(name,aspect)) o t !environment

let process_command lexbuf = (
  let c = protect (Grammar.command (Tokens.expr_tokens)) lexbuf lexpos in
  match c with (pos,c) ->
    match c with
    | Toplevel.UVariable (uvars,eqns) -> add_uVars uvars eqns
    | Toplevel.Variable tvars -> add_tVars tvars
    | Toplevel.Rule (num,name,t) -> ruleCommand num name t
    | Toplevel.F_Print x -> lf_type_printCommand x
    | Toplevel.Print x -> printCommand x
    | Toplevel.Check x -> checkCommand x
    | Toplevel.Alpha (x,y) -> alphaCommand (x,y)
    | Toplevel.Type x -> typeCommand x
    | Toplevel.Definition defs -> List.iter (fun (name, aspect, tm, tp) -> addDefinition name aspect tm tp) defs
    | Toplevel.End -> Printf.printf "%s: ending.\n" (Error.error_format_pos pos) ; flush stdout; raise StopParsingFile
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
    protect (grammar (Tokens.expr_tokens)) lexbuf lexpos
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
  (try printCommand (expr_from_string "Pi f:T->[U](uuu0), Pi o:T, *f o" ) with Error_Handled -> ());
  (try printCommand (expr_from_string "lambda f:T->U, lambda o:T, f o") with Error_Handled -> ());
  List.iter 
    (
     fun x -> Printf.printf "F_Print: %s : %s\n" (label_to_string x) (Printer.lftype_to_string (label_to_lftype x))
    )
    labels;
  List.iter 
    (
     fun (Rule(num,name) as head,_) -> 
       Printf.printf "Rule %d %s : %s\n" num name (Printer.lftype_to_string (label_to_lftype (R head)))
    )
    (List.rev !rules);
    *)
  flush stdout;
  error_summary "checker.ml:0:0"

let _ = try
  toplevel()
with
| Internal_expr      ( POS(pos,_) as e ) 
| Internal_expr      ( LAMBDA(_,POS(pos,_)) as e ) 
| Unimplemented_expr ( POS(pos,_) as e )
| Unimplemented_expr ( LAMBDA(_,POS(pos,_)) as e ) 
    as ex ->
    Printf.fprintf stderr "%s: internal error on expr %s\n" (Error.error_format_pos pos) (Printer.lfexpr_to_string e);
    raise ex

