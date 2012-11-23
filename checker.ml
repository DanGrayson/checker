(** Top level code. *)

open Typesystem
open Derivation				(*otherwise unused*)
open Universe

let leave () = exit (if !Tokens.error_count > 0 then 1 else 0)

exception Error_Handled

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
      Printf.fprintf stderr "%s:      %s\n" (Error.error_format_pos p2) s2;
      Printf.fprintf stderr "%s:      %s\n" (Error.error_format_pos p3) s3;
      flush stderr;
      Tokens.bump_error_count();
      raise Error_Handled

let protect parser lexbuf posfun =
    try parser lexbuf
    with 
      Error.Eof -> leave()
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

let definition_name = function
  | TDefinition(name,_) 
  | ODefinition(name,_) 
  | TeqDefinition(name,_) 
  | OeqDefinition(name,_) -> name
let printdefinition = function
  | TDefinition(name,_)
  | ODefinition(name,_)
  | TeqDefinition(name,_)
  | OeqDefinition(name,_) as x
    -> Printf.printf "%s\n" (Printer.definitiontostring x)

let lexpos lexbuf = 
  let p = Tokens.lexing_pos lexbuf in
  let _ = Tokens.command_flush lexbuf in
  p

let environment = ref {
  uc = emptyUContext;
  tc = emptyTContext;
  oc = emptyOContext;
  definitions = [];
  lookup_order = [];
}

let add_tVars tvars = environment := 
  { !environment with 
    tc = List.rev_append (List.map make_Var tvars) (!environment).tc ;
    lookup_order = List.rev_append (List.map (fun t -> (t,(make_Var t, Type_variable))) tvars) (!environment).lookup_order ;
  }
let add_uVars uvars eqns =
  environment := {
    !environment with
		  uc = mergeUContext (!environment).uc (UContext(List.map make_Var uvars,eqns));
		  lookup_order = List.rev_append (List.map (fun u -> (u,(make_Var u, Ulevel_variable))) uvars) (!environment).lookup_order;
		}

let fix t = Fillin.fillin !environment t

let tPrintCommand x =
  Printf.printf "Print type: %s\n" (Printer.etostring x);
  Printf.printf " ... LFPrint Type: %s\n" (Printer.lftostring x);
  flush stdout;
  let x' = protect fix x Error.nopos in
  if not (Alpha.UEqual.equiv (!environment).uc x' x) then Printf.printf "      : %s\n" (Printer.etostring x');
  flush stdout
  
let oPrintCommand x =
  Printf.printf "Print: %s\n" (Printer.etostring x); 
  Printf.printf " ... LFPrint Obj : %s\n" (Printer.lftostring x); 
  flush stdout;
  let x' = protect fix x Error.nopos in
  if not (Alpha.UEqual.equiv (!environment).uc x' x) then Printf.printf "      : %s\n" (Printer.etostring x');
  flush stdout

let uCheckCommand x =
  Printf.printf "Check ulevel: %s\n" (Printer.etostring x);
  flush stdout;
  protect1 (fun () -> Check.ucheck !environment x)

let tCheckCommand x =
  Printf.printf "Check type: %s\n" (Printer.etostring x);
  Printf.printf "        LF: %s\n" (Printer.lftostring x);
  flush stdout;
  protect1 (fun () -> Check.tcheck !environment x)

let oCheckCommand x =
  let x = protect1 ( fun () -> Fillin.fillin !environment x ) in
  Printf.printf "Check: %s\n" (Printer.etostring x);
  Printf.printf "   LF: %s\n" (Printer.lftostring x);
  flush stdout;
  protect1 (fun () -> Check.ocheck !environment x)

let uPrintCommand x =
  Printf.printf "Print ulevel: %s\n" (Printer.etostring x);
  flush stdout

let tAlphaCommand (x,y) =
  let x = protect fix x Error.nopos in
  let y = protect fix y Error.nopos in
  Printf.printf "tAlpha: %s\n" (if (Alpha.UEqual.equiv (!environment).uc x y) then "true" else "false");
  Printf.printf "      : %s\n" (Printer.etostring x);
  Printf.printf "      : %s\n" (Printer.etostring y);
  flush stdout

let oAlphaCommand = fun (x,y) ->
  let x = protect fix x Error.nopos in
  let y = protect fix y Error.nopos in
  Printf.printf "oAlpha: %s\n" (if (Alpha.UEqual.equiv (!environment).uc x y) then "true" else "false");
  Printf.printf "      : %s\n" (Printer.etostring x);
  Printf.printf "      : %s\n" (Printer.etostring y);
  flush stdout

let uAlphaCommand = fun (x,y) -> 
  Printf.printf "uAlpha: %s\n" (if (Alpha.UEqual.uequiv (!environment).uc x y) then "true" else "false");
  Printf.printf "      : %s\n" (Printer.etostring x);
  Printf.printf "      : %s\n" (Printer.etostring y);
  flush stdout

let checkUniversesCommand pos =
  try
    Universe.consistency (!environment.uc)
  with Error.UniverseInconsistency 
    ->Printf.fprintf stderr "%s: universe inconsistency\n" (Error.error_format_pos pos); 
      flush stderr;
      Tokens.bump_error_count()

let typeCommand x = (
  try 
    let tx = Tau.tau !environment x in
    Printf.printf "Tau: %s : %s\n" (Printer.etostring x) (Printer.etostring tx);
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
   Printf.printf "   Variable ";
   let UContext(uvars,ueqns) = (!environment).uc in 
   Printf.printf "%s.\n"
     ((String.concat " " (List.map vartostring' (List.rev uvars))) ^ " : Univ" ^ (String.concat "" (List.map Printer.ueqntostring ueqns)));
  );
  (
   Printf.printf "   Variable"; List.iter (fun x -> Printf.printf " %s" (vartostring' x)) (List.rev (!environment).tc); Printf.printf " : Type.\n";
  );
  (
   let p = List.rev_append (!environment).definitions [] in List.iter (fun x -> Printf.printf "   "; printdefinition (snd x)) p;
  );
  (
   Printf.printf "   Lookup order:";
   List.iter (fun (s,_) -> Printf.printf " %s" s) (!environment).lookup_order;
   Printf.printf "\n";
  );
  flush stdout

let addDefinition x =
  Printf.printf "Definition: %s\n" (Printer.definitiontostring x);
  flush stdout;
  environment := { !environment with definitions = (definition_name x,x) :: (!environment).definitions }

exception StopParsingFile

let process_command lexbuf = (
  let c = protect (Grammar.command (Tokens.expr_tokens)) lexbuf lexpos in
  match c with (pos,c) ->
    match c with
    | Toplevel.UVariable (uvars,eqns) -> add_uVars uvars eqns
    | Toplevel.Variable tvars -> add_tVars tvars
    | Toplevel.UPrint x -> uPrintCommand x
    | Toplevel.TPrint x -> tPrintCommand x
    | Toplevel.OPrint x -> oPrintCommand x
    | Toplevel.UCheck x -> uCheckCommand x
    | Toplevel.TCheck x -> tCheckCommand x
    | Toplevel.OCheck x -> oCheckCommand x
    | Toplevel.TAlpha (x,y) -> tAlphaCommand (x,y)
    | Toplevel.OAlpha (x,y) -> oAlphaCommand (x,y)
    | Toplevel.UAlpha (x,y) -> uAlphaCommand (x,y)
    | Toplevel.Type x -> typeCommand x
    | Toplevel.Definition x -> addDefinition x
    | Toplevel.End -> Printf.printf "%s: ending.\n" (Error.error_format_pos pos) ; flush stdout; raise StopParsingFile
    | Toplevel.Show -> show_command()
    | Toplevel.CheckUniverses -> checkUniversesCommand pos
 )

let parse_file filename =
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
let oExpr_from_string = parse_string Grammar.oExprEof
let tExpr_from_string = parse_string Grammar.tExprEof

let _ = 
  Arg.parse [
  ("--debug" , Arg.Set Debugging.debug_mode, "turn on debug mode")
]
    parse_file
    "usage: [options] filename ...";
(*
   (try tPrintCommand (tExpr_from_string "Pi f:T->[U](uuu0), Pi o:T, *f o" ) with Error_Handled -> ());
   (try oPrintCommand (oExpr_from_string "lambda f:T->U, lambda o:T, f o") with Error_Handled -> ());
 *)
  leave()
