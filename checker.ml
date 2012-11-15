open Typesystem

let leave () = exit (if !Tokens.error_count > 0 then 1 else 0)
let nopos x = "unknown position"

exception Error_Handled

let rec protect parser lexbuf posfun =
    try parser lexbuf
    with 
      Eof -> leave()
    | Failure s -> 
	Printf.fprintf stderr "%s: failure: %s\n" (posfun lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	raise (Failure s)
    | TypingError (p,s) ->
	Printf.fprintf stderr "%s: %s\n" (error_format_pos p) s;
	flush stderr;
	Tokens.bump_error_count();
	raise Error_Handled
    | GeneralError s ->
	Printf.fprintf stderr "%s: %s\n" (posfun lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	raise Error_Handled
    | Unimplemented s ->
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

let notation_name = function
  | TDefinition(name,_) -> name
  | ODefinition(name,_) -> name
let printnotation = function
  | TDefinition(name,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)
  | ODefinition(name,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)

let lexpos lexbuf = 
  let p = Tokens.lexing_pos lexbuf in
  let _ = Tokens.command_flush lexbuf in
  p

type var = U of uVar | T of tVar | O of oVar

type environment_type = {
    uc : uContext;
    tc : tContext;
    definitions : (Typesystem.identifier * Typesystem.notation) list;
    lookup_order : (string * var) list	(* put definitions in here later *)
  }

let environment = ref {
  uc = emptyUContext;
  tc = emptyTContext;
  definitions = [];
  lookup_order = [];
}

let add_tVars tvars = environment := { !environment with tc = List.rev_append (List.map make_tVar tvars) (!environment).tc }
let add_uVars uvars eqns =
  let uvars = List.map make_uVar uvars in
  environment := { !environment with uc = mergeUContext (!environment).uc (UContext(uvars,eqns)) }

let tfix t = Fillin.tfillin [] t
let ofix o = Fillin.ofillin [] o

let tPrintCommand x =
  Printf.printf "tPrint: %s\n" (Printer.ttostring x);
  flush stdout;
  let x' = protect tfix x nopos in
  if not (Alpha.tequal x' x) then Printf.printf "      : %s\n" (Printer.ttostring x');
  flush stdout
  
let oPrintCommand x =
  Printf.printf "oPrint: %s\n" (Printer.otostring x); 
  flush stdout;
  let x' = protect ofix x nopos in
  if not (Alpha.oequal x' x) then Printf.printf "      : %s\n" (Printer.otostring x');
  flush stdout

let uPrintCommand x =
  Printf.printf "uPrint: %s\n" (Printer.utostring x);
  flush stdout

let tAlphaCommand (x,y) =
  let x = protect tfix x nopos in
  let y = protect tfix y nopos in
  Printf.printf "tAlpha: %s\n" (if (Alpha.tequal x y) then "true" else "false");
  Printf.printf "      : %s\n" (Printer.ttostring x);
  Printf.printf "      : %s\n" (Printer.ttostring y);
  flush stdout

let oAlphaCommand = fun (x,y) ->
  let x = protect ofix x nopos in
  let y = protect ofix y nopos in
  Printf.printf "oAlpha: %s\n" (if (Alpha.oequal x y) then "true" else "false");
  Printf.printf "      : %s\n" (Printer.otostring x);
  Printf.printf "      : %s\n" (Printer.otostring y);
  flush stdout

let uAlphaCommand = fun (x,y) -> 
  Printf.printf "uAlpha: %s\n" (if (Alpha.uequal x y) then "true" else "false");
  Printf.printf "      : %s\n" (Printer.utostring x);
  Printf.printf "      : %s\n" (Printer.utostring y);
  flush stdout

let typeCommand x = (
  try 
    let tx = Tau.tau [] x in
    Printf.printf "Tau: %s : %s\n" (Printer.otostring x) (Printer.ttostring tx);
    flush stdout;
  with 
  | GeneralError s -> raise NotImplemented
  | TypingError (p,s) 
    -> Printf.fprintf stderr "%s: %s\n" (error_format_pos p) s; 
      flush stderr;
      Tokens.bump_error_count())
    
let show_command () = 
  Printf.printf "Show:\n";
  Printf.printf "   Variable ";
  let UContext(uvars,ueqns) = (!environment).uc in 
  Printf.printf "%s.\n" 
    ((String.concat " " (List.map Printer.uvartostring uvars)) ^ " : Univ" ^ (String.concat "" (List.map Printer.ueqntostring ueqns)));
  Printf.printf "   Variable"; List.iter (fun x -> Printf.printf " %s" (Printer.tvartostring x)) (List.rev (!environment).tc); Printf.printf " : Type.\n";
  let p = List.rev_append (!environment).definitions [] in List.iter (fun x -> Printf.printf "   "; printnotation (snd x)) p;
  flush stdout

let addDefinition x =
  Printf.printf "Notation: %s\n" (Printer.notationtostring x);
  flush stdout;
  environment := { !environment with definitions = (notation_name x,x) :: (!environment).definitions }

exception StopParsingFile

let process_command lexbuf = (
  match protect (Grammar.command (Tokens.expr_tokens)) lexbuf lexpos with 
  | Toplevel.UVariable (uvars,eqns) -> add_uVars uvars eqns
  | Toplevel.TVariable tvars -> add_tVars tvars
  | Toplevel.TPrint x -> tPrintCommand x
  | Toplevel.OPrint x -> oPrintCommand x
  | Toplevel.UPrint x -> uPrintCommand x
  | Toplevel.TAlpha (x,y) -> tAlphaCommand (x,y)
  | Toplevel.OAlpha (x,y) -> oAlphaCommand (x,y)
  | Toplevel.UAlpha (x,y) -> uAlphaCommand (x,y)
  | Toplevel.Type x -> typeCommand x
  | Toplevel.Notation x -> addDefinition x
  | Toplevel.Exit -> raise StopParsingFile
  | Toplevel.Show -> show_command()
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
      ("--debug" , Arg.Set debug_mode, "turn on debug mode")
      ]
    parse_file
    "usage: [options] filename ...";
  (try tPrintCommand (tExpr_from_string "Pi f:T->[U](uuu0), Pi o:T, *f o") with Error_Handled -> ());
  (try oPrintCommand (oExpr_from_string "lambda f:T->U, lambda o:T, f o") with Error_Handled -> ());
  leave()
