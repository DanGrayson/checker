open Typesystem

let leave () = exit (if !Tokens.error_count > 0 then 1 else 0)

let rec protect parser lexbuf =
    try parser lexbuf
    with 
      Eof -> leave()
    | Failure s -> 
	Printf.fprintf stderr "%s: failure: %s\n" (Tokens.lexing_pos lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	exit 1
    | TypingError (p,s) ->
	Printf.fprintf stderr "%s: %s\n" (error_format_pos p) s;
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf
    | GeneralError s ->
	Printf.fprintf stderr "%s: %s\n" (Tokens.lexing_pos lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf
    | Unimplemented s ->
	Printf.fprintf stderr "%s: feature not yet implemented: %s\n" (Tokens.lexing_pos lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf
    | Grammar.Error
    | Parsing.Parse_error -> 
	Printf.fprintf stderr "%s: syntax error\n" (Tokens.lexing_pos lexbuf);
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf

let notation_name = function
  | TDefinition(name,_) -> name
  | ODefinition(name,_) -> name
let printnotation = function
  | TDefinition(name,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)
  | ODefinition(name,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)

let parse_file filename = 
    let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
    let rec process notations (uc:uContext) (tc:tContext) =
      let continue notations uc tc = flush stdout; flush stderr; process notations uc tc in
      match protect (Grammar.command (Tokens.expr_tokens notations uc tc)) lexbuf with 
      | Toplevel.UVariable (vars,eqns) -> 
	  let vars = List.map make_uVar vars in
	  continue notations (mergeUContext uc (UContext(vars,eqns))) tc
      | Toplevel.TVariable tvars -> continue notations uc (tc@(List.map make_tVar tvars))
      | Toplevel.Print_t x -> Printf.printf "tPrint: %s\n" (Printer.ttostring x); continue notations uc tc
      | Toplevel.Print_o x -> Printf.printf "oPrint: %s\n" (Printer.otostring x); continue notations uc tc
      | Toplevel.Print_u x -> Printf.printf "uPrint: %s\n" (Printer.utostring x); continue notations uc tc
      | Toplevel.Type x ->
	  (
	   try 
	     let tx = Tau.tau [] x in
	     Printf.printf "Tau: %s : %s\n" (Printer.otostring x) (Printer.ttostring tx);
	   with 
	   | GeneralError s -> raise NotImplemented
	   | TypingError (p,s) 
	     -> Printf.fprintf stderr "%s: %s\n" (error_format_pos p) s; Tokens.bump_error_count());
	  continue notations uc tc
      | Toplevel.Notation x ->
	  Printf.printf "Notation: %s\n" (Printer.notationtostring x);
	  continue ((notation_name x,x) :: notations) uc tc
      | Toplevel.Exit -> ()
      | Toplevel.Show -> 
	  Printf.printf "Show:\n";
	  Printf.printf "   uVariable ";
	  let UContext(uvars,ueqns) = uc in 
	  Printf.printf "%s.\n" ((String.concat " " (List.map Printer.uvartostring uvars)) ^ ":Univ" ^ (String.concat "" (List.map Printer.ueqntostring ueqns)));
	  Printf.printf "   tVariable"; List.iter (fun x -> Printf.printf " %s" (Printer.tvartostring x)) tc; Printf.printf ".\n";
	  let p = List.rev_append notations [] in List.iter (fun x -> Printf.printf "   "; printnotation (snd x)) p;
	  continue notations uc tc
    in
    process [] emptyUContext emptyTContext

let _ = 
  Arg.parse 
    [
     ("--debug" , Arg.Set debug_mode, "turn on debug mode")
    ]
    parse_file
    "usage: [options] filename ...";
  leave()
