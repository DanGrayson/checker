let leave () = exit (if !Tokens.error_count > 0 then 1 else 0)

let rec protect parser lexbuf =
    try parser lexbuf
    with 
      Typesystem.Eof -> leave()
    | Failure s -> 
	Printf.fprintf stderr "%s: failure: %s\n" (Tokens.lexing_pos lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	exit 1
    | Typesystem.TypingError (p,s) ->
	Printf.fprintf stderr "%s: %s\n" (Typesystem.error_format_pos p) s;
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf
    | Typesystem.GeneralError s ->
	Printf.fprintf stderr "%s: %s\n" (Tokens.lexing_pos lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf
    | Typesystem.Unimplemented s ->
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
  | Typesystem.TDefinition(name,_,_) -> name
  | Typesystem.ODefinition(name,_,_,_) -> name
let printnotation = function
  | Typesystem.TDefinition(name,_,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)
  | Typesystem.ODefinition(name,_,_,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)

let parse_file filename = 
    let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
    let parser = Grammar.command Tokens.expr_tokens in
    let rec process notations =
      let continue notations = flush stdout; process notations in
      match protect parser lexbuf with 
      | Toplevel.Print_t x -> Printf.printf "tPrint: %s\n" (Printer.ttostring x); continue notations
      | Toplevel.Print_o x -> Printf.printf "oPrint: %s\n" (Printer.otostring x); continue notations
      | Toplevel.Print_u x -> Printf.printf "uPrint: %s\n" (Printer.utostring x); continue notations
      | Toplevel.Type x ->
	  (
	   try 
	     let tx = Tau.tau [] x in
	     Printf.printf "Tau: %s : %s\n" (Printer.otostring x) (Printer.ttostring tx);
	   with 
	   | Typesystem.GeneralError s -> raise Typesystem.NotImplemented
	   | Typesystem.TypingError (p,s) 
	     -> Printf.fprintf stderr "%s: %s\n" (Typesystem.error_format_pos p) s; flush stderr; Tokens.bump_error_count());
	  continue notations
      | Toplevel.Notation x ->
	  Printf.printf "Notation: %s\n" (Printer.notationtostring x);
	  continue ((notation_name x,x) :: notations)
      | Toplevel.Exit -> ()
      | Toplevel.Show -> 
	  Printf.printf "Show:\n";
	  let p = List.rev_append notations [] in
	  List.iter (fun x -> Printf.printf "   "; printnotation (snd x)) p;
	  continue notations
    in
    process []

let _ = 
  Arg.parse 
    [
     ("--debug" , Arg.Set Typesystem.debug_mode, "turn on debug mode")
    ]
    parse_file
    "usage: [options] filename ...";
  leave()
