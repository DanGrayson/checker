let rec protect parser lexbuf =
    try parser lexbuf
    with 
      Basic.Eof -> exit (if !Tokens.error_count > 0 then 1 else 0)
    | Failure s -> 
	Printf.fprintf stderr "%s: failure: %s\n" (Tokens.lexing_pos lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	exit 1
    | Basic.Error s ->
	Printf.fprintf stderr "%s: %s\n" (Tokens.lexing_pos lexbuf) s;
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf
    | Parsing.Parse_error -> 
	Printf.fprintf stderr "%s: syntax error\n" (Tokens.lexing_pos lexbuf);
	flush stderr;
	Tokens.bump_error_count();
	let _ = Tokens.command_flush lexbuf in
	protect parser lexbuf

let _ = 
  let lexbuf = Lexing.from_channel stdin in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "test.ts"};
    while true do
      match protect (Grammar.command Tokens.expr_tokens) lexbuf with 
      | Toplevel.Print_t x -> Printf.printf "Print_t: %s\n" (Printer.ttostring x); flush stdout
      | Toplevel.Print_o x -> Printf.printf "Print_o: %s\n" (Printer.otostring x); flush stdout
      | Toplevel.Print_u x -> Printf.printf "Print_u: %s\n" (Printer.utostring x); flush stdout
      | Toplevel.Type  x -> Printf.printf "Tau: %s : %s\n" 
	    (Printer.otostring x) 
	    (
	     try
	       Printer.ttostring (Tau.tau [] x)
	     with 
	       Basic.Error s -> "[[ error: " ^ s ^ " ]]"
	    );
	  flush stdout
      | Toplevel.Definition x -> Printf.printf "Definition: %s\n" (Printer.deftostring x); flush stdout
      | Toplevel.Declaration x -> Printf.printf "Declaration: %s\n" (Printer.dectostring x); flush stdout
    done;

