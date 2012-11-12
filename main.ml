let rec protect parser lexbuf =
    try parser lexbuf
    with 
      Tokens.Eof -> exit (if !Tokens.error_count > 0 then 1 else 0)
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
      match protect (Expressions.command Tokens.expr_tokens) lexbuf with 
	Toplevel.Print x -> Printf.printf "Print: %s\n" (Printer.tostring x); flush stdout
      | Toplevel.Subst (x,w,v) -> 
	  Printf.printf "Subst: %s[%s/%s] = %s\n" 
	    (Printer.tostring x) 
	    (Printer.otostring w) 
	    (Printer.ovartostring v) 
	    (Printer.tostring (Substitute.subst [(v,w)] x));
	  flush stdout
      | Toplevel.Type  x -> Printf.printf "Type: %s : %s\n" 
	    (Printer.otostring x) 
	    (
	     try
	       Printer.ttostring (Simpletyping.tau [] x)
	     with 
	       Basic.Error s -> "[[ error: " ^ s ^ " ]]"
	    );
	  flush stdout
      | Toplevel.Check x -> Printf.printf "Check: %s : ...\n" (Printer.tostring x); flush stdout
    done;

