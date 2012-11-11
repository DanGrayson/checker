let rec protect parser lexbuf =
    try parser lexbuf
    with 
      Tokens.Eof -> exit 0
    | Failure s -> 
	Tokens.curry3 (Printf.fprintf stderr "%s:%d:%d: failure: %s\n") (Tokens.position lexbuf) s;
	flush stderr;
	exit 1
    | Parsing.Parse_error -> 
	Tokens.curry3 (Printf.fprintf stderr "%s:%d:%d: syntax error\n") (Tokens.position lexbuf);
	flush stderr;
	Lexing.flush_input lexbuf;
	protect parser lexbuf

let _ = 
  let lexbuf = Lexing.from_channel stdin in
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
      | Toplevel.Type  x -> Printf.printf "Type: %s : ...\n" (Printer.tostring x); flush stdout
      | Toplevel.Check x -> Printf.printf "Check: %s : ...\n" (Printer.tostring x); flush stdout
    done
