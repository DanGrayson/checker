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
    | Basic.Unimplemented s ->
	Printf.fprintf stderr "%s: feature not implemented yet: %s\n" (Tokens.lexing_pos lexbuf) s;
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

let notation_name = function
  | Typesystem.Declaration(name,_,_) -> name
  | Typesystem.Definition(name,_,_,_) -> name
let printnotation = function
  | Typesystem.Declaration(name,_,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)
  | Typesystem.Definition(name,_,_,_) as x -> Printf.printf "%s\n" (Printer.notationtostring x)

let _ = 
  let lexbuf = Lexing.from_channel stdin in
  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "test.ts"};
  let parser = Grammar.command Tokens.expr_tokens in
  let rec process = function notations ->
    let continue notations = flush stdout; process notations in
    match protect parser lexbuf with 
    | Toplevel.Print_t x -> Printf.printf "Print_t: %s\n" (Printer.ttostring x); continue notations
    | Toplevel.Print_o x -> Printf.printf "Print_o: %s\n" (Printer.otostring x); continue notations
    | Toplevel.Print_u x -> Printf.printf "Print_u: %s\n" (Printer.utostring x); continue notations
    | Toplevel.Type  x -> Printf.printf "Tau: %s : %s\n" 
	  (Printer.otostring x) 
	  (try Printer.ttostring (Tau.tau [] x) with Basic.Error s -> "[[ error: " ^ s ^ " ]]");
	continue notations
    | Toplevel.Notation x ->
 	Printf.printf "Notation: %s\n" (Printer.notationtostring x);
	continue ((notation_name x,x) :: notations)
    | Toplevel.Exit -> ()
    | Toplevel.Show -> 
	Printf.printf "Show:\n";
	let p = List.rev_append notations [] in
	List.map (fun x -> Printf.printf "   "; printnotation (snd x)) p;
	continue notations
  in
  process [];
  Printf.printf "Exit."
