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

type environment_type = {
  uc : uContext;
  tc : tContext;
  notations : (Typesystem.identifier * Typesystem.notation) list;
}

let environment = ref {
  uc = initialUContext;
  tc = emptyTContext;
  notations = [];
}

let tfix t = Fillin.tfillin [] t
let ofix o = Fillin.ofillin [] o

let process_command lexbuf = (
  match protect (Grammar.command (Tokens.expr_tokens)) lexbuf lexpos with 
  | Toplevel.UVariable (vars,eqns) -> 
      let vars = List.map make_uVar vars in
      environment := { !environment with uc = mergeUContext (!environment).uc (UContext(vars,eqns)) }
  | Toplevel.TVariable tvars -> 
      environment := { !environment with tc = List.rev_append (List.map make_tVar tvars) (!environment).tc }
  | Toplevel.Print_t x ->
      Printf.printf "tPrint: %s\n" (Printer.ttostring x);
      flush stdout;
      let x' = protect tfix x nopos in
      if not (Alpha.tequal x' x) then Printf.printf "      : %s\n" (Printer.ttostring x');
  | Toplevel.Print_o x ->
      Printf.printf "oPrint: %s\n" (Printer.otostring x); 
      flush stdout;
      let x' = protect ofix x nopos in
      if not (Alpha.oequal x' x) then Printf.printf "      : %s\n" (Printer.otostring x')
  | Toplevel.Print_u x -> 
      Printf.printf "uPrint: %s\n" (Printer.utostring x); 
  | Toplevel.Type x ->
      (
       try 
	 let tx = Tau.tau [] x in
	 Printf.printf "Tau: %s : %s\n" (Printer.otostring x) (Printer.ttostring tx);
	 flush stdout;
       with 
       | GeneralError s -> raise NotImplemented
       | TypingError (p,s) 
	 -> Printf.fprintf stderr "%s: %s\n" (error_format_pos p) s; 
	   flush stderr;
	   Tokens.bump_error_count());
  | Toplevel.Notation x ->
      Printf.printf "Notation: %s\n" (Printer.notationtostring x);
      environment := { !environment with notations = (notation_name x,x) :: (!environment).notations }
  | Toplevel.Exit -> ()
  | Toplevel.Show -> 
      Printf.printf "Show:\n";
      Printf.printf "   uVariable ";
      let UContext(uvars,ueqns) = (!environment).uc in 
      Printf.printf "%s.\n" 
	((String.concat " " (List.map Printer.uvartostring uvars)) ^ ":Univ" ^ (String.concat "" (List.map Printer.ueqntostring ueqns)));
      Printf.printf "   tVariable"; List.iter (fun x -> Printf.printf " %s" (Printer.tvartostring x)) (List.rev (!environment).tc); Printf.printf ".\n";
      let p = List.rev_append (!environment).notations [] in List.iter (fun x -> Printf.printf "   "; printnotation (snd x)) p;
 )

let parse_file filename =
    let lexbuf = Lexing.from_channel (open_in filename) in
    lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename};
    while true do
      ( try process_command lexbuf with Error_Handled -> ());
      flush stderr;
      Printf.printf "\n";
      flush stdout;
    done

let _ = 
  Arg.parse [
      ("--debug" , Arg.Set debug_mode, "turn on debug mode")
      ]
    parse_file
    "usage: [options] filename ...";
  leave()
