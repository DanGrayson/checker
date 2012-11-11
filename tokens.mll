{
 open Printf
 open Expressions
 exception Eof
 let error_count = ref 0
 let bump_error_count () =
   incr error_count;
   flush stderr
 let lexing_pos lexbuf = 
   let p = Lexing.lexeme_start_p lexbuf in
   p.Lexing.pos_fname ^ ":" ^
   (string_of_int p.Lexing.pos_lnum) ^ ":" ^
   (string_of_int (p.Lexing.pos_cnum-p.Lexing.pos_bol+1))
}
let white = [ ' ' '\t' '\r' ]
let newline = [ '\n' ]
let digit = [ '0'-'9' ]
let tfirst = [ 'A'-'Z' ]
let ofirst = [ 'a'-'z' ]
let ufirst = "uu"
let after = [ 'A'-'Z' 'a'-'z' '0'-'9' '\'' ]
rule command_tokens = parse
  | "Check" { WCheck }
  | "Print" { WPrint }
  | "Type" { WType }
  | "Subst" { WSubst }
  | white { command_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; command_tokens lexbuf }
  | _ as c { fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count();
	     command_tokens lexbuf }
  | eof { raise Eof }
and expr_tokens = parse
  | "Check" { WCheck }
  | "Print" { WPrint }
  | "Type" { WType }
  | "Subst" { WSubst }
  | "[El]" { WEl }
  | "[U]" { WU }
  | "[u]" { Wu }
  | "[j]" { Wj }
  | "[Pi" { WPi }
  | "[ev" { Wev }
  | "[lambda" { Wlambda }
  | "[forall" { Wforall }
  | "max" { Wmax }
  | '('  { Wlparen }
  | ')'  { Wrparen }
  | '['  { Wlbracket }
  | ']'  { Wrbracket }
  | ';'  { Wsemi }
  | '.'  { Wperiod }
  | ','  { Wcomma }
  | '/'  { Wslash }
  | '+'  { Wplus }
  | digit* as n { Nat (int_of_string n) }
  | ufirst after* as id { UVar id }
  | tfirst after* as id { TVar id }
  | ofirst after* as id { OVar id }
  | white { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | _ as c { fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count;
	     expr_tokens lexbuf }
  | eof { raise Eof }
and command_flush = parse
  | newline { Lexing.new_line lexbuf; command_flush lexbuf }
  | '.' { Wflush }
  | _ { command_flush lexbuf }
