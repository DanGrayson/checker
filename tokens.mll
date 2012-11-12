{
 open Basic
 open Printf
 open Grammar
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
rule expr_tokens = parse
  | "Check" { WCheck }
  | "Derive" { WDerive }
  | "Print" { WPrint }
  | "Type" { WType }
  | "Subst" { WSubst }
  | "[El]" { WEl }
  | "[U]" { WU }
  | "[u]" { Wu }
  | "[j]" { Wj }
  | "[Pi;" { WPi }
  | "Pi" { KPi }
  | "lambda" { Klambda }
  | "[Sigma;" { WSigma }
  | "[Coprod]" { WCoprod }
  | "[Coprod;" { WCoprod2 }
  | "[Empty]" { WEmpty }
  | "[IC;" { WIC }
  | "[Id]" { WId }
  | "[ev;" { Wev }
  | "[lambda;" { Wlambda }
  | "[forall;" { Wforall }
  | "max" { Kmax }
  | '('  { Wlparen }
  | ')'  { Wrparen }
  | '['  { Wlbracket }
  | '-' '>'  { Warrow }
  | ']'  { Wrbracket }
  | '*'  { Wstar }
  | '.'  { Wperiod }
  | ','  { Wcomma }
  | '/'  { Wslash }
  | '+'  { Wplus }
  | ':'  { Wcolon }
  | digit* as n { Nat (int_of_string n) }
  | ufirst after* as id { UVar id }
  | tfirst after* as id { TVar id }
  | ofirst after* as id { OVar id }
  | white { expr_tokens lexbuf }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | _ as c { fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count();
	     expr_tokens lexbuf }
  | eof { raise Eof }
and command_flush = parse
  | newline { Lexing.new_line lexbuf; command_flush lexbuf }
  | '.' { Wflush }
  | _ { command_flush lexbuf }
