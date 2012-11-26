(** The lexical analyzer for the type theory. *)

{
 open Grammar
 open Typesystem
 let error_count = ref 0
 let bump_error_count () =
   incr error_count;
   if !error_count >= 7 then (
     Printf.fprintf stderr "Too many errors, exiting.\n"; 
     flush stderr; 
     exit 1);
   flush stderr
 let lexing_pos lexbuf = 
   let p = Lexing.lexeme_start_p lexbuf in
   p.Lexing.pos_fname ^ ":" ^
   (string_of_int p.Lexing.pos_lnum) ^ ":" ^
   (string_of_int (p.Lexing.pos_cnum-p.Lexing.pos_bol+1))
 let tab lexbuf =
   let p = lexbuf.Lexing.lex_curr_p in
   let bol = p.Lexing.pos_bol in
   let cnum = p.Lexing.pos_cnum in
   let col = cnum - bol in
   let col = (col + 7) / 8 * 8 in
   let bol = cnum - col in
   lexbuf.Lexing.lex_curr_p <- { p with Lexing.pos_bol = bol }
}
let nzdigit = [ '1'-'9' ]
let digit = [ '0'-'9' ]
let first = [ 'A'-'Z' 'a'-'z' ]
let after = [ 'A'-'Z' 'a'-'z' '0'-'9' '\'' '_' ]
let space = [ ' ' '\r' ]*
let newline = [ '\n' '\012' ]
let ident = first after*
rule expr_tokens = parse
  | "Check" space "Universes" { WCheckUniverses }
  | "Print" { WPrint }
  | "Rule" { WRule }
  | "F_Print" { WF_Print }
  | "Alpha" { WAlpha }
  | "Check" { WCheck }
  | "Tau" { WTau }
  | "Variable" { WVariable }
  | "Define" { WDefine }
  | "End" { WEnd }
  | "Show" { WShow }
  | '[' (ident as id) '.' (digit+ as aspect) ']' { DEF_APP(id,int_of_string aspect) }
  | '[' (ident as id) ']' { LABEL id }
  | '[' (ident as id) ';' { LABEL_SEMI id }
  | "Pi" { KPi }
  | "lambda" { Klambda }
  | "Sigma" { KSigma }
  | "Ulevel" { KUlevel }
  | "Type" { KType }
  | "type" { Ktype }
  | "max" { Kumax }
  | '('  { Wlparen }
  | ')'  { Wrparen }
  | ']'  { Wrbracket }
  | '['  { Wlbracket }
  | '-' '>'  { Warrow }
  | '*'  { Wstar }
  | ';'  { Wsemi }
  | '.'  { Wperiod }
  | ','  { Wcomma }
  | '+'  { Wplus }
  | ':'  { Wcolon }
  | '='  { Wequal }
  | '=' '=' { Wequalequal }
  | '@' '@' { Watat }
  | '>' '='  { Wgreaterequal }
  | '>' { Wgreater }
  | '<' '='  { Wlessequal }
  | '_' { Wunderscore }
  | '<' { Wless }
  | ':' '='  { Wcolonequal }
  | digit+ as n { Nat (int_of_string n) } (* eventually check for overflow and leading 0 *)
  | ident as id { IDENTIFIER id }
  | '\t' { tab lexbuf; expr_tokens lexbuf }
  | space { expr_tokens lexbuf }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | _ as c { Printf.fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count();
	     expr_tokens lexbuf }
  | eof { Weof }
and command_flush = parse
  | eof { Weof }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { command_flush lexbuf }
  | _ { command_flush lexbuf }
