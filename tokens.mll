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
let newline = [ '\n' ]
let nzdigit = [ '1'-'9' ]
let digit = [ '0'-'9' ]
let first = [ 'A'-'Z' 'a'-'z' ]
let after = [ 'A'-'Z' 'a'-'z' '0'-'9' '\'' ]
let white = [ ' ' '\r' '\n' '\t' '\012' ]*
rule expr_tokens = parse
  | "Check" white "Universes" { WCheckUniverses }
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
  | "[El]" { WEl }
  | "[U]" { WU }
  | "[u]" { Wu }
  | "[j]" { Wj }
  | "[def;" { Wdef }
  | "[Pi;" { WPi }
  | "PI" { FPi }
  | "Pi" { KPi }
  | "LAMBDA" { Flambda }
  | "lambda" { Klambda }
  | "[Sigma;" { WSigma }
  | "Sigma" { KSigma }
  | "[Coprod]" { WCoprod }
  | "[Coprod;" { WCoprod2 }
  | "[Empty]" { WEmpty }
  | "[empty]" { Wempty }
  | "[empty_r]" { Wempty_r }
  | "[IC;" { WIC }
  | "[Id]" { WId }
  | "[ev;" { Wev }
  | "[lambda;" { Wlambda }
  | "[forall;" { Wforall }
  | "forall" { Kforall }
  | "Ulevel" { KUlevel }
  | "Type" { KType }
  | "max" { Kumax }
  | "|" { Wbar }
  | '('  { Wlparen }
  | ')'  { Wrparen }
  | '['  { Wlbracket }
  | ']'  { Wrbracket }
  | '{'  { Wlbrace }
  | '}'  { Wrbrace }
  | '-' '>'  { Warrow }
  | '*'  { Wstar }
  | ';'  { Wsemi }
  | '.'  { Wperiod }
  | ','  { Wcomma }
  | '/'  { Wslash }
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
  | '|' '-'  { Wturnstile }
  | '|' '>'  { Wtriangle }
  | digit+ as n { Nat (int_of_string n) } (* eventually check for overflow and leading 0 *)
  | first after* as id { IDENTIFIER id }
  | [ '\t' ] { tab lexbuf; expr_tokens lexbuf }
  | [ ' ' '\r' ] { expr_tokens lexbuf }
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
  | '.' { Wflush }
  | _ { command_flush lexbuf }
