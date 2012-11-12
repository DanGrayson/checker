{
 open Basic
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
let first = [ 'A'-'Z' 'a'-'z' ]
let after = [ 'A'-'Z' 'a'-'z' '0'-'9' '\'' ]
rule expr_tokens = parse
  | "Print_o" { WPrint_o }
  | "Print_t" { WPrint_t }
  | "Print_u" { WPrint_u }
  | "Tau" { WTau }
  | "Definition" { WDefinition }
  | "[El]" { WEl }
  | "[U]" { WU }
  | "[u]" { Wu }
  | "[j]" { Wj }
  | "j" { Kj }
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
  | "ulevel" { Kulevel }
  | "Type" { KType }
  | "umax" { Kumax }
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
  | '='  { Wequal }
  | ':' '='  { Wcolonequal }
  | '|' '-'  { Wturnstile }
  | '|' '>'  { Wtriangle }
  | digit* as n { Nat (int_of_string n) }
  | first after* as id { Var_token id }
  | white { expr_tokens lexbuf }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | _ as c { Printf.fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count();
	     expr_tokens lexbuf }
  | eof { raise Eof }
and command_flush = parse
  | newline { Lexing.new_line lexbuf; command_flush lexbuf }
  | '.' { Wflush }
  | _ { command_flush lexbuf }
