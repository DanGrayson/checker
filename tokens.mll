{
 open Grammar
 open Typesystem
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
let nzdigit = [ '1'-'9' ]
let digit = [ '0'-'9' ]
let first = [ 'A'-'Z' 'a'-'z' ]
let after = [ 'A'-'Z' 'a'-'z' '0'-'9' '\'' ]
rule expr_tokens = 
parse
  | "uPrint" { WuPrint }
  | "tPrint" { WtPrint }
  | "oPrint" { WoPrint }
  | "uAlpha" { WuAlpha }
  | "tAlpha" { WtAlpha }
  | "oAlpha" { WoAlpha }
  | "uCheck" { WuCheck }
  | "tCheck" { WtCheck }
  | "oCheck" { WoCheck }
  | "Tau" { WTau }
  | "Variable" { WVariable }
  | "tDefinition" { WtDefinition }
  | "oDefinition" { WoDefinition }
  | "Exit" { WExit }
  | "Show" { WShow }
  | "[El]" { WEl }
  | "[U]" { WU }
  | "[u]" { Wu }
  | "[j]" { Wj }
  | "[udef;" { Wudef }
  | "[tdef;" { Wtdef }
  | "[odef;" { Wodef }
  | "[Pi;" { WPi }
  | "Pi" { KPi }
  | "lambda" { Klambda }
  | "[Sigma;" { WSigma }
  | "Sigma" { KSigma }
  | "[Coprod]" { WCoprod }
  | "[Coprod;" { WCoprod2 }
  | "[Empty]" { WEmpty }
  | "[IC;" { WIC }
  | "[Id]" { WId }
  | "[ev;" { Wev }
  | "[lambda;" { Wlambda }
  | "[forall;" { Wforall }
  | "Univ" { KUniv }
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
  | '>' '='  { Wgreaterequal }
  | '>' { Wgreater }
  | '<' '='  { Wlessequal }
  | '_' { Wunderscore }
  | '_' (digit | nzdigit digit as n) { Wunderscore_numeral (int_of_string n) }
  | '<' { Wless }
  | ':' '='  { Wcolonequal }
  | '|' '-'  { Wturnstile }
  | '|' '>'  { Wtriangle }
  | digit+ as n { Nat (int_of_string n) }
  | first after* as id { IDENTIFIER id }
  | white { expr_tokens lexbuf }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | _ as c { Printf.fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count();
	     expr_tokens lexbuf }
  | eof { Weof }
and command_flush = parse
  | eof { Weof }
  | newline { command_flush lexbuf }
  | '.' { Wflush }
  | _ { command_flush lexbuf }
