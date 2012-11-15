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
let digit = [ '0'-'9' ]
let first = [ 'A'-'Z' 'a'-'z' ]
let after = [ 'A'-'Z' 'a'-'z' '0'-'9' '\'' ]
rule expr_tokens = 
parse
  | "oPrint" { WPrint_o }
  | "tPrint" { WPrint_t }
  | "uPrint" { WPrint_u }
  | "Tau" { WTau }
  | "tVariable" { WtVariable }
  | "uVariable" { WuVariable }
  | "tDefinition" { WtDefinition }
  | "oDefinition" { WoDefinition }
  | "Exit" { WExit }
  | "Show" { WShow }
  | "[El]" { WEl }
  | "[U]" { WU }
  | "[u]" { Wu }
  | "[j]" { Wj }
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
  | "Univ" { Kulevel }
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
  | '>' '='  { Wgreaterequal }
  | '>' { Wgreater }
  | '<' '='  { Wlessequal }
  | '_' { Wunderscore }
  | '<' { Wless }
  | ':' '='  { Wcolonequal }
  | '|' '-'  { Wturnstile }
  | '|' '>'  { Wtriangle }
  | digit* as n { Nat (int_of_string n) }
  | first after* as id {
       (* an experiment: *)
       (* if List.mem (TVar id) tc then TVar_token (TVar id) else *)
       Var_token id }
  | white { expr_tokens lexbuf }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | _ as c { Printf.fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count();
	     expr_tokens lexbuf }
  | eof { raise Eof }
and command_flush = parse
  | newline { command_flush lexbuf }
  | '.' { Wflush }
  | _ { command_flush lexbuf }
