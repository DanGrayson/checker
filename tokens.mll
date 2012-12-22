(* -*- coding: utf-8 -*- *)

(** The lexical analyzer for the type theory. *)

{
 open Grammar
 open Variables
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
   string_of_int p.Lexing.pos_lnum ^ ":" ^
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
let space = [ ' ' '\r' ]*
let newline = [ '\n' '\012' ]
let utf8_next       = [ '\128' - '\191' ]
let utf8_first_of_1 = [ '\001' - '\127' ]
let utf8_first_of_2 = [ '\192' - '\223' ]
let utf8_first_of_3 = [ '\224' - '\225' '\227' - '\239' ] (* just guessing that characters starting with \226 \159 are symbols *)

(* Characters starting with \226 \159 seem to be symbols,
   and those starting with \226 \130 include SUBSCRIPT ONE and SUBSCRIPT TWO *)
let utf8_first_2_of_3 = '\226' [ '\128' - '\129' '\131' - '\158' '\160' - '\191' ] 

let utf8_first_of_4 = [ '\240' - '\255' ]
let utf8_1 = utf8_first_of_1
let utf8_2 = utf8_first_of_2 utf8_next
let utf8_3 = utf8_first_of_3 utf8_next utf8_next | utf8_first_2_of_3 utf8_next 
let utf8_4 = utf8_first_of_4 utf8_next utf8_next utf8_next
let utf8_char_nonascii = utf8_2 | utf8_3 | utf8_4
let utf8_char = utf8_1 | utf8_2 | utf8_3 | utf8_4
let utf8_word = utf8_char +
let first = [ 'A'-'Z' 'a'-'z' ] | utf8_char_nonascii
let after = [ 'A'-'Z' 'a'-'z' '0'-'9' '\'' ] | utf8_char_nonascii
let ident = first ( after | '_' first ) *

rule expr_tokens = parse

(* command tokens *)

  | "Check" space "Universes" { CheckUniverses }
  | "LF" { LF }
  | "TS" { TS }
  | "Check" { Check }
  | "Axiom" { Rule }
  | "Alpha" { WAlpha }
  | "Variable" { WVariable }
  | "End" { WEnd }
  | "Show" { WShow }

(* various synonyms of "Theorem" *)

  | "Theorem" { Theorem }
  | "Definition" { Theorem }
  | "Lemma" { Theorem }
  | "Proposition" { Theorem }
  | "Corollary" { Theorem }
  | "Derived" space "Rule" { Theorem }

(* white space, comments *)

  | '\t' { tab lexbuf; expr_tokens lexbuf }
  | space { expr_tokens lexbuf }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | eof { Weof }

(* punctuation *)

  | ":="  { ColonEqual }
  | "::="  { ColonColonEqual }
  | ';'  { Semicolon }
  | ','  { Wcomma }
  | '~'  { Wtilde }
  | '='  { Wequal }
  | ">="  { Wgreaterequal }
  | '>' { Wgreater }
  | "<="  { Wlessequal }
  | '_' { Wunderscore }
  | '<' { Wless }
  | '.'  { Wperiod }
  | '('  { Wlparen }
  | ')'  { Wrparen }
  | ']'  { Wrbracket }
  | '['  { Wlbracket }
  | '}'  { Wrbrace }
  | '{'  { Wlbrace }
  | '*'  { Wstar }			(* for [El] *)
  | '$'  { Wdollar }

(* LF-TS punctuation pairs *)

  | ( "->" | "⟶" ) { Arrow        }
  | ( "=>" | "⇒" ) { DoubleArrow }

  | ( "|->" | "⟼" ) { ArrowFromBar }
  | ( "|=>" | "⟾" ) { DoubleArrowFromBar }

  | '/'       { Slash }

(* TS punctuation *)

  | ':'     { Colon } 

  | ( "|-" | "⊢" ) { Turnstile }

(* tokens common to LF and TS *)

  | "Pi" { KPi }
  | "lambda" { Klambda }
  | "∏" { KPi }
  | "λ" { Klambda }

(* tokens of TS *)

  | "Ulevel" { Ulevel }
  | "Type" { Type }
  | "max" { Kumax }

(* tokens of LF *)

  | "Singleton" { Singleton }
  | "Σ" { KSigma }
  | "Sigma" { KSigma }
  | "×" { Times }
  | "**" { Times }

  | "pair" { Kpair }

  | "₁" { K_1 }
  | "₂" { K_2 }
  | "_1" { K_1 }
  | "_2" { K_2 }

(* variable names *)

  | '[' (ident as id) ']' { CONSTANT id }
  | '[' (ident as id) ';' { CONSTANT_SEMI id }
  | ( nzdigit digit* | '0' ) as n { NUMBER (int_of_string n) } (* eventually check for overflow *)
  | ident as id { IDENTIFIER id }
  | '[' (ident as name) '.' (digit+ as aspect) ']' { VARIABLE (VarDefined(name,int_of_string aspect)) }
  | (ident as name) '$' (digit+ as gen) { VARIABLE (VarGen(int_of_string gen,name)) }

(* invalid characters *)

  | _ as c { Printf.fprintf stderr "%s: invalid character: '%c'\n" (lexing_pos lexbuf) c; 
	     flush stderr ;
	     bump_error_count();
	     expr_tokens lexbuf }


and command_flush = parse
  | eof { Weof }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { command_flush lexbuf }
  | _ { command_flush lexbuf }
