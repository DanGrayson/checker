(* -*- coding: utf-8 -*- *)

(** The lexical analyzer for the type theory. *)

{
 open Error
 open Grammar
 open Variables
 open Typesystem
 open Printf

 let commands = Hashtbl.create 20
 let _ = List.iter (fun (w,t) -> Hashtbl.add commands w t) [
   "∏", Pi; "λ", Lambda; "Σ", Sigma; "Pi", Pi; "lambda", Lambda; "Ulevel",
   Ulevel; "Type", Type; "max", Kumax; "Singleton", Singleton; "Sigma", Sigma;
   "pair", Kpair; "CAR", K_CAR; "CDR", K_CDR; "Mode", Mode; "Simple", Simple;
   "Relative", Relative; "Pairs", Pairs; "Clear", Clear; "Universes",
   Universes; "LF", LF; "TS", TS; "Check", Check; "Axiom", Axiom; "Alpha",
   Alpha; "Variable", Variable; "End", End; "Include", Include; "Clear", Clear;
   "Show", Show; "Theorem", Theorem; "Definition", Theorem; "Lemma", Theorem;
   "Proposition", Theorem; "Corollary", Theorem ]

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

 let utf8_length id =
   let n = String.length id in
   let ulen = ref 0 in
   for i = 0 to n-1 do
     if id.[i] >= '\192' || id.[i] < '\128' then ulen := !ulen + 1;
   done;
   !ulen

 let utf8_fix lexbuf id =
   let m = String.length id in
   let n = utf8_length id in
   if m != n then (
     let p = lexbuf.Lexing.lex_curr_p in
     let bol = p.Lexing.pos_bol in
     lexbuf.Lexing.lex_curr_p <- { p with Lexing.pos_bol = bol + (m-n) }
     )

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

(* white space, comments *)

  | '\t' { tab lexbuf; expr_tokens lexbuf }
  | space { expr_tokens lexbuf }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { Lexing.new_line lexbuf; expr_tokens lexbuf }
  | eof { EOF }

(* punctuation *)

  | ":="  { ColonEqual }
  | "::="  { ColonColonEqual }
  | ';'  { Semicolon }
  | ','  { Comma }
  | '~'  { Tilde }
  | '='  { Equal }
  | ">="  { GreaterEqual }
  | '>' { Greater }
  | "<="  { LessEqual }
  | '_' { Underscore }
  | '<' { Less }
  | '.'  { Period }
  | '('  { LeftParen }
  | ')'  { RightParen }
  | ']'  { RightBracket }
  | '['  { LeftBracket }
  | '}'  { RightBrace }
  | '{'  { LeftBrace }
  | '*'  { Star }
  | '$'  { Dollar }
  | ':'  { Colon } 
  | "::" { ColonColon }
  | "**" { Times }

(* unicode symbols *)

  | "×" as symb { utf8_fix lexbuf symb; Times }
  | ( "₁" | "_1" ) as symb { utf8_fix lexbuf symb; K_1 }
  | ( "₂" | "_2" ) as symb { utf8_fix lexbuf symb; K_2 }
  | ( "->" | "⟶" ) as symb { utf8_fix lexbuf symb; Arrow }
  | ( "=>" | "⇒" ) as symb { utf8_fix lexbuf symb; DoubleArrow }
  | ( "|->" | "⟼" ) as symb { utf8_fix lexbuf symb; ArrowFromBar }
  | ( "|=>" | "⟾" ) as symb { utf8_fix lexbuf symb; DoubleArrowFromBar }
  | ( "|-" | "⊢" ) as symb { utf8_fix lexbuf symb; Turnstile }
  | ( "|=" | "⊨" ) as symb { utf8_fix lexbuf symb; TurnstileDouble }
  | ( "==" | "≡" ) as symb { utf8_fix lexbuf symb; EqualEqual }

(* variable names, keywords, and commands *)

  | "@[" (ident as id) "]" { utf8_fix lexbuf id; CONSTANT id }
  | "@[" (ident as id) ";" { utf8_fix lexbuf id; CONSTANT_SEMI id }
  | ident as id { utf8_fix lexbuf id; try Hashtbl.find commands id with Not_found -> IDENTIFIER id }
  | (ident as name) '$' (digit+ as gen) { utf8_fix lexbuf name; VARIABLE (VarGen(int_of_string gen,name)) }

(* constants *)

  | ( nzdigit digit* | '0' ) as n { NUMBER (int_of_string n) } (* eventually check for overflow *)
  | '"' ( [ ^ '"' ] * as s ) '"' { STRING s }

(* invalid characters *)

  | _ as c { fprintf stderr "%s: invalid character: '%c'\n%!" (lexing_pos lexbuf) c; 
	     bump_error_count();
	     expr_tokens lexbuf }

and command_flush = parse
  | eof { EOF }
  | '#' [ ^ '\n' ]* { expr_tokens lexbuf }
  | newline { command_flush lexbuf }
  | _ { command_flush lexbuf }

 
(* 
  Local Variables:
  compile-command: "make -C .. src/tokens.cmo "
  End:
 *)
