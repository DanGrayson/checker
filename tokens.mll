{
 open Printf
 open Expressions
 exception Eof
 let lastnewline = ref (-1)
 let linenum = ref 1
 let filename = ref "test.ts"
 let position lexbuf = ( !filename, !linenum, Lexing.lexeme_start lexbuf - !lastnewline )
let curry3 f (a,b,c) = f a b c
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
  | newline { incr linenum ; lastnewline := Lexing.lexeme_start lexbuf ; command_tokens lexbuf }
  | _ as c { curry3 (fprintf stderr "%s:%d:%d: invalid character: '%c'\n") (position lexbuf) c; 
	     flush stderr ;
	     command_tokens lexbuf }
  | eof { raise Eof }
and  expr_tokens = parse
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
  | newline { incr linenum ; lastnewline := Lexing.lexeme_start lexbuf ; expr_tokens lexbuf }
  | _ as c { curry3 (fprintf stderr "%s:%d:%d: invalid character: '%c'\n") (position lexbuf) c; 
	     flush stderr ;
	     expr_tokens lexbuf }
  | eof { raise Eof }
