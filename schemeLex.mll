{
 open Printf
 open SchemeGrammar
 exception Eof
}

let white = [ '\n' ' ' '\t' '\r' ]
let first = [ 'a' - 'z' 'A' - 'Z'  '!'  '$'  '%'  '&'  '*'  '/'  ':'  '<'  '='  '>'  '?'  '~'  '_'  '^' ]
let after = first | [ '0' - '9' '.' '+' '-' ]
rule main = parse
  | '('  { Tlparen }
  | ')'  { Trparen }
  | '\'' { Tapost }
  | '.' { Tdot }
  | first (after *) | '+' | '-' | "..." { Identifier (Lexing.lexeme lexbuf) }
  | white + { main lexbuf }
  | ';' (_ *) '\n' { main lexbuf }
  | _ as c		{ printf "invalid character: '%c'\n" c; main lexbuf }
  | eof { raise Eof }
