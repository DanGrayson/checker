{
 open Printf
 open SchemeGrammar
 exception Eof
}

let white = [ '\n' ' ' '\t' '\r' ]
let first = [ 'a'-'z' 'A'-'Z'  '!'  '$'  '%'  '&'  '*'  '/'  ':'  '<'  '='  '>'  '?'  '~'  '_'  '^' ]
let digit = [ '0'-'9' ]
let after = first | [ '0'-'9' '.' '+' '-' ]
rule main = parse
  | '('  { Tlparen }
  | ')'  { Trparen }
  | '\'' { Tapost }
  | '.' { Tdot }
  | '-'? digit* as i { Integer (int_of_string i) }
  | first after* | '+' | '-' | "..." as id { Identifier id }
  | white { main lexbuf }
  | ';' (_ *) '\n' { main lexbuf }
  | _ as c { printf "invalid character: '%c'\n" c; main lexbuf }
  | eof { raise Eof }
