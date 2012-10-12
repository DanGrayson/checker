{ open SchemeGrammar }

rule main = parse
  | '('  { Tlparen }
  | ')'  { Trparen }
  | '.'  { Tdot }
  | '\'' { Tapost }
  | [ 'a' - 'z' 'A' - 'Z' '0' - '9' '!' '"' '#' '$' '%' '&' '*' '+' ',' '-' '/' ':' '<' '=' 
      '>' '?' '@' '[' '\\' ']' '^' '_' '`' '{' '|' '}' '~' 
    ] + as id { IDENTIFIER id }		(*??*)
  | ';' (_ *) '\n' {}			(*comment*)
