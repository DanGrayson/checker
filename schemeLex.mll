{ open SchemeGrammar }

rule main = parse
  | '('  { Tlparen }
  | ')'  { Trparen }
  | '.'  { Tdot }
  | '\'' { Tapost }
  | [ 'a' - 'z' 'A' - 'Z' '0' - '9' '!' '"' '#' '$' '%' '&' '*' '+' ',' '-' '/' ':' '<' '=' 
      '>' '?' '@' '[' '\\' ']' '^' '_' '`' '{' '|' '}' '~' 
    ] + { IDENTIFIER }		(*??*)
  | ';' (_ *) '\n' { COMMENT }			(*??*)
