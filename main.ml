let _ = (
  let lexbuf = Lexing.from_channel stdin in
  while true do
    try
      let _ = Expressions.expr Tokens.main lexbuf in
      Printf.printf "expr found\n"; flush stdout;
      ()
    with 
      Tokens.Eof -> exit 0
    | Parsing.Parse_error -> Printf.fprintf stderr "syntax error\n"; flush stderr
  done
  )
