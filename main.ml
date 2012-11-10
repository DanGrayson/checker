let _ = (
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let _ = Expressions.expr Tokens.main lexbuf in
      Printf.printf "expr found\n";
      flush stdout;
      ()
    done
  with Tokens.Eof ->
    exit 0
  )
