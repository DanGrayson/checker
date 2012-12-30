let _ = (
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let result = SchemeGrammar.expr SchemeLex.main lexbuf in
      let _ = Interp.eval result [] [] in
      Printf.printf "expr found\n";
      ()
    done
  with SchemeLex.Eof ->
    exit 0
  )
