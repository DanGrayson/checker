let _ = (
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let result = SchemeGrammar.expr SchemeLex.main lexbuf in
	Printf.printf "expr obtained\n";
	ignore (Interp.eval result [] [])
    done
  with SchemeLex.Eof ->
    exit 0
  )
