%: %.ml; ocamlc -annot $<
%.cmo: %.ml; ocamlc -c -annot $<
%.cmi: %.mli; ocamlc -c -annot $<
%.ml: %.mll; ocamllex $< -o $@
%.ml: %.mly; ocamlyacc $<
# && rm $*.mli

all : checker
	echo '( () () (()) . () ) (123 345)' | ./checker
checker: interp.cmo typesystem.cmo schemeGrammar.cmo schemeLex.cmo main.cmo
	ocamlc -o $@ $^
top: interp.cmo typesystem.cmo schemeGrammar.cmo schemeLex.cmo
	ocaml $^
schemeLex.ml: schemeGrammar.ml
schemeLex.cmo: schemeGrammar.cmo
schemeGrammar.cmo: schemeGrammar.cmi
main.cmo: schemeLex.cmi schemeGrammar.cmi
clean:; rm -f *.annot *.cmi *.cmo a.out *-tmp.ml schemeGrammar.mli schemeGrammar.ml schemeLex.ml

