%.cmo: %.ml; ocamlc -annot $<
%.ml: %.mll; ocamllex $< -o $@
%.ml: %.mly; ocamlyacc $<

all : interp.cmo typesystem.cmo schemeGrammar.cmo schemeLex.cmo
schemeLex.ml: schemeGrammar.ml
clean:; rm -f *.annot *.cmi *.cmo a.out *-tmp.ml schemeGrammar.mli schemeGrammar.ml schemeLex.ml

