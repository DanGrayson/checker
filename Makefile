%: %.ml; ocamlc -annot $<
%.cmo: %.ml; ocamlc -c -annot $<
%.cmi: %.mli; ocamlc -c -annot $<
%.ml: %.mll; ocamllex $< -o $@
%.ml: %.mly; ocamlyacc $< && ocamlc $*.mli

all : checker doc
	echo '( () () (()) . () ) (123 345)' | ./checker
doc: doc.pdf
doc.pdf: typesystem.ml
	ocamldoc -charset utf8 -notoc -o doc.tex-out -latex $^
	pdflatex doc.tex-out
	pdflatex doc.tex-out
checker: typesystem.cmo
	ocamlc -o $@ $^
top: interp.cmo typesystem.cmo schemeGrammar.cmo schemeLex.cmo
	ocaml $^
schemeLex.ml: schemeGrammar.ml
schemeLex.cmo: schemeGrammar.cmo
schemeGrammar.cmo: schemeGrammar.cmi
main.cmo: schemeLex.cmi schemeGrammar.cmi
clean:
	rm -f *.annot *.cmi *.cmo a.out *-tmp.ml *.aux *.dvi *.log *.out *.pdf *.sty *.toc *.tex-out checker
	rm -f schemeGrammar.mli schemeGrammar.ml schemeLex.ml
