%: %.ml; ocamlc -g -annot $<
%.cmo: %.ml; ocamlc -g -c -annot $<
%.cmi: %.mli; ocamlc -g -c -annot $<
%.ml: %.mll; ocamllex $< -o $@
%.ml: %.mly; ocamlyacc $< && ocamlc -g $*.mli

all : checker doc TAGS
run : checker
	./checker
doc: doc.pdf
doc.pdf: typesystem.ml
	ocamldoc -charset utf8 -notoc -o doc.tex-out -latex $^
	pdflatex doc.tex-out
	pdflatex doc.tex-out
checker: typesystem.cmo
	ocamlc -g -o $@ $^
top: interp.cmo typesystem.cmo schemeGrammar.cmo schemeLex.cmo
	ocaml $^
schemeLex.ml: schemeGrammar.ml
schemeLex.cmo: schemeGrammar.cmo
schemeGrammar.cmo: schemeGrammar.cmi
main.cmo: schemeLex.cmi schemeGrammar.cmi
TAGS: typesystem.ml
	etags.ocaml $^ >$@
clean:
	rm -f *.annot *.cmi *.cmo a.out *-tmp.ml *.aux *.dvi *.log *.out *.pdf *.sty *.toc *.tex-out checker
	rm -f schemeGrammar.mli schemeGrammar.ml schemeLex.ml TAGS
