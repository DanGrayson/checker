%: %.ml; ocamlc -g -annot $<
%.depends: %.ml; ocamldep $< >$@
%.cmo: %.ml; ocamlc -g -c -annot $<
%.cmi: %.mli; ocamlc -g -c -annot $<
%.ml: %.mll; ocamllex $< -o $@
%.mli %.ml: %.mly; ocamlyacc $<
MLFILES = typesystem printer main
YFILES = expressions
LFILES = tokens
FILES = $(YFILES) $(LFILES) $(MLFILES)

all : checker doc TAGS
run : checker
	./checker <test.ts
doc: doc.pdf
doc.pdf: $(FILES:=.ml)
	ocamldoc -charset utf8 -notoc -o doc.tex-out -latex $^
	pdflatex doc.tex-out
	pdflatex doc.tex-out
checker: $(FILES:=.cmo)
	ocamlc -g -o $@ $^
tokens.cmo: expressions.cmo
expressions.cmo: expressions.cmi
expressions.cmi: typesystem.cmo
main.cmo: tokens.cmi expressions.cmi
TAGS: typesystem.ml
	etags.ocaml $^ >$@
clean:
	rm -f *.annot *.cmi *.cmo a.out *-tmp.ml *.aux *.dvi *.log *.out *.pdf *.sty *.toc *.tex-out checker *.depends
	rm -f expressions.mli expressions.ml tokens.ml TAGS
$(foreach x,$(MLFILES),$(eval include $x.depends))
