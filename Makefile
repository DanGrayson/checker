OCFLAGS = -g -annot -warn-error
OCAMLC = ocamlc -c $(OCFLAGS)
# a strange bug in ocamlc occurs if you put -c after -warn-error
%: %.ml; ocamlc $(OCFLAGS) $<
%.depends: %.ml; ocamldep $< >$@
%.cmo: %.ml; $(OCAMLC) -c $<
%.cmi: %.mli; $(OCAMLC) -c $<
%.ml: %.mll; ocamllex $< -o $@
%.mli %.ml: %.mly; ocamlyacc $<
# these files go in link order, left to right
MLFILES = typesystem printer toplevel substitute simpletyping main
YFILES = expressions
LFILES = tokens
FILES = $(YFILES) $(LFILES) $(MLFILES)
SRCFILES = $(YFILES:=.mly) $(LFILES:=.mll) $(MLFILES:=.ml)

run : checker
	 OCAMLRUNPARAM=b ./checker <test.ts
all : checker doc TAGS
doc: doc.pdf
doc.pdf: $(FILES:=.ml) $(FILES:=.cmi)
	ocamldoc -charset utf8 -notoc -o doc.tex-out -latex $(FILES:=.ml)
	pdflatex doc.tex-out
	pdflatex doc.tex-out
checker: $(FILES:=.cmo)
	ocamlc -g -o $@ $^
tokens.cmo: expressions.cmo
expressions.cmo: expressions.cmi
expressions.cmi: typesystem.cmo toplevel.cmo
tokens.cmi: typesystem.cmo
main.cmo: tokens.cmi expressions.cmi
TAGS: $(SRCFILES)
	etags.ocaml $^ >$@
clean:
	rm -f *.annot *.cmi *.cmo a.out *-tmp.ml *.aux *.dvi *.log *.out *.pdf *.sty *.toc *.tex-out checker *.depends
	rm -f expressions.mli expressions.ml tokens.ml TAGS
$(foreach x,$(MLFILES),$(eval include $x.depends)$(eval $x.depends:$x.ml))
