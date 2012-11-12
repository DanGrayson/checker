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
SRCFILES = basic.ml typesystem.ml substitute.ml printer.ml simpletyping.ml expressions.mly tokens.mll toplevel.ml main.ml 
CMOFILES = $(patsubst %.mly, %.cmo, $(patsubst %.mll, %.cmo, $(patsubst %.ml, %.cmo, $(SRCFILES))))

run : checker
	 OCAMLRUNPARAM=b ./checker <test.ts
all : checker doc TAGS
doc: doc.pdf
doc.pdf: $(SRCFILES)
	ocamldoc -charset utf8 -notoc -o doc.tex-out -latex $(SRCFILES)
	pdflatex doc.tex-out
	pdflatex doc.tex-out
checker: $(CMOFILES)
	ocamlc -g -o $@ $^

expressions.cmi: typesystem.cmo toplevel.cmo
expressions.cmo: expressions.cmi
main.cmo: tokens.cmi expressions.cmi
main.cmo: toplevel.cmo substitute.cmo simpletyping.cmo printer.cmo
main.cmo: toplevel.cmo tokens.cmo substitute.cmo simpletyping.cmo printer.cmo expressions.cmi
main.cmx: toplevel.cmx substitute.cmx simpletyping.cmx printer.cmx
main.cmx: toplevel.cmx tokens.cmx substitute.cmx simpletyping.cmx printer.cmx expressions.cmx
printer.cmo: typesystem.cmo
printer.cmx: typesystem.cmx
simpletyping.cmo: typesystem.cmo substitute.cmo printer.cmo
simpletyping.cmx: typesystem.cmx substitute.cmx printer.cmx
substitute.cmo: typesystem.cmo
substitute.cmx: typesystem.cmx
tokens.cmi: typesystem.cmo
tokens.cmo: expressions.cmo basic.cmo
toplevel.cmo: typesystem.cmo
toplevel.cmx: typesystem.cmx
expressions.cmo: basic.cmo

.PRECIOUS: expressions.ml tokens.ml

TAGS: $(SRCFILES) always
	etags.ocaml $(SRCFILES) >$@
	etags test.ts -o - >>$@
always:
clean:
	rm -f *.annot *.cmi *.cmo a.out *-tmp.ml *.aux *.dvi *.log *.out *.pdf *.sty *.toc *.tex-out checker *.depends
	rm -f expressions.mli expressions.ml tokens.ml TAGS
$(foreach x,$(MLFILES),$(eval include $x.depends)$(eval $x.depends:$x.ml))
