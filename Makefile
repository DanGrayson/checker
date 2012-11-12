# OCFLAGS = -g -annot -warn-error
SRCFILES = basic.ml typesystem.ml substitute.ml printer.ml simpletyping.ml scheme.ml grammar.mly tokens.mll toplevel.ml checker.ml 
all: TAGS run
checker.byte:; ocamlbuild $@
clean::; ocamlbuild -clean
TAGS: $(SRCFILES); ( etags.ocaml $(SRCFILES) && etags test.ts -o - ) >$@
clean::; rm -f TAGS
run: checker.byte; OCAMLRUNPARAM=b ./checker.byte <test.ts
