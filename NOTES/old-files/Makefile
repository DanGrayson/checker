FILES = interp.ml schemeGrammar.mly schemeLex.mll main.ml
FLAGS = -menhir 'menhir --explain' -use-menhir -cflags -annot
main.native: $(FILES); ocamlbuild $(FLAGS) $@
clean:
	rm -f interptmp.ml interptmp2.ml
	ocamlbuild -clean
TAGS:; etags.ocaml $(FILES) >$@

interptmp.ml: interp.sml
	ln -s interp.sml $@
interptmp2.ml: interptmp.ml
	camlp5 pa_sml.cmo pr_o.cmo $< >$@
interptmp2.cmo: interptmp2.ml
	ocamlbuild $(FLAGS) $@
interptmp.cmo: interptmp.ml
	ocamlc -pp 'camlp5 pa_sml.cmo pr_dump.cmo' $<
