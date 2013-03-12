FILES = interp.ml schemeGrammar.mly schemeLex.mll main.ml
FLAGS = -menhir 'menhir --explain --error-recovery' -use-menhir -cflags -annot
main.native: $(FILES); ocamlbuild $(FLAGS) $@
clean:; ocamlbuild -clean
TAGS:; etags.ocaml $(FILES) >$@
