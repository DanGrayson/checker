BFLAGS = -cflags -g,-annot -lflags -g -yaccflag -v
BFLAGS += -use-menhir

# add -yaccflag --trace to ocamlbuild command line to get the menhir parser to display a trace
# BFLAGS += -yaccflag --trace

# BFLAGS += -verbose 0
SRCFILES = 					\
	typesystem.ml				\
	alpha.ml				\
	substitute.ml				\
	fillin.ml				\
	check.ml				\
	tau.ml					\
	printer.ml				\
	grammar.mly				\
	tokens.mll				\
	toplevel.ml				\
	checker.ml

# add ,p to get the ocamlyacc parser to display a trace
RUN = -b
# RUN = -b,p

all: TAGS run
checker.byte checker.native: $(SRCFILES); ocamlbuild $(BFLAGS) $@
clean::; ocamlbuild -clean
TAGS: $(SRCFILES); ( scripts/etags.ocaml $(SRCFILES) && etags test.ts -o - ) >$@
clean::; rm -f TAGS
wc:; wc -l $(SRCFILES) Makefile test.ts
run: checker.byte; OCAMLRUNPARAM=$(RUN) ./$< test.ts
run_nofile: checker.byte; OCAMLRUNPARAM=$(RUN) ./$<
run.native: checker.native; OCAMLRUNPARAM=$(RUN) ./$< <test.ts
