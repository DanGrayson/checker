TSFILES = rules.ts test.ts test2.ts

CHECKER_EXE = checker.byte
BARE_CHECKER = OCAMLRUNPARAM=$(RUN) ./$(CHECKER_EXE)
CHECKER = $(BARE_CHECKER) rules.ts

BFLAGS = -cflags -g,-annot -lflags -g -yaccflag -v -menhir 'menhir --explain'
BFLAGS += -use-menhir

# add -yaccflag --trace to ocamlbuild command line to get the menhir parser to display a trace
# BFLAGS += -yaccflag --trace

# BFLAGS += -verbose 0
SRCFILES =					\
	error.ml				\
	variables.ml \
	typesystem.ml				\
	names.ml				\
	printer.ml				\
	hash.ml					\
	helpers.ml				\
	universe.ml				\
	alpha.ml alpha.mli			\
	substitute.ml				\
	equality.ml equality.mli		\
	tau.ml tau.mli				\
	lfcheck.ml				\
	tactics.ml				\
	definitions.ml				\
	grammar.mly				\
	tokens.mll				\
	toplevel.ml				\
	checker.ml

BASENAMES = $(shell for i in $(patsubst %.mli, %, $(patsubst %.mly, %, $(patsubst %.mll, %, $(patsubst %.ml, %, $(SRCFILES))))) ; do echo $$i ; done | uniq)

# add ,p to get the ocamlyacc parser to display a trace
RUN = -b
# RUN = -b,p

%.cmo: %.ml; ocamlbuild $(BFLAGS) $*.cmo
%.cmo: %.mll; ocamlbuild $(BFLAGS) $*.cmo
%.cmo: %.mly; ocamlbuild $(BFLAGS) $*.cmo

all: TAGS run run2 doc demo
build: $(CHECKER_EXE)
checker.byte checker.native: $(SRCFILES); ocamlbuild $(BFLAGS) $@
doc: checker.odocl $(SRCFILES)
	ocamlbuild $(BFLAGS) $(CHECKER_EXE) checker.docdir/index.html
checker.odocl: Makefile
	for i in $(BASENAMES) ; do echo $$i ; done >$@
clean::; ocamlbuild -clean
TAGS: $(SRCFILES) $(TSFILES) scripts/ts.etags Makefile
	( scripts/etags.ocaml $(SRCFILES) && etags --regex=@scripts/ts.etags $(TSFILES) -o - ) >$@
clean::; rm -f TAGS checker.odocl .DS_Store
lc:; wc -l $(SRCFILES) rules.ts
run:  $(CHECKER_EXE) rules.ts test.ts ; $(CHECKER) test.ts
run2: $(CHECKER_EXE) test2.ts ; $(BARE_CHECKER) test2.ts
demo: $(CHECKER_EXE) rules.ts test.ts ; $(CHECKER) demo.ts
debug:
	ocamlbuild $(BFLAGS) checker.byte 
	@ echo "enter:"
	@ echo "  set arg rules.ts test.ts"
	@ echo "  goto 100"
	@ echo "  break Debugging.trap"
	@ echo "  run"
	ocamldebug -I _build checker.byte 
