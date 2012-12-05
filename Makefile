TSFILES = rules.ts test.ts 

CHECKER_EXE = checker.byte
CHECKER = OCAMLRUNPARAM=$(RUN) ./$(CHECKER_EXE) rules.ts

BFLAGS = -cflags -g,-annot -lflags -g -yaccflag -v
BFLAGS += -use-menhir

# add -yaccflag --trace to ocamlbuild command line to get the menhir parser to display a trace
# BFLAGS += -yaccflag --trace

# BFLAGS += -verbose 0
SRCFILES =					\
	debugging.ml				\
	error.ml				\
	typesystem.ml				\
	hash.ml					\
	helpers.ml				\
	template.ml				\
	universe.ml				\
	alpha.ml alpha.mli			\
	substitute.ml				\
	equality.ml equality.mli		\
	lfcheck.ml				\
	tactics.ml \
	fillin.ml				\
	tau.ml tau.mli				\
	printer.ml				\
	grammar0.ml				\
	grammar.mly				\
	tokens.mll				\
	toplevel.ml				\
	checker.ml

BASENAMES = $(shell for i in $(patsubst %.mli, %, $(patsubst %.mly, %, $(patsubst %.mll, %, $(patsubst %.ml, %, $(SRCFILES))))) ; do echo $$i ; done | uniq)

# add ,p to get the ocamlyacc parser to display a trace
RUN = -b
# RUN = -b,p

%.cmo: %.ml; ocamlbuild $(BFLAGS) $*.cmo

all: TAGS run doc
checker.byte checker.native: $(SRCFILES); ocamlbuild $(BFLAGS) $@
doc: checker.odocl $(SRCFILES)
	ocamlbuild $(BFLAGS) $(CHECKER_EXE) checker.docdir/index.html
checker.odocl: Makefile
	for i in $(BASENAMES) ; do echo $$i ; done >$@
clean::; ocamlbuild -clean
TAGS: $(SRCFILES) $(TSFILES) scripts/ts.etags Makefile
	( scripts/etags.ocaml $(SRCFILES) && etags --regex=@scripts/ts.etags $(TSFILES) -o - ) >$@
clean::; rm -f TAGS checker.odocl .DS_Store
wc:; wc -l $(SRCFILES)
run:  $(CHECKER_EXE) rules.ts test.ts ; -$(CHECKER) test.ts
demo: $(CHECKER_EXE) rules.ts test.ts ; -$(CHECKER) demo.ts
debug:
	ocamlbuild $(BFLAGS) checker.byte 
	@ echo "enter:"
	@ echo "  set arg rules.ts test.ts"
	@ echo "  goto 100"
	@ echo "  break Debugging.trap"
	@ echo "  run"
	ocamldebug -I _build checker.byte 
