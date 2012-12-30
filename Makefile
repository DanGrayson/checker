SRCFILES =					\
	error.ml				\
	variables.ml				\
	typesystem.ml				\
	names.ml				\
	helpers.ml				\
	printer.ml				\
	hash.ml					\
	universe.ml				\
	alpha.ml alpha.mli			\
	substitute.ml				\
	equality.ml equality.mli		\
	tau.ml tau.mli				\
	lfcheck.ml				\
	tactics.ml				\
	grammar.mly				\
	tokens.mll				\
	toplevel.ml				\
	checker.ml

# CODE = native
CODE = byte

CHECKER_EXE = checker.$(CODE)
CHECKER := OCAMLRUNPARAM=$(RUN) time ./$(CHECKER_EXE)

DEBUG = no
ifeq "$(DEBUG)" "yes"
CHECKER += --debug
CHECKER += --debug
endif

BFLAGS = -cflags -g,-annot -lflags -g -yaccflag -v -menhir 'menhir --explain'
BFLAGS += -use-menhir

# add -yaccflag --trace to ocamlbuild command line to get the menhir parser to display a trace
# BFLAGS += -yaccflag --trace

# BFLAGS += -verbose 0

BASENAMES = $(shell for i in $(patsubst %.mli, %, $(patsubst %.mly, %, $(patsubst %.mll, %, $(patsubst %.ml, %, $(SRCFILES))))) ; do echo $$i ; done | uniq)

# add ,p to get the ocamlyacc parser to display a trace
RUN = -b
# RUN = -b,p

%.cmo: %.ml; ocamlbuild $(BFLAGS) $*.cmo
%.cmo: %.mll; ocamlbuild $(BFLAGS) $*.cmo
%.cmo: %.mly; ocamlbuild $(BFLAGS) $*.cmo
%.cmx: %.ml; ocamlbuild $(BFLAGS) $*.cmx
%.cmx: %.mll; ocamlbuild $(BFLAGS) $*.cmx
%.cmx: %.mly; ocamlbuild $(BFLAGS) $*.cmx

all: TAGS tests doc
include test/Makefile.include

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
lc:; wc -l $(SRCFILES) test/rules.ts
debug:
	ocamlbuild $(BFLAGS) checker.byte 
	@ echo "enter:"
	@ echo "  set arg test/demo.ts"
	@ echo "  goto 10000"
	@ echo "  break Error.trap"
	@ echo "  run"
	ocamldebug -I _build checker.byte 
