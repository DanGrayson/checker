all: TAGS
include src/Makefile.include
include test/Makefile.include
include rules/Makefile.include
TAGS: $(SRCFILES) $(TSFILES) scripts/ts.etags Makefile
	( scripts/etags.ocaml $(SRCFILES) && etags --regex=@scripts/ts.etags $(TSFILES) -o - ) >$@
