all: TAGS
include src/Makefile.include
include test/Makefile.include
include rules/Makefile.include
TAGS: $(SRCFILES) $(RULES_FILES) $(TSFILES) scripts/ts.etags Makefile
	( scripts/etags.ocaml $(SRCFILES) && etags --regex=@scripts/ts.etags $(RULES_FILES) $(TSFILES) -o - ) >$@
