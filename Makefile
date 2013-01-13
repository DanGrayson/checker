all: TAGS
include src/Makefile.include
include test/Makefile.include
include rules/Makefile.include
TAGS: $(SRCFILES) $(RULES_FILES) $(TSFILES) scripts/ts.etags Makefile rules/Makefile.include test/Makefile.include src/Makefile.include
	( scripts/etags.ocaml $(SRCFILES) && etags --regex=@scripts/ts.etags $(RULES_FILES) $(TSFILES) -o - ) >$@
