# -*- makefile-gmake -*-

all: TAGS
include src/Makefile.include
include rules/Makefile.include
include test/Makefile.include
TAGS: $(SRCFILES) $(RULES_FILES) $(TSFILES) scripts/ts.etags Makefile rules/Makefile.include test/Makefile.include src/Makefile.include
	( scripts/etags.ocaml $(SRCFILES) \
	  && \
	  etags --language=none --regex=@scripts/ts.etags $(RULES_FILES) $(TSFILES) -o - ) >$@



install_dirs = $(prefix)/share/emacs/site-lisp $(prefix)/bin $(prefix)/share/checker

$(install_dirs) :; mkdir -p $@

install: | $(install_dirs)
	cp checker.byte $(prefix)/bin/checker
	cp -a rules test $(prefix)/share/checker/.
	cp -a emacs/*.el $(prefix)/share/emacs/site-lisp/.
