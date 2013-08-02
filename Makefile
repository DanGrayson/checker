# -*- makefile-gmake -*-

all: TAGS
include Makefile-ocaml-rules
include src/Makefile.include
include rules/Makefile.include
include test/Makefile.include
TAGS_FILES = scripts/ts.etags Makefile rules/Makefile.include test/Makefile.include src/Makefile.include
TAGS: $(TAGS_FILES) 
	( scripts/etags.ocaml $(MLSRCFILES) \
	  && \
	  etags --language=none --regex=@scripts/ts.etags $(TAGS_FILES) -o - ) >$@

all: TAGS2
include src2/Makefile.include
TAGS2_FILES = Makefile src2/Makefile.include
TAGS2: $(TAGS2_FILES)
	( scripts/etags.ocaml $(MLSRC2FILES) \
	  && \
	  etags --language=none --regex=@scripts/ts.etags $(TAGS2_FILES) -o - ) >$@

install_dirs = $(prefix)/share/emacs/site-lisp $(prefix)/bin $(prefix)/share/checker

$(install_dirs) :; mkdir -p $@

install: | $(install_dirs)
	cp checker.byte $(prefix)/bin/checker
	cp -a rules test $(prefix)/share/checker/.
	cp -a emacs/*.el $(prefix)/share/emacs/site-lisp/.
