COQBIN?=$(dir $(shell which coqtop))
COQMAKEFILE?=$(COQBIN)coq_makefile
COQMAKEOPTIONS?=
COQMAKEFILEOPTIONS?=

all: Makefile-all.coq
	+$(MAKE) -f $< $(COQMAKEOPTIONS)

%: Makefile-%.coq
	+$(MAKE) -f $< $(COQMAKEOPTIONS)

Makefile-%.coq: Make.%
	$(COQMAKEFILE) $(COQMAKEFILEOPTIONS) -f $< -o $@

install: Makefile-all.coq
	+$(MAKE) -f $< $(COQMAKEOPTIONS) install

install-%: Makefile-%.coq
	+$(MAKE) -f $< $(COQMAKEOPTIONS) install

# Make of individual .vo
%.vo: Makefile-all.coq
	+$(MAKE) -f $< $(COQMAKEOPTIONS) $@

refman-html:
	dune build --no-buffer @refman-html

HEADER=doc/common/styles/html/coqremote/header.html
FOOTER=doc/common/styles/html/coqremote/header.html

stdlib-html: all doc/stdlib/index-list.html
	mkdir -p html
	cp doc/stdlib/depends.png html/
	coqdoc -q -d html --with-header $(HEADER) --with-footer $(FOOTER) --multi-index --html -g -R theories Stdlib $(shell find theories -name "*.v")
	mv html/index.html html/genindex.html
	cat $(HEADER) doc/stdlib/index-list.html $(FOOTER) > html/index.html

doc/stdlib/depends.png: doc/stdlib/depends
	dot -Tpng $< -o $@

doc/stdlib/index-list.html: doc/stdlib/depends.png doc/stdlib/make-library-index doc/stdlib/index-list.html.template doc/stdlib/hidden-files
	doc/stdlib/make-library-index doc/stdlib/index-list.html doc/stdlib/hidden-files
