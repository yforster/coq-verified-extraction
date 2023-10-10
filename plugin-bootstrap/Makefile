
all: Makefile.coq
	mkdir -p extraction
	cp ../plugin/extraction/*.ml* extraction
	make -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
