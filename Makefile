all: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html

install: Makefile.coq
	+make -f Makefile.coq install

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
