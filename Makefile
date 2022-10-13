all: coq plugin

coq: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html

install: Makefile.coq
	+make -f Makefile.coq install

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf

plugin/Makefile: plugin/_CoqProject
	cd plugin && coq_makefile -f _CoqProject -o Makefile

plugin: coq plugin/Makefile
	+make -C plugin

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
