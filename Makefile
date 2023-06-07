all: coq 

coq: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html

install: install-coq plugin

install-coq: Makefile.coq coq
	+make -f Makefile.coq install

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf

plugin/Makefile: plugin/_CoqProject
	cd plugin && coq_makefile -f _CoqProject -o Makefile

plugin: coq install-coq plugin/Makefile
	cd plugin && ./clean_extraction.sh
	+make -C plugin
	+make -C plugin install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
