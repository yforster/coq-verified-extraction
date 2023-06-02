all: coq plugin

coq: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html

.PHONY: install plugin
install: install-coq install-plugin

install-plugin: plugin
	+make -C plugin install

install-coq: Makefile.coq
	+make -f Makefile.coq install

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf

plugin/Makefile: plugin/_CoqProject
	cd plugin && coq_makefile -f _CoqProject -o Makefile

plugin: coq install-coq plugin/Makefile
	+make -C plugin

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
