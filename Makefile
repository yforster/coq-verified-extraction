all: coq extraction_plugin extraction_ocaml_ffi extraction_malfunction_ffi plugin bootstrap

extraction_malfunction_ffi:
	cd coq_verified_extraction_malfunction_ffi && dune build && dune install

extraction_ocaml_ffi:
	cd coq_verified_extraction_ocaml_ffi && dune build && dune install

extraction_plugin:
	cd coq_verified_extraction_plugin && dune build && dune install

coq: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html

install: install-coq plugin

install-coq: Makefile.coq coq
	+make -f Makefile.coq install

clean: Makefile.coq plugin/Makefile.coq plugin-bootstrap/Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	cd coq_verified_extraction_malfunction_ffi && dune clean
	cd coq_verified_extraction_ocaml_ffi && dune clean
	cd coq_verified_extraction_plugin && dune clean
	cd plugin && make clean
	cd plugin-bootstrap && make clean

plugin/Makefile.coq: plugin/_CoqProject
	cd plugin && make Makefile.coq

plugin: coq install-coq plugin/Makefile.coq extraction_plugin extraction_ocaml_ffi
	cd plugin && ./clean_extraction.sh
	+make -C plugin
	+make -C plugin install

test: 
	cd plugin/tests && make 

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

plugin-bootstrap/Makefile.coq: plugin-bootstrap/_CoqProject
	cd plugin && make Makefile.coq

bootstrap: coq plugin extraction_plugin extraction_malfunction_ffi
	+make -C plugin-bootstrap -j 1
	cd plugin-bootstrap && make -f Makefile.coq install

.PHONY: extraction_plugin extraction_ocaml_ffi extraction_malfunction_ffi
