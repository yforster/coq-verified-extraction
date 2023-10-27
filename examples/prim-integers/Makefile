
test: all
	./run

all:
	coqc append.v
	cp ../../lib/axioms.ml axioms.ml
	ocamlfind opt -package coq-core.kernel -c axioms.ml
	ocamlopt -c append.mli
	malfunction cmx append.mlf
	ocamlfind opt -package coq-core.kernel coqrun.cmxa clib.cmxa kernel.cmxa axioms.cmx append.cmx main.ml -o run

